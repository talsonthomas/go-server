#!/usr/bin/env python
"""InMobi URL Redirect Service.

Host header or URL path based redirector and URL shortener.
Copyright (c) 2014. InMobi Technology Services Pvt. Ltd.
"""
import Crypto
from Crypto.Hash import SHA256
from Crypto.Signature import PKCS1_v1_5 as PKCS_v1_5_sign
import base64
import config
import datetime
import json
import jwt
import ldap
import logging
import os
import pymongo
import re
import random
import string
import time
import tornado
import urllib
import urlparse
import x509_to_pubkey
from collections import defaultdict
from tornado.escape import xhtml_escape as escape
from tornado.escape import xhtml_unescape as unescape
from tornado.web import Application
from tornado.web import StaticFileHandler
from tornado.ioloop import IOLoop
from tornado.httpserver import HTTPServer

__author__ = 'sudhakar.bg@inmobi.com (BG Sudhakar)'
__version__ = '1.0'

DB_HOST = 'localhost'
DB_PORT = 27017

# Active Directory server
LDAP_HOST = 'mk-ad-1.mkhoj.com'
LDAP_PORT = 389
SSO_ENDPOINT = 'https://login.corp.inmobi.com/login'
LOGIN_CERT_FILE = '/opt/inmobi/irs/keys/logincert.pem'
LOGIN_PUBKEY_FILE = '/opt/inmobi/irs/keys/loginpubkey.pem'

# Admin user with authorization to arbitrarily reassign/delete short names.
ADMIN_USER = 'urlredirect.admin@inmobi.com'

# List of hostnames this service is known by - checked against incoming
# Host: headers to determine whether the request is for a Host: based redirect.
# An incoming Host: header that matches is considered to be bound for the service
# itself vs. as a redirect lookup key.
SELF_HOSTNAMES = ['localhost', os.uname()[1], 'redirect.corp.inmobi.com', 'go', 'go.corp.inmobi.com']
CANONICAL_HOST = 'go.corp.inmobi.com'

# Some short names are reserved/disallowed (for obvious reasons)
RESERVED_URL_SHORTNAMES = ['favicon.ico', '_app']

# AuthSession cookie expiration is a day, but this can limit validity further.
# Also limits replay by non-browser clients past cookie expiry.
AUTH_SESSION_TIMEOUT = 3600

# Set up logging
LOGFILE = '/var/log/irs/irs.log'

# Set up logging
log = logging.getLogger(__name__)
log.setLevel(logging.INFO)
logfile_handler = logging.handlers.RotatingFileHandler(
    LOGFILE, maxBytes=1048576, backupCount=10)
logfile_handler.setFormatter(
    logging.Formatter('%(asctime)s %(name)s: %(levelname)s: %(message)s'))
log.addHandler(logfile_handler)

# Set up exception handling
class Error(Exception):
    """Base class for exceptions in this module"""
    pass


class IRSError(Error):
    """IRS Errors"""
    pass


class Stats(object):
    '''Maintain and expose in-memory stats counters.

    Singleton class to maintain stats counters.
    Use defaultdict to initialize stats_key values on reference.
    '''
    instance = None
    stats = defaultdict(int)
    def __new__(klass, *args, **kwargs):
        if not Stats.instance:
            Stats.instance = object.__new__(klass, *args, **kwargs)
        return Stats.instance

    def update_stats(self, stats_key, count=1, reset=False):
        if not reset:
            log.debug('Incrementing key %s by count %s' % (stats_key, count))
            Stats.stats[stats_key] += count
        else:
            log.debug('Setting key %s to value %s' % (stats_key, count))
            Stats.stats[stats_key] = count

    def get_stats(self):
        return Stats.stats


class Root(tornado.web.RequestHandler):
    '''Handles requests to root (/).

    This could either be a Host: based redirect request or
    someone just trying to get to the front page of the app.
    Determine which one and handle appropriately.
    '''

    def get(self):
        '''Host based redirect requests should be, well, redirected.
        If this is not a redirect request, send the user along to
        the /_app endpoint, where they probably wanted to go.
        '''
        # Update in-memory stats counters
        stats = Stats().update_stats('total_request_count')
        host = self.request.host
        # Are we one of the hostnames we know ourselves by ?
        if not host in self.application.settings['self_hostnames']:
            # No. Assume it is a Host header based redirect request.
            log.info('Host based redirect request for: %s' % (host))
            redirect_key = host
            # Short name must exist in the database AND must be Host: based
            redirect_entry = shorturls.find_one({'shortname': redirect_key, 'host_header_based_redirect': True})
            if redirect_entry:
               log.info('Redirect entry found for key: %s' % (redirect_key))
               log.info(redirect_entry)
               redirect_url = redirect_entry.get('url', None)
               if redirect_url:
                   # Update stats counter first
                   shorturls.update(
                       {
                           'shortname': redirect_key, 'host_header_based_redirect': True
                       },
                       {
                           '$inc': {'redirect_count': 1} 
                       }
                   )
                   # Update in-memory stats counters
                   stats = Stats().update_stats('redirect_count')
                   # Append the incoming request uri in its entirety to the entry found in the DB.
                   redirect_url = redirect_url + self.request.uri
                   scheme, netloc, path, params, query, fragment = urlparse.urlparse(redirect_url)
                   if netloc.split(':')[0].endswith('.inmobi.com'):
                       # Do 302 server side redirect.
                       self.redirect(redirect_url)
                   else:
                       # Do client side redirect.
                       self.write('<head><meta name="referrer" content="never"><meta http-equiv="refresh" content="0;url=%s"></head>' % escape(redirect_url))
                   return
            else:
               log.info('No redirect entry found for key: %s' % (redirect_key))
            self.set_status(400)
            self.write('Host redirect for %s requested, but %s is not a valid short name<br>' % (escape(redirect_key), escape(redirect_key)))
            self.write('--Your friendly URL redirector service. Brought to you by: ')
            self.write('ops-engg@inmobi.com')
        else:
            # Yes. One of the hostnames we know ourselves by. Send the user
            # to the app. Doing so for requests that come in with a valid but
            # shortened Host: header (e.g,, 'go') avoids cert errors.
            if re.match(r'^(go)(|\.corp\.inmobi\.com)$', self.request.host):
                self.redirect('%s%s%s' % ('https://', CANONICAL_HOST, '/_app/'))
            else:
                self.redirect('/_app/')


class App(tornado.web.RequestHandler):
    '''Handles requests to the app itself (vs. redirect requests)
    
    Handle both GET and POST requests. POST requests are used to create, modify
    generate or search for short URLs. GET renders a page with <form> elements to
    do the above in addition to rendering login/logout status and links.

    Shortened URLs are stored in a Mongo DB collection similar to the following:
    redirect_entry = {
        'shortname': 'y',
        'url': 'http://www.yahoo.com',
        'owner': 'sudhakar.bg@inmobi.com',
        'group': None,
        'created': datetime.datetime.utcnow(),
        'modified': datetime.datetime.utcnow(),
        'host_header_based_redirect': True,
        'redirect_count'': 35
    }
    '''

    def get(self):
        '''Renders the main app page.
        '''
        # Update in-memory stats counters
        stats = Stats()
        stats.update_stats('total_request_count')

        if self.request.protocol == 'http':
            self.redirect('https://' + self.request.host + self.request.uri)
            return

        shorturls = self.application.settings['shorturls']
        host = self.request.headers.get('Host', None)

        # Is the request for one of the hostnames we know ourselves by ?
        if host in self.application.settings['self_hostnames']:

            username = self.get_current_user()
            # 
            if not username:
                # Send the user to the login/sso server to get authenticated.
                sso_endpoint = self.application.settings['sso_endpoint']
                original_uri = '%s%s%s' % ('https://', self.request.host, self.request.uri)
                verification_uri = '%s%s%s' % ('https://', self.request.host, '/_app/login')
                login_redirect = '%s?%s' % (
                sso_endpoint,
                urllib.urlencode(
                    [('redirect_uri', verification_uri),
                     ('orig_uri', original_uri),
                     ('logout', '/_app/logout')]))

                # Redirect to the SSO server for user authentication
                self.redirect(login_redirect)
            else:
                self.render('root.html', username=username, shorturls=shorturls, adminuser=self.application.settings.get('adminuser'))
        else:
            log.info('Something is wrong. Got a request with an incorrect or missing host header.')
            self.set_status(400)
            self.write('Malformed Request. Host: header is either missing or does not belong to this server!')
            return


    def get_current_user(self):
        '''Returns the current authenticated user (cookie based).
        '''
        auth_session = self.get_secure_cookie('AuthSession')
        if not auth_session:
            return None
        else:
            username, timestamp = auth_session.split(':')

        # This helps with non-browser replay of expired cookies.
        if time.time() - float(timestamp) > AUTH_SESSION_TIMEOUT:
            log.info('Auth session for user %s timed out.' % (username))
            return None

        return username

    def post(self):
        '''Create, auto-generate, modify, reassign and search URL redirects.
    
        Form submission based operations are performed, based on the
        'action' parameter. All operations (except search) require auth.
        User is redirected to the login endpoint if request doesn't carry auth.
        '''
        # Update in-memory stats counters
        stats = Stats()
        stats.update_stats('total_request_count')
        if self.request.protocol == 'http':
            self.redirect('https://' + self.request.host + self.request.uri)
            return

        self.check_xsrf_cookie()

        irs = self.application.settings['irs'] # Database
        shorturls = self.application.settings['shorturls'] # Collection
        shortname = self.get_body_argument('shortname', None)
        # Replace underscores in shortnames with hyphen.
        url = self.get_body_argument('url', None)
        action = self.get_body_argument('action', None)
        host_header_based_redirect = self.get_body_argument('hostbasedredirect', 'False')

        if host_header_based_redirect == 'True':
            host_header_based_redirect = True
        else:
            host_header_based_redirect = False

        username = self.get_current_user()

        # All operations except search require user login
        if not username and action != 'search':
            login_url = self.application.settings.get('login_url') 
            redirect_url = login_url
            self.redirect(redirect_url)
            return

        log.info('Request from user %s.' % (username))
        log.info('Request Body: %s' % self.request.body)

        if action == 'create':
            # We need a URL and shortname to work with!
            if not url or not shortname:
               log.info('Both URL and shortname are required! Got URL: %s and shortname: %s' % (url, shortname))
               self.send_error(status_code=400) 
               return

            # This standardizes short urls (to a degree) and enhances findability.
            shortname = shortname.replace('_', '-')

            # Check if the short name entry already exists
            redirect_entry = shorturls.find_one({'shortname': shortname, 'host_header_based_redirect': host_header_based_redirect})
            if redirect_entry:
                self.write('Shortcut <b>%s</b> already exists! Please edit the existing entry.' % (escape(shortname)))
            else:
                if shortname in RESERVED_URL_SHORTNAMES:
                    log.info('Shortcut %s is on the blacklist %s. Refusing to create shortcut!' % (shortname, RESERVED_URL_SHORTNAMES))
                    self.send_error(status_code=400)
                    return
               
                if host_header_based_redirect:
                    log.info('Creating Host: header based redirect. Host: %s URL: %s' %(shortname, url))

                parsed_url = urlparse.urlparse(url)
                if not parsed_url.scheme in ['http', 'https']:
                    log.info('URL target is not a supported protocol.')
                    self.send_error(status_code=400)
                    return

                if parsed_url.netloc in self.application.settings['self_hostnames']:
                    log.info('Target URL seems self referential. Could potentially generate a redirect loop.')
                    self.send_error(status_code=400)
                    return
  
                # Strip the target url of a trailing '/' (if any) so we don't
                # end up with redirects to urls ending in '//'
                #url = url.rstrip('/')
                url = url[:-1] if url.endswith('//') else url

                current_time = datetime.datetime.utcnow()
                shorturls.insert({
                    'shortname': shortname,
                    'url': url,
                    'owner': username,
                    'group': None,
                    'host_header_based_redirect': host_header_based_redirect,
                    'created': current_time,
                    'modified': current_time,
                    'redirect_count': 0
                })
                # Update in-memory stats counters
                stats = Stats()
                stats.update_stats('shortname_count')
                stats.update_stats('distinct_owner_count', len(shorturls.distinct('owner')), reset=True)
                collstats = irs.command('collstats', 'shorturls')
                stats.update_stats('collection_size_bytes', collstats['size'], reset=True)
                log.info('Shortcut %s for %s created.' % (shortname, url))
                self.write('Shortcut <b>%s</b> for URL <b>%s</b> created' % (escape(shortname), escape(url)))
                self.redirect('/_app/')
                return
        elif action == 'generate':
            # We need a URL to work with
            if not url:
               log.info('URL required! Got URL: %s' % (url))
               self.send_error(status_code=400) 
               return

            # Gotta love the ascii art!
            gibberish = ['_']

            # Generate a random 7 character string sequence lower and upper case
            # chars and digits
            # We should be good for (62!)/(55!) short URLs.
            for _ in xrange(7):
                gibberish.append(random.choice(string.ascii_letters + string.digits)) 
            shortname = ''.join(gibberish)

            if shorturls.find_one({'shortname': shortname}):
                self.write('Shortcut <b>%s</b> already exists! Please try again.' % shortname)
            else:
                if shortname in RESERVED_URL_SHORTNAMES:
                    log.info('Shortcut %s is reserved: %s. Refusing to create shortcut!' % (shortname, RESERVED_URL_SHORTNAMES))
                    self.send_error(status_code=400)
                    return

                parsed_url = urlparse.urlparse(url)
                if not parsed_url.scheme in ['http', 'https']:
                    log.info('URL target is not a supported protocol.')
                    self.send_error(status_code=400)
                    return

                if parsed_url.netloc in self.application.settings['self_hostnames']:
                    log.info('Target URL seems self referential. Could potentially generate a redirect loop.')
                    self.send_error(status_code=400)
                    return
  
                # Strip the target url of a trailing '/' (if any) so we don't
                # end up with redirects to urls ending in '//'
                #url = url.rstrip('/')
                url = url[:-1] if url.endswith('//') else url

                current_time = datetime.datetime.utcnow()
                shorturls.insert({
                    'shortname': shortname,
                    'url': url,
                    'owner': username,
                    'group': None,
                    'host_header_based_redirect': False,
                    'created': current_time,
                    'modified': current_time,
                    'redirect_count': 0
                })
                log.info('Shortcut %s for %s created.' % (shortname, url))
                # Update in-memory stats counters
                stats = Stats()
                stats.update_stats('shortname_count')
                stats.update_stats('distinct_owner_count', len(shorturls.distinct('owner')), reset=True)
                collstats = irs.command('collstats', 'shorturls')
                stats.update_stats('collection_size_bytes', collstats['size'], reset=True)
                self.write('Shortcut <b>%s</b> for URL <b>%s</b> created' % (escape(shortname), escape(url)))
                self.redirect('/_app/')
                return
        elif action == 'edit':
            # The shortname hidden form field and the url field is rendered escaped.
            # Need to unescape it now so database lookups with shortname as the key
            # works correctly.
            shortname = unescape(self.get_body_argument('shortname'))
            url = unescape(self.get_body_argument('url'))
            # We need a URL and shortname to work with
            if not url or not shortname:
               log.info('Both URL and shortname are required! Got URL: %s and shortname: %s' % (url, shortname))
               self.send_error(status_code=400) 
               return

            # Find the short name entry to edit
            redirect_entry = shorturls.find_one({'shortname': shortname, 'host_header_based_redirect': host_header_based_redirect})
            if not redirect_entry:
                self.write('Shortcut <b>%s</b> does not exist! Please create it first.' % (escape(shortname)))
            else:
                saved_url = redirect_entry.get('url', None)
                # Check authorization to modify the short name entry
                if username != redirect_entry['owner'] and username != self.application.settings['adminuser']:
                    self.set_status(403)
                    self.write('Shortcut <b>%s</b> is not owned by you! Please contact the owner %s.' % (escape(shortname), escape(redirect_entry['owner'])))
                    return
                else:
                    parsed_url = urlparse.urlparse(url)
                    if not parsed_url.scheme in ['http', 'https']:
                        log.info('URL target is not a supported protocol.')
                        self.send_error(status_code=400)
                        return

                    if parsed_url.netloc in self.application.settings['self_hostnames']:
                        log.info('Target URL seems self referential. Could potentially generate a redirect loop.')
                        self.send_error(status_code=400)
                        return
  
                    # Strip the target url of a trailing '/' (if any) so we don't
                    # end up with redirects to urls ending in '//'
                    #url = url.rstrip('/')
                    url = url[:-1] if url.endswith('//') else url

                    current_time = datetime.datetime.utcnow()
                    shorturls.update(
                        {
                            'shortname': shortname, 'host_header_based_redirect': host_header_based_redirect
                        },
                        {
                            '$set': {'url': url, 'modified': current_time}
                        }
                    )
                    # Update stats
                    collstats = irs.command('collstats', 'shorturls')
                    stats.update_stats('collection_size_bytes', collstats['size'], reset=True)
                    log.info('Shortcut %s edited. Old URL: %s New URL: %s' % (shortname, saved_url, url))
                    self.write('Shortcut <b>%s</b> edited successfully.' % (escape(shortname)))
                    self.redirect('/_app/')
                    return
        elif action == 'search':
            regex = self.get_body_argument('regex', None) 
            self.render('search.html', regex=regex, shorturls=shorturls, username=self.get_current_user())
        elif action == 'delete':
            # The shortname hidden form field is rendered escaped. Unescape it.
            shortname = unescape(shortname)
            redirect_entry = shorturls.find_one({'shortname': shortname, 'host_header_based_redirect': host_header_based_redirect})
            if redirect_entry:
                saved_url = redirect_entry.get('url', None)
                # Check authorization to delete the short name entry
                if username != redirect_entry['owner'] and username != self.application.settings['adminuser']:
                    self.set_status(403)
                    self.write('Shortcut <b>%s</b> is not owned by you! Please contact the owner %s.' % (escape(shortname), escape(redirect_entry['owner'])))
                    return
                shorturls.remove({'shortname': shortname, 'host_header_based_redirect': host_header_based_redirect})
                log.info('Shortcut %s for URL %s deleted.' % (shortname, saved_url))
                # Update in-memory stats counters. Decrement here.
                stats = Stats()
                stats.update_stats('shortname_count', -1)
                stats.update_stats('distinct_owner_count', len(shorturls.distinct('owner')), reset=True)
                collstats = irs.command('collstats', 'shorturls')
                stats.update_stats('collection_size_bytes', collstats['size'], reset=True)
                self.write('Shortcut <b>%s</b> for URL <b>%s</b> deleted' % (escape(shortname), escape(saved_url)))
                self.redirect('/_app/')
                return
            else:
                self.write('Shortcut <b>%s</b> does not exist!' % (escape(shortname)))
        elif action == 'reassign':
            # The shortname hidden form field is rendered escaped. Unescape it.
            shortname = unescape(shortname)
            redirect_entry = shorturls.find_one({'shortname': shortname, 'host_header_based_redirect': host_header_based_redirect})
            newowner = self.get_body_argument('newowner', None)
            if username != redirect_entry['owner'] and username != self.application.settings['adminuser']:
                self.set_status(403)
                self.write('You cannot reassign shortcut <b>%s</b> not owned by you! Please contact the owner %s.' % (escape(shortname), escape(redirect_entry['owner'])))
                return
            else:
                # Should really check if the user exists in LDAP/AD. However
                # AD (by default) does not allow anonymous searches. For now just 
                # make do with a basic regex check for valid userPrincipalName.
                if re.match(r'^[^@]+@inmobi.com$', newowner):
                    current_time = datetime.datetime.utcnow()
                    shorturls.update(
                        {
                            'shortname': shortname, 'host_header_based_redirect': host_header_based_redirect
                        },
                        {
                            '$set': {'owner': newowner, 'modified': current_time}
                        }
                    )
                    stats.update_stats('distinct_owner_count', len(shorturls.distinct('owner')), reset=True)
                    log.info('Ownership of short name %s re-assigned. From: %s -> %s' % (shortname, redirect_entry['owner'], newowner))
                    self.write('Ownership of short name %s re-assigned. From: %s -> %s' % (escape(shortname), escape(redirect_entry['owner']), escape(newowner)))
                    self.redirect('/')
                    return
                else:
                    self.set_status(400)
                    self.write('%s is not a valid user name. Should be first.last@inmobi.com' % (escape(newowner)))
                    return
        else:
            log.debug('Unrecognized action specified: shortname: %s url: %s action: %s' % (shortname, url, action))
            self.send_error(status_code=400)
            return
 

class Redirect(tornado.web.RequestHandler):
    '''Handles redirect requests.

    The bulk of redirect requests to this service are expected to end up here.
    The first component of the request URL path is extracted and used to lookup
    the redirect database for the target URL to redirect to. Host: header based
    requests with a path component end up here.

    For Host: based redirects, append everything after / to the redirect URL.
    For non Host: (i.e., path only) based redirects, the first component of the
    path becomes the shortname lookup key. The rest is simply appended to the
    redirect.
    '''

    def get(self):
        # Update in-memory stats counters
        stats = Stats()
        stats.update_stats('total_request_count')
        redirect_url = '/'
        shorturls = self.application.settings['shorturls']
        path = self.request.path
        path_tokens = path.split('/')

        host_header_based_redirect = False
        host = self.request.headers.get('Host', None)

        if not host:
            # No Host: header in the request. Assume path based redirect.
            host_header_based_redirect = False
        elif host in self.application.settings['self_hostnames']:
            # Host: header is one of our own names. Assume path based redirect.
            host_header_based_redirect = False
        else:
            # Host: header based redirect. User followed a CNAME shortcut to us
            # to get here.
            host_header_based_redirect = True
            log.info('Host based redirect request for: %s' % (host))
            
        if host_header_based_redirect:
            redirect_key = host
            # Short name must exist in the database AND must be Host: based
            redirect_entry = shorturls.find_one({'shortname': redirect_key, 'host_header_based_redirect': True})
            log.info('Redirect entry: %s' % redirect_entry)
        else:
            # Normal URL path based lookup
            redirect_key = path_tokens[1]
            redirect_entry = shorturls.find_one({'shortname': redirect_key, 'host_header_based_redirect': False})

        log.info('Redirect key: %s. Host based: %s' % (redirect_key, host_header_based_redirect))

        # If key does not exist in the DB, redirect to / by default
        if redirect_entry:
            log.info('Redirect entry found for key: %s' % (redirect_key))
            log.info(redirect_entry)
            url = redirect_entry.get('url', None)

            # Append path components from the incoming request to the redirect url.
            # Differs based on whether it is path or host header based redirect.
            if host_header_based_redirect:
                # Append the incoming path component in its entirety for host header based redirects
                redirect_url = url + self.request.uri
            else:
                if len(path_tokens) > 2:
                    # E.g., '/abcd/efgh'
                    # Skip the first request path component. 
                    redirect_url = url + '/'.join(path_tokens[2:]) 
                    if self.request.query:
                        # Query component is present (e.g., /abcd/efgh?ijk=lmn)
                        # Append query string from incoming uri
                        redirect_url = redirect_url + '?' + self.request.query
                else:
                    # Single path component (e.g., /abcd). First path component
                    # is the key. Redirect to URL found in the DB.
                    # Add query component if it exists.
                     redirect_url = url
                     if self.request.query:
                        # Query component is present (e.g., /abcd?efg=hji)
                        # Append query string from incoming uri.
                        redirect_url = redirect_url + '?' + self.request.query
                
        if redirect_url and redirect_url != '/':
            # Update stats counter
            shorturls.update(
                {
                    'shortname': redirect_key, 'host_header_based_redirect': host_header_based_redirect
                },
                {
                    '$inc': {'redirect_count': 1} 
                }
            )
            # Update in-memory stats counters
            stats = Stats()
            stats.update_stats('redirect_count')
        log.info('Redirecting shortname %s to: %s' % (redirect_key, redirect_url))
        # We could do a regular 302 redirect here, but that leaks the Referer
        # header to the target (same as a regular link on a page).
        # We have the opporunity to have this service scrub the Referer header so
        # internal URL namespace is not exposed while following external links.
        # We use the meta name=referrer tag to achieve referrer scrubbing.
        # Note: simply using <meta name=referrer content=never> with a regular
        # 302 redirect does not cut it. The browser simply ignores the 302
        # response body. We need to do a <meta http-equiv=refresh ...> too (a.k.a.
        # client side redirect) for the browser to honor the referrer setting.
        scheme, netloc, path, params, query, fragment = urlparse.urlparse(redirect_url)
        if netloc.split(':')[0].endswith('.inmobi.com'):
            # Do 302 server side redirect.
            self.redirect(redirect_url)
        else:
            # Do client side redirect.
            self.write('<head><meta name="referrer" content="never"><meta http-equiv="refresh" content="0;url=%s"></head>' % escape(redirect_url))
        return
        # TODO(sudhakar.bg): Possible enhancement: Scrub Referer only for
        # non inmobi.com URLs.


class LoginAuth(tornado.web.RequestHandler):
    '''Login authentication handler.

    Serves login form in response to a GET request.
    Process POST'ed login <form> to talk to LDAP to autheticate user.
    If authn succeeds, generate an AuthSession cookie of the form:
    AuthSession=username:timestamp
    encrypted with 'cookie_secret'. The timestamp is additional protection
    against replay by non-browser clients.

    Caveat: Requests needing authentication are mostly POST, so
    unauthenticated requests that get redirected to the login endpoint cannot
    preserve state. This means the original operation has to be retried after
    successful auth.
    '''

    def get(self):

        # Update in-memory stats counters
        stats = Stats()
        stats.update_stats('total_request_count')
        if self.request.protocol == 'http':
            self.redirect('https://' + self.request.host + self.request.uri)
            return

        if not self.request.query:
            self.render('login.html')
        else:
            log.info('Verify URL: %s' % (self.request.uri))
            jwt_param = self.get_query_argument('jwt')

            if not jwt_param:
                self.render('login.html')

            # PyCrypto does not directly support extracting a public key from an
            # X509 cert file. Need to use a low level primitive to extract it.
            # See: https://gist.github.com/piotrbulinski/ba553b21652ea1e9601a
            ####public_key = x509_to_pubkey.get_public_key(LOGIN_CERT_FILE)
            public_key = open(LOGIN_PUBKEY_FILE, 'r').read()  
            try:
                jwt_token = jwt.decode(jwt_param, public_key, verify_expiration=True, algorithms=['RS256'], leeway=10, audience='go.corp.inmobi.com')
            except jwt.ExpiredSignature:
                log.info('Expired signature on JWT %s!' % jwt)
                self.write('SSO Failed!')
                self.send_error(401)
                return
            except jwt.DecodeError:
                log.info('Failed to verify signature on JWT %s!' % jwt)
                self.write('SSO Failed!')
                self.send_error(401)
                return

            username = jwt_token['u']
            auth_realm = jwt_token['realm']
            groups = jwt_token['g']
            timestamp = jwt_token['exp']
            aud = jwt_token['aud']
            orig_uri = jwt_token['orig_uri']
            jti = jwt_token['jti']
            state = jwt_token['state']

            log.info('Verified: user=%s groups=%s auth_realm=%s expiry=%s' % (username, groups, auth_realm, timestamp))

            auth_session = '%s:%s' % (username, time.time())
            self.set_secure_cookie('AuthSession', auth_session, expires_days=1, path='/_app/', secure=True, httponly=True)
            log.info('Redirecting to: %s' % (orig_uri))
            self.redirect(orig_uri)


    def verify_signature(self, token, signature):
        '''Verify token signature using the login server public key.
        '''
        # Replace ' ' with '+'. We get the query argument url_unescaped.
        # And by default, '+' is replaced with a space. Since '+' is a valid
        # base64 char, undo the unescape so we can decode correctly.
        # TODO(sudhakar.bg): Figure out the right thing to do here.
        signature = signature.replace(' ', '+')
        try:
            signature = base64.b64decode(signature)
        except TypeError as e:
            log.info('Unable to b64decode signature: %s' % (e))
        # PyCrypto does not directly support extracting a public key from an
        # X509 cert file. Need to use a low level primitive to extract it.
        # See: https://gist.github.com/piotrbulinski/ba553b21652ea1e9601a
        public_key = x509_to_pubkey.get_public_key(LOGIN_CERT_FILE)

        hash = SHA256.new()
        hash.update(token)

        verifier = PKCS_v1_5_sign.new(public_key)
        verified = verifier.verify(hash, signature)
        return verified


    def post(self):
        '''Local login (non-SSO). Should probably go away at some point.
        '''
        # Update in-memory stats counters
        stats = Stats()
        stats.update_stats('total_request_count')
        if self.request.protocol == 'http':
            self.redirect('https://' + self.request.host + self.request.uri)
            return
        self.check_xsrf_cookie()
        username = self.get_body_argument('username', None)
        password = self.get_body_argument('password', None)

        if not username or not password:
            self.redirect(self.application.settings.get('login_url'))
            return

        if not username.endswith('@inmobi.com'):
            username = username + '@inmobi.com'

        # Check for a well formed AD userPrincipalName
        if not re.match(r'^[^@]+@inmobi.com$', username):
            self.redirect(self.application.settings.get('login_url'))
            return


        l = ldap.ldapobject.SimpleLDAPObject(
            'ldap://%s:%s/' % (
                self.application.settings.get('ldap_server'),
                self.application.settings.get('ldap_port')
                )
            )

        try:
            # Start TLS. <method>_s calls are synchronous.
            l.start_tls_s()

            # Bind with 'username@inmobi.com' as bind DN. This quirkily *works*
            # with Active Directory (vs. the typical fully qualified bind DN)
            # cn=user name string,cn=users,dc=example,dc=com
            l.simple_bind_s(username, password)
        except ldap.LDAPError as e:
            self.set_status(403)
            log.info('Unable to authenticate against LDAP. Error: %s' % e)
            self.write('Unable to authenticate against LDAP. Error: %s' % e)
            return

        # Auth against LDAP succeeded. Construct AuthSession cookie by
        # appending current time.
        auth_session = '%s:%s' % (username, time.time())
        # Scope AuthSession path to /_app/, with httponly and secure properties.
        self.set_secure_cookie('AuthSession', auth_session, expires_days=1, path='/_app/', secure=True, httponly=True)
        log.info('Logged in user: %s' % (username))
        self.redirect('/_app/')


class LogoutAuth(tornado.web.RequestHandler):
    '''Logout handler.

    If user is logged in, clear AuthSession cookie set by us and redirect client
    back to the app page.
    '''

    def get(self):

        # Update in-memory stats counters
        stats = Stats()
        stats.update_stats('total_request_count')
        if self.request.protocol == 'http':
            self.redirect('https://' + self.request.host + self.request.uri)
            return

        username = self.get_current_user()
        if username:
            # WARNING: The clear_cookie() method below to clear cookies
            # doesn't work! (tested on Chrome)
            # Cookies only get cleared correctly if path=/. Why ??? 
            # TODO(sudhakar.bg): Investigate further.
            #self.clear_cookie('AuthSession', path='/_app/')
            #self.clear_all_cookies()
            # So, we set the cookie with expiry in the past as a workaround.  
            self.set_secure_cookie('AuthSession', '', expires_days=-1, path='/_app/', secure=True, httponly=True)
            log.info('Logged out user: %s' % (username))
            self.write('Logged out: %s' % (username))

    def get_current_user(self):
        '''Get current logged in user from the auth_session cookie.
        '''
        auth_session = self.get_secure_cookie('AuthSession')
        if not auth_session:
            return None
        else:
            username, timestamp = auth_session.split(':')
        return username


class ServerStatus(tornado.web.RequestHandler):
    '''Server Status Handler.

    Serve up internal server state as JSON. 
    '''
    def get(self):
        # Update in-memory stats counters
        stats = Stats()
        stats.update_stats('total_request_count')
        stats.update_stats('monitoring_request_count')
        self.write(json.dumps(stats.get_stats()))



# Open a database collection object. Pass it into request handlers via settings.
# settings are globally shared across handlers defined for an application
database_client = pymongo.MongoClient(DB_HOST, DB_PORT)

# Database 'irs' (InMobi Redirect Service)
irs = database_client.irs

#irs.authenticate(config.dbcreds['username'], config.dbcreds['password'])

# Collection (a.k.a. table) 'shorturls' in database 'irs'
shorturls = irs.shorturls

# Configure shortname as an indexed field.
# Sort order does not matter.
# Build index in the background.
irs.shorturls.ensure_index(
    [('shortname', pymongo.TEXT), ('url', pymongo.TEXT), ('owner', pymongo.TEXT)], background=True)

# Initialize stats counter with the number of DB records.
stats = Stats()
stats.update_stats('shortname_count', irs.shorturls.count())
stats.update_stats('distinct_owner_count', len(irs.shorturls.distinct('owner')))

# Get stats (for the 'shorturls' collection) using the Mongo
# 'collStats' command.
collstats = irs.command('collstats', 'shorturls')
stats.update_stats('collection_size_bytes', collstats['size'])

# Generate cookie_secret at startup. Since this is done on the fly, server
# restart will mean previously set cookies will fail to decrypt.
# TODO(sudhakar.bg): Revisit this if it causes major problems.
secret = []
for _ in xrange(48):
    secret.append(random.choice(string.ascii_letters + string.digits)) 
cookie_secret = ''.join(secret)

settings = {
    'version': __version__,
    'login_url': '/_app/login',
    'ldap_server': LDAP_HOST,
    'ldap_port': LDAP_PORT,
    'irs': irs,
    'shorturls': shorturls,
    'adminuser': ADMIN_USER,
    'self_hostnames': SELF_HOSTNAMES,
    'debug': True,
    # TODO(sudhakar.bg): Investigate feasibility of generating runtime cookie_secret
    'cookie_secret': cookie_secret,
    'sso_endpoint': SSO_ENDPOINT
}


# Register URL handlers with the application
app = Application([
    (r'^/$', Root),
    (r'^/(favicon\.ico)', StaticFileHandler, {'path': '/opt/inmobi/irs/static/'}),
    (r'^/_app/login$', LoginAuth),
    (r'^/_app/logout$', LogoutAuth),
    (r'^/_app/server-status$', ServerStatus),
    (r'^/_app/.*$', App),
    (r'^/_app$', App),
    (r'^/.+$', Redirect)
    ], **settings)

# We redirect app requests (including auth) back over SSL.
# Normal URL redirect requests don't require auth and are served
# over plain HTTP.
app_insecure = Application([
    (r'^/$', Root),
    (r'^/(favicon\.ico)', StaticFileHandler, {'path': '/opt/inmobi/irs/static/'}),
    (r'^/_app/login$', LoginAuth),
    (r'^/_app/logout$', LogoutAuth),
    (r'^/_app/server-status$', ServerStatus),
    (r'^/_app/.*$', App),
    (r'^/_app$', App),
    (r'^/.+$', Redirect)
    ], **settings)


if __name__ == '__main__':

    # Serve app requests over SSL
    httpserver_secure = HTTPServer(app, ssl_options = {
        'certfile': '/opt/inmobi/irs/keys/irs.pem',
        'keyfile': '/opt/inmobi/irs/keys/irs-key.pem'
    })
    httpserver_secure.listen(443)

    # Serve redirect requests
    httpserver = HTTPServer(app_insecure)
    httpserver.listen(80)

    IOLoop.instance().start()
