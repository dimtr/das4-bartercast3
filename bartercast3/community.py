try:
    # python 2.7 only...
    from collections import OrderedDict
except ImportError:
    from dispersy.python27_ordereddict import OrderedDict

from json import dumps
from httplib import HTTPConnection
#from random import *
from time import time
from zlib import compress
import math
from .conversion import BarterConversion
from .database import BarterDatabase
from .efforthistory import CYCLE_SIZE, EffortHistory
from .payload import BarterRecordPayload, PingPayload, PongPayload, UploadPayload

from dispersy.authentication import DoubleMemberAuthentication, NoAuthentication, MemberAuthentication
from dispersy.candidate import BootstrapCandidate, WalkCandidate, FIVE_FACTOR
from dispersy.community import Community
from dispersy.conversion import DefaultConversion
from dispersy.destination import CommunityDestination, CandidateDestination
from dispersy.distribution import LastSyncDistribution, DirectDistribution, SyncDistribution
from dispersy.member import Member
from dispersy.message import BatchConfiguration, Message, DropMessage, DelayMessageByProof
from dispersy.requestcache import NumberCache
from dispersy.resolution import PublicResolution, LinearResolution
from dispersy.logger import get_logger
logger = get_logger(__name__)

import numpy as np
import random as pythonrandlib
from scipy.sparse.linalg import eigsh
from scipy import *

from scipy.sparse import *
# generated: Fri Sep 28 11:08:39 2012
# curve: high <<< NID_sect571r1 >>>
# len: 571 bits ~ 144 bytes signature
# pub: 170 3081a7301006072a8648ce3d020106052b810400270381920004007400b944435773b2d2dc63b67eecb7207eeff40edde1351cd03b823adabe92af2e5988a1f8ee363911fec9d71c6442720f6b12598c1f4228c4ec173799597e5a7c9f836bd8b18d06a948d07eba5e31a8e6e442c7a376010532819b479375d6f10f102d2d679762736a5bb13878e38b77bbcd5d9cfba0700da46c033909f8402e4e467cb17f0c55f125b1e4adfef696
# pub-sha1 d32eed7948b3339d5ebc2cee59fcc36a28d7f256
# -----BEGIN PUBLIC KEY-----
# MIGnMBAGByqGSM49AgEGBSuBBAAnA4GSAAQAdAC5RENXc7LS3GO2fuy3IH7v9A7d
# 4TUc0DuCOtq+kq8uWYih+O42ORH+ydccZEJyD2sSWYwfQijE7Bc3mVl+Wnyfg2vY
# sY0GqUjQfrpeMajm5ELHo3YBBTKBm0eTddbxDxAtLWeXYnNqW7E4eOOLd7vNXZz7
# oHANpGwDOQn4QC5ORnyxfwxV8SWx5K3+9pY=
# -----END PUBLIC KEY-----
MASTER_MEMBER_PUBLIC_KEY = "3081a7301006072a8648ce3d020106052b810400270381920004007400b944435773b2d2dc63b67eecb7207eeff40edde1351cd03b823adabe92af2e5988a1f8ee363911fec9d71c6442720f6b12598c1f4228c4ec173799597e5a7c9f836bd8b18d06a948d07eba5e31a8e6e442c7a376010532819b479375d6f10f102d2d679762736a5bb13878e38b77bbcd5d9cfba0700da46c033909f8402e4e467cb17f0c55f125b1e4adfef696".decode("HEX")
MASTER_MEMBER_PUBLIC_KEY_DIGEST = "d32eed7948b3339d5ebc2cee59fcc36a28d7f256".decode("HEX")

def bitcount(l):
    c = 0
    while l:
        if l & 1:
            c += 1
        l >>= 1
    return c

class PingCache(NumberCache):

    @staticmethod
    def create_identifier(number):
        assert isinstance(number, (int, long)), type(number)
        return u"request-cache:ping:%d" % (number,)

    @classmethod
    def create_identifier_from_message(cls, message):
        assert isinstance(message, Message.Implementation), type(message)
        return cls.create_identifier(message.payload.identifier)

    def __init__(self, community, candidate, member):
        super(PingCache, self).__init__(community.request_cache)
        self.community = community
        self.candidate = candidate
        self.member = member

    @property
    def cleanup_delay(self):
        return 0.0

    def on_timeout(self):
        self.community.remove_from_slope(self.member)
        if isinstance(self.candidate, WalkCandidate):
            self.candidate.obsolete(time())

class RecordCandidate(object):
    """
    Container class for a candidate that is on our slope.
    """
    def __init__(self, candidate, callback_id):
        self.candidate = candidate
        self.callback_id = callback_id

class Book(object):
    """
    Container class for all the bookkeeping information per peer.
    """
    def __init__(self, member):
        self.member = member
        self.cycle = 0
        self.effort = None
        self.upload = 0
        self.download = 0

    @property
    def score(self):
        must_go_offline = False
        return self.download - self.upload

class BarterCommunity(Community):
    @classmethod
    def get_master_members(cls, dispersy):
        return [dispersy.get_member(MASTER_MEMBER_PUBLIC_KEY)]

    @classmethod
    def load_community(cls, dispersy, master, **kargs):
        try:
            # test if this community already exists
            classification, = next(dispersy.database.execute(u"SELECT classification FROM community WHERE master = ?", (master.database_id,)))
        except StopIteration:
            # join the community with a new my_member, using a cheap cryptography key
            return cls.join_community(dispersy, master, dispersy.get_new_member(u"NID_secp160r1"), *args, **kargs)
        else:
            if classification == cls.get_classification():
                return super(BarterCommunity, cls).load_community(dispersy, master, **kargs)
            else:
                raise RuntimeError("Unable to load an BarterCommunity that has been killed")

    def __init__(self, dispersy, master, scenario_script):
        logger.info("loading Bartercast community")
        self._scenario_script = scenario_script
        self.log = scenario_script.log
        self._scores={}

        # original walker callbacks (will be set during super(...).__init__)
        self._original_on_introduction_request = None
        self._original_on_introduction_response = None

        super(BarterCommunity, self).__init__(dispersy, master)
        #meta=self.get_meta_message(u"barter-record")
        #meta.distribution.members.add(self._my_member)
        
        # _DATABASE stores all direct observations and indirect hearsay
        self._database = BarterDatabase(self._dispersy)
        self._database.open()

        # _BOOKS cache (reduce _DATABASE access)
        self._books_length = 512
        self._books = OrderedDict()

        # _DOWNLOAD_STATES contains all peers that are currently downloading.  when we determine
        # that a peer is missing, we will update its bandwidth statistics
        self._download_states = dict()
        self._swift_raw_bytes_up = 0
        self._swift_raw_bytes_down = 0

        # _SLOPE contains the promising members as Member:RecordCandidate
        self._slope_length = 10
        self._slope = {}

        # _SIGNATURE_COUNT is the number of members that will be asked to sign
        self._signature_count = 5

        # simple statistics
        self._statistic_incoming_signature_request_success = 0
        self._statistic_outgoing_signature_request = 0
        self._statistic_outgoing_signature_request_success = 0
        self._statistic_outgoing_signature_request_timeout = 0
        self._statistic_member_ordering_fail = 0
        self._statistic_initial_timestamp_fail = 0
        self._statistic_cycle_fail = 0
        self._statistic_cumulative_records_received = 0

        self._has_been_killed = False

        # wait till next time we can create records with the candidates on our slope
        self._pending_callbacks.append(self._dispersy.callback.register(self._periodically_compute_score))

        # setup sync strategy
        strategy = scenario_script.sync_strategy
        if strategy:
            if strategy[0] == "enable_top_n_edge":
                self.enable_top_n_edge(strategy[1], strategy[2])
            if strategy[0] == "enable_top_n_vertex":
                self.enable_top_n_vertex(strategy[1], strategy[2], strategy[3])

    @property
    def dispersy_acceptable_global_time_range(self):
       return 11000
    @property                                       
    def dispersy_sync_bloom_filter_error_rate(self):
        return 0.05
    @property
    def dispersy_sync_bloom_filter_bits(self):
        default = 3*(1500 - 60 - 8 - 51 - self._my_member.signature_length - 21 - 30) * 8
        return default * 2
    def dispersy_claim_sync_bloom_filter(self, request_cache):
       sync = self.dispersy_sync_bloom_filter_strategy()
       if sync:
           time_low, time_high, modulo, offset, bloom_filter = sync
           self.log("sync-bloom", time_low=time_low,time_high=time_high, modulo=modulo, offset=offset,prefix=bloom_filter.prefix, binary=bloom_filter.bytes, functions=bloom_filter.functions)
       else:
           self.log("sync-bloom", time_low=-1, time_high=-1, modulo=-1,offset=-1, prefix=-1, binary="", functions=-1)
       return sync
    
    def dispersy_take_step(self, allow_sync):
       # if not allow_sync:
       #    logger.warning("allow_sync was False, forcing True")
       return self._dispersy.take_step(self, self._scenario_script.enable_sync)

    def _periodically_compute_score(self):
        # who am I?
        self.my_member.database_id

        method = self._scenario_script.rw_intro_strategy
        #method="local_metr"

        yield 5.0 * FIVE_FACTOR
        while True:
            # store all cached bookkeeping
            self.flush_books()

            exception = None
            begin = time()
            try:
                if method=="global_rep":
                        #            # do expensive calculation here
                  
                        # do expensive calculation here
                        self.log("Computation of Reputation... Phase 1: accessing the database ")
                        node = self.my_member.database_id
                        ver = dict(((node, member), download) for member, download in self._database.execute(u"SELECT member,download FROM book"))
                        #weights1 = [peer_number for peer_number, in self._database.execute(u"SELECT download FROM book")]
                        ver4 = dict(((member,node), upload) for member, upload in self._database.execute(u"SELECT member,upload FROM book"))

                        #vera = [node, member for member, download in self._database.execute(u"SELECT member,download FROM book"))
                        neig = [member for member, in self._database.execute(u"SELECT member FROM book")]
                        ver2 = dict(((first, second), upload) for first, second, upload in self._database.execute(u"SELECT first_member,second_member,first_upload  FROM record"))
                        ver3 = dict(((second, first), upload) for first, second, upload in self._database.execute(u"SELECT first_member,second_member,second_upload  FROM record"))

                        comb = dict()
                        comb.update(ver2)
                        comb.update(ver3)
                        comb.update(ver)
                        comb.update(ver4)
                        if comb:
                            members = set()
                            members.update(member_id for member_id, _ in comb.iterkeys())
                            members.update(member_id for _, member_id in comb.iterkeys())
                                                
                            rows=array([member_id for member_id, _ in comb.iterkeys()])
                            cols=array([member_id for _, member_id in comb.iterkeys()])
                            maxid=max(members)+1
                            val =comb.values()
                            val2=np.ones(len(val))

                            X=csr_matrix((array(val2),(rows,cols)),shape=(maxid,maxid),dtype=float)
                            #X.astype(float)
                            #g = Graph()

                            #g.add_vertices(maxid+1)
                            #g.add_edges(ed+ed2)
                            #g.vs["id"]=range(maxid+1)
                            #g.es["weights"]=weightsa
                        
                            #g=g.simplify()
                            #multi_edges=g.es.is_multiple()
                            #g.es[multi_edges].delete()
                            #clust = g.clusters(mode='weak')
                            #lcc = clust.giant()
                            evals_large, evecs_large = eigsh(X, k=2, which='LM')
                            score=np.zeros(len(neig),dtype=float)

                            #logger.info("Computation of eigenvalues %f\n",evals_large)
                            B=csr_matrix.todok(X)
                            k=0
                            for i in neig:
                                 score[k] =B[i,node]*evecs_large[i,0]/(evals_large[0]*evecs_large[node,0]) 
                                 k=k+1
                            #self.log("Computation of Reputation... Phase 3: computing the Reputations", count=len(lcc.es), len_ed=len(ed), len_ed2=len(ed2))
                            #score=lcc.personalized_pagerank(directed=True, damping=0.7, reset_vertices=node, weights=g.es["weights"]) #arpack_options=None)

                            #logger.info("computed scores %f\n",score)
                            self._scores=dict(zip(neig,score))


                if method=="local_rep":
                        # do expensive calculation here
                        self.log("Computation of Reputation... Phase 1: accessing the database ")
                        node = self.my_member.database_id
                        ver = dict(((node, member), download) for member, download in self._database.execute(u"SELECT member,download FROM book"))
                        #weights1 = [peer_number for peer_number, in self._database.execute(u"SELECT download FROM book")]
                        ver4 = dict(((member,node), upload) for member, upload in self._database.execute(u"SELECT member,upload FROM book"))

                        #vera = [node, member for member, download in self._database.execute(u"SELECT member,download FROM book"))
                        neig = [member for member, in self._database.execute(u"SELECT member FROM book")]
                        ver2 = dict(((first, second), upload) for first, second, upload in self._database.execute(u"SELECT first_member,second_member,first_upload  FROM record"))
                        ver3 = dict(((second, first), upload) for first, second, upload in self._database.execute(u"SELECT first_member,second_member,second_upload  FROM record"))

                        comb = dict()
                        comb.update(ver2)
                        comb.update(ver3)
                        comb.update(ver)
                        comb.update(ver4)
                        if comb:
                            members = set()
                            members.update(member_id for member_id, _ in comb.iterkeys())
                            members.update(member_id for _, member_id in comb.iterkeys())
                                                
                            rows=array([member_id for member_id, _ in comb.iterkeys()])
                            cols=array([member_id for _, member_id in comb.iterkeys()])
                            maxid=max(members)+1
                            val =comb.values()
                            val2=np.ones(len(val))
                            X=csr_matrix((array(val2),(rows,cols)),shape=(maxid,maxid),dtype=float)
                            #ver3 = dict(self._database.execute(u"SELECT second_member,second_upload FROM record"))
                            #self.log("Computation of Reputation... Phase 2: constructing the graph", count=len(comb))
                            #ed = [(node, peer_number) for peer_number in ver]
                            #ed2 = zip(ver2, ver3) #[(peer_number1, peer_number2) for peer_number1, peer_number2 in zip(ver2, ver3)]

                            score=np.zeros(len(neig),dtype=float)
                            k=0
                            #B=X.todense()
                            B=csr_matrix.todok(X)
                            for i in neig:
                                score[k] =sum(B[i,:].todense())
                                k=k+1 
                            #weights2 = [peer_number for peer_number, in self._database.execute(u"SELECT second_upload FROM record")]
                            #weightsa = weights1 + weights2
                        
                            #g = Graph()
                            #g.add_vertices(len(members))                 

                            #maxid=max(max(ver+ver2+ver3),node)
 
                            #g.add_vertices(maxid+1)
                            #g.add_edges(comb.iterkeys())
                            #g.vs["id"]=members.iterkeys()
                            #g.es["weights"]=comb.itervalues()
                            #self.log("Computation of Reputation... Phase 1: accessing the database ")
                            #node = self.my_member.database_id
                            #print score
                            #ver = [peer_number for peer_number, in self._database.execute(u"SELECT member FROM book")]
                            #weights = [peer_number for peer_number, in self._database.execute(u"SELECT download FROM book")]
                            #self.log("Computation of Reputation... Phase 2: computing the score", count=len(ver))
                        
                            #scores = g.degree( mode=ALL, loops=True)
                            #scores =g.strength(mode=In, loops=False, weights=g.es["weights"])
                            # score=weights
                        
                        
                            self._scores=dict(zip(neig, score))





                if method=="weights":
                        # do expensive calculation here
                        self.log("Computation of Reputation... Phase 1: accessing the database ")
                        node = self.my_member.database_id
                        ver = dict(((node, member), download) for member, download in self._database.execute(u"SELECT member,download FROM book"))
                        #weights1 = [peer_number for peer_number, in self._database.execute(u"SELECT download FROM book")]
                        ver4 = dict(((member,node), upload) for member, upload in self._database.execute(u"SELECT member,upload FROM book"))

                        #vera = [node, member for member, download in self._database.execute(u"SELECT member,download FROM book"))
                        neig = [member for member, in self._database.execute(u"SELECT member FROM book")]
                        ver2 = dict(((first, second), upload) for first, second, upload in self._database.execute(u"SELECT first_member,second_member,first_upload  FROM record"))
                        ver3 = dict(((second, first), upload) for first, second, upload in self._database.execute(u"SELECT first_member,second_member,second_upload  FROM record"))

                        comb = dict()
                        comb.update(ver2)
                        comb.update(ver3)
                        comb.update(ver)
                        comb.update(ver4)
                        if comb:
	                    members = set()
                            members.update(member_id for member_id, _ in comb.iterkeys())
                            members.update(member_id for _, member_id in comb.iterkeys())

                            rows=array([member_id for member_id, _ in comb.iterkeys()])
                            cols=array([member_id for _, member_id in comb.iterkeys()])
	                    maxid=max(members)+1
	                    val =comb.values()
	                    val2=np.ones(len(val))
                            X=csr_matrix((array(val),(rows,cols)),shape=(maxid,maxid),dtype=float)

                            score=np.zeros(len(neig),dtype=float)
	                    k=0
                            B=csr_matrix.todok(X)
	                    for i in neig:
                                 score[k] =max(B[i,node],B[node,i]) #.todense()
	                         k=k+1 


                            self._scores=dict(zip(neig, score))



                if method=="metr":
                        # do expensive calculation here
                        self.log("Computation of Reputation... Phase 1: accessing the database ")
                        node = self.my_member.database_id
                        ver = dict(((node, member), download) for member, download in self._database.execute(u"SELECT member,download FROM book"))
                        ver4 = dict(((member,node), upload) for member, upload in self._database.execute(u"SELECT member,upload FROM book"))

                        neig = [member for member, in self._database.execute(u"SELECT member FROM book")]
                        ver2 = dict(((first, second), upload) for first, second, upload in self._database.execute(u"SELECT first_member,second_member,first_upload  FROM record"))

                        neig = [member for member, in self._database.execute(u"SELECT member FROM book")]
                        ver2 = dict(((first, second), upload) for first, second, upload in self._database.execute(u"SELECT first_member,second_member,first_upload  FROM record"))
                        ver3 = dict(((second, first), upload) for first, second, upload in self._database.execute(u"SELECT first_member,second_member,second_upload  FROM record"))

                        comb = dict()
                        comb.update(ver2)
                        comb.update(ver3)
                        comb.update(ver)
                        comb.update(ver4)
                        if comb:
                              members = set()
                              members.update(member_id for member_id, _ in comb.iterkeys())
                              members.update(member_id for _, member_id in comb.iterkeys())

                              rows=array([member_id for member_id, _ in comb.iterkeys()])
                              cols=array([member_id for _, member_id in comb.iterkeys()])
                              maxid=max(members)+1
                              val =comb.values()
                              val2=np.ones(len(val))
                              X=csr_matrix((array(val2),(rows,cols)),shape=(maxid,maxid),dtype=float)
                              #ver3 = dict(self._database.execute(u"SELECT second_member,second_upload FROM record"))
                              self.log("Computation of Reputation... Phase 2: constructing the graph", count=len(comb))
                              k=0
                              score1=np.zeros(len(neig),dtype=float)
                              #B=X.todense()
                              B=csr_matrix.todok(X)
	                      for i in neig:
                                     score1[k] =sum(B[i,:].todense())
                                     score1[k]=float(score1[k])
                                     k=k+1 

                              deg=float(sum(B[node,:].todense()))

                              score=np.zeros(len(neig)+1)
	                      k=0
                              for i in range(len(neig)):
                                       score[i]=(1/deg)*min(1.0,(score1[i]/deg))

                              score[len(neig)]=1-sum(score[range(len(neig))])

                              neig.append(None)
                              self._scores=dict(zip(neig, score))

            except Exception as exception:
                exception = str(exception)
                logger.exception("%s", exception)

            finally:
                end = time()
                self.log("compute-score", delay=end-begin, exception=exception)

            # wait 60 seconds
            yield 5.0 * FIVE_FACTOR

    @property
    def database(self):
        return self._database

    @property
    def has_been_killed(self):
        return self._has_been_killed

    #this decides the max size of data responded after being contact on a RW
    @property
    def dispersy_sync_response_limit(self):
        return 5 * 1024 *10000 #at most 5kB returned

    @property
    def dispersy_sync_bloom_filter_strategy(self):
        return self._dispersy_claim_sync_bloom_filter_modulo

    def initiate_meta_messages(self):
        return [Message(self, u"barter-record", DoubleMemberAuthentication(allow_signature_func=self.allow_signature_request, encoding="bin"), PublicResolution(), LastSyncDistribution(synchronization_direction=u"RANDOM", priority=128, history_size=1), CommunityDestination(node_count=0), BarterRecordPayload(), self.check_barter_record, self.on_barter_record, batch=BatchConfiguration(2.5 * FIVE_FACTOR)),
                Message(self, u"ping", NoAuthentication(), PublicResolution(), DirectDistribution(), CandidateDestination(), PingPayload(), self.check_ping, self.on_ping),
                Message(self, u"pong", NoAuthentication(), PublicResolution(), DirectDistribution(), CandidateDestination(), PongPayload(), self.check_pong, self.on_pong),
                Message(self, u"upload", NoAuthentication(), PublicResolution(), DirectDistribution(), CandidateDestination(), UploadPayload(), self.check_upload, self.on_upload),
                ]

    def _initialize_meta_messages(self):
        super(BarterCommunity, self)._initialize_meta_messages()

        # replace the callbacks for the dispersy-introduction-request and
        # dispersy-introduction-response messages
        meta = self._meta_messages[u"dispersy-introduction-request"]
        self._original_on_introduction_request = meta.handle_callback
        self._meta_messages[meta.name] = Message(meta.community, meta.name, meta.authentication, meta.resolution, meta.distribution, meta.destination, meta.payload, meta.check_callback, self.on_introduction_request, meta.undo_callback, meta.batch)
        assert self._original_on_introduction_request

        meta = self._meta_messages[u"dispersy-introduction-response"]
        self._original_on_introduction_response = meta.handle_callback
        self._meta_messages[meta.name] = Message(meta.community, meta.name, meta.authentication, meta.resolution, meta.distribution, meta.destination, meta.payload, meta.check_callback, self.on_introduction_response, meta.undo_callback, meta.batch)
        assert self._original_on_introduction_response

    def initiate_conversions(self):
        return [DefaultConversion(self), BarterConversion(self)]

    def dispersy_cleanup_community(self, message):
        self._has_been_killed = True
        # remove all data from the local database
        self._database.cleanup()
        # re-classify to prevent loading
        return super(BarterCommunity, self).dispersy_cleanup_community(message)

    def unload_community(self):
        logger.info("unloading Bartercast community")
        super(BarterCommunity, self).unload_community()

        # cancel outstanding pings
        for record_candidate in self._slope.itervalues():
            self._dispersy.callback.unregister(record_candidate.callback_id)
        self._slope = {}

        # update all up and download values
        self.download_state_callback([])

        # store all cached bookkeeping
        self.flush_books()

        # close database
        self._database.close()

    def get_book(self, member):
        assert self._books_length > 0

        # try cache
        book = self._books.get(member.database_id)
        if not book:
            book = Book(member)

            # fetch from database
            try:
                cycle, effort, upload, download = self._database.execute(u"SELECT cycle, effort, upload, download FROM book WHERE member = ?",
                                                                         (member.database_id,)).next()
            except StopIteration:
                now = time()
                book.cycle = int(now / CYCLE_SIZE)
                book.effort = EffortHistory(now)
            else:
                book.cycle = cycle
                book.effort = EffortHistory(str(effort), float(cycle * CYCLE_SIZE))
                book.upload = upload
                book.download = download

            # store in cache
            self._books[member.database_id] = book
            if len(self._books) > self._books_length:
                _, old = self._books.popitem(False)
                self._database.execute(u"INSERT OR REPLACE INTO book (member, cycle, effort, upload, download) VALUES (?, ?, ?, ?,?)",
                                       (old.member.database_id, old.cycle, buffer(old.effort.bytes), old.upload, old.download))
        return book

    def flush_books(self):
        # store all cached bookkeeping
        self._database.executemany(u"INSERT OR REPLACE INTO book (member, cycle, effort, upload, download) VALUES (?, ?, ?, ?, ?)",
                                   [(book.member.database_id, book.cycle, buffer(book.effort.bytes), book.upload, book.download) for book in self._books.itervalues()])

    def download_state_callback(self, states):
        assert self._dispersy.callback.is_current_thread, "Must be called on the dispersy.callback thread"
        assert isinstance(states, list)
        timestamp = int(time())

        # get all swift downloads that have peers
        active = dict((state.get_download().get_def().get_id(), state)
                      for state
                      in states
                      if state.get_download().get_def().get_def_type() == "swift" and state.get_peerlist())

        # get global up and download for swift
        for state in active.itervalues():
            stats = state.stats["stats"]
            self._swift_raw_bytes_up = stats.rawUpTotal
            self._swift_raw_bytes_down = stats.rawDownTotal

        # OLD is used to determine stopped downloads and peers that left.  NEW will become the next OLD
        old = self._download_states
        new = self._download_states = dict()

        # find downloads that stopped
        for identifier in set(old.iterkeys()).difference(set(active.iterkeys())):
            for ip, (up, down) in old[identifier].iteritems():
                guess = self._get_bandwidth_guess_from_ip(ip)
                guess.timestamp = timestamp
                guess.upload += up
                guess.download += down

        for identifier, state in active.iteritems():
            if identifier in old:
                # find peers that left
                for ip in set(old[identifier]).difference(set(peer["ip"] for peer in state.get_peerlist())):
                    up, down = old[identifier][ip]
                    guess = self._get_bandwidth_guess_from_ip(ip)
                    guess.timestamp = timestamp
                    guess.upload += up
                    guess.download += down

            # set OLD for the next call to DOWNLOAD_STATE_CALLBACK
            new[identifier] = dict((peer["ip"], (peer["utotal"], peer["dtotal"])) for peer in state.get_peerlist() if peer["utotal"] > 0.0 or peer["dtotal"] > 0.0)

    def on_introduction_request(self, messages):
        try:
            return self._original_on_introduction_request(messages)
        finally:
            cycle = int(time() / CYCLE_SIZE)
            for message in messages:
                book = self.get_book(message.authentication.member)
                if book.cycle < cycle:
                    book.cycle = cycle
                    book.effort.set(cycle * CYCLE_SIZE)

    def on_introduction_response(self, messages):
        try:
            return self._original_on_introduction_response(messages)
        finally:
            cycle = int(time() / CYCLE_SIZE)
            for message in messages:
                book = self.get_book(message.authentication.member)
                if book.cycle < cycle:
                    book.cycle = cycle
                    book.effort.set(cycle * CYCLE_SIZE)

    def create_barter_record(self, candidate, second_member):
        """
        Create a dispersy-signature-request that encapsulates an barter-record.
        """
        self._statistic_outgoing_signature_request += 1
        book = self.get_book(second_member)
        upload_first_to_second = book.download
        upload_second_to_first = book.upload
        logger.debug("asking %s to sign effort: %s self->peer:%d peer->self:%d", second_member.mid.encode("HEX"), bin(book.effort.long), upload_first_to_second, upload_second_to_first)
        meta = self.get_meta_message(u"barter-record")

        # 18/12/13 Boudewijn: when peer A and B both want to create records at approximately the
        # same time, and they both claim the same global time, then the code will flag this as
        # malicious behaviour.  we introduce the following hack to prevent this: assuming
        # A.public_key < B.public_key, then A may only claim even global time values and B may only
        # claim uneven global time values.
        global_time = self.claim_global_time()
        if self.my_member.public_key < second_member.public_key:
            # global time must be EVEN
            while global_time % 2 == 1:
                global_time = self.claim_global_time()

        else:
            # global time must be UNEVEN
            while global_time % 2 == 0:
                global_time = self.claim_global_time()

        record = meta.impl(authentication=([self._my_member, second_member],),
                           distribution=(global_time,),
                           payload=(book.cycle, book.effort, upload_first_to_second, upload_second_to_first,
                                    # the following parameters are used for debugging only
                                    time(), time(), book.download, book.upload, 0, 0),
                           sign=False)
        return self.create_dispersy_signature_request(candidate, record, self.on_signature_response,
                                                      success_func=self.on_signature_success)

    def allow_signature_request(self, message):
        """
        A dispersy-signature-request has been received.

        Return None or a Message.Implementation.
        """
        assert message.name == u"barter-record"
        assert not message.authentication.is_signed
        logger.debug("incoming signature request %s %d@%d",
                     message,
                     message.authentication.member.database_id,
                     message.distribution.global_time)

        _, first_member = message.authentication.signed_members[0]
        _, second_member = message.authentication.signed_members[1]

        if not second_member == self._my_member:
            # the first_member is us.  meaning that we will get duplicate global times because
            # someone else claimed the global time for us
            logger.warning("invalid request.  second_member != my_member")
            self._statistic_member_ordering_fail += 1
            return None

        book = self.get_book(first_member)
        proposed_effort = message.payload.effort
        local_effort = book.effort

        if not (message.payload.cycle == proposed_effort.cycle == local_effort.cycle):
            # there is a problem determining the current cycle.  this can be caused by (a)
            # difference in local clock times, (b) record creation during transition between cycles,
            # (c) delay in message processing resulting in issue b.
            logger.warning("invalid request. cycle mismatch (%d ?= %d ?= %d)", message.payload.cycle, proposed_effort.cycle, local_effort.cycle)
            self._statistic_cycle_fail += 1
            return None
        cycle = message.payload.cycle

        if proposed_effort.long ^ local_effort.long:
            # there is a mismatch in bits, this should not occur on the DAS4, however, we will need
            # to repair this once we go into the big bad world
            self.log("record-disagreement", reason="invalid bits", proposed=bin(proposed_effort.long), local=bin(local_effort.long))
            logger.warning("bits mismatch. using AND merge (%s != %s)", bin(proposed_effort.long), bin(local_effort.long))
            # return None

        # merge effort using AND
        effort = EffortHistory(proposed_effort.long & local_effort.long, cycle * CYCLE_SIZE)

        # merge bandwidth using MIN/MAX
        upload_first_to_second = min(message.payload.upload_first_to_second, book.upload)
        upload_second_to_first = max(message.payload.upload_second_to_first, book.download)

        # the first_member took the initiative this cycle.  prevent us from also taking the
        # initiative and create duplicate records this cycle
        self.remove_from_slope(first_member)

        # the following parameters are used for debugging only
        first_timestamp = message.payload.first_timestamp
        second_timestamp = time()
        first_upload = message.payload.first_upload
        first_download = message.payload.first_download
        second_upload = book.download
        second_download = book.upload

        self._statistic_incoming_signature_request_success += 1
        # return the modified barter-record we propose
        meta = self.get_meta_message(u"barter-record")
        return meta.impl(authentication=([first_member, second_member],),
                         distribution=(message.distribution.global_time,),
                         payload=(cycle, effort, upload_first_to_second, upload_second_to_first,
                                  # the following parameters are used for debugging only
                                  first_timestamp, second_timestamp, first_upload, first_download, second_upload, second_download))

    def on_signature_response(self, cache, new_message, changed):
        """
        A dispersy-signature-response has been received.

        Return True or False to either accept or decline the message.
        """
        # TODO: we should ensure that new_message is correct (i.e. all checks made above)

        if new_message:
            self._statistic_outgoing_signature_request_success += 1
            # self._observation(new_message.candidate, cache.members[0], time())

            assert cache.request.payload.message.meta == new_message.meta
            return True

        else:
            self._statistic_outgoing_signature_request_timeout += 1
            self.remove_from_slope(cache.members[0])
            return False

    def on_signature_success(self, cache, new_message):
        """
        A dispersy-signature-response has been accepted.

        NEW_MESSAGE contains the double signed message.  CACHE contains the other participating
        candidates.
        """
        # push the new message to the other peer
        self._dispersy.endpoint.send(cache.candidates, [new_message.packet])

    def _periodically_create_records(self):
        """
        Periodically initiates signature requests with the current optimal peers on self._SLOPE.

        Each cycle is divided into three phases.  The first phase consists of only hill climbing,
        during the second phase signature requests are made at random intervals, and during the
        third phase hill climbing already start for the next phase, although no signature request
        are made.

        |-----------50%-----------|---------40%--------|-10%-|
                                      record creation
        """
        # WINNERS holds the members that have 'won' this cycle
        winners = set()

        while True:
            now = time()
            start_climb = int(now / CYCLE_SIZE) * CYCLE_SIZE
            start_create = start_climb + CYCLE_SIZE * 0.5
            start_idle = start_climb + CYCLE_SIZE * 0.9
            start_next = start_climb + CYCLE_SIZE

            if start_climb <= now < start_create:
                yield start_create - now

            elif start_create <= now < start_idle and len(winners) < self._signature_count:
                logger.debug("c%d  record creation phase.  wait %.2f seconds until record creation", int(now / CYCLE_SIZE), CYCLE_SIZE * 0.4 / self._signature_count)
                yield (CYCLE_SIZE * 0.4 / self._signature_count) * pythonrandlib.random()

                # find the best candidate for this cycle
                score = 0
                winner = None
                for member in self._slope.iterkeys():
                    book = self.get_book(member)
                    if book.score > score and not member in winners:
                        winner = member

                if winner:
                    logger.debug("c%d  attempt record creation %s", int(now / CYCLE_SIZE), winner.mid.encode("HEX"))
                    record_candidate = self._slope[winner]

                    # prevent this winner to 'win' again in this cycle
                    winners.add(winner)

                    # # TODO: this may be and invalid assumption
                    # # assume that the peer is online
                    # record_candidate.history.set(now)

                    self._dispersy.callback.unregister(record_candidate.callback_id)
                    self.create_barter_record(record_candidate.candidate, winner)

                else:
                    logger.debug("c%d  no peers available for record creation (%d peers on slope)", int(now / CYCLE_SIZE), len(self._slope))

            else:
                logger.debug("c%d  second climbing phase.  wait %d seconds until the next phase", int(now / CYCLE_SIZE), start_next - now)
                assert now >= start_idle or len(winners) >= self._signature_count
                for record_candidate in self._slope.itervalues():
                    self._dispersy.callback.unregister(record_candidate.callback_id)
                self._slope = {}
                winners = set()
                yield start_next - now

    def try_adding_to_slope(self, candidate, member):
        if self._scenario_script.enable_hill_climbing and not member in self._slope:
            book = self.get_book(member)
            logger.debug("attempt to add %s with score %d", member, book.score)
            if (book.score > 0 and
                (len(self._slope) < self._slope_length or
                 min(self.get_book(mbr).score for mbr in self._slope.iterkeys()) < book.score)):

                logger.debug("add %s with score %d", member, book.score)
                callback_id = self._dispersy.callback.register(self._ping, (candidate, member), delay=50.0)
                self._slope[member] = RecordCandidate(candidate, callback_id)

                if len(self._slope) > self._slope_length:
                    smallest_member = member
                    smallest_score = book.score

                    for member in self._slope.iterkeys():
                        candidate_book = self.get_book(member)
                        if candidate_book.score < smallest_score:
                            smallest_member = member
                            smallest_score = candidate_book.score

                    self.remove_from_slope(smallest_member)

                return True
        return False

    def remove_from_slope(self, member):
        try:
            record_candidate = self._slope.pop(member)
        except KeyError:
            pass
        else:
            self._dispersy.callback.unregister(record_candidate.callback_id)

    def _ping(self, candidate, member):
        meta = self._meta_messages[u"ping"]
        while True:
            cache = self._request_cache.add(PingCache(self, candidate, member))
            ping = meta.impl(distribution=(self._global_time,), destination=(candidate,), payload=(cache.number, self._my_member))
            self._dispersy.store_update_forward([ping], False, False, True)

            yield 50.0

    def check_ping(self, messages):
        return messages

    def on_ping(self, messages):
        cycle = int(time() / CYCLE_SIZE)
        for message in messages:
            book = self.get_book(message.payload.member)
            if book.cycle < cycle:
                book.cycle = cycle
                book.effort.set(cycle * CYCLE_SIZE)

        meta = self._meta_messages[u"pong"]
        responses = [meta.impl(distribution=(self._global_time,), destination=(ping.candidate,), payload=(ping.payload.identifier, self._my_member)) for ping in messages]
        self._dispersy.store_update_forward(responses, False, False, True)

    def check_pong(self, messages):
        for message in messages:
            if not self._request_cache.has(PingCache.create_identifier_from_message(message)):
                yield DropMessage(message, "invalid response identifier")
                continue

            yield message

    def on_pong(self, messages):
        cycle = int(time() / CYCLE_SIZE)
        for message in messages:
            self._request_cache.pop(PingCache.create_identifier_from_message(message))
            book = self.get_book(message.payload.member)
            if book.cycle < cycle:
                book.cycle = cycle
                book.effort.set(cycle * CYCLE_SIZE)

    def check_barter_record(self, messages):
        # stupidly accept everything...
        return messages

    def on_barter_record(self, messages):
        def ordering(message):
            self.log("barter-record",
                     first_member=message.authentication.members[0].public_key,
                     second_member=message.authentication.members[1].public_key,
                     global_time=message.distribution.global_time,
                     cycle=message.payload.cycle,
                     effort=message.payload.effort.bytes,
                     upload_first_to_second=message.payload.upload_first_to_second,
                     upload_second_to_first=message.payload.upload_second_to_first,
                     # debug only parameters
                     first_timestamp=int(message.payload.first_timestamp),
                     second_timestamp=int(message.payload.second_timestamp),
                     first_upload=message.payload.first_upload,
                     first_download=message.payload.first_download,
                     second_upload=message.payload.second_upload,
                     second_download=message.payload.second_download)

            if message.authentication.members[0].database_id < message.authentication.members[1].database_id:
                return (message.packet_id,
                        message.authentication.members[0].database_id,
                        message.authentication.members[1].database_id,
                        message.distribution.global_time,
                        message.payload.cycle,
                        buffer(message.payload.effort.bytes),
                        message.payload.upload_first_to_second,
                        message.payload.upload_second_to_first,
                        int(message.payload.first_timestamp),
                        int(message.payload.second_timestamp),
                        message.payload.first_upload,
                        message.payload.first_download,
                        message.payload.second_upload,
                        message.payload.second_download)

            else:
                return (message.packet_id,
                        message.authentication.members[1].database_id,
                        message.authentication.members[0].database_id,
                        message.distribution.global_time,
                        message.payload.cycle,
                        buffer(message.payload.effort.bytes),
                        message.payload.upload_second_to_first,
                        message.payload.upload_first_to_second,
                        int(message.payload.second_timestamp),
                        int(message.payload.first_timestamp),
                        message.payload.second_upload,
                        message.payload.second_download,
                        message.payload.first_upload,
                        message.payload.first_download)

        self._statistic_cumulative_records_received += len(messages)
        logger.info("storing %s barter records (%d this session)", len(messages), self._statistic_cumulative_records_received)
        self.log("receive-records", count=len(messages))
        self._database.executemany(u"INSERT OR REPLACE INTO record (sync, first_member, second_member, global_time, cycle, effort, upload_first_to_second, upload_second_to_first, first_timestamp, second_timestamp, first_upload, first_download, second_upload, second_download) VALUES (?, ?, ?, ?, ?, ?, ? ,?, ?, ?, ?, ?, ?, ?)",
                                   (ordering(message) for message in messages))

    def create_upload(self, amount, candidate):
        meta = self.get_meta_message(u"upload")
        upload = meta.impl(distribution=(self._global_time,),
                           destination=(candidate,),
                           payload=(amount, self._my_member))
        self._dispersy.store_update_forward([upload], False, False, True)

    def do_upload_activity(self, peer_number):
        upload_amount = peer_number * 1024

        # all (this is a pythonrandlib.shuffled list)
        candidates = list(self.dispersy_yield_verified_candidates())

        # only upload to one pythonrandlib.candidate
        candidates = candidates[:1]

        for candidate in candidates:
            peer = self._scenario_script.get_peer_from_candidate(candidate)
            member = self._dispersy.get_member(peer.public_key)
            logger.debug("emulating activity with %s.  adding %d bytes to download", member, upload_amount)

            # local book keeping
            book = self.get_book(member)
            book.download += upload_amount
            self.try_adding_to_slope(candidate, member)

            # notify the receiving peer that we uploaded something
            self.create_upload(upload_amount, candidate)

    def check_upload(self, messages):
        # accept everything
        return messages

    def on_upload(self, messages):
        for message in messages:
            book = self.get_book(message.payload.member)
            book.upload += message.payload.amount

    def dispersy_get_introduce_candidate(self, exclude_candidate=None):
        method = self._scenario_script.introduction_strategy
        selection=self._scenario_script.decision_rw

        # malicious peers don't walk and hence do not have anyone in their neighbourhood to
        # introduce.  however, we assume they are all connected and will randomly choose one of the
        # other malicious peers
        #lowest_malicious_peer = 900
        #highest_malicious_peer = 999
        #if lowest_malicious_peer <= self._scenario_script.peer_number <= highest_malicious_peer:
        #    malicious_peer_numbers = range(lowest_malicious_peer, highest_malicious_peer + 1)
        #    malicious_peer_numbers.remove(self._scenario_script.peer_number)
        #    destination_peer_number = choice(malicious_peer_numbers)
        #    peer = self._scenario_script.get_peer_from_number(destination_peer_number)
        #    candidate = WalkCandidate(peer.lan_address, False, peer.lan_address,peer.wan_address,u"unknown")
        #    return candidate

        if method == "local-intro":
            
            def get_score(peer):
                member = self._dispersy.get_member(peer.public_key)
                return self._scores.get(member.database_id, 0.0)

            def intersect(a, b):
                 return list(set(a) & set(b))
            #now=time()
            #candidates=list(self.dispersy_yield_verified_candidates())
            #ver = [peer_number for peer_number, in self._database.execute(u"SELECT member FROM book")]

            try:
                list_member = [self._dispersy.get_member_from_database_id(member_id) for member_id, in self._database.execute(u"SELECT member FROM book")]
                list_peer = [self._scenario_script.get_peer_from_public_key(member.public_key) for member in list_member]
                exclude_peer = self._scenario_script.get_peer_from_candidate(exclude_candidate)

            except RuntimError:
                return None



            def prob_choice(bias):
                randNum = pythonrandlib.random() # in [1,1)
                if sum(bias)>0:
                     sum_mass = 0.0
                     result = 0
                     norm_bias=[ x*(1/sum(bias)) for x in bias]
                     for mass in norm_bias:
                            sum_mass += mass
                            if randNum < sum_mass:
                                return result
                            result+=1
                else:
                     result = int(randNum*len(bias))
                     return result

            #can=[self._scenario_script.get_peer_from_candidate(candidate).peer_number for candidate in candidates]
            #list_cand= intersect(ver,can)
            list_peer.sort(key=lambda peer: peer.peer_number)
      
            if list_peer:
               if selection=="random":
                   index=pythonrandlib.randint(0,(len(list_peer)-1))
               if selection=="scores":
                   peer_scores = [get_score(peer) for peer in list_peer]
                   peer_scores.append(self._scores.get(None, 0.0))
                   index = prob_choice(peer_scores)
                   logger.info("chosen index %d", index)
               if index<len(list_peer):
                   peer = list_peer[index]
                   if exclude_peer.peer_number == peer.peer_number:
                        candidate=None
                        logger.info("node %d cannot introduce a candidate",self._scenario_script.peer_number)
                   else:
                        #candidate = candidates[index_in_can]
                        #candidate=
                        #peer_tuple=self._scenario_script.get_peer_from_public_key(member.public_key)
                        candidate = WalkCandidate(peer.lan_address, False, peer.lan_address,peer.wan_address,u"unknown")

                        logger.info("node %d chooses peer_number:%d;  address:%s", self._scenario_script.peer_number, peer.peer_number, candidate.lan_address)
               else:
                        candidate=None
                        #if self._scenario_script.peer_number in (0, 499):
                        logger.info("node %d choose None", self._scenario_script.peer_number)
       
                        #    peer = list_peer[0] 
                        #else:
                        #    peer  = list_peer[-1]
               
               
            else:
               #except ValueError:
               print "Could not introduce a candidate."
               candidate=None
            #after=time()
            #logger.info("local introduction time equals to %f", after-now)
            return candidate
        if method == "dispersy":
            return super(BarterCommunity, self).dispersy_get_introduce_candidate(exclude_candidate)

        raise RuntimeError("unknown method [%s]" % method)


    def dimitra_dispersy_get_walk_candidate(self):
        """
        Returns a candidate from either the walk, stumble or intro category which is eligible for walking.
        Selects a category based on predifined probabilities.
        """
        # 13/02/12 Boudewijn: normal peers can not be visited multiple times within 30 seconds,
        # bootstrap peers can not be visited multiple times within 55 seconds.  this is handled by
        # the Candidate.is_eligible_for_walk(...) method

        assert all(not sock_address in self._candidates for sock_address in self._dispersy._bootstrap_candidates.iterkeys()), "none of the bootstrap candidates may be in self._candidates"

        from sys import maxint

        now = time()
        categories = [(maxint, None), (maxint, None), (maxint, None)]
        category_sizes = [0, 0, 0]

        for candidate in self._candidates.itervalues():
            if candidate.is_eligible_for_walk(now):
                category = candidate.get_category(now)
                if category == u"walk":
                    categories[0] = min(categories[0], (candidate.last_walk, candidate))
                    category_sizes[0] += 1
                elif category == u"stumble":
                    categories[1] = min(categories[1], (candidate.last_stumble, candidate))
                    category_sizes[1] += 1
                elif category == u"intro":
                    categories[2] = min(categories[2], (candidate.last_intro, candidate))
                    category_sizes[2] += 1

        walk, stumble, intro = [candidate for _, candidate in categories]
        while walk or stumble or intro:
            r = pythonrandlib.random()

            # 13/02/12 Boudewijn: we decrease the 1% chance to contact a bootstrap peer to .5%
            if r <= .4975:  # ~50%
                if walk:
                    logger.debug("returning [%2d:%2d:%2d walk   ] %s", category_sizes[0] , category_sizes[1], category_sizes[2], walk)
                    return walk

            elif r <= .995:  # ~50%
                if stumble or intro:
                    while True:
                        if pythonrandlib.random() <= .5:
                            if stumble:
                                logger.debug("returning [%2d:%2d:%2d stumble] %s", category_sizes[0] , category_sizes[1], category_sizes[2], stumble)
                                return stumble

                        else:
                            if intro:
                                logger.debug("returning [%2d:%2d:%2d intro  ] %s", category_sizes[0] , category_sizes[1], category_sizes[2], intro)
                                return intro

            # else:  # ~.5%
            #     candidate = self._bootstrap_candidates.next()
            #     if candidate:
            #         logger.debug("returning [%2d:%2d:%2d bootstr] %s", category_sizes[0] , category_sizes[1], category_sizes[2], candidate)
            #         return candidate

        bootstrap_candidates = list(self._iter_bootstrap(once=True))
        pythonrandlib.shuffle(bootstrap_candidates)
        for candidate in bootstrap_candidates:
            if candidate:
                logger.debug("returning [%2d:%2d:%2d bootstr] %s", category_sizes[0] , category_sizes[1], category_sizes[2], candidate)
        
        logger.debug("no candidates or bootstrap candidates available")
        return None

    def dispersy_get_walk_candidate(self):
        """
        Return candidate to walk to.
        This function works under two methods
        enter method equal to "probabilistic" or "deterministic"
        1. chance to go to bootstrap node? (IGNORE FOR NOW?)
        2. Dimitra's magic box
        3. fallback to bootstrap node?
        """
        now = time()
        result = None
        method = self._scenario_script.candidate_strategy
        #walk_type="with_restarts"

        def get_score(candidate):
                try:
                    peer = self._scenario_script.get_peer_from_candidate(candidate)
                except:
                    logger.warning("fault in the database: unable to get peer from candidate")
                    return 0.0
                member = self._dispersy.get_member(peer.public_key)
                return self._scores.get(member.database_id, 0.0)
        
        def prob_choice(bias):
                    randNum = pythonrandlib.random() # in [0,1)
                    if sum(bias)>0:
                        sum_mass = 0.0
                        result = 0
                        norm_bias=[ x*(1/sum(bias)) for x in bias]
                        for mass in norm_bias:
                            sum_mass += mass
                            if randNum <= sum_mass:
                                return result
                            result+=1
                    else:
                        result = int(randNum*len(bias))
                        return result
        # use the default Dispersy strategy if neither enable_probabilistic_candidate nor
        # enable_deterministic_candidate is chosen
        if method == "dispersy":
            result = self.dimitra_dispersy_get_walk_candidate()

        # introduction based on the locally compute scores

        if self._scenario_script.enable_following:
            #if walk_type="with_restarts":
            logger.info("start of the RW-following")
        
            # with teleportation probability 0.2
            if pythonrandlib.random() < 0.2:
                self.log("walk-teleport")
                logger.info("teleportation phase with probability 0.2")
                pass


            else: 
                logger.info("RW on process: selection of  the next node")
                candidates = [(candidate.last_intro, candidate)
                              for candidate
                              in self._candidates.itervalues()]
                              # if candidate.is_eligible_for_walk(now, method=method)]
                if candidates:
                    candidates.sort()
                    result = candidates[-1][1]
                    # this must be enabled for churn
                    # if not result.is_eligible_for_walk(now, method="dispersy"):
                    #   result = None

                #logger.info("node %d chooses peer_number:%d", self._scenario_script.peer_number, result.peer_number)
                #if walk_type="early_teminated":
                #    ttl<-0
                #    # with teleportation probability 0.2
                #    if ttl>7:
                #        method = "probabilistic"

                #   else:
                #        candidates = [(candidate.last_intro, candidate) for candidate in self._candidates.itervalues() if candidate.is_eligible_for_walk(now)]
                #           if candidates:
                #               ttl<-ttl+1
                #               candidates.sort()
                #               yield candidates[-1]

        #if method in ("probabilistic", "deterministic"):

            #[(SCORE, CANDIDATE), (SCORE, CANDIDATE), ...]
         #   candidates = [(get_score(candidate), candidate)
         #                 for candidate
         #                 in self._candidates.itervalues()
         #                 if candidate.is_eligible_for_walk(now, method=method)]
         #   if candidates:
                #### Preobabilistic
                # assume sum of bias is 1

         #       if method=="probabilistic":
                    
         #           candidate_index = prob_choice([score for score, candidate in candidates])
         #           result = candidates[candidate_index][1]

        #         if method=="deterministic":
                    # yield candidates in best to worst order
         #           sorted(candidates, reverse=True)
         #           result = candidates[0][1]

        if result is None: 
            logger.info("RW failed: back to the bootstrap nodes ")
            # FALLBACK TO BOOTSTRAP NODES
            #bootstrap_candidates = list(self._iter_bootstrap(once=True))
            #pythonrandlib.shuffle(bootstrap_candidates)
            #for candidate in bootstrap_candidates:
            #    if candidate:
            #        result = candidate
            #        break
            try:
               list_member = [self._dispersy.get_member_from_database_id(member_id) for member_id, in self._database.execute(u"SELECT member FROM book")]
               list_peer = [self._scenario_script.get_peer_from_public_key(member.public_key) for member in list_member]
            except RuntimeError:
               return None
            
            candidates = [WalkCandidate(peer.lan_address, False, peer.lan_address, peer.wan_address, u"unknown")
                          for peer
                          in list_peer]
            candidates = [(get_score(candidate), candidate) for candidate in candidates]       
            if candidates:
                 candidate_index = prob_choice([score for score, candidate in candidates])
                 result = candidates[candidate_index][1]
            #can=[self._scenario_script.get_peer_from_candidate(candidate).peer_number for candidate in candidates]
            #list_cand= intersect(ver,can)
           # list_peer.sort(key=lambda peer: peer.peer_number)
            #if list_peer:
               #index=randint(0,(len(list_cand)-1))
               #member = list_cand[index]
               
             #  if self._scenario_script.peer_number in (0, 499):
             #      peer = list_peer[0] 
             #  else:
             #      peer  = list_peer[-1]
               
                  #candidate = candidates[index_in_can]
                  #candidate=
                  #peer_tuple=self._scenario_script.get_peer_from_public_key(member.public_key)
              # result = WalkCandidate(peer.lan_address, False, peer.lan_address,peer.wan_address,u"unknown")
        #self.log("available-candidates", 
         #        verified=[str(candidate) for candidate in self.dispersy_yield_verified_candidates()], 
         #        unverified=[str(candidate) for candidate in self.dispersy_yield_candidates()])

        if result is None:
            self.log("walk-candidate", strategy=method, lan_address=None, wan_address=None)
            logger.warning("no candidates or bootstrap candidates available")

        else:
            self.log("walk-candidate", strategy=method, lan_address=result.lan_address, wan_address=result.wan_address)

        return result

    def enable_top_n_edge(self, n, method):
        self._top_n = n
        self._top_n_edges = []
        self._top_n_method = method
        self._dispersy.on_sync = self.dispersy_on_sync_top_n_edge
        self._pending_callbacks.append(self._dispersy.callback.register(self._periodically_calculate_top_n_edges))

    def _periodically_calculate_top_n_edges(self):
        # self._database has the record table.  This table has a 'sync' column, this column
        # corresponds with the binary Dispersy packet that must be stored in _top_n_edges.

        topN = self._top_n
        methodTopN = self._top_n_method
        my_member_database_id = self.my_member.database_id

        #two methods
        #1st. return the topN interactions you participated
        #2nd. return your interactions with the topN highly reputed nodes

        def get_score(candidate):
            try:
                peer = self._scenario_script.get_peer_from_candidate(candidate)
            except:
                return 0.0
            member = self._dispersy.get_member(peer.public_key)
            return self._scores.get(member.database_id, 0.0)

        if methodTopN=="Default":
            # for now we will take the most recent N packets from the database.  remove this code when a
            # proper TOP is calculated.
            top = [sync for sync, in self._database.execute(u"SELECT sync FROM record ORDER BY global_time DESC LIMIT ?", (self._top_n,))]

            # convert TOP into _TOP_N_EDGES
            self._top_n_edges = [(global_time, str(packet))
                                 for global_time, packet in (self._dispersy.database.execute(u"SELECT global_time, packet FROM sync WHERE id = ?", (sync,)).next()
                                                             for sync in top)]

        if methodTopN=="simpleTopN":

            #topNcandidates1 = [peer_number for peer_number, in self._database.execute(u"SELECT second_member FROM records WHERE first_member = %d", self.my_member.database_id)]
            topNupload1 = [peer_upload for peer_upload, in self._database.execute(u"SELECT upload_first_to_second FROM records WHERE first_member = %d",  self.my_member.database_id)]
            time1 = [time_stamp for time_stamp, in self._database.execute(u"SELECT global_time FROM records WHERE first_member = %d",  self.my_member.database_id)]
            sync1 = [sync_stamp for sync_stamp, in self._database.execute(u"SELECT sync FROM records WHERE first_member = %d",  self.my_member.database_id)]


            #topNcandidates2 = [peer_number for peer_number, in self._database.execute(u"SELECT first_member FROM records WHERE second_member = = %d",  self.my_member.database_id)]
            topNupload2 = [peer_upload for peer_upload, in self._database.execute(u"SELECT upload_second_to_first FROM records WHERE second_member = %d",  self.my_member.database_id)]
            time2 = [time_stamp for time_stamp, in self._database.execute(u"SELECT global_time FROM records WHERE second_member = %d", self.my_member.database_id)]
            sync2 = [sync_stamp for sync_stamp, in self._database.execute(u"SELECT sync FROM records WHERE second_member = %d",  self.my_member.database_id)]

            tot_time=time1+time2
            min_time=min(tot_time)
            tot_time=[(i+1-min_time) for i in tot_time]

            tot_upload=topNupload1+topNupload2
            tot_score=tot_upload*math.exp(tot_time)
            #[(SCORE, CANDIDATE), (SCORE, CANDIDATE), ...]
            candidates1 = dict(zip(sync1+sync2, tot_score))
            candidates = sorted(candidates1.items(), key=lambda x: x[1], reverse=True)
            top_n_sync = candidates.keys()
            self._top_n_edges  = top_n_sync[0:(topN-1)]

        if methodTopN=="reputation_hop1":

            topNcandidates1 = [peer_number for peer_number, in self._database.execute(u"SELECT second_member FROM records WHERE first_member = %d", self.my_member.database_id)]
            sync1 = [sync_stamp for sync_stamp, in self._database.execute(u"SELECT sync FROM records WHERE first_member = %d", self.my_member.database_id)]

            topNcandidates2 = [peer_number for peer_number, in self._database.execute(u"SELECT first_member FROM records WHERE second_member = = %d", self.my_member.database_id)]
            sync2 = [sync_stamp for sync_stamp, in self._database.execute(u"SELECT sync FROM records WHERE second_member = %d", self.my_member.database_id)]
            #[(SCORE, CANDIDATE), (SCORE, CANDIDATE), ...]
            topNcandidates=topNcandidates1 +topNcandidates2
            score = [get_score(candidate) for candidate in topNcandidates]
            candidates1 = dict(zip(sync1+sync2, score))

            candidates = sorted(candidates1.items(), key=lambda x: x[1], reverse=True)
            top_n_sync = candidates.keys()
            self._top_n_edges  = top_n_sync[0:(topN-1)]

        if methodTopN=="reputation_hops":
            ver2 = [peer_number for peer_number, in self._database.execute(u"SELECT first_member FROM records")]
            ver3 = [peer_number for peer_number, in self._database.execute(u"SELECT second_member FROM records")]
            #ed = [(node, peer_number) for peer_number in ver
            ed2 = zip(ver2, ver3) #[(peer_number1, peer_number2) for peer_number1, peer_number2 in zip(ver2, ver3)]

            sync = [sync_stamp for sync_stamp, in self._database.execute(u"SELECT sync FROM records")]

            #[(SCORE, CANDIDATE), (SCORE, CANDIDATE), ...]
            topNcandidates=ver2+ver3
            score = [get_score(candidate) for candidate in topNcandidates]
            candidates1 = dict(zip(sync, score))
            candidates = sorted(candidates1.items(), key=lambda x: x[1], reverse=True)
            top_n_sync = candidates.keys()
            self._top_n_edges  = top_n_sync[0:(topN-1)]

        if methodTopN=="simpleTopN_hops":
            #ver2 = [peer_number for peer_number, in self._database.execute(u"SELECT first_member FROM records")]
            #ver3 = [peer_number for peer_number, in self._database.execute(u"SELECT second_member FROM records")]
            #ed = [(node, peer_number) for peer_number in ver]
            #ed2 = zip(ver2, ver3) #[(peer_number1, peer_number2) for peer_number1, peer_number2 in zip(ver2, ver3)]
            topNupload = [peer_upload for peer_upload, in self._database.execute(u"SELECT upload_second_to_first FROM records")]
            sync = [sync_stamp for sync_stamp, in self._database.execute(u"SELECT sync FROM records")]

            time1 = [time_stamp for time_stamp, in self._database.execute(u"SELECT global_time FROM records")]
            tot_time=time1
            min_time=min(tot_time)
            tot_time=[(i+1-min_time) for i in tot_time]

            tot_upload=topNupload
            tot_score=tot_upload*math.exp(tot_time)
            #[(SCORE, CANDIDATE), (SCORE, CANDIDATE), ...]
            candidates1 = dict(zip(sync, tot_score))
            candidates = sorted(candidates1.items(), key=lambda x: x[1], reverse=True)
            top_n_sync = candidates.keys()
            self._top_n_edges  = top_n_sync[0:(topN-1)]

    def dispersy_on_sync_top_n_edge(self, messages):
        """
        Overrides Dispersy.on_sync when the scenario script calls: "scenario_enable_top_n_edge 250".
        Requires SELF._TOP_N_EDGES to contain a list with (global_time, packet) tuples.
        """
        for message in messages:
            payload = message.payload

            if payload.sync:
                # we limit the response by byte_limit bytes
                byte_limit = self.dispersy_sync_response_limit

                # 07/05/12 Boudewijn: for an unknown reason values larger than 2^63-1 cause
                # overflow exceptions in the sqlite3 wrapper
                time_low = min(payload.time_low, 2**63-1)
                time_high = min(payload.time_high if payload.has_time_high else self.global_time, 2**63-1)

                offset = long(payload.offset)
                modulo = long(payload.modulo)

                packets = []
                generator = ((packet,)
                             for global_time, packet
                             in self._top_n_edges
                             if (time_low <= global_time <= time_high and
                                 (global_time + offset) % modulo == 0))

                for packet, in payload.bloom_filter.not_filter(generator):
                    packets.append(packet)
                    byte_limit -= len(packet)
                    if byte_limit <= 0:
                        logger.debug("bandwidth throttle")
                        break

                if packets:
                    logger.debug("syncing %d packets (%d bytes) over [%d:%d] selecting (%%%d+%d) to %s",len(packets),
                                 sum(len(packet) for packet in packets),
                                 time_low, time_high, message.payload.modulo, message.payload.offset,
                                 message.candidate)
                    self._dispersy.endpoint.send([message.candidate], packets)

    def enable_top_n_vertex(self, n, distribute, gather):
        self._top_n = n
        self._top_n_distribute = distribute
        self._top_n_gather = gather
        self._top_n_vertexes = set()

        self._dispersy.on_sync = self.dispersy_on_sync_top_n_vertex
        self._pending_callbacks.append(self._dispersy.callback.register(self._periodically_calculate_top_n_vertexes))

    def _periodically_calculate_top_n_vertexes(self):
        # Dimitra: fill TOP with first_member and second_member values from the record table and
        # member values from the book table
        top = set()

        # for now we will take the members from the most recent N packets from the database.  remove
        # this code when a proper TOP is calculated.
        top = set(member for member, in self._database.execute(u"SELECT member FROM book ORDER BY cycle DESC LIMIT ?", (self._top_n,)))
        #

        self._top_n_vertexes = top

    def dispersy_on_sync_top_n_vertex(self, messages):
        """
        Overrides Dispersy.on_sync when the scenario script calls: "scenario_enable_top_n_vertex 250 both".

        Requires SELF._TOP_N_VERTEXES to contain a list or set with member_id's.
        """
        # obtain all available messages for this community        

        meta_messages = [(meta.distribution.priority, -meta.distribution.synchronization_direction_value, meta) for meta in self.get_meta_messages() if isinstance(meta.distribution, SyncDistribution) and meta.distribution.priority > 32]
        meta_messages.sort(reverse = True)
        sub_selects = []
        for _, _, meta in meta_messages:
            sub_selects.append(u"""SELECT * FROM (SELECT sync.packet, double_signed_sync.member1, double_signed_sync.member2 FROM sync
JOIN double_signed_sync ON double_signed_sync.sync = sync.id
WHERE sync.meta_message = %d AND sync.undone = 0 AND sync.global_time BETWEEN ? AND ? AND (sync.global_time + ?) %% ? = 0
ORDER BY RANDOM())""" % (meta.database_id,))

        sql = u"SELECT * FROM ("
        sql += " UNION ALL ".join(sub_selects)
        sql += ")"

        top_n = self._top_n_vertexes
        logger.debug(sql)

        for message in messages:
            payload = message.payload

            if payload.sync:
                # we limit the response by byte_limit bytes
                byte_limit = self.dispersy_sync_response_limit

                # 07/05/12 Boudewijn: for an unknown reason values larger than 2^63-1 cause
                # overflow exceptions in the sqlite3 wrapper
                time_low = min(payload.time_low, 2**63-1)
                time_high = min(payload.time_high if payload.has_time_high else self.global_time, 2**63-1)

                offset = long(payload.offset)
                modulo = long(payload.modulo)

                packets = []
                generator = ((str(packet), member1_id, member2_id)
                             for packet, member1_id, member2_id
                             in self._dispersy.database.execute(sql, (time_low, long(time_high), offset, modulo) * len(sub_selects))
                             if member1_id in top_n or member2_id in top_n)

                for packet, _, _ in payload.bloom_filter.not_filter(generator):
                    packets.append(packet)
                    byte_limit -= len(packet)
                    if byte_limit <= 0:
                        logger.debug("bandwidth throttle")
                        break

                if packets:
                    logger.debug("syncing %d packets (%d bytes) over [%d:%d] selecting (%%%d+%d) to %s",
                                 len(packets),
                                 sum(len(packet) for packet in packets),
                                 time_low, time_high, message.payload.modulo, message.payload.offset,
                                 message.candidate)
                    self._dispersy.endpoint.send([message.candidate], packets)
