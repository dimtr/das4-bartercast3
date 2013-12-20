import time
import sqlite3
import os
import collections
import itertools
import random

from dispersy.logger import get_logger
from dispersy.tests.debugcommunity.node import DebugNode
from dispersy.tool.lencoder import bz2log
from dispersy.tool.scenarioscript import ScenarioScript, ScenarioShareDatabase
from .community import BarterCommunity
logger = get_logger(__name__)

Activity = collections.namedtuple("Activity", ["value", "interval", "slots"])


from dispersy.candidate import WalkCandidate, CANDIDATE_ELIGIBLE_DELAY, CANDIDATE_WALK_LIFETIME, CANDIDATE_STUMBLE_LIFETIME, CANDIDATE_INTRO_LIFETIME
# Dimitra, hack in the METHOD
def is_eligible_for_walk(self, now, method="unknown"):
    assert isinstance(self, WalkCandidate), type(self)
    assert isinstance(now, float), type(now)
    assert isinstance(method, str), type(method)

    if method == "deterministic" or method == "probabilistic":
        OUR_CANDIDATE_ELIGIBLE_DELAY = 0.0
    else:
        OUR_CANDIDATE_ELIGIBLE_DELAY = CANDIDATE_ELIGIBLE_DELAY

    return (self._last_walk + OUR_CANDIDATE_ELIGIBLE_DELAY <= now and
            (self._last_walk + self._timeout_adjustment <= now < self._last_walk + CANDIDATE_WALK_LIFETIME or
             now < self._last_stumble + CANDIDATE_STUMBLE_LIFETIME or
             now < self._last_intro + CANDIDATE_INTRO_LIFETIME))

# use our modded is_eligible_for_walk for these experiments
WalkCandidate.is_eligible_for_walk = is_eligible_for_walk


class BarterScenarioScript(ScenarioScript, ScenarioShareDatabase):
    def __init__(self, *args, **kargs):
        super(BarterScenarioScript, self).__init__(*args, **kargs)
        self._online_beta = None
        self._offline_beta = None
        self._upload_activity = Activity(value=0.0, interval=0.0, slots=0)
        self._sync_strategy = ("dispersy",)
        self._candidate_strategy = "dispersy"
        self._introduction_strategy = "dispersy"
        self._enable_hill_climbing = True # default is enabled
        self._enable_following = False # default is disable
        self._enable_sync = True # default is enabled
        self._decision_rw="random"
        self._rw_strategy="local_rep"

    @property
    def enable_wait_for_wan_address(self):
        return True

    @property
    def my_member_security(self):
        # return u"NID_sect233k1"
        # NID_secp224r1 is approximately 2.5 times faster than NID_sect233k1
        # NID_secp224r1 has 56 byte signatures
        return u"NID_secp224r1"

    @property
    def master_member_public_key(self):
        # SHA1 digest: 4d854cbc14f36f6ef9411a689fc90ce7679f210a
        return "3081a7301006072a8648ce3d020106052b81040027038192000403ecf262a5a0272a5eb84f829866fef8babde34f173f2457d48281b24468ffdde079853a3f39b84b3126b65fa6bfbc07072f12b13c73d964b8a815ac7080c73b80b59419ba7c8ab007d7321c328d90cd49aa044440c825eae78f0dbcd6c7beadea5c5580252f5457f3a7611b22708f355b446c11a3a6f571f2613e408503c14c949b579ef99dd040196836be19bf42bb".decode("HEX")
    @property
    def master_member_private_key(self):
        return "3081ed0201010447c02882be008cee3bfdbfd1b66a948ff915e659558f03df180eee3035e171f797dab9ad20ab1843308f6c0fc598645f52d0a23036cf7c318f1b7f524e2fc701b592eae240eaa8bda00706052b81040027a18195038192000403ecf262a5a0272a5eb84f829866fef8babde34f173f2457d48281b24468ffdde079853a3f39b84b3126b65fa6bfbc07072f12b13c73d964b8a815ac7080c73b80b59419ba7c8ab007d7321c328d90cd49aa044440c825eae78f0dbcd6c7beadea5c5580252f5457f3a7611b22708f355b446c11a3a6f571f2613e408503c14c949b579ef99dd040196836be19bf42bb".decode("HEX")

    @property
    def community_class(self):
        return BarterCommunity

    @property
    def community_kargs(self):
        return {"scenario_script":self}

    def log(self, _message, **kargs):
        bz2log("log", _message, **kargs)

    @property
    def enable_sync(self):
        return self._enable_sync

    def scenario_enable_sync(self):
        self._enable_sync = True

    def scenario_disable_sync(self):
        self._enable_sync = False

    @property
    def candidate_strategy(self):
        return self._candidate_strategy

    def scenario_enable_probabilistic_candidate(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_probabilistic_candidate must be called BEFORE scenario_start")
        self._candidate_strategy = "probabilistic"

    def scenario_enable_deterministic_candidate(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_deterministic_candidate must be called BEFORE scenario_start")
        self._candidate_strategy = "deterministic"

    @property
    def decision_rw(self):
        return self._decision_rw

    def scenario_enable_scores(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_decision_rw must be called BEFORE scenario_start")
        self._decision_rw = "scores"

    def scenario_enable_random(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_decision_rw must be called BEFORE scenario_start")
        self._decision_rw = "random"
    
    @property
    def rw_intro_strategy(self):
        return self._rw_strategy

    def scenario_enable_local_rep(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_local_rep must be called BEFORE scenario_start")
        self._rw_strategy = "local_rep"
    
    def scenario_enable_global_rep(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_global_rep must be called BEFORE scenario_start")
        self._rw_strategy = "global_rep"
    
    def scenario_enable_metr(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_metr must be called BEFORE scenario_start")
        self._rw_strategy = "metr"
    
    def scenario_enable_weights(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_metr must be called BEFORE scenario_start")
        self._rw_strategy = "weights"
    
    @property
    def introduction_strategy(self):
        return self._introduction_strategy

    def scenario_enable_local_intro(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_local_intro must be called BEFORE scenario_start")
        self._introduction_strategy = "local-intro"

    def scenario_enable_deterministic_introduction(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_deterministic_candidate must be called BEFORE scenario_start")
        self._introduction_strategy = "deterministic"

    @property
    def enable_following(self):
        return self._enable_following
    
    def scenario_enable_following(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_follow_introduction must be called BEFORE scenario_start")
        self._enable_following = True

    
    @property
    def enable_hill_climbing(self):
        assert isinstance(self._enable_hill_climbing, bool), type(self._enable_hill_climbing)
        return self._enable_hill_climbing

    def scenario_enable_hill_climbing(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_hill_climbing must be called BEFORE scenario_start")
        self._enable_hill_climbing = True

    def scenario_disable_hill_climbing(self):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_hill_climbing must be called BEFORE scenario_start")
        self._enable_hill_climbing = False

    @property
    def sync_strategy(self):
        return self._sync_strategy

    def scenario_enable_top_n_edge(self, n, method):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_top_n_edge must be called BEFORE scenario_start")
        self._sync_strategy = ("enable_top_n_edge", int(n), method)

    def scenario_enable_top_n_vertex(self, n, method):
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_enable_top_n_vertex must be called BEFORE scenario_start")

        distribute = method == "both" or method == "distribute"
        gather = method == "both" or method == "gather"
        if not (distribute or gather):
            raise RuntimeError("scenario_enable_top_n_vertex requires METHOD to be: 'distribute', 'gather', or 'both'")
        self._sync_strategy = ("enable_top_n_vertex", int(n), distribute, gather)

    def scenario_upload_activity_from_database(self, filepath, runtime): # begin="0", end="0", multiplier="1.0"):
        db = sqlite3.connect(os.path.join(self._kargs["localcodedir"], filepath))
        cur = db.cursor()
        maxpeerid1, maxpeerid2, mintime, maxtime = next(cur.execute(u"SELECT MAX(interactions.first_peer_number), MAX(interactions.second_peer_number), MIN(interactions.time), MAX(interactions.time) FROM interactions"))
        maxpeerid = int(max(maxpeerid1, maxpeerid2))

        # begin = int(begin)
        # end = int(end) if int(end) > 0 else maxtime
        # multiplier = float(multiplier)
        minutes, seconds = runtime.split(":")
        runtime = int(minutes) * 60 + int(seconds)
        multiplier = 1.0 * runtime/(maxtime - mintime)
        peernumber = int(self._kargs["peernumber"])
        startstamp = time.time() #float(self._kargs["startstamp"])

        # activity = [((timestamp - mintime - begin) * multiplier + startstamp, int(peer2), int(upload))
        activity = [((timestamp - mintime) * multiplier + startstamp, int(peer2), int(upload))
                    for timestamp, peer2, upload
                    in cur.execute(u"SELECT time, second_peer_number, upload_first_to_second FROM interactions WHERE first_peer_number = ? ORDER BY time",
                                   (peernumber,))]
        #logger.warning("MULTIPLIER:%.2f ACTIVITY:%s", multiplier, [tup[0] - startstamp for tup in activity])

        if activity:
            self._dispersy.callback.register(self._scenario_upload_activity_from_database_helper, (activity,))
        else:
            self.log("scenario-upload-activity", state="fail", reason="no activity found in database")

    def _scenario_upload_activity_from_database_helper(self, activity):
        for timestamp, destination_peer, upload_activity in activity:
            delay = max(0.0, timestamp - time.time())
            logger.debug("will upload %d bytes to peer %d in %.2f seconds", upload_activity, destination_peer, delay)
            yield delay

            community = self.has_community()
            if community:
                peer = self.get_peer_from_number(destination_peer)
                candidate = community.get_candidate(peer.lan_address)
                if not candidate:
                    # did not yet meet this peer
                    candidate = community.create_candidate(peer.lan_address, False, peer.lan_address, peer.wan_address, u"unknown")

                self._do_upload_activity(candidate, upload_activity)

            else:
                self.log("scenario-upload-activity", state="fail", reason="can not upload when offline")

    def scenario_upload_activity(self, value, interval, slots):
        """
        Set how active the peer is.  VALUE bytes in upload are divided amount SLOTS peers every
        INTERVAL seconds.
        """
        self._upload_activity = Activity(value=float(value), interval=float(interval), slots=int(slots))
        self._dispersy.callback.replace_register(u"scenario-script-upload-activity", self._scenario_upload_activity_helper)

    def _scenario_upload_activity_helper(self):
        while True:
            yield self._upload_activity.interval

            community = self.has_community()
            if community:

                candidates = [candidate for candidate in itertools.islice(community.dispersy_yield_verified_candidates(), self._upload_activity.slots) if candidate]
                if candidates:

                    upload_per_candidate = int(self._upload_activity.value / len(candidates))
                    for candidate in candidates:
                        self._do_upload_activity(candidate, upload_per_candidate)

            else:
                self.log("scenario-upload-activity", state="fail", reason="can not upload when offline")

    def _do_upload_activity(self, candidate, upload_activity):
        community = self.has_community()
        if community:
            peer = self.get_peer_from_candidate(candidate)
            member = self._dispersy.get_member(peer.public_key)
            logger.debug("emulating activity with %s.  adding %d bytes to download", member, upload_activity)

            # local book keeping
            book = community.get_book(member)
            book.download += upload_activity
            community.try_adding_to_slope(candidate, member)

            # notify the receiving peer that we uploaded something
            self.log("scenario-upload-activity", state="success", destination_peer_number=peer.peer_number, activity=upload_activity)
            community.create_upload(upload_activity, candidate)

            # immediately create a barter record for this edge
            candidate.associate(member)
            community.create_barter_record(candidate, member)

        else:
            self.log("scenario-upload-activity", state="fail", reason="can not upload when offline")

    def scenario_predefined_identities(self, filepath):
        """
        Force peers to use predefined identities.

        Scenario_predefined_identities must be scheduled before scenario_start.  FILEPATH must
        contain the below table to find the associated public and private key.

        CREATE TABLE predefined_identities (peer_number INTEGER PRIVATE KEY, public_key BLOB, private_key BLOB)

        When no public/private key is found, the peer will generate a random key.
        """
        # dependencies
        if not (self._scenario_calls["scenario_start"] <= 0):
            raise RuntimeError("scenario_predefined_identities must be called BEFORE scenario_start")

        db = sqlite3.connect(os.path.join(self._kargs["localcodedir"], filepath))
        try:
            public_key, private_key = db.execute(u"SELECT public_key, private_key FROM predefined_identities WHERE peer_number = ?",
                                                 (int(self._kargs["peernumber"]),)).next()
        except StopIteration:
            self.log("scenario-predefined-identities", state="not-found")
        else:
            self.log("scenario-predefined-identities", state="found")
            self._my_member = self._dispersy.get_member(str(public_key), str(private_key))

    def scenario_predefined_books(self, filepath):
        """
        Populate the book table with predefined values.

        Scenario_predefined_book should be scheduled after scenario_start.  FILEPATH must contain
        the below table containing the books.

        CREATE TABLE predefined_books (
         first_peer_number INTEGER,
         second_peer_number INTEGER,
         cycle INTEGER,
         effort BLOB,
         upload_first_to_second INTEGER,
         upload_second_to_first INTEGER,
         PRIMARY KEY (first_peer_number, second_peer_number))
        """
        # dependencies
        if not (0 < self._scenario_calls["scenario_start"]):
            raise RuntimeError("scenario_predefined_book must be called AFTER scenario_start")
        if not (0 < self._scenario_calls["scenario_predefined_identities"]):
            raise RuntimeError("scenario_predefined_book must be called AFTER scenario_predefined_identities")

        peer_number = int(self._kargs["peernumber"])
        db = sqlite3.connect(os.path.join(self._kargs["localcodedir"], filepath))
        cur = db.cursor()
        books = []
        books.extend(cur.execute(u"""
SELECT i.public_key, b.cycle, b.effort, b.upload_second_to_first, b.upload_first_to_second
FROM predefined_books b
JOIN predefined_identities i ON i.peer_number = b.second_peer_number
WHERE b.first_peer_number = ?""", (peer_number,)))
        books.extend(cur.execute(u"""
SELECT i.public_key, b.cycle, b.effort, b.upload_first_to_second, b.upload_second_to_first
FROM predefined_books b
JOIN predefined_identities i ON i.peer_number = b.first_peer_number
WHERE b.second_peer_number = ?""", (peer_number,)))

        # get database
        must_go_offline = False
        community = self.has_community()
        if not community:
            must_go_offline = True
            self.scenario_churn("online")
            community = self.has_community()
            assert community

        for public_key, cycle, effort, upload, download in books:
            member = self._dispersy.get_member(str(public_key))
            community.database.execute(u"INSERT INTO book (member, cycle, effort, upload, download) VALUES (?, ?, ?, ?, ?)",
                                       (member.database_id, cycle, effort, upload, download))

        if must_go_offline:
            self.scenario_churn("offline")
        self.log("scenario-predefined-books", book_count=len(books))

    def scenario_predefined_direct_records(self, filepath):
        return self.scenario_predefined_records(filepath, direct_only="True")

    def scenario_predefined_records(self, filepath, chance="DEF", min_global_time="DEF", max_global_time="DEF", direct_only="DEF"):
        """
        Populate the record table with predefined values.

        Scenario_predefined_records should be scheduled after scenario_start.  FILEPATH must contain
        the below table containing the records.  CHANCE is the probability that a peer has a record.
        Records are only considered when their global time is larger or equal to MIN_GLOBAL_TIME and
        smaller or equal to MAX_GLOBAL_TIME.

        CREATE TABLE predefined_records (
         first_peer_number INTEGER,
         second_peer_number INTEGER,
         global_time INTEGER,
         cycle INTEGER,
         effort BLOB,
         upload_first_to_second INTEGER,
         upload_second_to_first INTEGER,
         packet BLOB,
         PRIMARY KEY (first_peer_number, second_peer_number))

         Because we do not actually have the double signed records (i.e. we do not have the Dispersy
         message) we can not set the record.sync field to a valid value.  Hence we will assigned
         negative values to this field.
        """
        # dependencies
        if not (0 < self._scenario_calls["scenario_start"]):
            raise RuntimeError("scenario_predefined_book must be called AFTER scenario_start")
        if not (0 < self._scenario_calls["scenario_predefined_identities"]):
            raise RuntimeError("scenario_predefined_book must be called AFTER scenario_predefined_identities")

        chance = 1.0 if chance == "DEF" else float(chance)
        min_global_time = 1 if min_global_time == "DEF" else int(min_global_time)
        max_global_time = (2**63 - 1) if max_global_time == "DEF" else int(max_global_time)
        direct_only = direct_only.lower() not in ("false", "0", "def")
        peer_number = int(self._kargs["peernumber"])

        where = u" WHERE global_time BETWEEN %d AND %d" % (min_global_time, max_global_time)
        if direct_only:
            where += u" AND (first_peer_number = %d OR second_peer_number = %d)" % (peer_number, peer_number)

        db = sqlite3.connect(os.path.join(self._kargs["localcodedir"], filepath))
        cur = db.cursor()
        records = [tup for tup in cur.execute(u"""
SELECT f.public_key, s.public_key, r.global_time, r.cycle, r.effort, r.upload_first_to_second, r.upload_second_to_first, r.packet
FROM predefined_records r
JOIN predefined_identities f ON f.peer_number = r.first_peer_number
JOIN predefined_identities s ON s.peer_number = r.second_peer_number""" + where)
                   if random.random() < chance]
        self.log("scenario-predefined-records", record_count=len(records), peer_number=peer_number, state="init")

        # get database
        must_go_offline = False
        community = self.has_community()
        if not community:
            must_go_offline = True
            self.scenario_churn("online")
            community = self.has_community()
            assert community

        # push all packets into dispersy
        node = DebugNode(community)
        node.init_socket()
        node.init_my_member(candidate=False)
        node.give_packets([str(packet)
                           for first_public_key, second_public_key, global_time, cycle, effort, upload_first_to_second, upload_second_to_first, packet
                           in records
                           if packet])

        # test that the records have been set
        for first_public_key, second_public_key, global_time, cycle, effort, upload_first_to_second, upload_second_to_first, packet in records:
            if packet:
                first_member = self._dispersy.get_member(str(first_public_key))
                second_member = self._dispersy.get_member(str(second_public_key))
                correct_order = first_member.database_id < second_member.database_id

                try:
                    if correct_order:
                        up122, up221 = community.database.execute(u"SELECT upload_first_to_second, upload_second_to_first FROM record WHERE first_member = ? AND second_member = ?",
                                                                  (first_member.database_id, second_member.database_id)).next()
                    else:
                        up221, up122 = community.database.execute(u"SELECT upload_first_to_second, upload_second_to_first FROM record WHERE first_member = ? AND second_member = ?",
                                                                  (second_member.database_id, first_member.database_id)).next()

                except StopIteration:
                    self.log("ERROR", cid_hex=community.cid.encode("HEX"), packet_hex=str(packet).encode("HEX"))
                    raise RuntimeError("Missing record")

                if not (up122 == upload_first_to_second and up221 == upload_second_to_first):
                    self.log("ERROR", m1=first_member.public_key.encode("HEX"), m2=second_member.public_key.encode("HEX"), up122_in_database=up122, up122_in_record=upload_first_to_second, up221_in_database=up221, up221_in_record=upload_second_to_first)
                    raise RuntimeError("Inconsistent record counters")

        # sync = -1
        # for first_public_key, second_public_key, global_time, cycle, effort, upload_first_to_second, upload_second_to_first, packet in records:
        #     first_member = Member(str(first_public_key))
        #     second_member = Member(str(second_public_key))
        #     community.database.execute(u"INSERT INTO record (sync, first_member, second_member, global_time, cycle, effort, upload_first_to_second, upload_second_to_first) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
        #                                (sync, first_member.database_id, second_member.database_id, global_time, cycle, effort, upload_first_to_second, upload_second_to_first))
        #     sync -= 1

        if must_go_offline:
            self.scenario_churn("offline")

        self.log("scenario-predefined-records", record_count=len(records), peer_number=peer_number, state="done")

    def scenario_database_churn(self, filepath, begin="0", end="0", multiplier="1.0"):
        db = sqlite3.connect(os.path.join(self._kargs["localcodedir"], filepath))
        cur = db.cursor()
        maxpeerid, minonline, maxonline = next(cur.execute(u"SELECT MAX(session.peer), MIN(session.online), MAX(session.online) FROM session")) #JOIN sample ON sample.peer = session.peer"))

        begin = int(begin)
        end = int(end) if int(end) > 0 else maxonline
        multiplier = float(multiplier)
        peernumber = int(self._kargs["peernumber"]) % maxpeerid
        startstamp = float(self._kargs["startstamp"])

        # get the peerid from the database (we will use the peernumber'th peer in the sample table)
        peerid, = next(cur.execute(u"SELECT peer FROM sample ORDER BY peer LIMIT 1 OFFSET ?", (peernumber,)))

        churn = [((online - minonline - begin) * multiplier + startstamp, (offline - online - max((begin-online), 0)) * multiplier)
                 for online, offline
                 in cur.execute(u"SELECT online, offline FROM session WHERE peer = ? AND offline >= ? AND online <= ? ORDER BY online", (peerid, begin, end))]
        self._dispersy.callback.register(self._database_churn_helper, (churn,))

    def _database_churn_helper(self, churn):
        for online, duration in churn:
            delay = max(0.0, online - time.time())
            logger.debug("will go online in %.2f seconds", delay)
            yield delay
            self.scenario_churn("online", duration)

            yield duration
            self.scenario_churn("offline")

    def scenario_kill_community(self):
        # ensure the community is online
        self.scenario_churn("online", 0.0)
        community = self.has_community()
        if not isinstance(community, HardKilledCommunity):
            community.auto_load = True

            # prepare master member
            self._dispersy.get_member(self.master_member_public_key, self.master_member_private_key)
            community.create_dispersy_identity(sign_with_master=True)

            # grant permission to my member
            community.create_dispersy_authorize([(community.my_member, community.get_meta_message(u"dispersy-destroy-community"), u"permit")], sign_with_master=True)

            # destroy
            community.create_dispersy_destroy_community(u"hard-kill")


    def scenario_indexpl_churn(self):
         max_peernum=500
         onlinetime=60 #in minutes

         peernumber=int(self._kargs["peernumber"])
         online_beta= (max_peernum -peernumber)^(-0.5)*60*3600
         offline_beta= (peernumber)^(-0.5)*60*3600
         self.scenario_expon_churn(online_beta,offline_beta)
