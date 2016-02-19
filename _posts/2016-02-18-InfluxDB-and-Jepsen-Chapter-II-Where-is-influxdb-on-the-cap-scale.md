---           
layout: post
title: Jepsen and InfluxDB, Chapter II. Where is InfluxDB on the CAP scale?
date: 2016-02-18
comments: true
categories: Distributed_Systems
tags: [jepsen, influxdb, distributed systems, testing, consistency models]
---

This is a continuation of [the hacking to get Jepsen work with InfluxDB](/distributed_systems/Hacking-up-a-testing-environment-for-jepsen-and-influxdb/). I'm reviewing both technologies at the same time and logging it on my blog in the hope that readers will learn from it, that both Kyle Kingsbury and InfluxData will benefit from my feedback, if not other than one of the many feedbacks that they have produced products that are great - and lastly that I'll manage to organize my experimentation around a memorable narrative. 

# 1. The journey towards an almost stable Jepsen/InfluxDB environment 

This section is all about fixing my Jepsen environment for InfluxDB, and getting to a stage where it's usable for exploring InfluxDB's behavior. If you're not interested in these gory details, just want to learn about InfluxDB, please go ahead and skip to [Is InfluxDB CP or AP?](#is-influxdb-ap-or-cp)

## 1.1 Solving the hung SSH issue

In [my first post in this series](/distributed_systems/Hacking-up-a-testing-environment-for-jepsen-and-influxdb#whats-next) I struggled with the clj-ssh: The locking mechanism ran into a deadlock sometime...one thread seemed to be Thread.sleeping in clj-ssh library while the others are waiting on that thread to release the lock. Why locking? Please read the first post, for a bit more details, but essentially, in order to cluster InfluxDB 0.9.6.1, you'll have to know the startup order upfront and configure the nodes that way, or orchestrate synchronization across the nodes with locking so you know who started first, second and third. 

Debugging the problem with threaddumps, I realized that the command the nodes (it could happen to any of the nodes) choke on was 

<pre><code class="clojure">(c/exec :echo 
    (-> (io/resource "influxdb")  slurp 
        (str/replace #"%NODES_TO_JOIN%" (nodesToJoin nodeOrder)))  
         :> "/etc/default/influxdb")
</code></pre>

What does this command do? 

1. It reads the ````influxdb```` template file from the src/resources directory into memory 
2. does a little string replacement for the nodes to join 
3. starts an ssh session with the node (n1, n2, n3)
4. runs echo _\<replaced string\>_ > /etc/default/influxdb 

And that's where it hung, inside the node! In the background clj-ssh is waiting for the command to finish and the connection to close, but it never happens, as the session is stuck on something. 

<img src="{{ site.url }}/images/jepsenII_01_ssh_session.png" height="253" width="546">

Doing an lsof on this process yields the following list: 

<pre><code class="bash">root@n2:~# lsof -np 22582 | egrep -v '(DIR|REG)'
COMMAND   PID USER   FD   TYPE             DEVICE SIZE/OFF    NODE NAME
sshd    22582 root    0u   CHR                1,3      0t0   15470 /dev/null
sshd    22582 root    1u   CHR                1,3      0t0   15470 /dev/null
sshd    22582 root    2u   CHR                1,3      0t0   15470 /dev/null
sshd    22582 root    3u  IPv4             977964      0t0     TCP 192.168.122.12:ssh->192.168.122.1:55118 (ESTABLISHED)
sshd    22582 root    4u  unix 0xffff880001b37780      0t0  978021 socket
sshd    22582 root    5r  FIFO                0,8      0t0  978033 pipe
sshd    22582 root    6w  FIFO                0,8      0t0  978033 pipe</code></pre>

strace shows the last executed kernel commands for our process:

<pre><code class="bash">root@n2:~# strace -p 22582
Process 22582 attached
select(12, [3 5], [], NULL, NULL
</code></pre>

Okay...somewhere I read a similar hung issue, related to SSH, so I figured I'll dig around /proc/net/tcp:

<pre><code class="bash">root@n1:~# cat /proc/net/tcp
  sl  local_address rem_address   st tx_queue rx_queue tr tm->when retrnsmt   uid  timeout inode                                                     
   0: 00000000:0016 00000000:0000 0A 00000000:00000000 00:00000000 00000000     0        0 15134 1 ffff880004717840 100 0 0 10 0                     
   1: 0100007F:0019 00000000:0000 0A 00000000:00000000 00:00000000 00000000     0        0 15103 1 ffff88001357c100 100 0 0 10 0                     
   2: 0B7AA8C0:0016 017AA8C0:B370 01 00000000:00000000 02:000988E0 00000000     0        0 249802 4 ffff880011fcc0c0 20 4 27 10 17                   
   3: 0B7AA8C0:0016 017AA8C0:8143 01 00000000:00000000 02:000935AD 00000000     0        0 1243363 2 ffff880003b00840 21 4 19 10 -1       
</code></pre>

Well, this still did not enlighten me, even though I managed to figure out based on the inode numbre that the last socket is the culprit one, but besides that not much, as that socket seems to be very similar to the one above which is actually my own terminal ssh session. And...this is the point where I currently gave up the digging, because I found a workaround: <strong>I just needed to put the statement in (c/su) and it NEVER locks up then.</strong>

<pre><code class="clojure">(c/exec :echo 
    (c/su ; the extra c/su 
      (-> (io/resource "influxdb")  slurp 
        (str/replace #"%NODES_TO_JOIN%" (nodesToJoin nodeOrder)))  
         :> "/etc/default/influxdb"))
</code></pre>

But - given the fact that I'm _already_ logging in as root, this should not change a thing. It's a weird synchronization/race condition issue, because it just happens 60% of the time. 

If you, my dear reader have any solution to this, please let me know, it is driving me crazy! Thanks! 

## 1.2 Solving the serialization issue

The next problem was serialization error when the tests finished. It was resulting from my decision to store the state with regards to the order of nodes in the test itself. Kyle responded on Twitter to this problem: 

>∀sket ‏@aphyr  23 Dec 2015
>@balopat 
>"tests can take extra tags but they have to be serializable via fressian. The right place for the state var you added is probably in
>the db object, not the test. Just use a let binding; reify closes over lexical scope"

OK, time to learn some Clojure stuff! What the heck is reify? Finding it on the Clojure docs site: 

<pre><code class="clojure">  ;The method bodies of reify are lexical
  ;closures, and can refer to the surrounding local scope:
  
  (str (let [f "foo"] 
       (reify Object 
         (toString [this] f))))
  == "foo"</code></pre>

But...the best description I found was on the [Practical Elegance blog](http://decomplecting.org/blog/2014/10/29/reify-this/). Aha! So "reifying a protocol" in Clojure is like creating an inline anonymous class implementing an interface in Java.

With my upgraded understanding it was much simpler, I just had to put the let expression around my db object and voila, it worked! 

# 2. Is InfluxDB AP or CP?

InfluxDB's design is in its early stage and still constantly in flux (pun intended). 
Hopefully, as the product matures things will start to stabilize. I admire the courage of the company to be bold enough to go through three raft implementations and three storage engines since they started the project! Even though this might alienate some early adopters, it seems to be the necessary evil if they can invent better and better solutions. Also they are getting better at backward compatibility and providing migraton paths - although nothing is promised yet, they reserve their rights to break things! Clustering is in beta now (Feb 2016, from 0.10).

Just since I started working on the experiments for this second blogpost in early January, a new version came out. Clustering design in 0.9.6.1 compared to v0.10 has significant changes. The introduction of Meta Nodes and Data Nodes as an explicit concept wasn't there and the order of nodes doesn't matter anymore as long as there is one first node who everybody joins. Let's see how the safety is with InfluxDB finally! 

## 2.1. "What does the docs say?"

Kyle Kingbury's "Call me maybe" (just recently renamed to jepsen tests...) articles are mostly about findings of discrepancies between the documentation of a database/distributed system and it's actual behaviour under the presence of network partitions. It's a fantastic series of articles, and if you haven't read them, please do: [https://aphyr.com/tags/jepsen](https://aphyr.com/tags/jepsen). 

Inspired by the "do they walk the talk?" approach of jepsen tests, let's see what documentation we can find about InfluxDB! InfluxDB's documentation follows an interesting model: first Paul Dix blogs about the design ideas in detail. Then the documentaton links the blogpost. Then slowly they start to migrate the ideas over from the blogpost into the structured documentation. 

Thus, the base of my Jepsen testing was a blogpost - Paul Dix's (InfluxData CEO) June 2015 [InfluxDB Clustering - Neither strictly CP or AP](https://influxdata.com/blog/influxdb-clustering-design-neither-strictly-cp-or-ap/) and his [latest post on the 0.10 release](https://influxdata.com/blog/announcing-influxdb-v0-10-100000s-writes-per-second-better-compression/).

## 2.2. Metadata Nodes and Data Nodes

There are basically two separate clusters in InfluxDB, but you can choose nodes to play two roles at the same time. 

<u>Metadata Nodes</u> contain global state about the cluster, which every node should know, for example: 

- peers
- shards
- shard groups 
- etc.

The metadata cluster is using the Raft protocol to come to consensus. They are using Hashicorp's go based Raft implementation. 
What decides if a node is metanode? 

- it has to have the [meta] section
- it has to have unique bind address across the cluster for the bind-address and http-bind-address in the [meta] section 


<u>Data Nodes</u> contain the actual timeseries data stored in shards. The data clustering is a <i>proprietary protocol</i> and meant to be AP by design. 
What decides whether a node is a data node? 

- it has to have the [data] section
- it has to have unique bind address across the cluster for the [http] section - I ran into this one during experimentation, left http.bind-andress localhost:8086 and then only one data node is created, the first one to start up! 


## 2.3. Data Nodes write consistency model

One of the requirements in InfluxDB's design is availability: 

> "...for the read and write path, favor an AP design. Time series are constantly moving and we rarely need a fully consistent view of the most recent data." /Paul Dix/

Not exactly the original use case for Jepsen - as it checks consistency (linearizability) - but we can still use it to double check these statements! 


Let me pull an exact quote from Paul Dix's blog to show what they have there explaining the expected behaviour when we write data on a node (1) into a shard which is owned across multiple nodes (1, 2, 3, 4).

<blockquote>

<img src="{{ site.url }}/images/write_3_owners.png"/>

<p>What happens next depends on the requested consistency level of the write operation. The different levels are:</p>

<ul>
<li> <b>Any</b> – succeed if any of the servers that owns the data accept the write or once the receiving server (1 in our example) writes the data as a durable hinted handoff (more on this later)</li>
<li> <b>One</b>  – succeed once one of the servers that owns the data (2, 3, 4) responds with success</li>
<li> <b>Quorum</b>  – succeed when n/2 + 1 servers accept the write where n is the number of servers that have a copy of the shard</li>
<li> <b>All</b>  – succeed when all servers (2, 3, 4) accept the write</li>
</ul>

Requests to write the data are made in parallel and success is returned to the client when the requested level is hit. 

<h4> WRITE FAILURES </h4> 

What happens when a write fails or partially succeeds? For example, say you asked for a quorum, but were only able to write to host 2, while hosts 3 and 4 timed out. At this point we take advantage of one of our key assumptions about time series data: writes are always for new data that is keyed off information provided by the client. We return a partial write failure to the client. In the meantime, the write could be replicated in the background by hinted handoff. The client can then either fail, or it can make the request again, which would only overwrite the existing value. But it’s important to note that a failed partial write could end up being taken in and fully replicated.

</blockquote>

We will have a look at this behavior on *ConsistencyLevel.ALL* and *ANY*! 

# 3 Jepsen setup

The C in the CAP theorem denotes the concept of linearizability - which operates on a single valued register. 
Jepsen's linerizability checker, Knossos can work with a model to validate the history of operations and their results. 
The model I chose is the simple write/read register. 

OK...but what is the single register in a timeseries database? It's <b>the value of a field in the timeseries at a single moment in time</b>! 

Let's choose this to be the first nanosecond of all computer time big bang: 1ns epoch time (1970. Jan. 1. midnight + 1ns)! 

Let's also choose the initial value of the register to be 42, the Answer to Life, the Universe and Everything. 

<pre><code class="clojure">(let [
                c (connect node)
                initialPoint (-> (Point/measurement "answers")
                                 (.time 1 TimeUnit/NANOSECONDS)
                                 (.field "answer" 42)
                                 (.build)
                                 )
                ]
            (info node "creating jepsen DB...")
            (.createDatabase c dbName)
            (.write c dbName "default" initialPoint)
            )</code></pre>

Our operations:


<pre><code class="clojure">  :read (assoc op :type :ok, :value
                                 (queryInflux conn "SELECT answer from answers where time = 1")
                                 )
                 :write (try
                          (do (writeToInflux conn (:value op) writeConsistencyLevel)
                              (assoc op :type :ok))
                          (catch Throwable e
                            (do
                              (info "Write failed with " e)
                              (if (.contains (.getMessage e) "timeout")
                                (assoc op :type :info, :error (.getMessage e))
                                (assoc op :type :fail, :error (.getMessage e))
                                )

                              )
                            )
                          )
                 )
</code></pre>

As it's stated above, when writes fail with timeout exceptions, that could mean that the write was successful. we actually don't know too much whether the operation succeeded or not, hence we mark it <b>:info</b>. Every other Exception will result in <b>:fail</b>. 


Reads are the simple query of the value of the <b>answer</b> field from the <b>anwsers</b> measurement in the <b>jepsen</b> database from when time = 1. 


# 4 Results

## 4.1 Shards get replicated on both ConsistencyLevel.ANY and ALL

Data Nodes are AP, but you can choose to write on different consistency levels on the client side! 
<pre><code class="java">public enum ConsistencyLevel {
    /** Write succeeds only if write reached all cluster members. */
    ALL("all"),
    /** Write succeeds if write reached any cluster members. */
    ANY("any"),
    /** Write succeeds if write reached at least one cluster members. */
    ONE("one"),
    /** Write succeeds only if write reached a quorum of cluster members. */
    QUORUM("quorum");
    ...
    }
</code></pre>


The interesting part is that this **does not mean that the data won't get replicated**! 


I prepared 4 tests with regards to linearizability checking in Jepsen. Out of that 2 is healthy (there is no distruption) and 2 is torn apart by nemesis. Within those 2 categories I have *ConsistencyLevel.ALL* and *ConsistencyLevel.ANY* writes. 

The result is that the two healthy cluster tests are passing (linearizable) while the nemesis ones fail: 

<pre><code class="bash">Ran 4 tests containing 4 assertions.
2 failures, 0 errors.
</code></pre>


<i>ConsistencyLevel just means that the client gets informed if the replication of the shards to the specified amount of members doesn't happen in a given time, data will be fully replicated to all nodes as soon as it's possible.</i>

(caveat: I only checked for ANY and ALL)

## 4.2 Partially failing writes during network partitions 

If you choose *ConsistencyLevel.ALL*, then, based on the specs in the AP/CP blogpost, your write will fail with timeout on the client side, but it will successfully be written to the local copy of the shard. 

In order to see the fun effects I had the following setup: 

<pre><code class="properties">[cluster]
  shard-writer-timeout = "1s" # The time within which a remote shard must respond to a write request.
  write-timeout = "1s" # The time within which a write request must complete on the cluster.
</code></pre>

Nemesis was setup to disrupt the network for 3s intervals, and let the system recover 1s. 

**The results were consistent with the documentation!**


<img src="{{ site.url }}/images/j02-latency-ALL.png" />

> operation latency for InfluxDB 0.10, at consistency level ALL -- most writes succeed after ~1s, but significant amount fails, and by design the setup won't be linearizable: 

<img src="{{ site.url }}/images/j02-illegal-ALL.png" />


<img src="{{ site.url }}/images/j02-latency-ANY.png"/>

> operation latency for InfluxDB 0.10, at consistency level ANY -- all writes succeed immediately, and understandably, the setup won't be linerizable: 

<img src="{{ site.url }}/images/j02-illegal-ANY.png" />


## 4.3 How available is AP?

An interesting edge case was mentioned by Paul Dix in his original AP/CP blogpost: 

As the Metadata cluster is CP, even if the write ConsistencyLevel is set to ANY, the write should time out after a while or just fail <i>if it requires the Metadata service</i> to succeed. 

I had to test this out of curiousity! 

How do we force a write operaton to use the Metadata service? <b>We need to make every write create a shard!</b> The Metadata service stores the information about shards, shard groups, etc. so if a point requires the creation of a new shard, the Metadata service will be on the critical path! 

The original single point insertion leaves us with one single shard: 

<pre><code class="bash"> show shards
name: jepsen
------------
id  database  retention_policy  shard_group start_time  end_time    expiry_time   owners
1 jepsen    default     1   1969-12-29T00:00:00Z  1970-01-05T00:00:00Z  1970-01-05T00:00:00Z  1,2,3
</code></pre>


So if I insert another one for today, we'll get another shard: 

<pre><code class="bash">root@n3:~# curl -i -XPOST 'http://localhost:8086/write?db=jepsen' --data-binary 'answers value=83 1453382821000000000'
HTTP/1.1 204 No Content
Request-Id: e7faae32-c042-11e5-802d-000000000000
X-Influxdb-Version: 0.9.6.1
Date: Thu, 21 Jan 2016 13:28:49 GMT

root@n3:~# influx
Visit https://enterprise.influxdata.com to register for updates, InfluxDB server management, and monitoring.
Connected to http://localhost:8086 version 0.9.6.1
InfluxDB shell 0.9.6.1
> show shards
name: jepsen
------------
id  database  retention_policy  shard_group start_time    end_time    expiry_time   owners
1 jepsen    default     1   1969-12-29T00:00:00Z  1970-01-05T00:00:00Z  1970-01-05T00:00:00Z  1,2,3
5 jepsen    default     3   2016-01-18T00:00:00Z  2016-01-25T00:00:00Z  2016-01-25T00:00:00Z  2,3,1
</code></pre>

Fantastic! 
Now, let's insert our random bits to random moments in time by introducing a new operation wTimed: 

<pre><code class="clojure">(defn wTimed [_ _ ] {:type       :invoke, :f :timedWrite, :value (double (rand-int 5)),
                     :writeTime (*' (long 1000000000000000) (+ 100 (rand-int 1000)))})
</code></pre>

The timedWrite operation will be handled by our client similarly as the write op, plus setting the random timestamp and we're going to :info all failures: 

<pre><code class="clojure"> :timedWrite (try
                          (do (writeToInflux conn (:value op) writeConsistencyLevel (:writeTime op))
                              (assoc op :type :ok))
                          (catch Throwable e
                            (do
                              (info "Write failed with " e)
                                (assoc op :type :info, :error (.getMessage e))
                              )
                            )
                          )
</code></pre>

The "test" I wrote for this is not really a test, as I don't want to put a model around just writing stuff, I don't have a linearizability criteria, I just wanted to see the availability of the product. This could be written in form of a test too -- fail it when there is a timeout or failure, or when the system SLA is failed with regards to latency percentiles...but for this blogpost just running the reports was satisfactory for me. 

<pre><code class="clojure">:generator (->> (gen/mix [wTimed])
                     (gen/nemesis
                       (gen/seq
                         (cycle [(gen/sleep 1)
                                 {:type :info :f :start}
                                 (gen/sleep 3)
                                 {:type :info :f :stop}
                                 ])
                         )
                       )
                     (gen/time-limit 30))
     :model model/noop
</code></pre>

It works with the same nemesis cycle as the previous tests but noop model and the generator is only generating wTimed operations.

After running the test, voila, the shards are created: 

<pre><code class="ssh">> show shards
name: jepsen
------------
id  database  retention_policy  shard_group start_time    end_time    expiry_time   owners
1 jepsen    default     1   1969-12-29T00:00:00Z  1970-01-05T00:00:00Z  1970-01-05T00:00:00Z  1,4,5
2 jepsen    default     2   2001-09-03T00:00:00Z  2001-09-10T00:00:00Z  2001-09-10T00:00:00Z  1,4,5
24  jepsen    default     22    2002-04-22T00:00:00Z  2002-04-29T00:00:00Z  2002-04-29T00:00:00Z  4,5,1
8 jepsen    default     8   2002-08-19T00:00:00Z  2002-08-26T00:00:00Z  2002-08-26T00:00:00Z  1,4,5
44  jepsen    default     42    2002-12-16T00:00:00Z  2002-12-23T00:00:00Z  2002-12-23T00:00:00Z  4,5,1
43  jepsen    default     41    2003-04-07T00:00:00Z  2003-04-14T00:00:00Z  2003-04-14T00:00:00Z  1,4,5
3 jepsen    default     3   2003-08-04T00:00:00Z  2003-08-11T00:00:00Z  2003-08-11T00:00:00Z  4,5,1
16  jepsen    default     14    2004-11-08T00:00:00Z  2004-11-15T00:00:00Z  2004-11-15T00:00:00Z  5,1,4
29  jepsen    default     27    2005-10-17T00:00:00Z  2005-10-24T00:00:00Z  2005-10-24T00:00:00Z  1,4,5
28  jepsen    default     26    2006-02-13T00:00:00Z  2006-02-20T00:00:00Z  2006-02-20T00:00:00Z  5,1,4
31  jepsen    default     29    2007-05-21T00:00:00Z  2007-05-28T00:00:00Z  2007-05-28T00:00:00Z  5,1,4
22  jepsen    default     20    2007-09-17T00:00:00Z  2007-09-24T00:00:00Z  2007-09-24T00:00:00Z  5,1,4
13  jepsen    default     11    2008-01-07T00:00:00Z  2008-01-14T00:00:00Z  2008-01-14T00:00:00Z  5,1,4
6 jepsen    default     6   2008-05-05T00:00:00Z  2008-05-12T00:00:00Z  2008-05-12T00:00:00Z  4,5,1
25  jepsen    default     23    2009-08-10T00:00:00Z  2009-08-17T00:00:00Z  2009-08-17T00:00:00Z  5,1,4
14  jepsen    default     12    2010-03-29T00:00:00Z  2010-04-05T00:00:00Z  2010-04-05T00:00:00Z  4,5,1
18  jepsen    default     16    2010-07-19T00:00:00Z  2010-07-26T00:00:00Z  2010-07-26T00:00:00Z  4,5,1
5 jepsen    default     5   2012-06-18T00:00:00Z  2012-06-25T00:00:00Z  2012-06-25T00:00:00Z  1,4,5
19  jepsen    default     17    2012-10-08T00:00:00Z  2012-10-15T00:00:00Z  2012-10-15T00:00:00Z  5,1,4
40  jepsen    default     38    2013-05-27T00:00:00Z  2013-06-03T00:00:00Z  2013-06-03T00:00:00Z  1,4,5
23  jepsen    default     21    2014-09-01T00:00:00Z  2014-09-08T00:00:00Z  2014-09-08T00:00:00Z  1,4,5
34  jepsen    default     32    2015-04-20T00:00:00Z  2015-04-27T00:00:00Z  2015-04-27T00:00:00Z  5,1,4
38  jepsen    default     36    2016-07-25T00:00:00Z  2016-08-01T00:00:00Z  2016-08-01T00:00:00Z  4,5,1
37  jepsen    default     35    2017-11-06T00:00:00Z  2017-11-13T00:00:00Z  2017-11-13T00:00:00Z  1,4,5
41  jepsen    default     39    2019-02-11T00:00:00Z  2019-02-18T00:00:00Z  2019-02-18T00:00:00Z  4,5,1
27  jepsen    default     25    2019-09-30T00:00:00Z  2019-10-07T00:00:00Z  2019-10-07T00:00:00Z  4,5,1
36  jepsen    default     34    2021-01-04T00:00:00Z  2021-01-11T00:00:00Z  2021-01-11T00:00:00Z  5,1,4
26  jepsen    default     24    2022-04-11T00:00:00Z  2022-04-18T00:00:00Z  2022-04-18T00:00:00Z  1,4,5
17  jepsen    default     15    2023-03-27T00:00:00Z  2023-04-03T00:00:00Z  2023-04-03T00:00:00Z  1,4,5
35  jepsen    default     33    2023-07-17T00:00:00Z  2023-07-24T00:00:00Z  2023-07-24T00:00:00Z  4,5,1
32  jepsen    default     30    2023-11-13T00:00:00Z  2023-11-20T00:00:00Z  2023-11-20T00:00:00Z  1,4,5
20  jepsen    default     18    2024-10-21T00:00:00Z  2024-10-28T00:00:00Z  2024-10-28T00:00:00Z  1,4,5
45  jepsen    default     43    2025-10-06T00:00:00Z  2025-10-13T00:00:00Z  2025-10-13T00:00:00Z  5,1,4
15  jepsen    default     13    2026-02-02T00:00:00Z  2026-02-09T00:00:00Z  2026-02-09T00:00:00Z  4,5,1
39  jepsen    default     37    2026-05-25T00:00:00Z  2026-06-01T00:00:00Z  2026-06-01T00:00:00Z  5,1,4
21  jepsen    default     19    2026-09-21T00:00:00Z  2026-09-28T00:00:00Z  2026-09-28T00:00:00Z  4,5,1
12  jepsen    default     10    2028-12-04T00:00:00Z  2028-12-11T00:00:00Z  2028-12-11T00:00:00Z  4,5,1
4 jepsen    default     4   2029-07-23T00:00:00Z  2029-07-30T00:00:00Z  2029-07-30T00:00:00Z  5,1,4
33  jepsen    default     31    2029-11-19T00:00:00Z  2029-11-26T00:00:00Z  2029-11-26T00:00:00Z  4,5,1
30  jepsen    default     28    2030-03-11T00:00:00Z  2030-03-18T00:00:00Z  2030-03-18T00:00:00Z  4,5,1
42  jepsen    default     40    2030-07-08T00:00:00Z  2030-07-15T00:00:00Z  2030-07-15T00:00:00Z  5,1,4
7 jepsen    default     7   2032-09-27T00:00:00Z  2032-10-04T00:00:00Z  2032-10-04T00:00:00Z  5,1,4
</code></pre>

And the final analysis: 

This is how latency looks like when everything is healthy: 

<img src="{{ site.url }}/images/j02-latency-multi-healthy.png"/>

Compared to when nemesis creates network partitions: 

<img src="{{ site.url }}/images/j02-latency-multi-nemesis.png"/>

Also the client experiences errors like the following ones: 

<pre><code class="bash">:type java.lang.RuntimeException
   :message {"error":"meta service returned 503 Service Unavailable"}
</code></pre>

<pre><code class="bash">:type retrofit.RetrofitError
   :message timeout
   :at [retrofit.RetrofitError networkError RetrofitError.java 27]}
  {:type java.io.InterruptedIOException
   :message timeout
   :at [okio.AsyncTimeout exit AsyncTimeout.java 258]}
  {:type java.net.SocketException
   :message Socket closed
   :at [java.net.SocketInputStream read SocketInputStream.java 203]}]
</code></pre>

This behaviour is - similarly to the single point write consistency modes - in agreement with the documentation: when the actual operation depends on the CP metadataservice (e.g. writing a new datapoint requires a new shard to be created), and there are network partitions in place, the system will become unavailable, rendering the AP part of the design non-strict. 

# 5. Summary 


What we've learned: 

* Jepsen is an excellent tool to construct statistically stable tests for distributed systems and was a big help in automating the different scenarios exploring InfluxDB's behaviour. With a bit of effort distributed system builders could even turn it into a CI tool, to test continuously the assumptions with regards to linearizability scenarios (I wonder why nobody is doing it yet?). 

* InfluxDB has an interesting take on safety, it is a hybrid non-strict CP/AP, they are explicit about there assumptions they base their design decisions on each point - which shows how much more subtle the picture can be than just a dichotomic AP vs CP world view. Having said that, with the right order of failures, dataloss is more than possible in an AP architecture, so I would not trust my super-hyper mission critical data with this setup - my metrics? sure! 

* InfluxDB continuously improves and got better in the last month only: more stable startups and less finicky clustering setup (although still has some rough edges when nodes are joining, 1 out of 3 tests fail to connect up all nodes!)

* InfluxDB docs around safety, or what exactly defines a DataNode or MetaNode for example are a bit all over the place (blog, docs) but that's improving as well, and in the end there is an obvious effort to be extremely transparent about the design decisions and trade-offs 


I have to say thank you for Kyle Kingsbury for helping resolving the issues with the setup, he was super helpful and always quick to respond. 

Thoughts, feedback, as always, are more than welcome! 
