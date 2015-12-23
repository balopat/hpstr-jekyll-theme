---           
layout: post
title: Hacking up a test environment for InfluxDB and Jepsen 
date: 2015-12-23
comments: true
categories: Distributed_Systems
tags: [jepsen, influxdb, distributed systems, testing, consistency models]
---

Before the holidays (2 days) I promised myself and my wife that I won’t code during the holidays. So I won’t. However, I’m setting up an environment for January on my Mac so they will wait for me when I come back for my next train #CommuteProject: a Jepsen test for InfluxDB! 

My motivation is that I'm genuinely curious in both technologies, I work with InfluxDB at work, and learned so much from the Jepsen articles, that I wanted to try it out. 

All my experiments are on my github too: 

<a href="https://github.com/balopat/jepsen">https://github.com/balopat/jepsen</a>

<a href="https://github.com/balopat/jepsen-vagrant">https://github.com/balopat/jepsen-vagrant</a>

Disclaimer: this is a hack, not meant to be a finalized version of any of the forks, also I'm a newbie in Clojure, Jepsen and InfluxDB 

## What is InfluxDB? 

<a href="http://influxdb.com">InfluxDB</a> is an open source, distributed time series database, one of the most promising ones out there, written by the company now called InfluxData, in Go. From distributed systems point of view, the clustering protocol is an implementation of Raft. 

## What is Jepsen? 

<a href="https://aphyr.com/tags/jepsen">Jepsen</a> is a tool to torture distributed systems, written by Kyle Kingsbury in Clojure. The tool creates nodes of the tested system and starts to generate operations on them while messing with the network and the clocks of the nodes. 

##1. Setting up the LXC nodes and basic Jepsen run


I started with going through <a href="https://github.com/aphyr/jepsen/blob/master/README.md">aphyr's instructions</a>, but I missed the crucial part of creating 5 machines, so I ran into an “UnknownHostException: n1”. Jepsen expects n1, n2, n3, n4, and n5 hosts to be reachable. As the LXC scripts are written for a debian system, I needed to look for some alternative ways. 

Not too much Googling brought me to try <a href="https://github.com/abailly/jepsen-vagrant">jepsen-vagrant from abailly</a>. I started working with it, but quickly ran into the following issue:

<pre><code class="bash">   jepsen: /jepsen => /Users/balopat/proj/jepsen
Failed to mount folders in Linux guest. This is usually because
the "vboxsf" file system is not available. Please verify that
the guest additions are properly installed in the guest and
can work properly. The command attempted was:

mount -t vboxsf -o uid=`id -u vagrant`,gid=`getent group vagrant | cut -d: -f3` jepsen /jepsen
mount -t vboxsf -o uid=`id -u vagrant`,gid=`id -g vagrant` jepsen /jepsen

The error output from the last command was:

stdin: is not a tty
mount: unknown filesystem type 'vboxsf'
</code></pre>


Which is was due to the fact that the original debian/jessie64 vagrant box does not have the VirtualBox GuestAdditions installed. So I looked for one, and found **xezpeleta/jessie64**. 

This seemed to do the trick, however I ran into some big red lines, when the vagrant script started creating the LXC hosts. 

<img src="{{site.url}}/images/errors_with_jepsen_creating_the_lxc_hosts.png"/>

It seemed that the vagrant user’s home folder was owned by root! OK, ````chown -R vagrant /home/vagrant````, [host] vagrant reload, [guest]: cd /vagrant; sudo bash net.sh; sudo bash lxc.sh

Did the magic! 

The caveat part in the README was accurate, I did need to modify my test setup to cater for the login to the LXC boxes: 

<pre><code class="clojure">(defn basic-test
  "A simple test of InfluxDB's safety."
  [version]
  (merge tests/noop-test 
  	 {:ssh 
  	 	{ :username "root"
  	 	  :private-key-path "~/.ssh/id_rsa"
  	 	}
  	 }
  	)
 )
</code></pre>

And success: 
<pre><code class="bash">jepsen.core - Everything looks good! ヽ(‘ー`)ノ
</code>
</pre>


##2. Setting up InfluxDB on the LXC nodes

Setup and tear down scripts - I looked into the rabbitmq setup and it looks straightforward...however...I'm a big believer of baby steps, let's try the simple noop teardown/setup steps written in the jepsen docs: 

<pre><code class="clojure">(defn db
  "Sets up and tears down InfluxDB"
  [version]
  (reify db/DB
    (setup! [_ test node]
      (info node "set up"))

    (teardown! [_ test node]
      (info node "tore down"))))
</code></pre>


Aaand...error:

<pre><code>lein test jepsen.influxdb-test
INFO  jepsen.os.debian - :n3 setting up debian
INFO  jepsen.os.debian - :n4 setting up debian
INFO  jepsen.os.debian - :n2 setting up debian
INFO  jepsen.os.debian - :n1 setting up debian
INFO  jepsen.os.debian - Installing #{man-db curl iputils-ping logrotate sysvinit-core rsyslog faketime vim unzip wget sysvinit}
INFO  jepsen.os.debian - Installing #{man-db curl iputils-ping logrotate sysvinit-core rsyslog faketime vim unzip wget sysvinit}
INFO  jepsen.os.debian - Installing #{man-db curl iputils-ping logrotate sysvinit-core rsyslog faketime vim unzip wget sysvinit}
INFO  jepsen.os.debian - Installing #{man-db curl iputils-ping logrotate sysvinit-core rsyslog faketime vim unzip wget sysvinit}

lein test :only jepsen.influxdb-test/basic-test

ERROR in (basic-test) (FutureTask.java:122)
expected: (:valid? (:results (run! (influxdb/basic-test version))))
  actual: java.util.concurrent.ExecutionException: java.lang.RuntimeException: E: Sub-process /usr/bin/dpkg returned an error code (1)

Reading package lists...
Building dependency tree...
Reading state information...
The following packages will be REMOVED:
  systemd*
0 upgraded, 0 newly installed, 1 to remove and 0 not upgraded.
After this operation, 14.2 MB disk space will be freed.
(Reading database ... 13478 files and directories currently installed.)
Removing systemd (215-17+deb8u2) ...
systemd is the active init system, please switch to another before removing systemd.
dpkg: error processing package systemd (--purge):
 subprocess installed pre-removal script returned error exit status 1
Failed to stop lib-init-rw.mount: Unit lib-init-rw.mount not loaded.
Failed to execute operation: File exists
Errors were encountered while processing:
 systemd

 at java.util.concurrent.FutureTask.report (FutureTask.java:122)
    java.util.concurrent.FutureTask.get (FutureTask.java:192)
    clojure.core$deref_future.invoke (core.clj:2186)
    clojure.core$future_call$reify__6736.deref (core.clj:6683)
    clojure.core$deref.invoke (core.clj:2206)
    clojure.core$pmap$step__6749$fn__6751.invoke (core.clj:6733)
    clojure.lang.LazySeq.sval (LazySeq.java:40)
    clojure.lang.LazySeq.seq (LazySeq.java:49)
    clojure.lang.RT.seq (RT.java:507)
    clojure.core/seq (core.clj:137)
    clojure.core$dorun.invoke (core.clj:3009)
    jepsen.core$on_nodes.invoke (core.clj:84)
    jepsen.core$run_BANG_$fn__6821.invoke (core.clj:404)
    jepsen.core$run_BANG_.invoke (core.clj:373)
    jepsen.influxdb_test/fn (influxdb_test.clj:15)
    clojure.test$test_var$fn__7670.invoke (test.clj:704)
    clojure.test$test_var.invoke (test.clj:704)
    clojure.test$test_vars$fn__7692$fn__7697.invoke (test.clj:722)
    clojure.test$default_fixture.invoke (test.clj:674)
    clojure.test$test_vars$fn__7692.invoke (test.clj:722)
    clojure.test$default_fixture.invoke (test.clj:674)
    clojure.test$test_vars.invoke (test.clj:718)
    clojure.test$test_all_vars.invoke (test.clj:728)
    clojure.test$test_ns.invoke (test.clj:747)
    clojure.core$map$fn__4553.invoke (core.clj:2624)
    clojure.lang.LazySeq.sval (LazySeq.java:40)
    clojure.lang.LazySeq.seq (LazySeq.java:49)
    clojure.lang.Cons.next (Cons.java:39)
    clojure.lang.RT.boundedLength (RT.java:1735)
    clojure.lang.RestFn.applyTo (RestFn.java:130)
    clojure.core$apply.invoke (core.clj:632)
    clojure.test$run_tests.doInvoke (test.clj:762)
    clojure.lang.RestFn.applyTo (RestFn.java:137)
    clojure.core$apply.invoke (core.clj:630)
    user$eval85$fn__144$fn__175.invoke (form-init4656407246406385084.clj:1)
    user$eval85$fn__144$fn__145.invoke (form-init4656407246406385084.clj:1)
    user$eval85$fn__144.invoke (form-init4656407246406385084.clj:1)
    user$eval85.invoke (form-init4656407246406385084.clj:1)
    clojure.lang.Compiler.eval (Compiler.java:6782)
    clojure.lang.Compiler.eval (Compiler.java:6772)
    clojure.lang.Compiler.load (Compiler.java:7227)
    clojure.lang.Compiler.loadFile (Compiler.java:7165)
    clojure.main$load_script.invoke (main.clj:275)
    clojure.main$init_opt.invoke (main.clj:280)
    clojure.main$initialize.invoke (main.clj:308)
    clojure.main$null_opt.invoke (main.clj:343)
    clojure.main$main.doInvoke (main.clj:421)
    clojure.lang.RestFn.invoke (RestFn.java:421)
    clojure.lang.Var.invoke (Var.java:383)
    clojure.lang.AFn.applyToHelper (AFn.java:156)
    clojure.lang.Var.applyTo (Var.java:700)
    clojure.main.main (main.java:37)
Caused by: java.lang.RuntimeException: E: Sub-process /usr/bin/dpkg returned an error code (1)

Reading package lists...
Building dependency tree...
Reading state information...
The following packages will be REMOVED:
  systemd*
0 upgraded, 0 newly installed, 1 to remove and 0 not upgraded.
After this operation, 14.2 MB disk space will be freed.
(Reading database ... 13478 files and directories currently installed.)
Removing systemd (215-17+deb8u2) ...
systemd is the active init system, please switch to another before removing systemd.
dpkg: error processing package systemd (--purge):
 subprocess installed pre-removal script returned error exit status 1
Failed to stop lib-init-rw.mount: Unit lib-init-rw.mount not loaded.
Failed to execute operation: File exists
Errors were encountered while processing:
 systemd

 at jepsen.control$throw_on_nonzero_exit.invoke (control.clj:105)
    jepsen.control$exec_STAR_.doInvoke (control.clj:120)
    clojure.lang.RestFn.applyTo (RestFn.java:137)
    clojure.core$apply.invoke (core.clj:630)
    jepsen.control$exec.doInvoke (control.clj:136)
    clojure.lang.RestFn.invoke (RestFn.java:512)
    jepsen.os.debian$reify__7263$fn__7264.invoke (debian.clj:148)
    jepsen.os.debian$reify__7263.setup_BANG_ (debian.clj:130)
    jepsen.os$eval4164$fn__4165$G__4154__4169.invoke (os.clj:4)
    jepsen.os$eval4164$fn__4165$G__4153__4174.invoke (os.clj:4)
    clojure.core$partial$fn__4527.invoke (core.clj:2494)
    jepsen.core$on_nodes$fn__6710.invoke (core.clj:86)
    clojure.core$pmap$fn__6744$fn__6745.invoke (core.clj:6729)
    clojure.core$binding_conveyor_fn$fn__4444.invoke (core.clj:1916)
    clojure.lang.AFn.call (AFn.java:18)
    java.util.concurrent.FutureTask.run (FutureTask.java:266)
    java.util.concurrent.ThreadPoolExecutor.runWorker (ThreadPoolExecutor.java:1142)
    java.util.concurrent.ThreadPoolExecutor$Worker.run (ThreadPoolExecutor.java:617)
    java.lang.Thread.run (Thread.java:745)

Ran 1 tests containing 1 assertions.
0 failures, 1 errors.
Tests failed.

</code></pre>

Why would jepsen want to remove systemd? Well: seemingly <a href="https://github.com/aphyr/jepsen/blob/0.0.7/jepsen/src/jepsen/os/debian.clj#L146-L148">"fucking systemd" breaks a bunch of packages!</a>
Hahaha. But how do I remove it then?!

<a href="http://without-systemd.org/wiki/index.php/How_to_remove_systemd_from_a_Debian_jessie/sid_installation">http://without-systemd.org/wiki/index.php/How_to_remove_systemd_from_a_Debian_jessie/sid_installation</a>

OK, so I just need to restart the nodes after I copied the inittab from sysvinit so apt doesn't complain. Easy beasy manually, not sure how I'll do it automatically yet. 

I did this for every node manually (this example shows n5):

<pre><code>vagrant@jepsen:/jepsen/jepsen.influxdb$ ssh root@n5
Warning: Permanently added the ECDSA host key for IP address '192.168.122.15' to the list of known hosts.

The programs included with the Debian GNU/Linux system are free software;
the exact distribution terms for each program are described in the
individual files in /usr/share/doc/*/copyright.

Debian GNU/Linux comes with ABSOLUTELY NO WARRANTY, to the extent
permitted by applicable law.
root@n5:~# cp /usr/share/sysvinit/inittab /etc/inittab; shutdown -r now; exit

Broadcast message from root@n5 (pts/0) (Tue Dec 22 16:31:11 2015):

The system is going down for reboot NOW!
logout
Connection to n5 closed.
</code></pre>

And voila, `lein test` now succeeds:

<img src="{{site.url}}/images/jepsen_02_dummy_influxdb_setup.png"/>

After a bit of experimentation I managed to get the InfluxDB installation on debian. The results include a copy of the influxdb init.sh script to the init.d directory -- we have to fall back to SysV, as now we don't have systemd! 

The script looks like this after the first stab (I commented out the tear down part for now, so that I can check the state of the running nodes, but I'll uncomment those when I want to recover from crazy states and start fresh):

<pre><code class="clojure">(defn db
  "Sets up and tears down InfluxDB"
  [version]
  (reify db/DB
    (setup! [_ test node]
     (try
      (c/cd "/tmp"
            (let [version "0.9.6.1"
                  file (str "influxdb_" version "_amd64.deb")]
              (when-not (cu/file? file)
                (info "Fetching deb package from influxdb repo")
                (c/exec :wget (str "https://s3.amazonaws.com/influxdb/" file)))

              (c/su
                ; Install package
                (try (c/exec :dpkg-query :-l :influxdb)
                     (catch RuntimeException _
                       (info "Installing influxdb...")                    
                       (c/exec :dpkg :-i file)))))

              (c/exec :cp "/usr/lib/influxdb/scripts/init.sh" "/etc/init.d/influxdb")

              ; preparing for the clustering, hostname should be the node's name
                (info node "Copying influxdb configuration...")              
              (c/exec :echo (-> (io/resource "influxdb.conf")
                      slurp
                      (str/replace #"%HOSTNAME%" (name node)))
                 :> "/etc/influxdb/influxdb.conf")
                  
                ; first stab at clustering -- doesn't really work yet
              (c/exec :echo 
                (-> (io/resource "peers.json")  slurp) :> "/var/lib/influxdb/meta/peers.json")
              

              ; Ensure node is running
                (try (c/exec :service :influxdb :status)
                     (catch RuntimeException _
                     (info "Starting influxdb...")
                     (c/exec :service :influxdb :start)))

            )
    
        (catch RuntimeException e
            (error node "Error at Setup: " e (.getMessage e))
            (throw e)
          )
        )
      )


    (teardown! [_ test node]
      (try
        (c/su
      (info node "Stopping influxdb...")
      ;(meh (c/exec :killall :-9 "influxd"))
      ;(c/exec :service :influxdb :stop)
      (info node "Removing influxdb...")
      ;(c/exec :dpkg :--purge "influxdb")
      (info node "Removed influxdb")
         )
        (catch RuntimeException e
            (error node "Error at TearDown: " e (.getMessage e))
            (throw e)
          )
      )
     ))


    )

(defn basic-test
  "A simple test of InfluxDB's safety."
  [version]
  (merge tests/noop-test 
     {:ssh 
      { :username "root"
        :private-key-path "~/.ssh/id_rsa"
      }
       :os debian/os
       :db (db version)
     }
    )
 )
</code></pre>

As you can see there are already some efforts here to get InfluxDB clustered. Unfortunately they don't work. It seems that clustering will be a separate topic to get right as just setting up peers.json with all the nodes on all the nodes is not sufficient...

Currently this is what I have in /var/lib/influxdb/meta/peers.json:

<pre><code class="json">["n1:8088", "n2:8088", "n3:8088", "n4:8088", "n5:8088"]
</code></pre>

And the output of SHOW SERVERS on all nodes is: 

<pre><code class="sql">root@n2:~# influx
Visit https://enterprise.influxdata.com to register for updates, InfluxDB server management, and monitoring.
Connected to http://localhost:8086 version 0.9.6.1
InfluxDB shell 0.9.6.1
> SHOW SERVERS
id  cluster_addr  raft  raft-leader
1 n4:8088   true  true
</code></pre>

So all of them sees only n4 as a leader and nobody else is in the cluster.
Hmmm...what am I missing? 

##3. Setting up clustering for InfluxDB 

Obviously the peers.json method doesn't work. What else? <a href="https://influxdb.com/docs/v0.9/guides/clustering.html">I have to start the InfluxDB instances one-by-one</a> and depending on which order the nodes were started, the INFLUXDB_OPTS variable will need to be set with the right previous members of the cluster. Argh. Yippee, serialization! 

### 3.1 Sidetrack: pmap and parallelization issues 

On my mac the number of logical CPUs is 4, hardware is 2, out of wich the vagrant machine got 1. 

As I needed serialization of the nodes, I wanted to use the *locking* macro of clojure. This was working fine, except for 5 nodes it always hung :( 

The problem is in Jepsen's use of **pmap** which runs the tests in a fixed-size threadpool based on the number of CPU's + 2 -- which somehow resulted in 4...This is still a bit of a mistery for me why I got stuck at exactly 4...but hey, this is a hack before holidays, so let's just solve it! 

I found an excellent clojure library called <a href="https://github.com/TheClimateCorporation/claypoole">claypoole</a> which saved me, I changed the pmap in jepsen to cp/pmap pool and voila, it started working!!! 

Ironic: later I realized InfluxDB can't create a cluster bigger than 3 members, so I could have just used 3 nodes :) 

### 3.2 Sidetrack: ordering of the test execution with locks and sharing state with refs 

The next hack was to somehow get the order of started nodes shared between the test executions and somehow synchronize them on it. 

As the *test* variable is the only shared, "contextual" object, I raped it with an extra field called :nodeOrder, learned a bit about refs in clojure, which is part of the fascinating STM implementation...and wrote my first clojure transaction to read and update the ref for this shared state:

<pre><code class="clojure">(defn getNodeOrder [node test]    
    (dosync
        (let [norder  (cons node (deref (:nodeOrder test)) )]
           (ref-set (:nodeOrder test) norder)        
           norder
           )
      )
)
</code></pre>

This is used in the setup method while locking (which is the Java synchronized equivalent) on the test object itself: 

<pre><code class="clojure">(info node "I am waiting for the lock...")
             (locking (:nodeOrder  test) 
                (info node "I have the lock!")
                (let [norder (getNodeOrder node test)]                              
                 
                     (info node "nodes to join: " (nodesToJoin norder) norder (deref (:nodeOrder test)) )    
                     
                     (c/exec :echo 
                        (-> (io/resource "influxdb")  slurp 
                          (str/replace #"%NODES_TO_JOIN%" (nodesToJoin norder)))  
                        :> "/etc/default/influxdb")      

                      ; Ensure node is running
                     (try (c/exec :service :influxdb :status)
                         (catch RuntimeException _
                         (info node "Starting influxdb...")
                         (c/exec :service :influxdb :start)))
                    
                      (info node "InfluxDB started!")                    
                 )
               )
</code></pre>

The order of the nodes is transformed into the right join string (e.g.: "-join n1:8088,n3:8088" or "" in case of the first node) and written to the /etc/default/influxdb file on the node. 

Guess what, it worked! 

### 3.3 Ooops, too many nodes

However, on node four and five influxdb was dead because of this log message: 

`run: open server: open meta store: too many peers; influxdb v0.9.0 is limited to 3 nodes in a cluster`


### 3.4 The node order changes from test run to test run


Okay...it worked the first time, but the next time the number of clusters didn't add up to 3 again. 

I realized that by removing the meta dir (rm -rf /var/lib/influxdb/meta/*) and restarting influxdb actually worked:  



<pre><code>n3: 


      2015/12/23 18:25:27 Using configuration at: /etc/influxdb/influxdb.conf
      [metastore] 2015/12/23 18:25:27 Using data dir: /var/lib/influxdb/meta
      [metastore] 2015/12/23 18:25:27 Node at n3:8088 [Follower]
      [metastore] 2015/12/23 18:25:27 Joining cluster at: [n1:8088 n2:8088]
      [metastore] 2015/12/23 18:25:27 Joined remote node n1:8088
      [metastore] 2015/12/23 18:25:27 nodeId=3 raftEnabled=true peers=[n3:8088 n2:8088 n1:8088]
      [metastore] 2015/12/23 18:25:28 spun up monitoring for 3
      [store] 2015/12/23 18:25:28 Using data dir: /var/lib/influxdb/data
      [metastore] 2015/12/23 18:25:28 Updating metastore to term=5697 index=114
      [metastore] 2015/12/23 18:25:28 Updated node id=3 hostname=n3:8088

> SHOW SERVERS
id  cluster_addr  raft  raft-leader
1 n2:8088   true  true
2 n1:8088   true  false
3 n3:8088   true  false
4 localhost:8088  false false
</code></pre>
anddd...


<pre><code>root@n2:~# influx
Visit https://enterprise.influxdata.com to register for updates, InfluxDB server management, and monitoring.
Connected to http://localhost:8086 version 0.9.6.1
InfluxDB shell 0.9.6.1
> SHOW SERVERS
id  cluster_addr  raft  raft-leader
1 n2:8088   true  true
2 n1:8088   true  false
3 n3:8088   true  false



root@n1:~# influx
Visit https://enterprise.influxdata.com to register for updates, InfluxDB server management, and monitoring.
Connected to http://localhost:8086 version 0.9.6.1
InfluxDB shell 0.9.6.1
> show servers
id  cluster_addr  raft  raft-leader
1 n2:8088   true  true
2 n1:8088   true  false
3 n3:8088   true  false
</code></pre>


OKay, so in the end the teardown method has to clear out the metadata directory and it's all good.

##3.5. Asserting that all is ok in the setup method

But I won't "be there" every time a test runs to make sure the number of cluster members is 3 on every node! It would be great if we could automate that and fail the test if the setup did not satisfy this condition! 

I managed to put some scripts together with the *influx* client executable. 
The snippet below 

1. waits until the node is up (I can connect with *influx*) - or waits until infinity, 
2. then waits until every other node is up too
3. tests that the SHOW SERVERS outputs 3 lines 


<pre><code class="clojure">(while 
      (try (c/exec :bash "/root/test_cluster.sh") 
              false
           (catch Exception _
              true
            )
       )
       (do 
            (info node "waiting for influx to start...")
            (Thread/sleep 1000)
        )
      )
     (jepsen/synchronize test)
     (c/exec :bash "/root/test_cluster.sh") 
     (info node "This node is OK, sees 3 members in the raft cluster")
</code></pre>


## 4. Questions I have from all this hacking


Questions I have for aphyr:

- is using claypool a bad idea? if not, I'll raise a clean pull request for jepsen.
- have you ran into clj-ssh issues before? any ideas why that could be? 
- what does systemd exactly break?

Question I have for InfluxDB: 

- is there a way to predefine all cluster members in a file (e.g. peers.json)? That would be much easier to deal with compared to the consecutive start
- when are the higher number clusters planned to be supported? 


## 5. What's next? 

We got covered: creating the LXC containers with InfluxDB setup on them in a repeatable, clustered manner for 3 nodes. 


Well, the hard part is ahead: 

Cleanup my hacking mess: 


- Weird locking issue in clj-ssh

The locking mechanism runs on a deadlock sometime...one thread seems to be Thread.sleeping in clj-ssh library while the others are waiting to do something. 
<pre><code>"claypoole-0-4": sleeping, holding [0x00000000fbbe3e68]
  at java.lang.Thread.sleep(Native Method)
  at clj_ssh.ssh$ssh_exec.invoke(ssh.clj:691)
  at clj_ssh.ssh$ssh.invoke(ssh.clj:724)
  at jepsen.control$ssh_STAR_.invoke(control.clj:115)
  at jepsen.control$exec_STAR_.doInvoke(control.clj:120)
  at clojure.lang.RestFn.applyTo(RestFn.java:137)
  at clojure.core$apply.invoke(core.clj:630)
  at jepsen.control$exec.doInvoke(control.clj:136)
  at clojure.lang.RestFn.invoke(RestFn.java:457)
  at jepsen.influxdb$db$reify__7522.setup_BANG_(influxdb.clj:107)
  at jepsen.db$cycle_BANG_.invoke(db.clj:26)
  at clojure.core$partial$fn__4527.invoke(core.clj:2494)
  at jepsen.core$on_nodes$fn__6937.invoke(core.clj:91)
  at clojure.lang.AFn.applyToHelper(AFn.java:154)
  at clojure.lang.AFn.applyTo(AFn.java:144)
  at clojure.core$apply.invoke(core.clj:630)
  at com.climate.claypoole$pmap_core$start_task__6834$fn__6835.invoke(claypoole.clj:312)
  at clojure.lang.AFn.applyToHelper(AFn.java:152)
  at clojure.lang.AFn.applyTo(AFn.java:144)
  at clojure.lang.AFunction$1.doInvoke(AFunction.java:29)
  at clojure.lang.RestFn.invoke(RestFn.java:397)
  at com.climate.claypoole.impl$binding_conveyor_fn$fn__6704.invoke(impl.clj:46)
  at clojure.lang.AFn.applyToHelper(AFn.java:152)
  at clojure.lang.AFn.applyTo(AFn.java:144)
  at clojure.lang.AFunction$1.doInvoke(AFunction.java:29)
  at clojure.lang.RestFn.invoke(RestFn.java:397)
  at clojure.lang.AFn.call(AFn.java:18)
  at java.util.concurrent.FutureTask.run(FutureTask.java:266)
  at java.util.concurrent.ScheduledThreadPoolExecutor$ScheduledFutureTask.access$201(ScheduledThreadPoolExecutor.java:180)
  at java.util.concurrent.ScheduledThreadPoolExecutor$ScheduledFutureTask.run(ScheduledThreadPoolExecutor.java:293)
  at java.util.concurrent.ThreadPoolExecutor.runWorker(ThreadPoolExecutor.java:1142)
  at java.util.concurrent.ThreadPoolExecutor$Worker.run(ThreadPoolExecutor.java:617)
  at java.lang.Thread.run(Thread.java:745)
</code></pre>
- I have to find a better way to store the node orders - this fails at the end, in the test validation currently in Jepsen -- the framework doesn't expect extra tags...
- The real test:) - I'll have to write a client, generators and checkers for InfluxDB, to check whether linearizability holds for all sorts of operations in the presence of network failures created by with nemesis.





I hope this hacking log is useful for anyone who tries to run Jepsen, and/or is experimenting with clustering InfluxDB 0.9.6.1. Comments are welcome! 

Now, I will lay back, and enjoy 10 days of touching no code! 





