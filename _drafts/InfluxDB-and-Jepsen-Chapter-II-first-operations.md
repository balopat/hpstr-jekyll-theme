---           
layout: post
title: Jepsen and InfluxDB, Chapter II. Where is InfluxDB on the CAP scale?
comments: true
categories: Distributed_Systems
tags: [jepsen, influxdb, distributed systems, testing, consistency models]
---

This is a continuation of [the hacking to get Jepsen work with InfluxDB](/distributed_systems/Hacking-up-a-testing-environment-for-jepsen-and-influxdb/). I'm reviewing both technologies at the same time and logging it on my blog in the hope that readers will learn from it, that both Kyle Kingsbury and InfluxDB will benefit from my feedback, if not anything else than that they have produced products that are great - and lastly that I'll manage to organize my experimentation around a memorable narrative. 

# 1. The journey towards an almost stable Jepsen/InfluxDB environment 

This part is all about fixing my Jepsen environment for InfluxDB, and getting to a stage where it's usable for exploring InfluxDB's behavior. If you're not interested in these gory details, just want to learn about InfluxDB, please go ahead and skip to [Is InfluxDB CP or AP?](#is-influxdb-ap-or-cp)

## Solving the hung SSH issue

In [my first post in this series](/distributed_systems/Hacking-up-a-testing-environment-for-jepsen-and-influxdb/) I struggled with SSH: 

- problem was that the SSH command did not finish 
- c/su solves it - but I am already root, why would I need su? it must be a bug somewhere...

## Solving the serialization issue

Next problem was serialization, which Kyle responded to on Twitter: 


>∀sket ‏@aphyr  23 Dec 2015
>@balopat 
>"tests can take extra tags but they have to be serializable via fressian. The right place for the state var you added is probably in
>the db object, not the test. Just use a let binding; reify closes over lexical scope"

OK, time to learn some Clojure stuff! What the heck is reify? 

<pre><code class="clojure">  ;The method bodies of reify are lexical
  ;closures, and can refer to the surrounding local scope:
  
  (str (let [f "foo"] 
       (reify Object 
         (toString [this] f))))
  == "foo"</code></pre>

But...the best description I found was on the [Practical Elegance blog](http://decomplecting.org/blog/2014/10/29/reify-this/)

So it was pretty simple, just to put let around my db object and voila, it works! 

## The first real failure

Failing r w mix, maybe due to consistency=one?

<pre><code class="bash"><--- HTTP 204 http://n2:8086/write?u=root&p=root&db=jepsen&rp=default&precision=n&consistency=one (18ms)
Content-Encoding: gzip
Request-Id: c8fb8be0-b3d7-11e5-8018-000000000000
X-Influxdb-Version: 0.9.6.1
Date: Tue, 05 Jan 2016 18:11:47 GMT
OkHttp-Selected-Protocol: http/1.1
OkHttp-Sent-Millis: 1452017507593
OkHttp-Received-Millis: 1452017507610


<--- END HTTP (0-byte body)
INFO  jepsen.util - 1	:ok	:write	4
INFO  jepsen.core - Worker 1 done
INFO  jepsen.util - 2	:invoke	:write	4
---> HTTP POST http://n3:8086/write?u=root&p=root&db=jepsen&rp=default&precision=n&consistency=one
Content-Type: text/plain
Content-Length: 21
answers answer=4.0 1
</code></pre>


## Double problems... 

Then...weird assertion error:


<pre><code class="clojure">java.util.concurrent.ExecutionException: java.lang.AssertionError: Assert failed: i
 at java.util.concurrent.FutureTask.report (FutureTask.java:122)
    java.util.concurrent.FutureTask.get (FutureTask.java:192)
    clojure.core$deref_future.invoke (core.clj:2186)
    clojure.core$future_call$reify__6736.deref (core.clj:6683)
    clojure.core$deref.invoke (core.clj:2206)
    clojure.core$map$fn__4553.invoke (core.clj:2624)
    clojure.lang.LazySeq.sval (LazySeq.java:40)
    clojure.lang.LazySeq.seq (LazySeq.java:49)
    clojure.lang.Cons.next (Cons.java:39)
    clojure.lang.RT.next (RT.java:674)
    clojure.core/next (core.clj:64)
    clojure.core.protocols/fn (protocols.clj:170)
    clojure.core.protocols$fn__6478$G__6473__6487.invoke (protocols.clj:19)
    clojure.core.protocols$seq_reduce.invoke (protocols.clj:31)
    clojure.core.protocols/fn (protocols.clj:101)
    clojure.core.protocols$fn__6452$G__6447__6465.invoke (protocols.clj:13)
    clojure.core$reduce.invoke (core.clj:6519)
    clojure.core$into.invoke (core.clj:6600)
    jepsen.checker$compose$reify__6600.check (checker.clj:257)
    jepsen.checker$check_safe.invoke (checker.clj:39)
    jepsen.core$run_BANG_$fn__6821.invoke (core.clj:421)
    jepsen.core$run_BANG_.invoke (core.clj:373)
    jepsen.influxdb_test/fn (influxdb_test.clj:13)
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
    user$eval85$fn__144$fn__175.invoke (form-init7200082598926404175.clj:1)
    user$eval85$fn__144$fn__145.invoke (form-init7200082598926404175.clj:1)
    user$eval85$fn__144.invoke (form-init7200082598926404175.clj:1)
    user$eval85.invoke (form-init7200082598926404175.clj:1)
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
Caused by: java.lang.AssertionError: Assert failed: i
 at knossos.linear.report$time_coords$fn__6396.invoke (report.clj:179)
    clojure.core$map$fn__4553.invoke (core.clj:2624)
    clojure.lang.LazySeq.sval (LazySeq.java:40)
    clojure.lang.LazySeq.seq (LazySeq.java:49)
    clojure.lang.RT.seq (RT.java:507)
    clojure.core/seq (core.clj:137)
    clojure.core.protocols$seq_reduce.invoke (protocols.clj:30)
    clojure.core.protocols/fn (protocols.clj:101)
    clojure.core.protocols$fn__6452$G__6447__6465.invoke (protocols.clj:13)
    clojure.core$reduce.invoke (core.clj:6519)
    clojure.core$into.invoke (core.clj:6600)
    knossos.linear.report$time_coords.invoke (report.clj:185)
    knossos.linear.report$learnings.invoke (report.clj:427)
    knossos.linear.report$render_analysis_BANG_.invoke (report.clj:632)
    jepsen.checker$reify__6560.check (checker.clj:55)
    jepsen.checker$compose$reify__6600$fn__6602.invoke (checker.clj:256)
    clojure.core$pmap$fn__6744$fn__6745.invoke (core.clj:6729)
    clojure.core$binding_conveyor_fn$fn__4444.invoke (core.clj:1916)
    clojure.lang.AFn.call (AFn.java:18)
    java.util.concurrent.FutureTask.run (FutureTask.java:266)
    java.util.concurrent.ThreadPoolExecutor.runWorker (ThreadPoolExecutor.java:1142)
    java.util.concurrent.ThreadPoolExecutor$Worker.run (ThreadPoolExecutor.java:617)
    java.lang.Thread.run (Thread.java:745)
</code></pre>


 Then weird error write 3 read 3.0 illegal? (svg)

Then (double cast) it:


same error came up in a very obscure way in knossos:


<pre><code class="clojure">lein test knossos.linear.report-test
analyis: {:valid? false, :configs ({:model #knossos.model.CASRegister{:value 42}, :pending [{:process 0, :type :invoke, :f :read, :value 42.0, :index 0}]}), :final-paths #{[{:op nil, :model #knossos.model.CASRegister{:value 42}} {:op {:process 0, :type :ok, :f :read, :value 42.0, :index 1}, :model #knossos.model.Inconsistent{:msg can't read 42.0 from register 42}}]}, :previous-ok nil, :op {:process 0, :type :ok, :f :read, :value 42.0, :index 1}} 
hello:  :index nil 
 (nil {:process 0, :type :ok, :f :read, :value 42.0, :index 1})
lein test :only knossos.linear.report-test/bad-analysis-test-3
</code></pre>

But --- this was after I opened a ticket: [https://github.com/aphyr/knossos/issues/8](https://github.com/aphyr/knossos/issues/8)

Thoughts: we can still fail it, but we need to be more clear about it. 

## 1.2 InfluxDB issues close to startup  

These issues still haunt me. Sometimes, when the cluster was just created, InfluxDB gets into weird states. 


Sometimes: 

<pre><code class="clojure">
Error at Setup:  #error {
 :cause {"error":"metastore database error: error fetching meta data: no leader detected during fetchMetaData"}

 :via
 [{:type java.lang.RuntimeException
   :message {"error":"metastore database error: error fetching meta data: no leader detected during fetchMetaData"}

   :at [org.influxdb.impl.InfluxDBErrorHandler handleError InfluxDBErrorHandler.java 19]}]
 :trace
 [[org.influxdb.impl.InfluxDBErrorHandler handleError InfluxDBErrorHandler.java 19]
  [retrofit.RestAdapter$RestHandler invoke RestAdapter.java 242]
  [org.influxdb.impl.$Proxy0 writePoints nil -1]
  [org.influxdb.impl.InfluxDBImpl write InfluxDBImpl.java 161]
  [org.influxdb.impl.BatchProcessor write BatchProcessor.java 166]
  [org.influxdb.impl.BatchProcessor put BatchProcessor.java 179]
  [org.influxdb.impl.InfluxDBImpl write InfluxDBImpl.java 147]
  [sun.reflect.NativeMethodAccessorImpl invoke0 NativeMethodAccessorImpl.java -2]
  [sun.reflect.NativeMethodAccessorImpl invoke NativeMethodAccessorImpl.java 62]
  [sun.reflect.DelegatingMethodAccessorImpl invoke DelegatingMethodAccessorImpl.java 43]
  [java.lang.reflect.Method invoke Method.java 497]
  [clojure.lang.Reflector invokeMatchingMethod Reflector.java 93]
  [clojure.lang.Reflector invokeInstanceMethod Reflector.java 28]
  [jepsen.influxdb$db$reify__7310 setup_BANG_ influxdb.clj 237]
  [jepsen.db$cycle_BANG_ invoke db.clj 25]
  [clojure.core$partial$fn__4527 invoke core.clj 2494]
  [jepsen.core$on_nodes$fn__6710 invoke core.clj 86]
  [clojure.core$pmap$fn__6744$fn__6745 invoke core.clj 6729]
  [clojure.core$binding_conveyor_fn$fn__4444 invoke core.clj 1916]
  [clojure.lang.AFn call AFn.java 18]
  [java.util.concurrent.FutureTask run FutureTask.java 266]
  [java.util.concurrent.ThreadPoolExecutor runWorker ThreadPoolExecutor.java 1142]
  [java.util.concurrent.ThreadPoolExecutor$Worker run ThreadPoolExecutor.java 617]
  [java.lang.Thread run Thread.java 745]]}
</code></pre>


This happens when WAL is not started yet for DB: 
<pre><code class="">
java.lang.RuntimeException: {"error":"retention policy not found: default"}

 at org.influxdb.impl.InfluxDBErrorHandler.handleError (InfluxDBErrorHandler.java:19)
    retrofit.RestAdapter$RestHandler.invoke (RestAdapter.java:242)
    org.influxdb.impl.$Proxy0.writePoints (:-1)
    org.influxdb.impl.InfluxDBImpl.write (InfluxDBImpl.java:161)
    org.influxdb.impl.BatchProcessor.write (BatchProcessor.java:166)
    org.influxdb.impl.BatchProcessor.put (BatchProcessor.java:179)
    org.influxdb.impl.InfluxDBImpl.write (InfluxDBImpl.java:147)
    sun.reflect.NativeMethodAccessorImpl.invoke0 (NativeMethodAccessorImpl.java:-2)
    sun.reflect.NativeMethodAccessorImpl.invoke (NativeMethodAccessorImpl.java:62)
    sun.reflect.DelegatingMethodAccessorImpl.invoke (DelegatingMethodAccessorImpl.java:43)
    java.lang.reflect.Method.invoke (Method.java:497)
    clojure.lang.Reflector.invokeMatchingMethod (Reflector.java:93)
    clojure.lang.Reflector.invokeInstanceMethod (Reflector.java:28)
    jepsen.influxdb$db$reify__7310.setup_BANG_ (influxdb.clj:237)
    jepsen.db$cycle_BANG_.invoke (db.clj:25)
    clojure.core$partial$fn__4527.invoke (core.clj:2494)
    jepsen.core$on_nodes$fn__6710.invoke (core.clj:86)
    clojure.core$pmap$fn__6744$fn__6745.invoke (core.clj:6729)
    clojure.core$binding_conveyor_fn$fn__4444.invoke (core.clj:1916)
    clojure.lang.AFn.call (AFn.java:18)
    java.util.concurrent.FutureTask.run (FutureTask.java:266)
    java.util.concurrent.ThreadPoolExecutor.runWorker (ThreadPoolExecutor.java:1142)
    java.util.concurrent.ThreadPoolExecutor$Worker.run (ThreadPoolExecutor.java:617)
    java.lang.Thread.run (Thread.java:745)
</code></pre>



# 2. Is InfluxDB AP or CP?



For data it is AP: 

If you choose consistency level ALL, then your write will fail, and it will succeed, which is a bit confusing, you'll get a timeout error, but you don't have any information about that the write actually succeeded to the local shard.  
If you choose consistency level ANY, then your write will succeed, but the history won't be linearizable. 

How available is AP? 

1. with consistency level ALL your writes will wait until "shard-timemout"
2. ideally the shard groups are in the CP cluster, so even if the consistency level is ANY, the write should time out after a while (?) or just wait --- it depends on the timestamp I guess whether it needs a new shard or not

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

Meaning, that if my random data is going to be 




