---           
layout: post
title: Jepsen and InfluxDB, Chapter II. Stabilizing the environment and our first healthy histories  
date: 2016-01-15
comments: true
categories: Distributed_Systems
tags: [jepsen, influxdb, distributed systems, testing, consistency models]
---


In my first post I struggled with SSH: 
- problem was that the SSH command did not finish 
- c/su solves it - but I am already root, why would I need su? it must be a bug somewhere...

Next problem was serialization: 


∀sket ‏@aphyr  23 Dec 2015
@balopat 
"tests can take extra tags but they have to be serializable via fressian. The right place for the state var you added is probably in
the db object, not the test. Just use a let binding; reify closes over lexical scope"


OK.


  recur works to method heads The method bodies of reify are lexical
  closures, and can refer to the surrounding local scope:
  
  (str (let [f "foo"] 
       (reify Object 
         (toString [this] f))))
  == "foo"

So it was pretty simple, just to put let around my db object and voila, it works! 



Failing r w mix, maybe due to consistency=one?

<--- HTTP 204 http://n2:8086/write?u=root&p=root&db=jepsen&rp=default&precision=n&consistency=one (18ms)
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


Then...weird assertion error:



java.util.concurrent.ExecutionException: java.lang.AssertionError: Assert failed: i
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


 Then weird error write 3 read 3.0 illegal? (svg)

Then (double cast) it:




