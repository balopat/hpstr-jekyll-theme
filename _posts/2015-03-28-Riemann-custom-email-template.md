---           
layout: post
title: A taste of riemann.io with templatized emails
date: 2015-05-28
comments: true
categories: Tech
tags: [software craftsmanship, agile, persistence]
---

#Riemann is a flexible monitoring/alerting solution

At a client, currently we are facing a very interesting problem: we have a lot of tiny little applications which are all monitoring different parts of different applications. Some of them are written in Java some of them in C#, or maybe even in Python, some of them have very simple logic, some of them are much more complex and obscurely hides it within a couple of stored procedures. As this is a financial firm, it is very important to react in time if certain metrics go into the danger zone, otherwise the underlying problem might have a big financial impact. 

Some of the features these monitoring/reporting/alerting applications have in common: 

- a periodic observation of a system for health check
- customizable logic around the alerting, sometimes via using multiple observations rolled up over time (i.e. standard deviation over a moving time window)
- customizable email templates, which are using the details of the observation

<a href="http://riemann.io">Riemann</a> came into the picture because of it's flexibility compared to Nagios, and because it's programmability for alerts compared to Graphana & Graphite which we use for creating our dashboards and near-realtime post-mortem analysis of our distributed systems if something goes wrong.   

Riemann's mission statement also sounds convincing enough to jump into the setup:
 
> Riemann provides low-latency, transient shared state for systems with many moving parts.

My biggest concerns against Riemann are: 
 
 * how does it scale? 
 * How hard it is going to be to explain Clojure to our infrastructure guys? 

**I will not answer these concerns in this post** but I will share the first steps of my proof of concept. 


#Proof of concept: setting up my own email templates in Riemann.

Goals: I want to be able to use my event data freely. I want to be able to define as many email templates as I feel like for specialized event streams, as a function of the data of my events.  If I can prove that Riemann can does that, that will be one big step in the Proof of Concept process. 

#Step 1. Setting up Riemann 

I went through the  <a href="http://riemann.io/quickstart.html">Riemann quickstart</a> and had the server setup, the test event was working, and this is how it looked like: 

This is a Ruby client using Interactive Ruby (IRB), wh

<pre><code>
$  r << { 
host: "www1", 
service: "http req", 
metric: 2.53, 
state: "critical", 
description: "Request took 2.53 seconds.", 
tags: ["http"]
}

ruby-1.9.3 :003 > r['service =~ "http%"']
[<Riemann::Event time: 1330041937, 
state: "critical", 
service: "http req", 
host: "www1", 
description: "Request took 2.53 seconds.", 
tags: ["http"], 
ttl: 300.0, 
metric_f: 2.5299999713897705>]
</code></pre>

#Step 2. Sending email about my own event 

I wanted to send an email about my own field. 

The following IRB code submits my event with a field called "testfield" with a value "bla"

<pre><code>
$ irb -r riemann/client
irb(main):004:0> r = Riemann::Client.new
 => #<Riemann::Client ... >
irb(main):004:0> r << { testfield: "bla" }
=> nil
</code></pre>

I wanted to send an email with a subject "test" using my own smtp server with authentication to send the body containing "bla".



## 2.1. Write unit tests for your alerting configuration logic!! 

Riemann provides a test framework to test your configuration, I followed <a href="http://riemann.io/howto.html#writing-tests">the guide to write tests</a>.
After spamming my inbox with loads of messages, and being a TDD enthusiast, I realized that I should point it out first :) 

So let's run the tester without any testcode:


<pre><code>
~/dev/riemann-0.2.9 $ bin/riemann test etc/riemann.config
INFO [2015-03-28 15:21:41,514] main - riemann.repl - REPL server {:port 5557, :host 127.0.0.1} online

Testing clojure.core

Ran 0 tests containing 0 assertions.
0 failures, 0 errors.
</code></pre>

The tests are expressing my expectation, that I would like to see events turning up on my test tap called **:my-events** which are not nil in the :testfield. 


<pre><code>
(let [email (mailer {
					  :from "fromemail@address"
			          :host "...mysmtp..." 
				  	  :tls :yes 
				  	  :user "..." 
				  	  :pass "..." 
				  	  :port 587
					})]
		(streams
		     (tap :my-events (io (email "to-email@address")))
		)
)



(tests
  (deftest my-events-test
    ;; tests case 1: testfield is not nil
    (is (= (inject! [
                      { 
                      :service "an event with testfield"
                      :testfield "bla"
                      :time 1
                      }
                    ])
           {:my-events [ ;; I expect that my tap will contain this exact one event
                      { 
                      :service "an event with testfield"
                      :testfield "bla"
                      :time 1
                      }
            ]}))
    ;; tests case 2: testfield is nil
    (is (= (inject! [
                      { 
                        :service "an event without testfield"
                        :time 1
                      }
                    ])
           {:my-events []})) ;; I expect that my tap will contain no events

))
</code></pre>


Executing the test fails as expected:

<pre><code>
bin/riemann test etc/riemann.config
INFO [2015-03-28 15:54:59,110] main - riemann.repl - REPL server {:port 5557, :host 127.0.0.1} online

Testing riemann.config-test

FAIL in (my-events-test) (riemann.config:63)
expected: (= (inject! [{:service "an event without testfield", :time 1}]) {:my-events []})
  actual: (not (= {:my-events [{:service "an event without testfield", :time 1}]} {:my-events []}))

Ran 1 tests containing 2 assertions.
1 failures, 0 errors.
</code></pre>

To make my tests pass I used the **where*** function which enables me to define my filter as the function of my event.
Also for experimentation I put in a prn function, to see the actual event as well. 

<pre><code>
...
(streams
   (where* (fn [e](not (= nil (:testfield e))))
     (tap :my-events (io (email "to-email@address")))
     prn
   )
 )
 ....
</code></pre>

And the result: 

<pre><code>
bin/riemann test etc/riemann.config
INFO [2015-03-28 16:01:44,937] main - riemann.repl - REPL server {:port 5557, :host 127.0.0.1} online

Testing riemann.config-test
{:service "an event with testfield", :time 1, :testfield "bla"}

Ran 1 tests containing 2 assertions.
0 failures, 0 errors.
</code></pre>


## 2.2 Let's use the default mailer in Riemann 

I started off with the first recommended solution on the <a href="http://riemann.io/howto.html">Riemann - How to page</a> and used the default mailer setup. Also as Riemann is using Postal in the background, I managed to set up after a bit of tweaking the right TLS based authentication with my own SMTP server. 

<pre><code>
(let [email (mailer {
					  :from "fromemail@address"
			          :host "...mysmtp..." 
				  	  :tls :yes 
				  	  :user "..." 
				  	  :pass "..." 
				  	  :port 587
					})]

</code></pre>

And, as expected, I got the email, I was happy to see the details, and the actual default email format Riemann chose to represent events: 

<img src="/images/riemann_default_email_02.png">


## 2.3 Gaining control: fill out details from the event 

One step towards the template solution is to actually use the event fields in the body of the email. 
I did manage to achieve this via these steps:

- I had to use **smap** in the Riemann library to transform my email sending into an explicit function of the event
- I had to use Postal's send-message function directly so that I can get control over the :body tag 
- I used Clojure's str function to concatate the desired values adding up to this line: 

**:body (reduce str [ "test body: " (:testfield e) ] )**

Putting it into context:

<pre><code>
(streams
        (where* (fn [e](not (= nil (:testfield e))))
     		(tap :my-events (io (
	            (smap (fn [e] 
	                (postal.core/send-message 
	                  { 	
	                  	  :host "...mysmtp..." 
	                  	  :tls :yes 
	                  	  :user "..." 
	                  	  :pass "..." 
	                  	  :port 587}  
	                  { 
		                  :from "fromemail@address" 
		                  :to "to-email@address" 
		                  :subject "My test subject" 
		                  :body (reduce str [ "test body: " (:testfield e) ] )
	                }
	              )
	            )
	          )
	          )))
          prn	
        )
  )
</code></pre>

So when I send exactly the same event again:

<pre><code>
irb(main):004:0> r << { testfield: "bla" }
=> nil
</code></pre>

It results in a nice email with the body actually containing my testfield's value, great!!!	

<img src="/images/riemann_my_test_email_01.png">


#Step 3. Introducing Selmer for templating

In order to get to a template based email, I needed a template language. I wanted to have an existing HTML template, which I can change from the config. 

<pre><code>
&lt;html&gt;
    &lt;head&gt;
        &lt;meta http-equiv=&quot;Content-Type&quot; content=&quot;text/html; charset=UTF-8&quot;&gt;
        &lt;title&gt;My beautiful email&lt;/title&gt;
    &lt;/head&gt;
    &lt;body&gt;
        &lt;h2&gt;Hello &#123;&#123;testfield&#125;&#125;!&lt;/h2&gt;
    &lt;/body&gt;
&lt;/html&gt;
</code></pre>

After researching the available Clojure templating solutions I chose to use <a href="https://github.com/yogthos/Selmer">Selmer</a> because simply that was the closest to my current mindset, I haven't spent too much time on comparing other solutions, I am sure that if you want, you can integrate with any other templating solutions with very similar steps. 

In order to enable Selmer I just downloaded the jar (I had it in my local maven repo after playing with it in leiningen) and added it to the classpath:

<pre><code>
~/dev/riemann-0.2.9 $ export EXTRA_CLASSPATH=lib/selmer-0.8.2.jar 
~/dev/riemann-0.2.9 $ bin/riemann etc/riemann.config 
</code></pre>


And this is the riemann.config to enable it:

<pre><code>
(use 'selmer.parser)

(selmer.parser/set-resource-path! "/Users/balopat/dev/riemann-0.2.9/etc/")

(streams
   (where* (fn [e] (not (= nil (:testfield e))))
       prn 
       (tap :my-events 
          (io 
            (smap (fn [e] 
               (let [msg-body [
                                   {:type "text/html"
                                   :content (render-file "template.html" e) }
                                   ] 
                               ]
                 (postal.core/send-message 
                   { :host "..." 
                     :tls :yes 
                     :user "..." 
                     :pass  "..."
                     :port 587}  
                   { 
                   	:from "fromemail@address" 
                   	:to "to-email@address" 
                   	:subject "Templatized fun"                 
                   	:body msg-body 
                   }
                 )                
               )
               )
            ) 
          )
      )
   )
)
</code></pre>

And the result: 

<img src="/images/riemann_templatized_email_03.png">

Yaay! 

#4. Conclusion 

Riemann is as hackable/transformable as Clojure which basically sets the functional limits to nothing. 
Clojure itself is a matter of taste, but I personally think that having a testable, functional language as configuration is a big plus. 

As per the proof of concept, I believe the functionally Riemann is very promising. In terms of non-functional requirements I will have to look into it more heavily and benchmark it to determine if this is going to be a viable solution or not. 

I hope you enjoyed the walkthrough, please let me know if I overcomplicated things, I would love to learn more about the technologies involved!




