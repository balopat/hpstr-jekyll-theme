---           
layout: post
title: Crash management vs Bug/Issue tracking
date: 2014-03-26 
updated: 2014-03-26
comments: true
categories: Web/Tech
tags: [blog, culture, lean, systems thinking, big design upfront]
---


I bumped into [an article about bugtracking systems](http://mashable.com/2014/02/16/bug-tracking-apps/) last month, and I was really thinking about reacting to it as I think it mixes two type of software: bug/issue tracking and crash management. 

This is totally understandable as the crash management market as such is relatively new (4-5 years old), and does not have yet a huge proliferation in the industry. 

So what is exactly the difference? 

Let's start with the **bug&issue management systems**: historically these tools were created to manage the workflow of your bugs **reported by your users**. Then later it seemed to be a good idea to start to capture actual tasks in these tools (the dream of the micromanagers) - then later on it became the center of the agile backlog management universe (where in my humble opinion Rally beats most of them). 

Examples: JIRA, Bugzilla, Mantis, FogBugz, etc.

Ok.

So what is crash management then? 

**Crash management** is specifically a piece of software which handles submission of stacktraces from automated sources. **The entries are created by apps** running into exceptional constellations where they typically have an either transparent (catch all unhandled exception automatically) or non-transparent (reporter.logthis(exception)) way of reporting it to a central server. The very same exception can be reported many times before it's fixed so these tools have usually advanced plotting and historical monitoring on the crashes. Also crashes change slightly due to changes in the codebase but still relate to the same underlying problem where systems can give a very good hint about who ran into the same issue within your company. 

Examples: Sentry, Raygun, Exceptional, Samebug, etc.



