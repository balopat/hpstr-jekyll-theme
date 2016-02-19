---
layout: 
title: Automated tests visualized like a protective layer around a graph
categories: []
tags: []
published: True

---

A program is a graph of potential execution paths. 
Automated tests are covering these execution paths. 

Consequences of this metaphor: 

When there is a disconnect, the program "pierces" through the protective layer. 
The difference between monolith and testable design is obvious, inlcuding the tradeoffs: more moving pieces, but they are simpler individually than the larg monolith

More entry points vs. single entry point = main method vs webservices vs microservices 

Tests: more entry points 

Visualization is: 
- capture at every execution point
 -- the stacktrace  (basic "stackspace" evolution)
 -- the values of local variables (more detailed "exact" statespace evolution)