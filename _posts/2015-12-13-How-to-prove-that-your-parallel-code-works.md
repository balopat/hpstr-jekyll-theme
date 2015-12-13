---           
layout: post
title: How to prove that your parallel code works?
date: 2015-12-13
comments: true
categories: Distributed_Systems Parallel_Computing tlaplus Formal_Methods Model_checking
tags: [formal methods, tlaplus, pluscal, messaging, enterprise, modelchecking, tlc]
---

<img src="{{site.url}}/images/Edsger_Dijkstra_1994.jpg"/>

>Dijkstra in 1994 (from wikipedia)

Testing parallel algorithms or distributed systems is notoriously hard. If you deal with either of them - and there is higher and higher chance that you are already, or will in the future -, you should look at <a href="https://en.wikipedia.org/wiki/Formal_methods">formal methods</a> to have confidence in your design! 
The world of formal methods is evolving fast, and already becoming useful to cutting edge tech companies dealing with complex problems. 


# Formal methods

Formal methods fascinated me since I learned about them at my alma mater, Eotvos Lorand Science University. Unfortunately I never got to use them in practice beyond a voice in the back of my head reminding me time to time while coding that I should articulate the invariant of a class or algorithm. This field was always looked as too impractical for most of the problems we are facing in our day job of software development. 

Formal specification, verification and the lightweight model checking are typically based on the likes of first order or higher order logic and some branch of math like set theory (ZFC). Formal logic and math are definitely something most programmers don't use (yet) in their daily work - it's coming from and used mostly by the academia, all the real life implementations, like prolog, suffer from performance problems. On the other hand, tools around formal verification and model checking are getting much better, and already becoming useful to cutting edge tech companies dealing with complex problems. 

Wikipedia puts model checking the lightweight branch of formal methods - and for a right reason. If you want to have a program formally verified, you have to construct correct mathematical proofs around your formal specification which - despite the tools and available automations are getting better in this space as well - still can be complex, expensive and hard to validate. <a href="https://en.wikipedia.org/wiki/Model_checking">Model checking</a> on the other hand checks a formally specified *model* of an algorithm against limited sections of the state space - keeping it focused, and much more approachable, even so that I could start to comprehend and use it as a software developer.


##Amazon is using TLA+ 

<a href="http://lamport.org/">Leslie Lamport</a>’s <a href="http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html">TLA+</a>, PlusCal and TLC model checker lets you design the tricky pieces in your software system in a precise way and have it verified by generating all the possible states your system can be! The model checker makes sure your safety invariants (e.g. the bank account should always be nonnegative) and liveness properties (e.g. there should be no deadlocks under any circumstances) are all true in all states or shows you the exact interleavings as a sequence of states of your system what can violate them.

If this all sounds very sci-fi for you, **check this out**: Amazon is using it already! The April, 2015 issue of CACM published the paper <a href="http://cacm.acm.org/magazines/2015/4/184701-how-amazon-web-services-uses-formal-methods/fulltext">"How Amazon Web Services Uses Formal Methods"</a>. It is about the success of Chris Newcombe, Tim Rath and other team members of the DynamoDB project where they managed to use TLA+ and the TLC model checker as a tool to prove correctness and discover subtle bugs in their various distributed protocols. 


I believe that **formal methods, especially model checking is slowly going to make its way into mainstream software development** in the up and coming years. Here are my reasons:

1. Distributed and parallel systems require specification
2. The demand for distributed and parallel systems is growing
3. Testing these systems is hard 
4. Verifiable design is an important addition to tools for making better software


###1. Distributed and parallel systems require specification

Distributed and parallel systems require another level of reasoning, where we have to explain how the individual nodes are interacting. 

This is something we rarely can explain by just looking at the code — hence people tend to specify them in comments, wiki pages, boxes and arrows, and other forms of documentation but more importantly: **we reason about them in informally, in prose**. 

As TLA+ and PlusCal are formal languages they make the description more precise. But they are not just another type of documentation: with TLC Model checker you can check for safety and liveness of your design. 

I like to think about it as a simulation of your distributed or parallel system. 

###2. The demand is growing for distributed and parallel systems 

There are a couple of driving forces which causes the everyday developer to meet more and more parallel and distributed systems: 

- computers stopped getting faster - we have to horizontally scale our computations, caching, parallel design and functional languages are the king 
- high availability is getting more and more the norm - it requires removal of SPOFs and hence replication 
- disaster recovery and business continuity is a crucial piece of every enterprise operational strategy - cross datacenter replication is also a non trivial challenge which requires knowledge in distributed systems 
- microservices - so you decided to go down this route and have independent, scalable nodes talking to each other? Great, but guess what: your system is distributed by definition. 

As more and more demand will build up for distributed and parallel systems, we will need expertise and tooling to deal with the complexity it brings.

###3. Why just not test it? 

Testing can become very challenging in distributed and parallel systems. Let me show it through a very simple example taken from Robert C. Martin. 

###The Clean Code example 

<a href="http://www.amazon.com/Clean-Code-Handbook-Software-Craftsmanship/dp/0132350882">Uncle Bob Martin’s Clean Code</a> brings up a very simple example to demonstrate the challenges of testing concurrent code. 

<pre><code>
public class IdGenerator {
	private int lastUsedId;

	public int generateNextId() {
		return ++lastUsedId;  
	}
}
</code></pre>
>The code from Clean Code chapter 13

The problem: given that we create one instance of this class, set the lastUsedId to 42 and then share the instance between two threads there can be three possible outcomes: 

- Thread 1 get's value 43 Thread 2 gets value 44 and lastIdUsed is 44 
- Thread 1 get's value 44 Thread 2 gets value 43 and lastIdUsed is 44 
- Thread 1 get's value 43 Thread 2 gets value 43 and lastIdUsed is 43

The third result can be surprising, we obviously would like to avoid it, and write a test against it. 
The problem is that it is very hard to write a test against it. When we write tests we want to be able to have control over the execution of our code. The concurrent, multithreaded execution of this code however introduces thousands of possible *interleavings* of the instructions in the threads! Controlling these execution paths without explicit control points in the code is currently very challenging. 

Let's see what model checking can offer as an alternative to gain confidence in our design: 

**How do we represent the above java code as a TLA+ model?** Getting the representation right is the most important aspect when creating a model, we have to find the right level of abstraction so that:

1. the abstraction is not too high level so that it is still relevant to the problem
2. the abstraction is not too low level so that the state space does not explode

The core behaviour what we have to recognize is that ++lastUsedId is **not an atomic operation**. 
Why isn't ++lastUsedId atomic? Because of how the Java Memory Model works!
Uncle Bob details it in the Appendix of Clean Code - where it turns out that this single Java statement actually translates to 8 instructions in the JVM bytecode! 

For the sake of simplicity I chose to represent this with two atomic steps in our model: a read and an update.

<div id="tabs">
  <ul>
    <li><a href="#tabs-1">PlusCal</a></li>
    <li><a href="#tabs-2">PDF</a></li>
  </ul>
  <div id="tabs-1">
<pre><code>------ MODULE IdGenerator -----------

EXTENDS Integers, TLC 
CONSTANT NumberOfProcesses

--fair algorithm IdGenerator {

  variable lastIdUsed = 42, processIds = [ i \in 1.. NumberOfProcesses |-> 0];
  
  define {
    AllIsDone ==  (\A i \in 1 .. NumberOfProcesses: pc[i] = "Done")
    IdsAreAllDifferent == (\A i,j \in 1 .. NumberOfProcesses: i#j => processIds[i] # processIds[j])
    IdGeneratorInvariant == AllIsDone => IdsAreAllDifferent
  }

  process(proc \in 1 .. NumberOfProcesses) {
    update: lastIdUsed := lastIdUsed + 1;
    read: processIds[self] := lastIdUsed
    
  }

}
</code></pre>
  </div>
  <div id="tabs-2"><img src="{{site.url}}/images/IdGenerator_v1.png">
  </div>
</div>
> The IdGenerator PlusCal specification in the original code and PDF version

There are a lot of little details here (usage of labels for steps, arrays are functions, PlusCal/TLA is untyped, processes are not real processes, how this gets tranlated to TLA, etc.) which are extensively described in the excellent, and engaging <a href="">TLA+ Hyperbook</a>. However on a high level I would like to explain what we see here. 


*(If your curiousity is not satisfied by the simple two step representation, I included at the bottom of this post the 8 step model with a parameter to switch between modes with and without locking).*



### Parts of the specification 

Our specification consists of the NumberOfProcesses constant, the definition of the algorithm and the definition of the mystical sounding IdGeneratorInvariant.


The algorithm defines the lastIdUsed variable - which could be anything, I set it to 42 so that it follows the Clean Code explanation. The processIds variable represents the id assigned to each of the processes as an array containing the processIds on the indices equivalent to the index of the process itself. 

The processes are defined by a simple "method-like" structure starting with *process*, and they all do the same: 

1. update the lastIdUsed
2. read the value to be the process' id

Labels play an important role: each labeled statement is an atomic step. As the observant reader might notice: this is exactly how we represent in this PlusCal code the lack of *synchronized* keyword in our Java code. 

The invariant is going to be our "test"! There are infinite amount of invariants which we could define, and all of them would be true. For example 2 == 2 is an invariant of all algorithms. Not too interesting though. The IdGeneratorInvariant is much more interesting in our case. What it means that "given all processes are done, the ids are all different". This is a boolean statement. Let's see if it's true initially, when the algorithm starts and even throughout the whole execution: as processes are not done, the invariant is true! To calculate all the possible combinations when processes finished, we'd have to decide one more factor: the number of processes. 

The NumberOfProcesses constant's role is to be the single parameter which we can change to try out different models. A valid model of the system where we have 1 process. This case the lack of synchronization won't cause any issues. We can have 3 or 4 processes, this will make more interesting cases. 

To understand what a model is (as defined in the TLA+ Hyperbook):

> **The Standard Model**
> An abstract system is described as a collection of behaviors, each representing a possible execution of the system, where a behavior is a sequence of states and a state is an assignment of values to variables.


### Let's do model checking finally! 

In order to check whether the model of our IdGenerator system with 3 processes would satisfy the IdGeneratorInvariant, we'll create the model in the Toolbox environment, add the IdGeneratorInvariant as a property to check and set the NumProcesses constant to 3. Then we run TLC, the model checker on the model. TLC will fail with the following error: 

<img src="{{site.url}}/images/failed_tlc.png"/>

> The TLC model checker fails with the violation of our Invariant

What this means is that TLC found a series of potential state transitions allowed by our step definitions where in 7 steps, all 3 processes finish, but two of them end up sharing 45 as an id!! This violates our invariant! 

### Let's fix it! 

The Java code would contain a *synchronized* keyword in Java.

<pre><code>
public class IdGenerator {
  private int lastUsedId;

  public synchronized int generateNextId() {
    return ++lastUsedId;  
  }
}
</code></pre>
> Fixed version with synchronized key word

As it's mentioned earlier, labels play an important role in defining atomicity of operations. 

By removing the second label, we are telling TLC that the *updateAndRead* label containing two "steps" is really one atomic operation: 

<img src="{{site.url}}/images/IdGenerator_v2.png"/>

> The IdGenerator PlusCal specification fixed version

This time, running TLC produces no errors. 

###4. Working with a verifiable design is cool

Anytime I show TLA+, TLC and Toolbox to developers, they get excited about it, insipired by the thought of a verified design, they start thinking about potential usages. I believe that these are not isolated cases and many programmers will be insipired to at least give it a go, or even go further and better the world of model checking and verification, and make it more approachable, more user friendly.

There are many more model checking tools out there, including Alloy, SPIN, PAT, MALPAS, UPPAAL which I know nothing about yet, but excited to have a look and check them out. 

The world is running on software. Having safer, well designed systems is more and more crucial, and as software crafters, it is imperative to explore new tools in our toolbox to tackle the increasing complexity. 


*Appendix: For the adventurous, the 8 step model of the IdGenerator in PlusCal:*

<div id="tabs-bytecode">
  <ul>
    <li><a href="#tabs-bytecode-pluscal">PlusCal</a></li>
    <li><a href="#tabs-bytecode-pdf">PDF</a></li>
  </ul>
  <div id="tabs-bytecode-pluscal">
<pre><code>------------------------ MODULE IdGeneratorByteCode ------------------------

EXTENDS Integers, Sequences,  TLC

CONSTANT  NumberOfProcesses, Locking

(*
--fair algorithm IdGenerator {

  variable  
  this = [lastId |-> 42, lock |-> 0],    
  stacks = [ i \in 1..NumberOfProcesses |-> <<>>],
  returnValue = [i\in 1..NumberOfProcesses |-> -1] 
  ;
  
  define {
    Last(S) == S[Len(S)]
    Pop(S) == SubSeq(S, 1, Len(S)-1)
    AllIsDone ==  (\A i \in 1 .. NumberOfProcesses: pc[i] = "Done")
    AllStacksAreEmpty ==  (\A i \in 1 .. NumberOfProcesses: stacks[i] = <<>>)
    IdsAreAllDifferent == (\A i,j \in 1 .. NumberOfProcesses: i#j => returnValue[i] # returnValue[j])
    IdGeneratorInvariant == AllIsDone => AllStacksAreEmpty /\ IdsAreAllDifferent
  }

  (* update and read are now one atomic step *)
  process(id \in 1 .. NumberOfProcesses) {
    \* if Locking constant is TRUE, then we can't start the process of executing ++lastId unless the lock is unlocked 
    checkLocking: if (Locking) {
                        waitForLock: 
                            await this.lock = 0;
                            this.lock := self;
                   };
    \* Load _this_ onto the operand stacks 
    aload0: stacks[self] := Append(stacks[self], this);
    \* copy the top of the stacks 
    dup: stacks[self] := Append(stacks[self], Last(stacks[self]));
    \* retrieve the value of field lastId from _this_ and store it back on the top of the stacks
    getfield_lastId: 
          with (lastId = Last(stacks[self]).lastId) {
            stacks[self] := Append(Pop(stacks[self]), lastId);
          };
    \* push the integer constant 1 on the stacks 
    iconst_1: stacks[self] := Append(stacks[self], 1);
     \* integer add the top two values on the top of the stacks
    iadd: 
        with (a = Last(stacks[self]), b = Last(Pop(stacks[self]))) {
            stacks[self] := Append(Pop(Pop(stacks[self])) , a+b);
        };
    \* duplicate the value on top of the stack and put it before _this_
    dup_x1: 
        stacks[self] := <<Last(stacks[self])>> \o stacks[self];
    \* Store the top value on the operand stack into the field value of the 
    \* current object, represented by the net-to-top value on the operand stack, _this_
    putfield: 
        this.lastId := Last(stacks[self]);
        stacks[self] := Pop(Pop(stacks[self])) ;
    \* return the top(and only) value on the stack
    ireturn: 
        returnValue[self] := Last(stacks[self]);
        stacks[self] := Pop(stacks[self]);
     if (Locking) {        
        unlock: this.lock := 0;
     };
  }
}*)
</code></pre>
</div>
<div id="tabs-bytecode-pdf"><img src="{{site.url}}/images/IdGeneratorByteCode-1.png"/> <img src="{{site.url}}/images/IdGeneratorByteCode-2.png"/></div>
</idv>