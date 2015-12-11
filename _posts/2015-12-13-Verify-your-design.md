---           
layout: post
title: Can you prove that your code works?
date: 2015-12-13
comments: true
categories: Distributed_Systems Parallel_Computing tlaplus Formal_Methods
tags: [formal methods, tlaplus, pluscal, messaging, enterprise]
---

<img src="images/Edsger_Dijkstra_1994.jpg"/>

>Dijkstra in 1994 (from wikipedia)


The world of formal methods is evolving fast, and already becoming useful to cutting edge tech companies dealing with complex problems. Testing parallel algorithms or ditributed systems is notoriously hard. If you deal with any of these (and there is higher and higher chance that you are), you will want to look at formal methods to have confidence in your design! 

Formal methods fascinated me since I learned about them at my alma mater, Eotvos Lorand Science University. Unfortunately I never got to use them in practice beyond a voice in the back of my head reminding me time to time while coding that I should articulate the invariant of a class or algorithm. This field was always looked as too impractical for most of the problems we are facing in our day job of software development. 

Formal methods - to be more precise: formal specification, verification and model checking - lie somewhere between computer science and engineering. They are typically based on the likes of first order or higher order logic and some branch of math like set theory (ZFC). Formal logic and math are definitely something most programmers don't use (yet) in their daily work - it's coming from and used mostly by the academia. On the other hand, tools around formal verification are getting much better, and already becoming useful to cutting edge tech companies dealing with complex problems. 

The real game changer is model checking. Formal verification is basically working with proofs which - despite the tools and available automations are getting better in this space as well - still can be complex, lengthy and hard to validate. <a href="https://en.wikipedia.org/wiki/Model_checking">Model checking</a> on the other hand is testing a formally defined specification of an algorithm against invariants with smartly chosen, limited sections of the state space. 



##Amazon is using TLA+ 

<a href="http://lamport.org/">Leslie Lamport</a>’s TLA+ (http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html), PlusCal and TLC model checker lets you design the tricky pieces in your software system in a precise way and have it verified by generating all the possible states your system can be! The model checker makes sure your safety invariants (e.g. the bank account should always be nonnegative) and liveness properties (e.g. there should be no deadlocks under any circumstances) are all true in all states or shows you the exact interleavings as a sequence of states of your system what can violate them.

If this all sounds very sci-fi for you, **check this out**!: Amazon is using it already! The April, 2015 issue of CACM published the paper <a href="http://cacm.acm.org/magazines/2015/4/184701-how-amazon-web-services-uses-formal-methods/fulltext">"How Amazon Web Services Uses Formal Methods"</a>. It is about the success of Chris Newcombe, Tim Rath and other team members of the DynamoDB project where they managed to use TLA+ and the TLC model checker as a tool to prove correctness and discover subtle bugs in their various distributed protocols. 

Since I read this paper I found multiple other posts and articles proving Raft for example in Verdi. The formal verification/model checking world is definitely appearing more and more places.

I believe that **formal methods, especially model checking is going to make its way into mainstream software development** in the up and coming years. Here are my reasons:

1. Distributed and parallel systems require specification
2. The demand for distributed and parallel systems is growing
3. Testing these systems is hard 
4. Working with a verifiable design is cool


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
- micro services - so you decided to go down this route and have independent, scalable nodes talking to each other? Great, but guess what: your system is distributed by definition. 

As more and more demand will build up for distributed and parallel systems, we will need expertise and tooling to deal with the complexity it brings.

###3. Why just not test it? 

Testing can become very challenging in distributed and parallel systems. You have to spin up test instances and exercise them real time to force them through interleaving states. 

Besides the possible state space is exponentially growing with every added component, running actual nodes can become prohibitively expensive. 


###The Clean Code example 

Uncle Bob Martin’s Clean Code brings up a very simple example to demonstrate the challenges of testing concurrent code. Let me use this simple example to demonstrate the power of model checking. 

<pre><code>
public class IdGenerator {
	private int lastUsedId;

	public int generateNextId() {
		return lastUsedId++;  
	}
}
</code></pre>
>The code from Clean Code chapter 17

//TODO: REVIEW, pull some explanation from the book

Uncle Bob states that the number of possible execution paths are 17500
Let's see how the PlusCal version of this algorithm looks like. PlusCal is pseudocode - a bit more readable/digestable for programmers - but it translates directly to TLA+. 

<pre><code>

------ MODULE IdGenerator -----------

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
>The IdGenerator PlusCal specification

There are a lot of little details here (usage of labels for steps, arrays are functions, PlusCal/TLA is untyped, processes are not real processes, how this gets tranlated to TLA, etc.) which are extensively described in the excellent, and engaging <a href="">TLA+ Hyperbook</a>. However on a high level I would like to explain what we see here. 


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

The ASCII symbols have actual mathematical corresponding characters. 
Here is the output of the same algorithm by the LaTEX2PDF tool, integrated into the Toolbox (Eclipse based) IDE:

<img src="images/IdGenerator_v1.png"/>

> The IdGenerator PlusCal specification PDF version

### Let's do model checking finally! 

In order to check whether the model of our IdGenerator system with 3 processes would satisfy the IdGeneratorInvariant, we'll create the model in the Toolbox environment, add the IdGeneratorInvariant as a property to check and set the NumProcesses constant to 3. Then we run TLC, the model checker on the model. TLC will fail with the following error: 

<img src="images/failed_tlc.png"/>

> The TLC model checker fails with the violation of our Invariant

What this means is that TLC found a series of potential state transitions allowed by our step definitions where in 7 steps, all 3 processes finish, but two of them end up sharing 45 as an id!! This violates our invariant! 

### Let's fix it! 

The Java code would contain a *synchronized* keyword in Java.

<pre><code>
public class IdGenerator {
  private int lastUsedId;

  public synchronized int generateNextId() {
    return lastUsedId++;  
  }
}
</code></pre>
> Fixed version with synchronized key word

As it's mentioned earlier, labels play an important role in defining atomicity of operations. 

By removing the second label, we are telling TLC that the *updateAndRead* label containing two "steps" is really one atomic operation: 

<img src="images/IdGenerator_v2.png"/>

> The IdGenerator PlusCal specification fixed version

This time, running TLC produces no errors. 


##Challenges and limitations


- Separated design and code 
- Developers are scared of specs because: 
— it smells like waterfall
—  it is hard to write them 
- You have to find the right, relevant abstraction level, otherwise your state space will blow up 


##Possibilities 

- test generation from model failures
- code generation from specs 
- beautiful visualization of specs 
- optimize your distributed system so that you can get more value out of it with more confidence 
-  simulation of 
	-  where your bottleneck will be 


<pre><code>

------------------------ MODULE IdGeneratorByteCode ------------------------


EXTENDS Integers, Sequences,  TLC

CONSTANT  NumberOfProcesses, Locking

(*

--fair algorithm IdGenerator {

  variable  
  object = [lastId |-> 42, lock |-> 0],    
  stacks = [ i \in 1..NumberOfProcesses |-> <<>>],
  returnValue = [i\in 1..NumberOfProcesses |-> -1] 
  ;
  
  define {
    Last(S) == S[Len(S)]
    Pop(S) == SubSeq(S, 1, Len(S)-1)
    AllIsDone ==  (\A i \in 1 .. NumberOfProcesses: pc[i] = "Done")
    AllstackssAreEmpty ==  (\A i \in 1 .. NumberOfProcesses: stacks[i] = <<>>)
    IdsAreAllDifferent == (\A i,j \in 1 .. NumberOfProcesses: i#j => returnValue[i] # returnValue[j])
    IdGeneratorInvariant == AllIsDone => AllstackssAreEmpty /\ IdsAreAllDifferent
  }

  (* update and read are now one atomic step *)
  process(id \in 1 .. NumberOfProcesses) {
   checkLocking: 
   if (Locking) {
        waitForLock: await object.lock = 0;
        lock: object.lock := self;
   };
    \* Load _this_ onto the operand stacks 
    aload0: stacks[self] := Append(stacks[self], object);
    \* copy the top of the stacks 
    dup: stacks[self] := Append(stacks[self], Last(stacks[self]));
    \* retrieve the value of field lastId from the object and store it back on the top of the stacks
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
        
    dup_x1: 
        stacks[self] := <<Last(stacks[self])>> \o stacks[self];
     putfield: 
        object.lastId := Last(stacks[self]);
        stacks[self] := Pop(Pop(stacks[self])) ;
     ret: 
        returnValue[self] := Last(stacks[self]);
        stacks[self] := Pop(stacks[self]);
     if (Locking) {        
        unlock: object.lock := 0;
     };
  }
}*)


</code></pre>