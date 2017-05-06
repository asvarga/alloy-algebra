
/*
Demo 2: This version uses a group module and uses ~28k clauses.

PROBLEM:

For the sake of good design, the 'groups' module is kept as general as possible.
Anything can go in a group, and we wish to restrict it fo this specific application.
Here we say that all elements of Groups are Dogs, so that this universe is the same
as that in demo 1.

Alloy's approach to this generate's a large amount of clauses for the general module,
and then adds a small amount of restricting clauses for this specific application,
resulting in an unnecessarily large number of clauses.

This defers the job of simplifying the model to the SAT-solver itself.
While this isn't too problematic in this case, I experienced cases where increased
extensibility caused a jump from ~300k to ~20M clauses, which is unacceptable.

FAILED SOLUTION:

Utilizing Alloy's support for parameterized modules doesn't work.
Alloy's approach to parameterization is purely syntactic.
In short, this allows for example Group<Dog> and Group<Cat> types to exist together,
but doesn't allow predicates/structures that use both together, like isomorphisms.

PROPOSED SOLUTION:

Add a phase to the compilation chain before reduction to CNF.
In general, interleaving phases that expand and reduce the representation of the model
will keep the maximum data footprint down:

   /\
  /  \   vs  
 /    \      /\/\/\

I don't know what such a phase would do because I don't know how Alloy works,
but one can imagine basic optimizations at the level of relations or sets.

Allowing coding practices and patterns from standard programming experience
to carry over to Alloy will be helpful in reducing the overhead of modelling.
*/

--------

open groups

sig Dog {}
fact onlyDogs { Group.E in Dog }

run {} for exactly 1 Group, exactly 4 Dog








