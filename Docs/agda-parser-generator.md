BNFC-like parser generator tool in Agda
=======================================

Background
----------

The Agda programming language, in version 2, has been developed at the Chalmers/GU Department of Computer Science and Engineering since 2006.  It is a functional programming language with strong type system.  Its _dependent types_ allow the programmer to express strong data structure invariants and properties of programs, enabling a correct-by-construction programming style.

Motivations:
* BNFC does not have an Agda backend
* BNFC's backends are quite hackish
* verified parsing is part of verified compilation


Task
----

Use Agda as a programming language to:
1. Parse LBNF-- grammar files.  In the first iteration, this can be done by binding a BNFC-generated Haskell parser for LBNF to Agda.  Finally, this can be done by boot-strapping.
2. Implement a lexer in Agda.
3. Implement the Earley parser in Agda.
4. Implement a lexer generator for Agda in Agda.
5. Implement a parser generator for Agda in Agda.
It is hard to estimate how long steps 3-5 will take.  Concluding the project at 3. would count as success, if correctness guarantees are included.  Step 5 has room for many optimizations and user experience improvements, but any of these would be optional.

Prerequisites
-------------

* Strong functional programming skills
* Strong interest in verified programming
* Good familiarity with proofs by structural induction
* DAT151/DIT231 Programming Language Technology
* DAT350/DIT232 Types for Proofs and Programs

Suggested supervisor: [Andreas Abel](https://www.cse.chalmers.se/~abela)

References
----------

* [BNFC](http://digitalgrammars.org)
* Jacques-Henri Jourdan, François Pottier, Xavier Leroy: [Validating LR(1) Parsers](http://gallium.inria.fr/~fpottier/publis/jourdan-leroy-pottier-validating-parsers.pdf). ESOP 2012: 397-416
* François Pottier: [Reachability and error diagnosis in LR(1) parsers](http://gallium.inria.fr/~fpottier/publis/fpottier-reachability-cc2016.pdf). CC 2016: 88-98
* Denis Firsov and Tarmo Uustalu, [Certified CYK parsing of context-free languages](http://firsov.ee/cert-cfg/), [JLAMP 2014](http://cs.ioc.ee/~tarmo/papers/nwpt12-jlamp.pdf).
* Denis Firsov and Tarmo Uustalu, [Certified normalization of context-free grammars](http://firsov.ee/cert-norm/), [CPP 2015](http://firsov.ee/cert-norm/cfg-norm.pdf).
* Denis Firsov, [Certification of Context-Free Grammar Algorithms](http://firsov.ee/phd/thesis.pdf), PhD thesis, Tallinn University of Technology, 2016.
* Kasper Brink, Stefan Holdermans, Andres Löh, [Dependently Typed Grammars](https://www.andres-loeh.de/DependentlyTypedGrammars/DependentlyTypedGrammars.pdf), MPC 2010.
* Agda development on [github](https://github.com/agda/agda).
* The [menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator.

Keywords
--------

* Agda
* Compiler construction
* Grammars
* Parsing
* Programming language technology
