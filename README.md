Isabelle formalisation of CRDTs
===============================

This repository shows how to use [Isabelle](http://isabelle.in.tum.de/)
(theorem-proving software) to prove the correctness of several operation-based
[CRDTs](https://hal.inria.fr/inria-00555588) (data structures that can be edited
concurrently and merged automatically).

The results from this work were published in a paper titled
[Verifying strong eventual consistency in distributed systems](https://dl.acm.org/citation.cfm?doid=3152284.3133933)
at OOPSLA 2017 ([arXiv version](https://arxiv.org/abs/1707.01747)). Please cite it as:

> Victor B. F. Gomes, Martin Kleppmann, Dominic P. Mulligan, and Alastair R. Beresford.
> Verifying Strong Eventual Consistency in Distributed Systems.
> Proceedings of the ACM on Programming Languages (PACMPL), Vol. 1, Issue OOPSLA, October 2017.
> [doi:10.1145/3133933](https://doi.org/10.1145/3133933)

The formal proof development is published in the
[Isabelle Archive of Formal Proofs](https://www.isa-afp.org/index.html) under the title
[A framework for establishing Strong Eventual Consistency for Conflict-free Replicated Datatypes](https://www.isa-afp.org/entries/CRDT.html) (July 2017).

About
-----

This project was developed by
[Victor Gomes](http://www.cl.cam.ac.uk/~vb358/),
[Martin Kleppmann](http://martin.kleppmann.com/),
[Dominic Mulligan](http://dominic-mulligan.co.uk/), and
[Alastair Beresford](http://www.cl.cam.ac.uk/~arb33/).

Copyright 2017, University of Cambridge.
This software is released under the Apache License, Version 2.0 (see `LICENSE`).

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
