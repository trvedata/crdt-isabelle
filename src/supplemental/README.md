# About

In this directory we provide (non-anonymised) supplementary material for the
OOPSLA/SPLASH 2017 submissions "Verifying Strong Eventual Consistency in
Distributed Systems" by Gomes, Kleppmann, Mulligan, and Beresford.

The directory consists of two components:

  1. An annotated auto-generated PDF of all of our Isabelle definitions and theorems.
  2. Our Isabelle theory files, containing our definitions and theorems which can be
     checked by Isabelle2016-1.

To verify that our proofs are correct follow these instructions:

Download Isabelle2016-1 from the Isabelle homepage:

    https://isabelle.in.tum.de/

(Assuming Linux) extract the .tar.gz file by

    tar xzf file.tar.gz

Run Isabelle for the first time by running

    $Isabelle2016-1-DIRECTORY/Isabelle2016-1.run

This will open a jEdit window after which Isabelle will begin building various
"heaps".  Once Complex_Main has been built, which should take around 15 minutes on
a moderately fast machine, open one of RGA.thy, ORSet.thy, or Counter.thy.

Isabelle will ask whether all theory dependencies should be loaded.  Click "yes".

After a few minutes, Isabelle will start to process the file that you have opened,
once all dependencies have been processed.  This is indicated by a "purple wave"
flowing down the theory file.  Scroll to the bottom of the file, and the entirety
of the theory should be processed.  Note that purple indicates Isabelle is processing
the definition or theorem (some steps may take a while), whereas red indicates
processing has failed.  Isabelle should not show any red when processing our
development.

To check that our theorems are "real" theorems: press CTRL+F to open search.  Type
sorry into the search box, click the "All buffers" radio button, and click "Search".
No instances of "sorry" (i.e. an admitted theorem, without proof) should be present,
indicating that we rely on no axioms other than those described in our paper.
     