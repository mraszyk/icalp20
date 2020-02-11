# From Functional Nondeterministic Transducers to Deterministic Two-Tape Automata

## Directory Structure:

`html/` contains the generated HTML page of the formalization in Isabelle

`thys/` contains the formalization of the paper in Isabelle

## Formalization in Isabelle

The formal development can be browsed as a generated HTML page (see the html directory).
A better way to study the theory files, however, is to open them in Isabelle/jEdit.

The raw Isabelle sources are included in a separate directory called `thys`.

The formalization can been processed with Isabelle2019, which can be downloaded from

https://isabelle.in.tum.de/website-Isabelle2019/

and installed following the standard instructions from

https://isabelle.in.tum.de/website-Isabelle2019/installation.html

To build the theories and regenerate the HTML page, run
`isabelle build -o browser_info -v -D thys`
in the root directory of this repository.
