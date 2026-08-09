# An Introduction to Intuitionistic Mathematics

This repo contains a single-file, exercise-focused tutorial on formal theorem proving with Intuitionistic Mathematics, [AnIntroductionToIntuitionisticMathematics.agda](AnIntroductionToIntuitionisticMathematics.agda).

By downloading it and filling out the exercises, you will learn how to write programs and formal proofs in the programming language and proof assistant Agda.

The reader is expected to install [Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html) along with the [Emacs text editor](https://www.gnu.org/software/emacs/download.html) and then run the shell command `agda --emacs-mode setup` *before* starting Emacs and navigating to the tutorial (e.g. through the menubar via *File* → *Open File...*).

There are no prerequisites to this tutorial beyond this installation and being interested in in math and/or coding.

Learning to formally state and prove propositions about programs and other mathematical objects is extremely rewarding, and well worth the effort.

## Index
### Preface
- Setting up Agda in Emacs
- Loading the file with "C-c C-l"
- Adjusting font size with "C-c C-+", "C-c C--"
### Part 1. Pure Functional Programming
- Purity and totality
#### Chapter 1. Booleans
- Curried functions
- Commenting code in and out with "C-x C-;"
- Filling in holes with "C-c C-Space"
- Testing code with "C-c C-n"
#### Chapter 2. Natural Numbers
- Structural recursion
- BUILTIN-pragmas
- Assisted pattern matching with "C-c C-c"
- Jumping between holes with "C-c C-f" and "C-c C-b"
#### Chapter 3. Parametric Polymorphism
- Explicit and implicit named parameters in types
- Parametric/Church encodings
- Inspecting types with "C-c C-,", "C-c C-.", and "C-u C-u ..."
- Refining a solution with "C-c C-r"
#### Chapter 4. Algebraic Datatypes
- Sum and product types
- Generic datatypes
- Defining helper functions with "where" clauses
- Exponential types
### Part 2. Constructive Theorem Proving
- Intuitionistic vs classical logic
#### Chapter 5. Intuitionistic Propositions
- Provable and refutable types
- Propositional "and", "or", "implies", and "forall"
- The principle of explosion and propositional negation
- The law of the excluded middle and double negation elimination
#### Chapter 6. Dependent Types

