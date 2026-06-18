# Formal Verification & Code Extraction Project

This repository contains the formal verification and code extraction work developed during my undergraduate thesis in Applied Mathematics at the Universidad Tecnológica de la Mixteca (UTM).

## Overview

The goal of this project is to demonstrate a complete workflow for **correct-by-construction software**:
1.  **Specify** algorithms and data structures in the Rocq (Coq) proof assistant.
2.  **Prove** their correctness (e.g., termination, functional correctness) using dependent types and tactical proofs.
3.  **Extract** the verified code into **executable Haskell and OCaml** code.

This approach is critical for developing **reliable and secure systems**, such as network protocols and critical infrastructure, where traditional testing is insufficient.

## Repository Structure

*   **`.v` files (Rocq/Coq):** Formal specifications, lemmas, and proofs.
    *   `PrimerosPasos.v`: Introductory examples of definitions and proofs in Rocq.
    *   `NumBinariosHaskell.v` / `NumBinariosOcaml.v`: Verified operations on binary numbers, extracted to Haskell and OCaml.
    *   `listasHaskell.v` / `listasOcaml.v`: Verified list functions (e.g., append, reverse) extracted to both languages.
*   **`.hs` files (Haskell):** Extracted, executable Haskell code.
*   **`.ml` and `.mli` files (OCaml):** Extracted, executable OCaml code and interface files.

## Key Example: Insertion Sort

The files `insertsort.v` (proof), `insertsort.hs`, `insertsort.ml`, and `insertsort.mli` implement a **verified insertion sort algorithm**.
*   **Property Proven:** The sorting algorithm is correct (produces a sorted permutation of the input list) and terminates for all inputs.
*   **Extraction:** The Coq proof is erased and the computational content is extracted to both Haskell and OCaml, producing efficient, side-effect-free code that inherits the correctness proof.

## How to Compile and Extract

To reproduce the extraction (using Rocq/Coq 8.18+):
1.  Load the `.v` file in CoqIDE or using `coqc`.
2.  Use the `Extraction` command to generate the Haskell or OCaml file (e.g., `Extraction Language Haskell.`).
3.  The extracted `.hs` or `.ml` file can be compiled with GHC or `ocamlc`.

## Skills Demonstrated

*   **Proof Assistants:** Rocq (Coq), dependent types, tactic-based proving.
*   **Functional Programming:** Haskell, OCaml (including module systems and interfaces).
*   **Formal Methods:** Proving termination, soundness, and functional correctness.
*   **Code Extraction:** Translating verified specifications into production-ready functional code.
*   **Machine Learning (Complementary):** Certified in MATLAB for Neural Network design and application.

## Author

Karla Monserrat Martínez López
Licenciatura en Matemáticas Aplicadas, Universidad Tecnológica de la Mixteca (UTM).
