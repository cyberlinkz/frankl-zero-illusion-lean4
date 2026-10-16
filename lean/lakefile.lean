import Lake
open Lake DSL

/-!
# Frankl Lab — Independent arXiv Release Lean 4 Package Configuration
Canonical Lake configuration (`lakefile.lean`) for Lean 4.8.0.
Compiles standalone with zero external dependencies.
-/

package «frankl_arxiv_release» where

@[default_target]
lean_lib «FranklArxivRelease» where
  srcDir := "."
  roots := #[
    `Frankl_a018,
    `Frankl_Biclosed,
    `Frankl_Universal_Certificates,
    `Frankl_Poonen_Breaker,
    `Frankl_Concrete_Bridge
  ]
