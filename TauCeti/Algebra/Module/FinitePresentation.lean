/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Scalar restriction for finitely presented modules

If an `S`-module `P` is finitely presented as an `R`-module along a ring extension where `S` is
finite as a left `R`-module, then `P` is also finitely presented over `S`: `P` is finite over `S`,
and the kernel of any `S`-linear surjection `(Fin n → S) →ₗ[S] P` is finitely generated over `R`
and hence over `S`. Combining this ascent with `Module.FinitePresentation.trans` shows that over a
commutative `R`-algebra `S` that is finitely presented as an `R`-module, an `S`-module is finitely
presented over `S` if and only if it is finitely presented over `R`.

## Main results

* `Module.FinitePresentation.of_restrictScalars_finitePresentation`: if `S` is finite as a left
  `R`-module and `P` is finitely presented over `R`, then `P` is finitely presented over `S`.
* `Module.finitePresentation_iff_of_finitePresentation`: over a commutative `R`-algebra `S` that is
  finitely presented as an `R`-module, an `S`-module `P` is finitely presented over `S` if and only
  if it is finitely presented over `R`.

## References

* [The Stacks Project, Lemma 10.6.4, Tag 0519](https://stacks.math.columbia.edu/tag/0519).
-/

public section

/-- If `S` is finite as a left `R`-module and `P` is finitely presented as an `R`-module, then `P`
is finitely presented as an `S`-module (Stacks, Lemma 10.6.4, Tag 0519). -/
@[stacks 0519]
theorem Module.FinitePresentation.of_restrictScalars_finitePresentation
    (R S P : Type*) [Ring R] [Ring S] [AddCommGroup P] [Module R S] [IsScalarTower R S S]
    [Module R P] [Module S P] [IsScalarTower R S P]
    [Module.Finite R S] [Module.FinitePresentation R P] :
    Module.FinitePresentation S P := by
  have : Module.Finite S P := .of_restrictScalars_finite R S P
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S P
  refine Module.finitePresentation_of_surjective f hf ?_
  exact Submodule.FG.of_restrictScalars R
    (Module.FinitePresentation.fg_ker (f.restrictScalars R) hf)

/-- Over an `R`-algebra `S` that is finitely presented as an `R`-module, an `S`-module `P` is
finitely presented over `S` if and only if it is finitely presented over `R`
(Stacks, Lemma 10.6.4, Tag 0519). -/
@[stacks 0519]
theorem Module.finitePresentation_iff_of_finitePresentation
    {R S P : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
    [Module.FinitePresentation R S] :
    Module.FinitePresentation S P ↔ Module.FinitePresentation R P :=
  ⟨fun _ ↦ .trans R P S, fun _ ↦ .of_restrictScalars_finitePresentation R S P⟩
