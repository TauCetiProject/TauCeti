/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Kernels, quotients, and scalar restriction for finitely presented modules

Over any ring `R`, factoring a linear map `f : M →ₗ[R] N` from a finitely generated module `M`
through `LinearMap.range f` shows that `LinearMap.ker f` is finitely generated whenever
`LinearMap.range f` is finitely presented (`Module.FinitePresentation.fg_ker_of_range`), and
presenting `M ⧸ N` by `Submodule.mkQ` shows that the quotient of a finitely presented module by a
finitely generated submodule is finitely presented (`Module.FinitePresentation.quotient`).

If an `S`-module `P` is finitely presented as an `R`-module along a ring extension where `S` is
finite as a left `R`-module, then `P` is also finitely presented over `S`: `P` is finite over `S`,
and the kernel of any `S`-linear surjection `(Fin n → S) →ₗ[S] P` is finitely generated over `R`
and hence over `S`. Combining this ascent with `Module.FinitePresentation.trans` shows that over a
commutative `R`-algebra `S` that is finitely presented as an `R`-module, an `S`-module is finitely
presented over `S` if and only if it is finitely presented over `R`.

## Main results

* `Module.FinitePresentation.fg_ker_of_range`: if `M` is finitely generated and `LinearMap.range f`
  is finitely presented, then `LinearMap.ker f` is finitely generated.
* `Module.FinitePresentation.quotient`: the quotient `M ⧸ N` of a finitely presented module by a
  finitely generated submodule `N` is finitely presented.
* `Module.FinitePresentation.of_restrictScalars_finitePresentation`: if `S` is finite as a left
  `R`-module and `P` is finitely presented over `R`, then `P` is finitely presented over `S`.
* `Module.finitePresentation_iff_of_finitePresentation`: over a commutative `R`-algebra `S` that is
  finitely presented as an `R`-module, an `S`-module `P` is finitely presented over `S` if and only
  if it is finitely presented over `R`.

## References

* [The Stacks Project, Lemma 10.6.4, Tag 0519](https://stacks.math.columbia.edu/tag/0519).
-/

public section

/-- If the range of a linear map from a finitely generated module is finitely presented, then its
kernel is finitely generated. -/
theorem Module.FinitePresentation.fg_ker_of_range {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R M]
    (f : M →ₗ[R] N) [Module.FinitePresentation R (LinearMap.range f)] :
    (LinearMap.ker f).FG := by
  rw [← LinearMap.ker_rangeRestrict f]
  exact Module.FinitePresentation.fg_ker f.rangeRestrict f.surjective_rangeRestrict

/-- The quotient of a finitely presented module by a finitely generated submodule is finitely
presented. -/
theorem Module.FinitePresentation.quotient {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] {N : Submodule R M} (hN : N.FG) :
    Module.FinitePresentation R (M ⧸ N) :=
  Module.finitePresentation_of_surjective N.mkQ N.mkQ_surjective (by rwa [Submodule.ker_mkQ])

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
