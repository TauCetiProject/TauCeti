/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.Geometry.Manifold.Morse.CWModel.Lacunary

/-!
# The lacunary principle for the integral cohomology of a Morse function

Let `f` be a Morse function on a compact boundaryless manifold `M` such that no two critical points
of `f` have indices differing by one, for instance one all of whose indices are even. By the
lacunary principle the integral homology `Hₙ(M; ℤ)` is the free abelian group `ℤ^(Cₙ)` on the set
`Cₙ` of critical points of index `n`
(`TauCeti.IsMorse.nonempty_singularHomology_int_linearEquiv_finsupp_of_forall_ne_add_one`). This
file deduces the cohomology of `M` with coefficients in any abelian group `A`.

Since the integral homology is free, hence projective, in every degree, the `Ext¹` terms of the
universal coefficient sequence vanish and the Kronecker map identifies `Hⁿ(M; ℤ, A)` with
`Hom(Hₙ(M; ℤ), A)` (`TopCat.singularKroneckerLinearEquivOfProjectiveHomology`). A homomorphism out
of the free abelian group on `Cₙ` is a function on `Cₙ` (`Finsupp.llift`), so

`Hⁿ(M; A) ≃ A^(Cₙ)`

(`TauCeti.IsMorse.nonempty_singularCohomology_int_linearEquiv_pi_of_forall_ne_add_one`). Hence:

* `Hⁿ(M; A)` is free when `A` is, and finitely generated when `A` is
  (`TauCeti.IsMorse.free_singularCohomology_int_of_forall_ne_add_one`,
  `TauCeti.IsMorse.finite_singularCohomology_int_of_forall_ne_add_one`);
* the rank of `Hⁿ(M; ℤ)` is the number of critical points of index `n`
  (`TauCeti.IsMorse.finrank_singularCohomology_int_eq_ncard_of_forall_ne_add_one`);
* if all indices are even, `Hⁿ(M; A)` vanishes in odd degrees
  (`TauCeti.IsMorse.isZero_singularCohomology_int_of_odd`).

The integral coefficients are the integers lifted to the universe of `M`, as for the singular
homology of a space in an arbitrary universe.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 (the CW model).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1, Theorem 3.2
  (the universal coefficient theorem).
-/

public section

open AlgebraicTopology CategoryTheory Limits Module Set
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

/-- Under the lacunary hypothesis the integral homology is projective in every degree, being free on
the critical points. -/
private theorem IsMorse.projective_singularHomology_int_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    Projective (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) :=
  have := hf.free_singularHomology_int_of_forall_ne_add_one hind n
  inferInstance

/-- **Cohomology is a product over the critical points.** If no two critical points of a Morse
function `f` on a compact boundaryless manifold have indices differing by one, then the cohomology
`Hⁿ(M; A)` with coefficients in an abelian group `A` is the group `A^(Cₙ)` of functions on the set
`Cₙ` of critical points of index `n`. -/
theorem IsMorse.nonempty_singularCohomology_int_linearEquiv_pi_of_forall_ne_add_one
    (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1)
    (A : Type u) [AddCommGroup A] (n : ℕ) :
    Nonempty ((TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{u} ℤ)) ℤ
        (ModuleCat.of ℤ A) n ≃ₗ[ℤ]
      (↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} → A)) := by
  have := hf.projective_singularHomology_int_of_forall_ne_add_one hind
  obtain ⟨e⟩ := hf.nonempty_singularHomology_int_linearEquiv_finsupp_of_forall_ne_add_one hind n
  exact ⟨(TopCat.of M).singularKroneckerLinearEquivOfProjectiveHomology _ (ModuleCat.of ℤ A) n ≪≫ₗ
    e.arrowCongr (LinearEquiv.refl ℤ A) ≪≫ₗ (Finsupp.llift A ℤ ℤ _).symm⟩

/-- **Cohomology is free.** If no two critical points of a Morse function on a compact boundaryless
manifold have indices differing by one, then the cohomology `Hⁿ(M; A)` is a free abelian group in
every degree when `A` is free; in particular the integral cohomology is free. -/
theorem IsMorse.free_singularCohomology_int_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1)
    (A : Type u) [AddCommGroup A] [Module.Free ℤ A] (n : ℕ) :
    Module.Free ℤ ((TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{u} ℤ)) ℤ
      (ModuleCat.of ℤ A) n) :=
  have := hf.free_singularHomology_int_of_forall_ne_add_one hind n
  have := hf.finite_singularHomology_int_of_forall_ne_add_one hind n
  TopCat.free_singularCohomology_of_projective_homology_lt _ _ n
    fun j _ ↦ hf.projective_singularHomology_int_of_forall_ne_add_one hind j

/-- **Cohomology is finitely generated.** If no two critical points of a Morse function on a compact
boundaryless manifold have indices differing by one, then the cohomology `Hⁿ(M; A)` is a finitely
generated abelian group in every degree when `A` is finitely generated. -/
theorem IsMorse.finite_singularCohomology_int_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1)
    (A : Type u) [AddCommGroup A] [Module.Finite ℤ A] (n : ℕ) :
    Module.Finite ℤ ((TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{u} ℤ)) ℤ
      (ModuleCat.of ℤ A) n) :=
  have := hf.projective_singularHomology_int_of_forall_ne_add_one hind n
  have := hf.finite_singularHomology_int_of_forall_ne_add_one hind n
  TopCat.finite_singularCohomology_of_projective_homology_lt _ _ n
    fun j _ ↦ hf.projective_singularHomology_int_of_forall_ne_add_one hind j

/-- **The rank of integral cohomology counts critical points.** If no two critical points of a Morse
function `f` on a compact boundaryless manifold have indices differing by one, then the rank of
`Hⁿ(M; ℤ)` is the number of critical points of index `n`. -/
theorem IsMorse.finrank_singularCohomology_int_eq_ncard_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    finrank ℤ ((TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{u} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{u} ℤ)) n) =
      {x ∈ criticalPoints I f | manifoldMorseIndex I f x = n}.ncard := by
  have := hf.projective_singularHomology_int_of_forall_ne_add_one hind
  have := hf.free_singularHomology_int_of_forall_ne_add_one hind n
  have := hf.finite_singularHomology_int_of_forall_ne_add_one hind n
  refine ((TopCat.of M).singularKroneckerLinearEquivOfProjectiveHomology _ _ n).finrank_eq.trans ?_
  rw [Module.finrank_linearMap, finrank_ulift, finrank_self, mul_one,
    hf.finrank_singularHomology_int_eq_ncard_of_forall_ne_add_one hind]

/-- **Odd cohomology vanishes for a Morse function with only even indices.** On a compact
boundaryless manifold carrying a Morse function all of whose critical points have even index, the
cohomology `Hⁿ(M; A)` vanishes in odd degrees `n`, for every abelian group `A`. -/
theorem IsMorse.isZero_singularCohomology_int_of_odd (hf : IsMorse I f)
    (heven : ∀ x ∈ criticalPoints I f, Even (manifoldMorseIndex I f x))
    (A : Type u) [AddCommGroup A] {n : ℕ} (hn : Odd n) :
    IsZero ((TopCat.of M).singularCohomology (ModuleCat.of ℤ (ULift.{u} ℤ)) ℤ
      (ModuleCat.of ℤ A) n) :=
  TopCat.isZero_singularCohomology_of_projective_homology_lt _ _
    (fun j _ ↦ hf.projective_singularHomology_int_of_forall_ne_add_one
      (forall_manifoldMorseIndex_ne_add_one_of_even heven) j)
    (hf.isZero_singularHomology_of_odd heven _ hn)

end TauCeti
