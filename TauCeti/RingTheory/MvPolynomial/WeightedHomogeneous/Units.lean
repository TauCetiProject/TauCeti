/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.GradedAlgebra.Localization.Away

/-!
# Homogeneous units and shift classes of weighted polynomial rings

Give `MvPolynomial σ R` the grading `weightedHomogeneousSubmodule R w` determined by an arbitrary
weight function `w : σ → ι` into an additive commutative group `ι`.

Over any nontrivial commutative semiring `R`, every weighted-homogeneous unit of `MvPolynomial σ R`
has nonzero constant term, hence lies in degree `0`:
`homogeneousUnitDegrees (weightedHomogeneousSubmodule R w) = ⊥`, without any positivity or
finiteness assumption on `w` or `σ`, and the shift class group is canonically `ι`.

Over an additively cancellative domain `R` (in particular any commutative domain or field),
`MvPolynomial σ R` is a domain. Localizing away from a weighted-homogeneous element `f` associated
to a finite product `∏ j ∈ s, p j` of weighted-homogeneous primes `p j` of weights `e j` produces
units whose degrees generate `s.sup (fun j ↦ AddSubgroup.zmultiples (e j))`, equivalently
`AddSubgroup.closure (e '' s)` (for the ungraded unit description see
`MvPolynomial.isUnit_away_iff_of_prime` and
`MvPolynomial.exists_unit_mul_prod_zpow_eq_of_associated_prod_prime` in
`TauCeti.Algebra.MvPolynomial.Units`). For a single weighted-homogeneous prime `f` of weight `e`,
the homogeneous unit degrees are `AddSubgroup.zmultiples e`; when `ι = ℤ`, the shift class group is
canonically `ZMod e.natAbs`, sending the class of a shift `d` to `(d : ZMod e.natAbs)`.

## Main definitions and results

* `SetLike.GradedMonoid (weightedHomogeneousSubmodule R w)`: global graded-monoid instance on the
  weighted homogeneous submodules.
* `TauCeti.homogeneousUnitDegrees_weightedHomogeneousSubmodule`: for a nontrivial `R` and any
  weights `w : σ → ι`, `homogeneousUnitDegrees (weightedHomogeneousSubmodule R w) = ⊥`.
* `TauCeti.shiftClassGroupWeightedEquiv`: the shift class group of `MvPolynomial σ R` is `ι`.
* `TauCeti.homogeneousUnitDegrees_awayGrading_weighted_of_associated_prod_prime` and
  `TauCeti.homogeneousUnitDegrees_awayGrading_weighted_of_prime`: the homogeneous unit degrees
  after inverting a product of weighted-homogeneous primes, or a single weighted-homogeneous prime.
* `TauCeti.shiftClassGroupAwayWeightedEquiv` and `TauCeti.shiftClassGroupAwayWeightedProdEquiv`:
  for `ℤ`-weights, the shift class groups `ZMod e.natAbs` and `ZMod (s.gcd e).natAbs`.
-/

public section

namespace TauCeti

open MvPolynomial TauCeti.GradedAlgebra

/-- The weighted homogeneous submodules of `MvPolynomial σ R` form a graded monoid. Since
`SetLike.GradedMonoid` is `Prop`-valued, registering this globally carries no data and cannot
conflict with another grading. -/
instance {R σ M : Type*} [CommSemiring R] [AddCommMonoid M] {w : σ → M} :
    SetLike.GradedMonoid (weightedHomogeneousSubmodule R w) :=
  WeightedHomogeneousSubmodule.gradedMonoid

section Semiring

variable (R : Type*) [CommSemiring R] [Nontrivial R] {σ ι : Type*} [AddCommGroup ι] (w : σ → ι)

/-- Over a nontrivial commutative semiring `R`, every weighted-homogeneous unit of
`MvPolynomial σ R` has nonzero constant coefficient, hence weight `0`. No positivity or finiteness
assumption on `w` or `σ`, nor reducedness of `R`, is needed. -/
@[simp]
theorem homogeneousUnitDegrees_weightedHomogeneousSubmodule :
    homogeneousUnitDegrees (weightedHomogeneousSubmodule R w) = ⊥ := by
  rw [eq_bot_iff]
  refine homogeneousUnitDegrees_le_iff.mpr fun u d hu ↦ ?_
  have h0 : (u : MvPolynomial σ R).coeff 0 ≠ 0 := by
    rw [← constantCoeff_eq]
    exact (u.isUnit.map constantCoeff).ne_zero
  rw [AddSubgroup.mem_bot, ← hu h0, map_zero]

/-- For a nontrivial commutative semiring `R` and any weights `w : σ → ι`, the shift class group of
`MvPolynomial σ R` is `ι`. -/
noncomputable def shiftClassGroupWeightedEquiv :
    ShiftClassGroup (weightedHomogeneousSubmodule R w) ≃+ ι :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (homogeneousUnitDegrees_weightedHomogeneousSubmodule R w)).trans
    QuotientAddGroup.quotientBot

/-- `shiftClassGroupWeightedEquiv` sends the shift class of `d : ι` to `d`. -/
@[simp]
theorem shiftClassGroupWeightedEquiv_mk (d : ι) :
    shiftClassGroupWeightedEquiv R w (d : ShiftClassGroup (weightedHomogeneousSubmodule R w)) =
      d := by
  -- Both quotient equivalences act as the identity on representatives.
  rfl

/-- The inverse of `shiftClassGroupWeightedEquiv` sends `d : ι` to its shift class. -/
@[simp]
theorem shiftClassGroupWeightedEquiv_symm_apply (d : ι) :
    (shiftClassGroupWeightedEquiv R w).symm d = d :=
  (shiftClassGroupWeightedEquiv R w).symm_apply_eq.mpr
    (shiftClassGroupWeightedEquiv_mk R w d).symm

end Semiring

section Domain

variable {R σ ι : Type*} [CommSemiring R] [IsCancelAdd R] [IsDomain R] [AddCommGroup ι]
  (w : σ → ι)

/-- **Homogeneous unit degrees of a weighted polynomial ring localized at a product of primes.**
Over an additively cancellative domain `R`, if `f : MvPolynomial σ R` is weighted homogeneous of
weight `e_f` and associated to a finite product `∏ j ∈ s, p j` of weighted-homogeneous primes `p j`
of weights `e j`, then the homogeneous unit degrees of `Localization.Away f` are
`s.sup (fun j ↦ AddSubgroup.zmultiples (e j))`. -/
theorem homogeneousUnitDegrees_awayGrading_weighted_of_associated_prod_prime
    {J : Type*} {s : Finset J} {f : MvPolynomial σ R} {e_f : ι}
    (hf : f ∈ weightedHomogeneousSubmodule R w e_f) {p : J → MvPolynomial σ R} {e : J → ι}
    (hp_mem : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (e j))
    (hp_prime : ∀ j ∈ s, Prime (p j)) (hassoc : Associated f (∏ j ∈ s, p j)) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      s.sup (fun j ↦ AddSubgroup.zmultiples (e j)) := by
  classical
  let _ : GradedAlgebra (weightedHomogeneousSubmodule R w) := weightedGradedAlgebra R w
  rw [homogeneousUnitDegrees_awayGrading_of_associated_prod_prime
    (weightedHomogeneousSubmodule R w) hf hp_mem hp_prime hassoc,
    homogeneousUnitDegrees_weightedHomogeneousSubmodule R w, bot_sup_eq]

/-- Closure form of `homogeneousUnitDegrees_awayGrading_weighted_of_associated_prod_prime`: the
homogeneous unit degrees of `Localization.Away f` are the subgroup generated by the weights `e j`
(`j ∈ s`). -/
theorem homogeneousUnitDegrees_awayGrading_weighted_eq_closure_of_associated_prod_prime
    {J : Type*} {s : Finset J} {f : MvPolynomial σ R} {e_f : ι}
    (hf : f ∈ weightedHomogeneousSubmodule R w e_f) {p : J → MvPolynomial σ R} {e : J → ι}
    (hp_mem : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (e j))
    (hp_prime : ∀ j ∈ s, Prime (p j)) (hassoc : Associated f (∏ j ∈ s, p j)) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.closure (e '' (s : Set J)) := by
  classical
  rw [homogeneousUnitDegrees_awayGrading_weighted_of_associated_prod_prime w
    hf hp_mem hp_prime hassoc, ← Function.comp_def, ← Finset.sup_image,
    AddSubgroup.finsetSup_zmultiples, Finset.coe_image]

/-- **Homogeneous unit degrees of a weighted polynomial ring localized at a prime.** Over an
additively cancellative domain `R`, if `f : MvPolynomial σ R` is prime and weighted homogeneous of
weight `e`, then the homogeneous unit degrees of `Localization.Away f` are
`AddSubgroup.zmultiples e`. -/
theorem homogeneousUnitDegrees_awayGrading_weighted_of_prime
    {f : MvPolynomial σ R} {e : ι} (hf : f ∈ weightedHomogeneousSubmodule R w e)
    (hp : Prime f) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples e := by
  classical
  let _ : GradedAlgebra (weightedHomogeneousSubmodule R w) := weightedGradedAlgebra R w
  rw [homogeneousUnitDegrees_awayGrading_of_prime (weightedHomogeneousSubmodule R w) hf hp,
    homogeneousUnitDegrees_weightedHomogeneousSubmodule R w, bot_sup_eq]

end Domain

section IntWeights

variable {R σ : Type*} [CommSemiring R] [IsCancelAdd R] [IsDomain R] (w : σ → ℤ)

/-- For integer weights `w : σ → ℤ`, localizing `MvPolynomial σ R` away from a weighted-homogeneous
element `f` associated to a finite product `∏ j ∈ s, p j` of weighted-homogeneous primes `p j` of
weights `e j` gives homogeneous unit degrees `AddSubgroup.zmultiples (s.gcd e)`. -/
theorem homogeneousUnitDegrees_awayGrading_weighted_int_of_associated_prod_prime
    {J : Type*} {s : Finset J} {f : MvPolynomial σ R} {e_f : ℤ}
    (hf : f ∈ weightedHomogeneousSubmodule R w e_f) {p : J → MvPolynomial σ R} {e : J → ℤ}
    (hp_mem : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (e j))
    (hp_prime : ∀ j ∈ s, Prime (p j)) (hassoc : Associated f (∏ j ∈ s, p j)) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples (s.gcd e) := by
  rw [homogeneousUnitDegrees_awayGrading_weighted_of_associated_prod_prime w
    hf hp_mem hp_prime hassoc, ← Function.comp_def, ← Finset.sup_image, Int.finsetSup_zmultiples,
    Finset.gcd_image, Function.id_comp]

/-- For integer weights `w : σ → ℤ` and a prime weighted-homogeneous polynomial `f` of weight `e`,
the shift class group of `Localization.Away f` is `ZMod e.natAbs`. -/
noncomputable def shiftClassGroupAwayWeightedEquiv {f : MvPolynomial σ R} {e : ℤ}
    (hf : f ∈ weightedHomogeneousSubmodule R w e) (hp : Prime f) :
    ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf) ≃+ ZMod e.natAbs :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (homogeneousUnitDegrees_awayGrading_weighted_of_prime w hf hp)).trans
    (Int.quotientZMultiplesEquivZMod e)

/-- `shiftClassGroupAwayWeightedEquiv` sends the class of a shift `d : ℤ` to `(d : ZMod e.natAbs)`.
-/
@[simp]
theorem shiftClassGroupAwayWeightedEquiv_mk {f : MvPolynomial σ R} {e : ℤ}
    (hf : f ∈ weightedHomogeneousSubmodule R w e) (hp : Prime f) (d : ℤ) :
    shiftClassGroupAwayWeightedEquiv w hf hp d = d := by
  -- Both quotient equivalences are induced by maps on representatives, the second being the cast
  -- `ℤ → ZMod e.natAbs`.
  rfl

/-- The inverse of `shiftClassGroupAwayWeightedEquiv` sends `(d : ZMod e.natAbs)` to the shift class
of `d`. -/
@[simp]
theorem shiftClassGroupAwayWeightedEquiv_symm_intCast {f : MvPolynomial σ R} {e : ℤ}
    (hf : f ∈ weightedHomogeneousSubmodule R w e) (hp : Prime f) (d : ℤ) :
    (shiftClassGroupAwayWeightedEquiv w hf hp).symm d = d :=
  (shiftClassGroupAwayWeightedEquiv w hf hp).symm_apply_eq.mpr
    (shiftClassGroupAwayWeightedEquiv_mk w hf hp d).symm

/-- The inverse of `shiftClassGroupAwayWeightedEquiv` sends `x : ZMod e.natAbs` to the shift class
of `ZMod.cast x : ℤ`. -/
theorem shiftClassGroupAwayWeightedEquiv_symm_apply {f : MvPolynomial σ R} {e : ℤ}
    (hf : f ∈ weightedHomogeneousSubmodule R w e) (hp : Prime f) (x : ZMod e.natAbs) :
    (shiftClassGroupAwayWeightedEquiv w hf hp).symm x = (ZMod.cast x : ℤ) := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast x]
  exact shiftClassGroupAwayWeightedEquiv_symm_intCast w hf hp (ZMod.cast x)

/-- For integer weights `w : σ → ℤ` and a weighted-homogeneous polynomial `f` associated to a finite
product `∏ j ∈ s, p j` of weighted-homogeneous primes of weights `e j`, the shift class group of
`Localization.Away f` is `ZMod (s.gcd e).natAbs`. -/
noncomputable def shiftClassGroupAwayWeightedProdEquiv {J : Type*} {s : Finset J}
    {f : MvPolynomial σ R} {e_f : ℤ} (hf : f ∈ weightedHomogeneousSubmodule R w e_f)
    {p : J → MvPolynomial σ R} {e : J → ℤ}
    (hp_mem : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (e j))
    (hp_prime : ∀ j ∈ s, Prime (p j)) (hassoc : Associated f (∏ j ∈ s, p j)) :
    ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf) ≃+
      ZMod (s.gcd e).natAbs :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (homogeneousUnitDegrees_awayGrading_weighted_int_of_associated_prod_prime w
      hf hp_mem hp_prime hassoc)).trans
    (Int.quotientZMultiplesEquivZMod (s.gcd e))

/-- `shiftClassGroupAwayWeightedProdEquiv` sends the class of `d : ℤ` to
`(d : ZMod (s.gcd e).natAbs)`. -/
@[simp]
theorem shiftClassGroupAwayWeightedProdEquiv_mk {J : Type*} {s : Finset J}
    {f : MvPolynomial σ R} {e_f : ℤ} (hf : f ∈ weightedHomogeneousSubmodule R w e_f)
    {p : J → MvPolynomial σ R} {e : J → ℤ}
    (hp_mem : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (e j))
    (hp_prime : ∀ j ∈ s, Prime (p j)) (hassoc : Associated f (∏ j ∈ s, p j)) (d : ℤ) :
    shiftClassGroupAwayWeightedProdEquiv w hf hp_mem hp_prime hassoc d = d := by
  -- Both quotient equivalences are induced by maps on representatives, the second being the cast
  -- `ℤ → ZMod (s.gcd e).natAbs`.
  rfl

/-- The inverse of `shiftClassGroupAwayWeightedProdEquiv` sends `(d : ZMod (s.gcd e).natAbs)` to the
shift class of `d`. -/
@[simp]
theorem shiftClassGroupAwayWeightedProdEquiv_symm_intCast {J : Type*} {s : Finset J}
    {f : MvPolynomial σ R} {e_f : ℤ} (hf : f ∈ weightedHomogeneousSubmodule R w e_f)
    {p : J → MvPolynomial σ R} {e : J → ℤ}
    (hp_mem : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (e j))
    (hp_prime : ∀ j ∈ s, Prime (p j)) (hassoc : Associated f (∏ j ∈ s, p j)) (d : ℤ) :
    (shiftClassGroupAwayWeightedProdEquiv w hf hp_mem hp_prime hassoc).symm d = d :=
  (shiftClassGroupAwayWeightedProdEquiv w hf hp_mem hp_prime hassoc).symm_apply_eq.mpr
    (shiftClassGroupAwayWeightedProdEquiv_mk w hf hp_mem hp_prime hassoc d).symm

/-- The inverse of `shiftClassGroupAwayWeightedProdEquiv` sends `x : ZMod (s.gcd e).natAbs` to the
shift class of `ZMod.cast x : ℤ`. -/
theorem shiftClassGroupAwayWeightedProdEquiv_symm_apply {J : Type*} {s : Finset J}
    {f : MvPolynomial σ R} {e_f : ℤ} (hf : f ∈ weightedHomogeneousSubmodule R w e_f)
    {p : J → MvPolynomial σ R} {e : J → ℤ}
    (hp_mem : ∀ j ∈ s, p j ∈ weightedHomogeneousSubmodule R w (e j))
    (hp_prime : ∀ j ∈ s, Prime (p j)) (hassoc : Associated f (∏ j ∈ s, p j))
    (x : ZMod (s.gcd e).natAbs) :
    (shiftClassGroupAwayWeightedProdEquiv w hf hp_mem hp_prime hassoc).symm x =
      (ZMod.cast x : ℤ) := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast x]
  exact shiftClassGroupAwayWeightedProdEquiv_symm_intCast w hf hp_mem hp_prime hassoc
    (ZMod.cast x)

end IntWeights

end TauCeti
