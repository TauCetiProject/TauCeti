/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.RingTheory.GradedAlgebra.Localization.Units

/-!
# Homogeneous units and shift classes of weighted polynomial rings

For a nontrivial commutative semiring `R`, any type of variables `σ`, and any weight function
`w : σ → ι` into an additive commutative group `ι`, the weighted polynomial ring
`MvPolynomial σ R` is graded by `MvPolynomial.weightedHomogeneousSubmodule R w`. Because the
constant term of any unit of `MvPolynomial σ R` is a unit of `R`, hence nonzero, every homogeneous
unit has degree `0`: `homogeneousUnitDegrees (weightedHomogeneousSubmodule R w) = ⊥`. No
positivity hypothesis on `w` and no finiteness hypothesis on `σ` are required.

Without any global cancellativity hypothesis on `R`, the localization results of
`TauCeti.RingTheory.GradedAlgebra.Localization.Units` apply directly to any regular
weighted-homogeneous element `f` (`IsLeftRegular f`):
* Inverting a regular weighted-homogeneous prime `f` of weight `e` yields homogeneous unit degrees
  `AddSubgroup.zmultiples e` (`TauCeti.homogeneousUnitDegrees_away_prime`), and for `ι = ℤ` the
  shift class group is `ZMod e.natAbs` (`TauCeti.shiftClassGroupWeightedAwayPrimeEquiv`).
* Inverting a nonzero power `f ^ k` of a regular weighted-homogeneous prime `f` of weight `e`
  still yields `AddSubgroup.zmultiples e` (`TauCeti.homogeneousUnitDegrees_away_prime_pow`),
  illustrating why primality of the inverted element cannot be dropped.
* Inverting a regular element associated to a finite product `∏ i ∈ s, p i` of
  weighted-homogeneous primes `p i` of weights `e i` yields `AddSubgroup.closure (e '' s)`
  (`TauCeti.homogeneousUnitDegrees_away_of_associated_prod`).
* Whenever `PrimeSpectrum (MvPolynomial σ R)` is preconnected (in particular over any domain `R`),
  every compatible `ℤ`-grading of the free rank-one module over `MvPolynomial σ R` is classified
  up to graded isomorphism by a unique integer shift
  (`TauCeti.GradedAlgebra.existsUnique_shift_linearEquiv_weighted`), and whenever
  `PrimeSpectrum (MvPolynomial σ R)` is preirreducible, every compatible `ℤ`-grading over
  `Localization.Away f` is classified by a unique element of `TauCeti.ShiftClassGroup`
  (`TauCeti.GradedAlgebra.existsUnique_shiftClass_weighted_away`).

## Main definitions

* `TauCeti.shiftClassGroupWeightedEquiv`:
  `ShiftClassGroup (weightedHomogeneousSubmodule R w) ≃+ ι`.
* `TauCeti.shiftClassGroupWeightedAwayPrimeEquiv`:
  `ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf) ≃+ ZMod e.natAbs` for a
  regular weighted-homogeneous prime `f` of integer weight `e`.

## Main results

* `TauCeti.homogeneousUnitDegrees_weighted`: the homogeneous unit degrees of a weighted polynomial
  ring are `⊥`.
* `TauCeti.homogeneousUnitDegrees_away_of_associated_prod`: homogeneous unit degrees after inverting
  a regular element associated to a finite product of weighted-homogeneous primes.
* `TauCeti.homogeneousUnitDegrees_away_prime` and
  `TauCeti.homogeneousUnitDegrees_away_prime_pow`: the single-prime and prime-power cases.
* `TauCeti.GradedAlgebra.existsUnique_shift_linearEquiv_weighted` and
  `TauCeti.GradedAlgebra.existsUnique_shiftClass_weighted_away`: classification of all compatible
  rank-one `ℤ`-gradings on `MvPolynomial σ R` and `Localization.Away f`.
-/

public section

attribute [local instance] MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid

open MvPolynomial TauCeti.GradedAlgebra

namespace TauCeti

section Weighted

variable {σ ι : Type*} [AddCommGroup ι]

/-- For any weights `w : σ → ι` into an additive commutative group over a nontrivial commutative
semiring `R`, every homogeneous unit of `MvPolynomial σ R` has degree `0`, because its constant
term is a unit and hence nonzero. -/
@[simp]
theorem homogeneousUnitDegrees_weighted {R : Type*} [CommSemiring R] [Nontrivial R]
    (w : σ → ι) :
    homogeneousUnitDegrees (weightedHomogeneousSubmodule R w) = ⊥ := by
  refine eq_bot_iff.mpr (homogeneousUnitDegrees_le_iff.mpr fun u d hu ↦ ?_)
  have h0 : (u : MvPolynomial σ R).coeff 0 ≠ 0 := by
    rw [← constantCoeff_eq]
    exact (u.isUnit.map (constantCoeff (σ := σ) (R := R))).ne_zero
  have hd : Finsupp.weight w (0 : σ →₀ ℕ) = d :=
    (mem_weightedHomogeneousSubmodule ..).mp hu h0
  simpa using hd.symm

/-- The shift class group of a weighted polynomial ring over a nontrivial commutative semiring is
the degree group `ι`. -/
noncomputable def shiftClassGroupWeightedEquiv (R : Type*) [CommSemiring R] [Nontrivial R]
    (w : σ → ι) : ShiftClassGroup (weightedHomogeneousSubmodule R w) ≃+ ι :=
  (QuotientAddGroup.quotientAddEquivOfEq (homogeneousUnitDegrees_weighted w)).trans
    QuotientAddGroup.quotientBot

/-- The identification of the shift class group of a weighted polynomial ring with `ι` sends the
class of `d` to `d`. -/
@[simp]
theorem shiftClassGroupWeightedEquiv_mk (R : Type*) [CommSemiring R] [Nontrivial R]
    (w : σ → ι) (d : ι) :
    shiftClassGroupWeightedEquiv R w d = d := by
  rfl

end Weighted

section Away

variable {σ β ι R : Type*} [AddCommGroup ι] [CommSemiring R]

/-- Inverting a regular element `f` associated to a finite product `∏ i ∈ s, p i` of
weighted-homogeneous primes `p i` of weights `e i` produces a graded localization whose
homogeneous unit degrees are generated by `{e i | i ∈ s}`. -/
theorem homogeneousUnitDegrees_away_of_associated_prod [Nontrivial R] (w : σ → ι)
    {s : Finset β} {p : β → MvPolynomial σ R} {e : β → ι}
    {f : MvPolynomial σ R} {e₀ : ι}
    (hf : f ∈ weightedHomogeneousSubmodule R w e₀)
    (hp : ∀ i ∈ s, Prime (p i))
    (hmem : ∀ i ∈ s, p i ∈ weightedHomogeneousSubmodule R w (e i))
    (hassoc : Associated f (∏ i ∈ s, p i))
    (hreg : IsLeftRegular f) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.closure (e '' (s : Set β)) := by
  classical
  let := MvPolynomial.weightedGradedAlgebra R w
  rw [homogeneousUnitDegrees_awayGrading_of_associated_prod (weightedHomogeneousSubmodule R w)
    hf hp hmem hassoc hreg, homogeneousUnitDegrees_weighted, bot_sup_eq]

/-- Inverting a regular weighted-homogeneous prime polynomial `f` of weight `e` produces a graded
localization whose homogeneous unit degrees are `AddSubgroup.zmultiples e`. -/
theorem homogeneousUnitDegrees_away_prime (w : σ → ι)
    {f : MvPolynomial σ R} {e : ι}
    (hf : f ∈ weightedHomogeneousSubmodule R w e) (hprime : Prime f) (hreg : IsLeftRegular f) :
    homogeneousUnitDegrees (awayGrading (weightedHomogeneousSubmodule R w) hf) =
      AddSubgroup.zmultiples e := by
  classical
  let := MvPolynomial.weightedGradedAlgebra R w
  have : Nontrivial R := not_subsingleton_iff_nontrivial.mp fun _ ↦
    hprime.ne_zero (Subsingleton.elim f 0)
  rw [homogeneousUnitDegrees_awayGrading_prime (weightedHomogeneousSubmodule R w) hf hprime hreg,
    homogeneousUnitDegrees_weighted, bot_sup_eq]

/-- Inverting a nonzero power `f ^ k` of a regular weighted-homogeneous prime `f` of weight `e`
still yields homogeneous unit degrees `AddSubgroup.zmultiples e`, since `f` itself becomes a unit
of degree `e`. -/
theorem homogeneousUnitDegrees_away_prime_pow (w : σ → ι)
    {f : MvPolynomial σ R} {e : ι} {k : ℕ}
    (hf : f ∈ weightedHomogeneousSubmodule R w e) (hprime : Prime f) (hreg : IsLeftRegular f)
    (hk : k ≠ 0) :
    homogeneousUnitDegrees
        (awayGrading (weightedHomogeneousSubmodule R w) (SetLike.pow_mem_graded k hf)) =
      AddSubgroup.zmultiples e := by
  classical
  let := MvPolynomial.weightedGradedAlgebra R w
  have : Nontrivial R := not_subsingleton_iff_nontrivial.mp fun _ ↦
    hprime.ne_zero (Subsingleton.elim f 0)
  rw [homogeneousUnitDegrees_awayGrading_prime_pow (weightedHomogeneousSubmodule R w) hf hprime
    hreg hk, homogeneousUnitDegrees_weighted, bot_sup_eq]

/-- For a regular weighted-homogeneous prime polynomial `f` of integer weight `e`, the shift class
group of `Localization.Away f` is `ZMod e.natAbs`. -/
noncomputable def shiftClassGroupWeightedAwayPrimeEquiv (w : σ → ℤ)
    {f : MvPolynomial σ R} {e : ℤ}
    (hf : f ∈ weightedHomogeneousSubmodule R w e) (hprime : Prime f) (hreg : IsLeftRegular f) :
    ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf) ≃+ ZMod e.natAbs :=
  let := MvPolynomial.weightedGradedAlgebra R w
  have : Nontrivial R := not_subsingleton_iff_nontrivial.mp fun _ ↦
    hprime.ne_zero (Subsingleton.elim f 0)
  shiftClassGroupAwayPrimeEquiv (weightedHomogeneousSubmodule R w)
    hf hprime hreg ((homogeneousUnitDegrees_weighted w).trans_le bot_le)

/-- The identification of the shift class group of `Localization.Away f` with `ZMod e.natAbs` sends
the class of a shift `d` to `d mod |e|`. -/
@[simp]
theorem shiftClassGroupWeightedAwayPrimeEquiv_mk (w : σ → ℤ)
    {f : MvPolynomial σ R} {e : ℤ}
    (hf : f ∈ weightedHomogeneousSubmodule R w e) (hprime : Prime f) (hreg : IsLeftRegular f)
    (d : ℤ) :
    shiftClassGroupWeightedAwayPrimeEquiv w hf hprime hreg d = d := by
  let := MvPolynomial.weightedGradedAlgebra R w
  have : Nontrivial R := not_subsingleton_iff_nontrivial.mp fun _ ↦
    hprime.ne_zero (Subsingleton.elim f 0)
  exact shiftClassGroupAwayPrimeEquiv_mk (weightedHomogeneousSubmodule R w)
    hf hprime hreg ((homogeneousUnitDegrees_weighted w).trans_le bot_le) d

end Away

end TauCeti

namespace TauCeti.GradedAlgebra

variable {σ R τ : Type*}

/-- Over a nontrivial commutative ring `R` such that `PrimeSpectrum (MvPolynomial σ R)` is
preconnected (in particular over any domain `R`), every compatible `ℤ`-grading of the free
rank-one module over a weighted polynomial ring `MvPolynomial σ R` is graded-isomorphic to a
shift by a unique integer `d`. -/
theorem existsUnique_shift_linearEquiv_weighted [CommRing R] [Nontrivial R]
    [PreconnectedSpace (PrimeSpectrum (MvPolynomial σ R))] (w : σ → ℤ)
    [SetLike τ (MvPolynomial σ R)] [AddSubmonoidClass τ (MvPolynomial σ R)]
    (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (weightedHomogeneousSubmodule R w) ℳ] :
    ∃! d : ℤ,
      ∃ φ : MvPolynomial σ R ≃ₗ[MvPolynomial σ R] MvPolynomial σ R,
        ∀ n x, φ x ∈ ℳ n ↔ x ∈ weightedHomogeneousSubmodule R w (n + d) := by
  let := MvPolynomial.weightedGradedAlgebra R w
  exact existsUnique_shift_linearEquiv_of_connected (weightedHomogeneousSubmodule R w) ℳ
    (homogeneousUnitDegrees_weighted w)

/-- Whenever `PrimeSpectrum (MvPolynomial σ R)` is preirreducible (in particular over any domain
`R`), every compatible `ℤ`-grading of the free rank-one module over `Localization.Away f` at a
weighted-homogeneous polynomial `f` is graded-isomorphic to a shift by `d` if and only if `d`
represents a unique class in
`TauCeti.ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf)`. -/
theorem existsUnique_shiftClass_weighted_away [CommRing R]
    [PreirreducibleSpace (PrimeSpectrum (MvPolynomial σ R))] (w : σ → ℤ)
    {f : MvPolynomial σ R} {e : ℤ} (hf : f ∈ weightedHomogeneousSubmodule R w e)
    [SetLike τ (Localization.Away f)] [AddSubmonoidClass τ (Localization.Away f)]
    (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (awayGrading (weightedHomogeneousSubmodule R w) hf) ℳ] :
    ∃! c : ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf),
      ∀ d : ℤ,
        (∃ φ : Localization.Away f ≃ₗ[Localization.Away f] Localization.Away f,
          ∀ n x,
            φ x ∈ ℳ n ↔ x ∈ awayGrading (weightedHomogeneousSubmodule R w) hf (n + d)) ↔
        (d : ShiftClassGroup (awayGrading (weightedHomogeneousSubmodule R w) hf)) = c := by
  let := MvPolynomial.weightedGradedAlgebra R w
  exact existsUnique_shiftClass_awayGrading_of_preirreducible
    (weightedHomogeneousSubmodule R w) hf ℳ

end TauCeti.GradedAlgebra
