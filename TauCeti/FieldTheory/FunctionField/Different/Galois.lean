/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Complementary
public import TauCeti.FieldTheory.FunctionField.Different.Divisor
-- `TauCeti.Divisor.tameDifferent` occurs in the statements below.
public import TauCeti.FieldTheory.FunctionField.Different.Tame
public import TauCeti.FieldTheory.FunctionField.Divisor.Automorphism

/-!
# The different exponent under the Galois action

Let `F / k` be a field extension and `F' / F` a finite separable extension.  An
`F`-automorphism `σ` of `F'` moves the places of `F' / k` (`TauCeti.Place.instMulActionAlgEquiv`)
without moving the places of `F / k` below them.  This file proves that it also preserves the
different exponent: `d(σ • P' ∣ P) = d(P' ∣ P)`.  Together with the transitivity of the Galois
action on the places over a place, this gives the remaining part of Stichtenoth's Corollary 3.7.2:
in a finite Galois extension `F' / F` all places over a given place of `F` share one different
exponent, as they share one ramification index and one relative degree
(`TauCeti.Place.ramificationIdx_eq_of_restrict_eq`,
`TauCeti.Place.relativeDegree_eq_of_restrict_eq`).  At the level of divisors, the different
divisor `Diff(F' / F)` is fixed by every `F`-automorphism of `F'`.

The different exponent is read off the different ideal of the local model `𝒪_P ⊆ 𝒪'_P`, where
`𝒪'_P` is the integral closure in `F'` of the valuation ring `𝒪_P` of `P`.  Since `σ` fixes `F`, it
maps `𝒪'_P` onto itself and preserves the trace of `F' / F`, so it preserves the complementary
module `C_P = {z ∣ Tr_{F'/F} (z · 𝒪'_P) ⊆ 𝒪_P}` and hence the different ideal, the inverse of
`C_P` (`TauCeti.galRestrict_apply_mem_differentIdeal_iff`).  An element of the different ideal of
order exactly `d(P' ∣ P)` at `P'` (`TauCeti.Place.exists_mem_differentIdeal_ord_eq`) is carried to
an element of the different ideal of the same order at `σ • P'`, which bounds `d(σ • P' ∣ P)` from
above; applying this to `σ⁻¹` gives the reverse bound.

## Main results

* `TauCeti.Place.differentExponent_smul`: an `F`-automorphism of `F'` preserves the different
  exponent.
* `TauCeti.Place.differentExponent_eq_of_restrict_eq`: **the different exponent is constant on the
  places over a place** in a finite Galois extension (Stichtenoth, Corollary 3.7.2).
* `TauCeti.Divisor.smul_different`: an `F`-automorphism of `F'` fixes the different divisor.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.7.1 and Corollary 3.7.2.
-/

public section

namespace TauCeti

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable [FiniteDimensional F F']

namespace Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section Action

variable [Algebra.IsSeparable F F']

/-- The different exponent at `σ • P'` is at most the different exponent at `P'`; the reverse
inequality is this one for `σ⁻¹`. -/
private theorem differentExponent_smul_le (σ : F' ≃ₐ[F] F') (P' : Place k F') :
    differentExponent k F (σ • P') ≤ differentExponent k F P' := by
  -- An element `y` of the different ideal has order `d(P' ∣ P)` at `P'`, and its image under `σ`
  -- lies in the different ideal and has the same order at `σ • P'`.
  obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
  set y' := galRestrict (P'.restrict k F).integers F F' _ σ y
  have hy' : y' ∈ differentIdeal _ _ := galRestrict_apply_mem_differentIdeal_iff.mpr hy
  have hyy' : algebraMap _ F' y' = σ (algebraMap _ F' y) := algebraMap_galRestrict_apply _ σ y
  have hy'0 : y' ≠ 0 := by simpa [y'] using hy0
  -- the local model at `σ • P'` is the one at `P'`, as the two places lie over the same place
  have key : ∀ P : Place k F, (σ • P').restrict k F = P →
      ∀ z ∈ differentIdeal P.integers (integralClosure P.integers F'), z ≠ 0 →
        (differentExponent k F (σ • P') : ℤ) ≤ (σ • P').ord (algebraMap _ F' z) := by
    rintro P rfl z hz hz0
    exact differentExponent_le_ord_of_mem_differentIdeal k F (σ • P') hz hz0
  have hle := key _ (restrict_smul σ P') y' hy' hy'0
  rw [hyy', ord_smul_apply, hord] at hle
  exact_mod_cast hle

/-- **An `F`-automorphism of `F'` preserves the different exponent**: `d(σ • P' ∣ P) = d(P' ∣ P)`
for every place `P'` of `F' / k` over the place `P` of `F / k`. -/
@[simp]
theorem differentExponent_smul (σ : F' ≃ₐ[F] F') (P' : Place k F') :
    differentExponent k F (σ • P') = differentExponent k F P' := by
  refine le_antisymm (differentExponent_smul_le σ P') ?_
  simpa using differentExponent_smul_le σ⁻¹ (σ • P')

end Action

/-- **The different exponent is constant on a fibre** (Stichtenoth, Corollary 3.7.2): in a finite
Galois extension `F' / F`, two places of `F' / k` over the same place of `F / k` have the same
different exponent. -/
theorem differentExponent_eq_of_restrict_eq [IsGalois F F'] {P Q : Place k F'}
    (h : P.restrict k F = Q.restrict k F) :
    differentExponent k F P = differentExponent k F Q := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_restrict_eq h
  rw [differentExponent_smul]

end Place

namespace Divisor

variable [Algebra.IsSeparable F F']

/-- **An `F`-automorphism of `F'` fixes the different divisor** `Diff(F' / F)`, as it preserves the
different exponent at every place. -/
@[simp]
theorem smul_different (hF : IsFunctionField k F) (σ : F' ≃ₐ[F] F') :
    σ • different k F' hF = different k F' hF := by
  ext P'
  rw [AlgebraicGeometry.WeilDivisor.coeff_smul, coeff_different, coeff_different,
    Place.differentExponent_smul]

/-- **The degree of the tame different of a Galois extension, through its branch data**: the places
over a place `P` of `F` share one ramification index `e_P`, so the tame different
`∑_{P'} (e(P' ∣ P) - 1) · P'` has degree

`[F' : F] · ∑_P (1 - 1/e_P) · deg P`,

the sum being over any finite set of places of `F` containing every ramified one.  With the Hurwitz
genus formula in its tame form this is Riemann--Hurwitz for the quotient `F' / F`: the branch data
`(genus F; e_P)` has deficit `(2g' - 2)/[F' : F]`. -/
theorem degree_tameDifferent_eq_finrank_mul_sum [IsGalois F F'] (hF : IsFunctionField k F)
    (hF' : IsFunctionField k F') (s : Finset (Place k F))
    (hs : ∀ P' : Place k F', 1 < Place.ramificationIdx F P' → P'.restrict k F ∈ s) :
    (degree (tameDifferent k F' hF) : ℚ) =
      Module.finrank F F' * ∑ P ∈ s, (1 - 1 / (P.ramificationIdxIn F' : ℚ)) * P.degree := by
  classical
  have hsurj := Place.restrict_surjective_of_finiteDimensional (k' := k) (F := F) (F' := F') hF hF'
  set fibre : Place k F → Finset (Place k F') :=
    fun P ↦ (Place.finite_setOf_restrict_eq (k' := k) (F' := F') k F P).toFinset
  have hmem : ∀ (P : Place k F) (P' : Place k F'), P' ∈ fibre P ↔ P'.restrict k F = P :=
    fun P P' ↦ Set.Finite.mem_toFinset _
  -- The degree of the tame different is the sum of `e - 1` over all the places above `s`.
  have hdeg : (degree (tameDifferent k F' hF) : ℤ) =
      ∑ P' ∈ s.biUnion fibre, ((Place.ramificationIdx F P' : ℤ) - 1) * P'.degree := by
    have hco : ∀ P' : Place k F',
        (tameDifferent k F' hF) P' = (Place.ramificationIdx F P' : ℤ) - 1 :=
      fun P' ↦ coeff_tameDifferent k F' hF P'
    rw [degree_eq_sum_support,
      Finset.sum_congr rfl fun P' _ ↦ congrArg (· * (P'.degree : ℤ)) (hco P')]
    refine Finset.sum_subset (fun P' hP' ↦ ?_) (fun P' _ hP' ↦ ?_)
    · refine Finset.mem_biUnion.mpr ⟨P'.restrict k F, hs P' ?_, (hmem _ _).mpr rfl⟩
      have hne : (tameDifferent k F' hF) P' ≠ 0 := Finsupp.mem_support_iff.mp hP'
      rw [hco P'] at hne
      have := Place.ramificationIdx_pos F P'
      omega
    · have hzero : (tameDifferent k F' hF) P' = 0 := Finsupp.notMem_support_iff.mp hP'
      rw [hco P'] at hzero
      rw [hzero, zero_mul]
  -- Fibres over distinct places are disjoint, so the sum splits over the fibres.
  have hdisj : (s : Set (Place k F)).PairwiseDisjoint fibre := by
    intro P _ Q _ hPQ
    simp only [Function.onFun, Finset.disjoint_left]
    intro P' hP' hQ'
    exact hPQ (((hmem P P').mp hP').symm.trans ((hmem Q P').mp hQ'))
  rw [hdeg, Finset.sum_biUnion hdisj, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  -- One fibre: clear the division by the common ramification index.
  obtain ⟨P', hP'⟩ := hsurj P
  have hpos : 0 < P.ramificationIdxIn F' := by
    rw [Place.ramificationIdxIn_eq_ramificationIdx hP']
    exact Place.ramificationIdx_pos F P'
  have hne : (P.ramificationIdxIn F' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hfib := Place.ramificationIdxIn_mul_sum_fibre_eq (k := k) (F' := F') hP'
  have hcast : (P.ramificationIdxIn F' : ℚ) *
      ∑ P' ∈ fibre P, ((Place.ramificationIdx F P' : ℚ) - 1) * P'.degree =
        Module.finrank F F' * (((P.ramificationIdxIn F' : ℚ) - 1) * P.degree) := by
    have := congrArg (fun n : ℤ ↦ (n : ℚ)) hfib
    push_cast at this
    exact this
  refine mul_left_cancel₀ hne (hcast.trans ?_)
  field_simp

end Divisor

end TauCeti
