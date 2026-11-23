/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import TauCeti.Topology.Algebra.Valued.Integer

/-!
# Discrete valuation rings and finite residue fields of nonarchimedean fields

Let `K` be a nontrivially normed field with an ultrametric norm, with valuation ring `𝒪[K]` (the
closed unit ball) and residue field `𝓀[K]`. This file collects criteria, phrased with the norm, for
`𝒪[K]` to be a discrete valuation ring and for `𝓀[K]` to be finite, and the resulting
finite-dimensionality of `K` over a complete field of scalars.

* A nontrivially normed field embedded isometrically into a field with discrete valuation ring has
  a discrete valuation ring as well: a nontrivially valued subfield of a discretely valued field is
  discretely valued, since its value group is a subgroup of a cyclic group.
* If every element `a` of norm at most `1` satisfies `‖a ^ q - a‖ < 1` for some `q > 1`, every
  residue is a root of `X ^ q - X`, so `𝓀[K]` is finite with at most `q` elements.
* By Riesz's theorem, a field whose valuation ring is a discrete valuation ring with finite
  residue field is finite-dimensional over every complete nontrivially normed field acting
  continuously on it: its valuation ring is a totally bounded neighbourhood of `0`.

These are the inputs for recognising a subfield of a discretely valued `p`-adic field, such as the
field fixed by a Frobenius lift, as a finite extension of `ℚ_[p]`.

## Main results

* `NormedField.instRankOneToValued`: the valuation `Valued.v` of a nonarchimedean nontrivially
  normed field has rank one.
* `RingHom.isDiscreteValuationRing_integer_of_norm_map_eq`: a nontrivially normed field embedded
  isometrically into a discretely valued field is discretely valued.
* `Valued.integer.pow_eq_self_of_norm_pow_sub_lt_one`,
  `Valued.integer.finite_residueField_of_norm_pow_sub_lt_one` and
  `Valued.integer.natCard_residueField_le_of_norm_pow_sub_lt_one`: the residue field consists of
  roots of `X ^ q - X`, hence is finite with at most `q` elements.
* `Valued.integer.finiteDimensional_of_finite_residueField`: a field with discrete valuation ring
  and finite residue field is finite-dimensional over a complete nontrivially normed field of
  scalars.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §1, and Chapter II, §1.
-/

public section

open IsLocalRing Polynomial
open scoped NNReal NormedField Valued

namespace Valued.integer

section Discrete

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The valuation `Valued.v` of a nonarchimedean nontrivially normed field has rank one: the
valuation of `NormedField.toValued` is by definition `NormedField.valuation`, which has rank one. -/
noncomputable instance _root_.NormedField.instRankOneToValued :
    (Valued.v : Valuation K ℝ≥0).RankOne :=
  inferInstanceAs (NormedField.valuation (K := K)).RankOne

/-- A nontrivially normed field `L` admitting a norm-preserving ring homomorphism into a
nonarchimedean field `K` whose valuation ring is a discrete valuation ring has a discrete
valuation ring as well: a nontrivially valued subfield of a discretely valued field is discretely
valued. -/
theorem _root_.RingHom.isDiscreteValuationRing_integer_of_norm_map_eq {L : Type*}
    [NontriviallyNormedField L] [IsUltrametricDist L] [IsDiscreteValuationRing 𝒪[K]]
    (φ : L →+* K) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : IsDiscreteValuationRing 𝒪[L] := by
  -- The value group of `K` is cyclic, since `𝒪[K]` is a discrete valuation ring. The ring
  -- `𝒪[K] = Valued.integer K` is by definition `Valued.v.integer`, which is also the carrier of
  -- `Valued.v.valuationSubring`, so the instance on `𝒪[K]` applies to the latter by unfolding.
  have : IsDiscreteValuationRing (Valued.v : Valuation K ℝ≥0).valuationSubring := ‹_›
  have : (Valued.v : Valuation K ℝ≥0).IsRankOneDiscrete :=
    .of_isEquiv (Valuation.isEquiv_valuation_valuationSubring _).symm
  -- `φ` preserves valuations, so the value group of `L` is a subgroup of that of `K`. The
  -- valuation `Valued.v` of `NormedField.toValued` is by definition `NormedField.valuation`,
  -- which is `‖·‖₊` by `NormedField.valuation_apply`.
  have hle : (Valued.v : Valuation L ℝ≥0).valueGroup ≤ (Valued.v : Valuation K ℝ≥0).valueGroup :=
    (Subgroup.closure_le _).2 fun _ ⟨x, hx⟩ ↦ MonoidWithZeroHom.mem_valueGroup _ ⟨φ x,
      by simpa [NormedField.valuation_apply, ← NNReal.coe_inj, hφ] using hx⟩
  -- `L` is nontrivially normed, so its value group is nontrivial: `Valued.v` has rank one by
  -- `NormedField.instRankOneToValued`.
  have : IsCyclic (Valued.v : Valuation L ℝ≥0).valueGroup := Subgroup.isCyclic_of_le hle
  -- As for `K`, `𝒪[L]` is by definition the carrier of `Valued.v.valuationSubring`.
  exact inferInstanceAs (IsDiscreteValuationRing (Valued.v : Valuation L ℝ≥0).valuationSubring)

/-- If the valuation ring of a nonarchimedean field is a discrete valuation ring with uniformizer
`ϖ`, every element of norm less than `1` has norm at most `‖ϖ‖`. -/
theorem _root_.Irreducible.norm_le_of_norm_lt_one [IsDiscreteValuationRing 𝒪[K]] {ϖ : 𝒪[K]}
    (hϖ : Irreducible ϖ) {x : K} (hx : ‖x‖ < 1) : ‖x‖ ≤ ‖ϖ‖ := by
  have hmem : (⟨x, mem_iff.2 hx.le⟩ : 𝒪[K]) ∈ (𝓂[K] : Set 𝒪[K]) := mem_maximalIdeal_iff.2 hx
  rw [hϖ.maximalIdeal_eq_closedBall, mem_closedBall_zero_iff] at hmem
  simpa using hmem

end Discrete

section Residue

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- If every element `a` of norm at most `1` of a nonarchimedean field satisfies
`‖a ^ q - a‖ < 1`, then every element of the residue field `𝓀[K]` is a root of `X ^ q - X`. -/
theorem pow_eq_self_of_norm_pow_sub_lt_one {q : ℕ} (h : ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ q - a‖ < 1)
    (x : 𝓀[K]) : x ^ q = x := by
  obtain ⟨a, rfl⟩ := residue_surjective x
  rw [← map_pow, residue_eq_residue_iff_norm_sub_lt_one]
  simpa using h a (norm_le_one a)

/-- If, for some `q > 1`, every element `a` of norm at most `1` of a nonarchimedean field satisfies
`‖a ^ q - a‖ < 1`, the residue field `𝓀[K]` is finite. -/
theorem finite_residueField_of_norm_pow_sub_lt_one {q : ℕ} (hq : 1 < q)
    (h : ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ q - a‖ < 1) : Finite 𝓀[K] :=
  Set.finite_univ_iff.1 <| (finite_setOfPred_isRoot (X_pow_sub_X_ne_zero hq)).subset fun x _ ↦ by
    simp [pow_eq_self_of_norm_pow_sub_lt_one h x]

/-- If, for some `q > 1`, every element `a` of norm at most `1` of a nonarchimedean field satisfies
`‖a ^ q - a‖ < 1`, the residue field `𝓀[K]` has at most `q` elements. -/
theorem natCard_residueField_le_of_norm_pow_sub_lt_one {q : ℕ} (hq : 1 < q)
    (h : ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ q - a‖ < 1) : Nat.card 𝓀[K] ≤ q := by
  have := finite_residueField_of_norm_pow_sub_lt_one hq h
  have := Fintype.ofFinite 𝓀[K]
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← natDegree_X_pow_sub_X (R := 𝓀[K]) hq]
  refine card_le_degree_of_subset_roots fun x _ ↦ ?_
  simp [X_pow_sub_X_ne_zero hq, pow_eq_self_of_norm_pow_sub_lt_one h x]

end Residue

section FiniteDimensional

variable (𝕜 : Type*) {K : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NontriviallyNormedField K] [IsUltrametricDist K] [Module 𝕜 K] [ContinuousSMul 𝕜 K]

/-- **Riesz's theorem** for nonarchimedean fields: a field whose valuation ring is a discrete
valuation ring with finite residue field is finite-dimensional over every complete nontrivially
normed field `𝕜` acting continuously on it; its valuation ring is a totally bounded neighbourhood
of `0`. For `𝕜 = ℚ_[p]` this recognises such a field as a finite extension of `ℚ_[p]`. -/
theorem finiteDimensional_of_finite_residueField [IsDiscreteValuationRing 𝒪[K]]
    [Finite 𝓀[K]] : FiniteDimensional 𝕜 K := by
  have htb : TotallyBounded (𝒪[K] : Set K) := by
    simpa using (totallyBounded_iff_finite_residueField.2 ‹_›).image uniformContinuous_subtypeVal
  have hball : (𝒪[K] : Set K) = Metric.closedBall 0 1 := by
    ext x
    simp [mem_iff]
  refine FiniteDimensional.of_totallyBounded_nhds 𝕜 (x := 0) ?_ htb
  rw [hball]
  exact Metric.closedBall_mem_nhds 0 one_pos

end FiniteDimensional

end Valued.integer
