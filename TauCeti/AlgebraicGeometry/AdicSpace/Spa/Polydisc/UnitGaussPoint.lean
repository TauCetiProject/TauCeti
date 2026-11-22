/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.PointTopology
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.GaussValuation

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued
import TauCeti.RingTheory.Huber.Restricted.Reduction
import TauCeti.RingTheory.Valuation.Continuous.Valued

/-!
# The unit Gauss point of a closed polydisc and rational-point closure

Let `K` be an ultrametric normed field and `D = closedPolydisc n K` the closed unit polydisc of
dimension `n` over `K`, whose coordinate ring is the trivial-weight restricted power series ring
`K⟨T₁, …, Tₙ⟩`. Extending the norm valuation `NormedField.valuation` on `K` via
`TauCeti.Huber.weightedGaussValuation` produces the *unit Gauss valuation* `unitGaussValuation n K`
on `K⟨T₁, …, Tₙ⟩`, sending `f = ∑_ν a_ν T^ν` to `max_ν ‖a_ν‖₊`. Its coercion to `ℝ` coincides with
Mathlib's `MvPowerSeries.gaussNorm norm (fun _ ↦ 1)`. This valuation is continuous and bounded by
`1` on `K⟨T₁, …, Tₙ⟩°`, so it defines the *unit Gauss point*
`unitGaussPoint n K : closedPolydisc n K`.

A point `η` of `closedPolydisc n K` satisfies the predicate `IsUnitGaussPoint K n η` when it
compares restricted power series by their unit Gauss norms; this uniquely characterizes
`unitGaussPoint n K`. In dimension `1` over a nontrivially normed field, `unitGaussPoint 1 K`
agrees with the radius-`1` Gauss point `TauCeti.ValuationSpectrum.gaussPoint zero_lt_one le_rfl`.
In dimension `0`, `closedPolydisc 0 K` is a subsingleton, so the unit Gauss point coincides with
the unique classical point without any residue-field assumption. In positive dimension over a
complete field, `unitGaussPoint n K` has trivial support and is therefore never classical.

To study the closure of the classical points, we reduce unit-bounded series `f ∈ K°⟨T₁, …, Tₙ⟩`
coefficientwise modulo the maximal ideal `K°° = topologicallyNilpotentIdeal K` of `K°`, obtaining
a polynomial `polydiscReduction n K f ∈ (K° ⧸ K°°)[T₁, …, Tₙ]`. Over a complete field, reduction
commutes with evaluation at any `a ∈ (K°)ⁿ`, so `‖f(a)‖ = 1` if and only if the reduced polynomial
is nonzero at the residue tuple `ā`. Given any basic open `Spv(K⟨T⟩)(T/g)` containing the unit
Gauss point, scaling by the inverse of a coefficient attaining the Gauss norm of `g` normalizes `g`
to unit Gauss norm and every numerator to Gauss norm at most `1`. Every `a ∈ (K°)ⁿ` whose residue
avoids the vanishing locus of the reduced denominator then lies in `R(T/g)`.

When the residue field `K° ⧸ K°°` is infinite, `MvPolynomial.funext` provides such a tuple `a`, so
every rational open (and hence every open neighbourhood) of `unitGaussPoint n K` contains a
classical point. Thus `unitGaussPoint n K` lies in the closure of the classical points
(`TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_classicalPoint` and
`TauCeti.ValuationSpectrum.gaussPoint_mem_closure_rationalPoints`), and consequently every closed
subset of a topological space containing the image of the classical points under a continuous map
from `closedPolydisc n K` also contains the image of the unit Gauss point. In positive dimension
this implies that the classical points do not form a closed subset of the polydisc.

Conversely, when `K° ⧸ K°°` is finite of cardinality `q` and `n ≥ 1`, the rational open
`R({1} / (T₀^q - T₀))` contains `unitGaussPoint n K` but no classical point, since `‖a₀^q - a₀‖ < 1`
for every `a₀ ∈ K°` by `FiniteField.pow_card`. Thus, in positive dimension, the unit Gauss point
lies in the closure of the classical points if and only if the residue field `K° ⧸ K°°` is
infinite.

All results above — other than the comparison with the one-variable `gaussPoint` — require only
`[NormedField K] [IsUltrametricDist K]` (plus `[CompleteSpace K]` for evaluation), and thus apply
both to nontrivially normed complete nonarchimedean fields and to trivially normed fields.

## Main definitions

* `TauCeti.ValuationSpectrum.unitGaussValuation`: the unit-radius Gauss valuation
  `K⟨T₁, …, Tₙ⟩ → ℝ≥0`.
* `TauCeti.ValuationSpectrum.IsUnitGaussPoint`: predicate characterizing the valuation class of
  the unit Gauss point of `closedPolydisc n K` via `MvPowerSeries.gaussNorm`.
* `TauCeti.ValuationSpectrum.unitGaussPoint`: the unit Gauss point of `closedPolydisc n K`.
* `TauCeti.ValuationSpectrum.polydiscReduction`: coefficientwise reduction
  `K°⟨T₁, …, Tₙ⟩ →+* (K° ⧸ K°°)[T₁, …, Tₙ]`.

## Main results

* `TauCeti.ValuationSpectrum.coe_unitGaussValuation`: the unit Gauss valuation coincides with
  `MvPowerSeries.gaussNorm norm (fun _ ↦ 1)`.
* `TauCeti.ValuationSpectrum.isUnitGaussPoint_iff_eq_unitGaussPoint`: `IsUnitGaussPoint K n η`
  holds if and only if `η = unitGaussPoint n K`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_one_eq_gaussPoint`: in dimension `1`,
  `unitGaussPoint 1 K` equals `gaussPoint zero_lt_one le_rfl`.
* `TauCeti.ValuationSpectrum.subsingleton_closedPolydisc_zero` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_zero_eq_classicalPoint`: in dimension `0`, the polydisc
  is a subsingleton and its unit Gauss point is classical.
* `TauCeti.ValuationSpectrum.mk_evalAtHom_eq_eval_polydiscReduction`: reduction commutes with
  evaluation at power-bounded tuples.
* `TauCeti.ValuationSpectrum.classicalPoint_mem_rationalSubset_of_eval_polydiscReduction_ne_zero`:
  normalized rational neighbourhoods of `unitGaussPoint n K` contain every classical point whose
  reduction does not kill the reduced denominator.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_classicalPoint` and
  `TauCeti.ValuationSpectrum.gaussPoint_mem_closure_rationalPoints`: over a complete ultrametric
  normed field with infinite residue field, the unit Gauss point lies in the closure of the
  classical points.
* `TauCeti.ValuationSpectrum.map_unitGaussPoint_mem_of_isClosed`: any closed set containing the
  image of the classical points under a continuous map out of `closedPolydisc n K` contains the
  image of the unit Gauss point.
* `TauCeti.ValuationSpectrum.not_isClosed_range_classicalPoint`: in positive dimension with
  infinite residue field, the classical points do not form a closed subset of the polydisc.
* `TauCeti.ValuationSpectrum.unitGaussPoint_notMem_closure_classicalPoint_of_finite` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_classicalPoint_iff`: in positive dimension,
  membership of `unitGaussPoint n K` in the closure of the classical points is equivalent to
  infinitude of `K° ⧸ K°°`.

## References

* Sean Howe and Christian Klevdal, *Admissible pairs and p-adic Hodge structures II: the
  bi-analytic Ax–Lindemann theorem*, arXiv:2308.11064v2, proof of Lemma 9.3.5.
* Bhargav Bhatt and David Hansen, *The six functors for Zariski-constructible sheaves in rigid
  geometry*, arXiv:2101.09759v2, Example 2.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50 and
  Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber Filter Topology
open scoped NNReal

section UnitGaussValuation

variable (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- **The unit Gauss valuation on `K⟨T₁, …, Tₙ⟩`**, sending `f = ∑_ν a_ν T^ν` to `max_ν ‖a_ν‖₊`. -/
noncomputable def unitGaussValuation :
    Valuation
      (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
      ℝ≥0 :=
  weightedGaussValuation n (NormedField.isContinuous_valuation (K := K))

/-- Every coefficient of `f` has `nnNorm` at most `unitGaussValuation n K f`. -/
theorem nnNorm_coeff_le_unitGaussValuation
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (ν : Fin n →₀ ℕ) :
    ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) K)‖₊ ≤ unitGaussValuation n K f :=
  coeff_le_weightedGaussValuation (NormedField.isContinuous_valuation (K := K)) f ν

/-- The unit Gauss valuation is attained at some multi-index. -/
theorem exists_nnNorm_coeff_eq_unitGaussValuation
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    ∃ ν, ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) K)‖₊ = unitGaussValuation n K f :=
  exists_coeff_eq_weightedGaussValuation (NormedField.isContinuous_valuation (K := K)) (f := f)

/-- `unitGaussValuation n K f ≤ r` if and only if every coefficient of `f` has `nnNorm` at most
`r`. -/
theorem unitGaussValuation_le_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    {r : ℝ≥0} :
    unitGaussValuation n K f ≤ r ↔
      ∀ ν, ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) K)‖₊ ≤ r :=
  weightedGaussValuation_le_iff (NormedField.isContinuous_valuation (K := K))

/-- `unitGaussValuation n K f < r` if and only if every coefficient of `f` has `nnNorm` strictly
less than `r`. -/
theorem unitGaussValuation_lt_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    {r : ℝ≥0} :
    unitGaussValuation n K f < r ↔
      ∀ ν, ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) K)‖₊ < r :=
  weightedGaussValuation_lt_iff (NormedField.isContinuous_valuation (K := K))

/-- The unit Gauss valuation vanishes only on the zero series. -/
@[simp]
theorem unitGaussValuation_eq_zero_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    unitGaussValuation n K f = 0 ↔ f = 0 := by
  rw [unitGaussValuation, weightedGaussValuation_eq_zero_iff]
  simp only [NormedField.valuation_apply, nnNorm_eq_zero]
  exact ⟨fun h ↦ Subtype.ext (MvPowerSeries.ext fun ν ↦ by simp [h ν]), fun h ν ↦ by simp [h]⟩

/-- On constants, the unit Gauss valuation is the `nnNorm`. -/
@[simp]
theorem unitGaussValuation_weightedC (a : K) :
    unitGaussValuation n K
        (weightedC (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight a) = ‖a‖₊ :=
  weightedGaussValuation_weightedC (NormedField.isContinuous_valuation (K := K)) a

/-- Every coordinate variable has unit Gauss valuation `1`. -/
@[simp]
theorem unitGaussValuation_weightedX (i : Fin n) :
    unitGaussValuation n K
        (weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight i) = 1 :=
  weightedGaussValuation_weightedX (NormedField.isContinuous_valuation (K := K)) i

/-- The unit Gauss valuation coerces to Mathlib's unit-radius `MvPowerSeries.gaussNorm`. -/
theorem coe_unitGaussValuation
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussValuation n K f : ℝ) =
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) := by
  rw [← coe_restrictedMvPowerSeriesGaussEquiv f, ← MvPowerSeries.norm_eq_gaussNorm]
  refine le_antisymm ?_ (MvPowerSeries.norm_le_iff.mpr fun ν ↦ ?_)
  · obtain ⟨ν, hν⟩ := exists_nnNorm_coeff_eq_unitGaussValuation n K f
    have h := MvPowerSeries.norm_coeff_mul_prod_le (restrictedMvPowerSeriesGaussEquiv f) ν
    simpa only [coe_restrictedMvPowerSeriesGaussEquiv, one_pow, Finsupp.prod,
      Finset.prod_const_one, mul_one, ← coe_nnNorm, hν] using h
  · simpa only [coe_restrictedMvPowerSeriesGaussEquiv, one_pow, Finsupp.prod,
      Finset.prod_const_one, mul_one, ← coe_nnNorm] using
      NNReal.coe_le_coe.mpr (nnNorm_coeff_le_unitGaussValuation n K f ν)

/-- The unit Gauss valuation is continuous for the restricted-series topology. -/
theorem isContinuous_unitGaussValuation : (unitGaussValuation n K).IsContinuous :=
  isContinuous_weightedGaussValuation (NormedField.isContinuous_valuation (K := K))

/-- A series has unit Gauss valuation at most `1` if and only if it lies in `K°⟨T₁, …, Tₙ⟩`. -/
theorem unitGaussValuation_le_one_iff_mem_weightedSubring
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    unitGaussValuation n K f ≤ 1 ↔
      f ∈ weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) := by
  rw [unitGaussValuation_le_iff, mem_weightedSubring, mem_weightedNhd]
  refine forall_congr' fun ν ↦ ?_
  rw [weightMul_one_weight, Subring.mem_toAddSubgroup, mem_powerBoundedSubring,
    isPowerBounded_iff_norm_le_one, ← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]

variable {n K} in
/-- **The unit Gauss valuation is at most `1` on power-bounded series.** When `K` is nontrivially
normed, `K⟨T⟩° = K°⟨T⟩`; when `K` is trivially normed, every element of `K` already has norm at
most `1`. -/
theorem unitGaussValuation_le_one_of_mem_powerBoundedSubring
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hf : f ∈ powerBoundedSubring
      (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)) :
    unitGaussValuation n K f ≤ 1 := by
  by_cases hnt : ∃ c : K, 1 < ‖c‖
  · let : NontriviallyNormedField K := { ‹NormedField K› with non_trivial := hnt }
    rw [unitGaussValuation_le_one_iff_mem_weightedSubring,
      weightedSubring_powerBoundedSubring_eq n]
    exact hf
  · push Not at hnt
    exact (unitGaussValuation_le_iff n K).mpr fun ν ↦ by
      rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]
      exact hnt _

end UnitGaussValuation

section UnitGaussPoint

variable (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- A point `η` of the closed unit polydisc of dimension `n` over `K` is the unit Gauss point if it
compares restricted power series as their unit Gauss norms `‖∑ a_α T^α‖ = max ‖a_α‖` do. -/
def IsUnitGaussPoint (K : Type*) [NormedField K] [IsUltrametricDist K] (n : ℕ)
    (η : closedPolydisc n K) : Prop :=
  ∀ f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
    η.val.toValuativeRel.vle f g ↔
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) ≤
        MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (g : MvPowerSeries (Fin n) K)

/-- Unfolding lemma for `IsUnitGaussPoint`. -/
theorem isUnitGaussPoint_iff {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]
    {η : closedPolydisc n K} :
    IsUnitGaussPoint K n η ↔
      ∀ f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
        η.val.toValuativeRel.vle f g ↔
          MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) ≤
            MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (g : MvPowerSeries (Fin n) K) :=
  Iff.rfl

/-- **The unit Gauss point of `closedPolydisc n K`**: the point of `Spa (K⟨T₁, …, Tₙ⟩, K⟨T⟩°)`
defined by `unitGaussValuation n K`. -/
noncomputable def unitGaussPoint : closedPolydisc n K :=
  ⟨ofValuation (unitGaussValuation n K), (mem_closedPolydisc_iff n K _).mpr
    ⟨(isContinuous_ofValuation_iff _).mpr (isContinuous_unitGaussValuation n K),
      fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
        rw [map_one]
        exact unitGaussValuation_le_one_of_mem_powerBoundedSubring hf⟩⟩

/-- The underlying point of `unitGaussPoint n K` in `Spv K⟨T₁, …, Tₙ⟩`. -/
theorem unitGaussPoint_val :
    (unitGaussPoint n K).val = ofValuation (unitGaussValuation n K) := (rfl)

/-- The unit Gauss point compares restricted power series by their unit Gauss valuations. -/
@[simp]
theorem unitGaussPoint_vle_iff
    (f g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussPoint n K).val.toValuativeRel.vle f g ↔
      unitGaussValuation n K f ≤ unitGaussValuation n K g := by
  rw [unitGaussPoint_val, vle_ofValuation]

/-- The unit Gauss point kills only the zero series. -/
theorem unitGaussPoint_vle_zero_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    (unitGaussPoint n K).val.toValuativeRel.vle f 0 ↔ f = 0 := by
  rw [unitGaussPoint_vle_iff, map_zero, nonpos_iff_eq_zero, unitGaussValuation_eq_zero_iff]

/-- **The support of the unit Gauss point is trivial.** -/
@[simp]
theorem supp_unitGaussPoint : (unitGaussPoint n K).val.supp = ⊥ :=
  Ideal.ext fun _ ↦ by rw [mem_supp_iff, unitGaussPoint_vle_zero_iff, Ideal.mem_bot]

/-- `unitGaussPoint n K` satisfies `IsUnitGaussPoint K n`. -/
theorem isUnitGaussPoint_unitGaussPoint : IsUnitGaussPoint K n (unitGaussPoint n K) := by
  intro f g
  rw [unitGaussPoint_vle_iff, ← NNReal.coe_le_coe, coe_unitGaussValuation, coe_unitGaussValuation]

variable {n K} in
/-- Any point satisfying `IsUnitGaussPoint K n` equals `unitGaussPoint n K`. -/
theorem IsUnitGaussPoint.eq_unitGaussPoint {η : closedPolydisc n K}
    (hη : IsUnitGaussPoint K n η) : η = unitGaussPoint n K :=
  Subtype.ext <| ext' fun f g ↦
    (isUnitGaussPoint_iff.mp hη f g).trans (isUnitGaussPoint_unitGaussPoint n K f g).symm

/-- `IsUnitGaussPoint K n η` uniquely characterizes `unitGaussPoint n K`. -/
theorem isUnitGaussPoint_iff_eq_unitGaussPoint {n : ℕ} {K : Type*} [NormedField K]
    [IsUltrametricDist K] {η : closedPolydisc n K} :
    IsUnitGaussPoint K n η ↔ η = unitGaussPoint n K :=
  ⟨IsUnitGaussPoint.eq_unitGaussPoint, fun h ↦ h ▸ isUnitGaussPoint_unitGaussPoint n K⟩

/-- **In positive dimension over a complete field, the unit Gauss point is not classical.** -/
theorem unitGaussPoint_ne_classicalPoint {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [NeZero n] (x : spa (powerBoundedSubring K)) (a : Fin n → K)
    (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint n K ≠ classicalPoint x a ha :=
  ne_classicalPoint_of_supp_eq_bot _ (supp_unitGaussPoint n K) x a ha

/-- **In dimension `1`, `unitGaussPoint 1 K` coincides with the radius-`1` Gauss point
`gaussPoint zero_lt_one le_rfl`.** -/
theorem unitGaussPoint_one_eq_gaussPoint {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    unitGaussPoint 1 K = gaussPoint (K := K) zero_lt_one le_rfl := by
  have hval : ∀ f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
      isWeightFamily_one_weight,
      unitGaussValuation 1 K f = closedDiscGaussValuation (R := K) zero_lt_one le_rfl f := by
    intro f
    refine le_antisymm ?_ ?_
    · refine (unitGaussValuation_le_iff 1 K).mpr fun ν ↦ ?_
      have hν : ν = Finsupp.single 0 (ν 0) := Finsupp.ext fun i ↦ by
        rw [Subsingleton.elim i 0, Finsupp.single_eq_same]
      have h := norm_coeff_mul_pow_le_closedDiscGaussValuation (R := K) zero_lt_one le_rfl f (ν 0)
      rw [one_pow, mul_one, ← hν] at h
      exact_mod_cast h
    · refine NNReal.coe_le_coe.mp ?_
      refine closedDiscGaussValuation_le_of_forall_norm_coeff_le zero_lt_one le_rfl fun ν ↦ ?_
      exact_mod_cast nnNorm_coeff_le_unitGaussValuation 1 K f ν
  refine Subtype.ext <| ext' fun f g ↦ ?_
  rw [unitGaussPoint_vle_iff, gaussPoint_vle_iff, hval f, hval g]

/-- **The zero-dimensional closed polydisc over an ultrametric normed field is a subsingleton**:
every restricted power series in zero variables is constant, and every point of the polydisc
compares constants by their norms. -/
theorem subsingleton_closedPolydisc_zero {K : Type*} [NormedField K] [IsUltrametricDist K] :
    Subsingleton (closedPolydisc 0 K) := by
  refine ⟨fun v w ↦ Subtype.ext <| ext' fun f g ↦ ?_⟩
  have hconst : ∀ h : weightedRestrictedSubring (fun _ : Fin 0 ↦ ({1} : Set K))
      isWeightFamily_one_weight,
      h = weightedC _ isWeightFamily_one_weight (weightedRestrictedSubringFinZeroEquiv _ h) :=
    fun h ↦ ((weightedRestrictedSubringFinZeroEquiv _).symm_apply_apply h).symm.trans
      (Subtype.ext (by simp))
  rw [hconst f, hconst g, closedPolydisc_vle_weightedC_iff, closedPolydisc_vle_weightedC_iff]

/-- **In dimension `0`, the unit Gauss point coincides with every classical point**, without any
residue-field assumption. -/
theorem unitGaussPoint_zero_eq_classicalPoint {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (x : spa (powerBoundedSubring K)) (a : Fin 0 → K)
    (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint 0 K = classicalPoint x a ha :=
  @Subsingleton.elim _ subsingleton_closedPolydisc_zero _ _

/-- **In dimension `0`, the unit Gauss point lies in the closure of the classical points** over
every complete ultrametric normed field, with no residue-field infinitude hypothesis. -/
theorem unitGaussPoint_zero_mem_closure_classicalPoint {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (x : spa (powerBoundedSubring K)) :
    unitGaussPoint 0 K ∈ closure (Set.range
      (fun a : {a : Fin 0 → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property)) :=
  subset_closure ⟨⟨Fin.elim0, fun i ↦ i.elim0⟩,
    (unitGaussPoint_zero_eq_classicalPoint x Fin.elim0 fun i ↦ i.elim0).symm⟩

end UnitGaussPoint

section ReductionAndClosure

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The canonical ring isomorphism between unit-weight restricted series over `K°` and
`K°⟨T₁, …, Tₙ⟩`, obtained by codomain-restricting `weightedMap` along `K° ↪ K` and inverting. -/
private noncomputable def weightedRestrictedSubringEquivWeightedSubring :
    weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set (powerBoundedSubring K)))
        isWeightFamily_one_weight ≃+*
      weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) := by
  let hsub : Continuous (powerBoundedSubring K).subtype := continuous_subtypeVal
  let ι : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set (powerBoundedSubring K)))
        isWeightFamily_one_weight →+*
      weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) :=
    (weightedMap hsub isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ by simp)).codRestrict _ fun f ↦ by
      rw [mem_weightedSubring, mem_weightedNhd]
      intro ν
      rw [weightMul_one_weight, coe_weightedMap, MvPowerSeries.coeff_map, Subring.coe_subtype,
        Subring.mem_toAddSubgroup]
      exact (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) (powerBoundedSubring K))).property
  refine RingEquiv.ofBijective ι ⟨fun f g h ↦ Subtype.ext <| MvPowerSeries.ext fun ν ↦
      Subtype.ext ?_, fun g ↦ ?_⟩
  · have h' := congrArg (fun x ↦ MvPowerSeries.coeff ν (x.val : MvPowerSeries (Fin n) K)) h
    simpa [ι, coe_weightedMap] using h'
  · let f : MvPowerSeries (Fin n) (powerBoundedSubring K) := fun ν ↦
      ⟨MvPowerSeries.coeff ν (g.val : MvPowerSeries (Fin n) K),
        by simpa only [weightMul_one_weight, Subring.mem_toAddSubgroup] using
          mem_weightedNhd.mp (mem_weightedSubring.mp g.property) ν⟩
    have hf : IsWeightedRestricted (fun _ : Fin n ↦ ({1} : Set (powerBoundedSubring K))) f :=
      isWeightedRestricted_one_weight_iff.mpr <| tendsto_subtype_rng.mpr <|
        isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp g.val.property)
    exact ⟨⟨f, mem_weightedRestrictedSubring.mpr hf⟩,
      Subtype.ext <| Subtype.ext <| MvPowerSeries.ext fun ν ↦ by simp [ι, f]; rfl⟩

/-- **Coefficientwise reduction on `K°⟨T₁, …, Tₙ⟩`**, sending a unit-bounded restricted power
series to the polynomial over the canonical residue field `K° ⧸ K°°` obtained by reducing each
coefficient. -/
noncomputable def polydiscReduction (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K] :
    weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) →+*
      MvPolynomial (Fin n) (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K) :=
  (Ideal.restrictedReduction (k := n) (topologicallyNilpotentIdeal K) <| by
    have hopen : (topologicallyNilpotentIdeal K : Set (powerBoundedSubring K)) =
        (Subtype.val : powerBoundedSubring K → K) ⁻¹' Metric.ball 0 1 := by
      ext a
      simp only [SetLike.mem_coe, mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
        tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, Set.mem_preimage, mem_ball_zero_iff]
    rw [hopen]
    exact Metric.isOpen_ball.preimage continuous_subtypeVal).comp
    weightedRestrictedSubringEquivWeightedSubring.symm.toRingHom

/-- Each coefficient of `polydiscReduction n K f` is the residue class of the corresponding
coefficient of `f`. -/
@[simp]
theorem coeff_polydiscReduction
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) (ν : Fin n →₀ ℕ) :
    (polydiscReduction n K f).coeff ν =
      Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
        ⟨MvPowerSeries.coeff ν (f.val : MvPowerSeries (Fin n) K),
          by simpa only [weightMul_one_weight, Subring.mem_toAddSubgroup] using
            mem_weightedNhd.mp (mem_weightedSubring.mp f.property) ν⟩ := by
  simp only [polydiscReduction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, Ideal.coeff_restrictedReduction]
  refine congrArg (Ideal.Quotient.mk _) (Subtype.ext ?_)
  have hsub : Continuous (powerBoundedSubring K).subtype := continuous_subtypeVal
  have h : MvPowerSeries.coeff ν ((weightedMap hsub isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ by simp)
      (weightedRestrictedSubringEquivWeightedSubring.symm f) :
        weightedRestrictedSubring _ _) : MvPowerSeries (Fin n) K) =
      MvPowerSeries.coeff ν (f.val : MvPowerSeries (Fin n) K) :=
    congrArg (fun g ↦ MvPowerSeries.coeff ν (g.val : MvPowerSeries (Fin n) K))
      (weightedRestrictedSubringEquivWeightedSubring.apply_symm_apply f)
  rwa [coe_weightedMap, MvPowerSeries.coeff_map, Subring.coe_subtype] at h

/-- A coefficient of `polydiscReduction n K f` vanishes if and only if the corresponding
coefficient of `f` has norm strictly less than `1`. -/
theorem coeff_polydiscReduction_eq_zero_iff
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) (ν : Fin n →₀ ℕ) :
    (polydiscReduction n K f).coeff ν = 0 ↔
      ‖MvPowerSeries.coeff ν (f.val : MvPowerSeries (Fin n) K)‖ < 1 := by
  rw [coeff_polydiscReduction, Ideal.Quotient.eq_zero_iff_mem, mem_topologicallyNilpotentIdeal,
    IsTopologicallyNilpotent, tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]

/-- The reduction of a unit-bounded series vanishes if and only if its unit Gauss valuation is
strictly less than `1`. -/
theorem polydiscReduction_eq_zero_iff
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    polydiscReduction n K f = 0 ↔ unitGaussValuation n K f.val < 1 := by
  rw [MvPolynomial.ext_iff, unitGaussValuation_lt_iff]
  refine forall_congr' fun ν ↦ ?_
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
    coeff_polydiscReduction_eq_zero_iff, ← NNReal.coe_lt_coe, coe_nnNorm, NNReal.coe_one]

/-- The reduction of a unit-bounded series is nonzero if and only if its unit Gauss valuation
equals `1`. -/
theorem polydiscReduction_ne_zero_iff
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    polydiscReduction n K f ≠ 0 ↔ unitGaussValuation n K f.val = 1 := by
  rw [Ne, polydiscReduction_eq_zero_iff, not_lt]
  have hle : unitGaussValuation n K f.val ≤ 1 :=
    (unitGaussValuation_le_one_iff_mem_weightedSubring n K).mpr f.property
  exact ⟨fun h ↦ le_antisymm hle h, fun h ↦ h.ge⟩

open scoped Classical in
/-- Scaling by the inverse of a coefficient attaining `unitGaussValuation n K g` normalizes any
basic open `Spv(K⟨T⟩)(T/g)` containing `unitGaussPoint n K` to unit Gauss valuation `1` on the
denominator and at most `1` on all numerators. -/
private theorem exists_unit_mul_unitGaussValuation_eq_one
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hη : (unitGaussPoint n K).val ∈ basicOpenFinset T g) :
    ∃ u : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight,
      IsUnit u ∧ unitGaussValuation n K (g * u) = 1 ∧
        ∀ f ∈ T.image (· * u), unitGaussValuation n K f ≤ 1 := by
  rw [mem_basicOpenFinset_iff] at hη
  obtain ⟨hT, hg0⟩ := hη
  have hgv0 : unitGaussValuation n K g ≠ 0 := fun h0 ↦
    hg0 ((unitGaussPoint_vle_zero_iff n K).mpr ((unitGaussValuation_eq_zero_iff n K).mp h0))
  obtain ⟨ν₀, hν₀⟩ := exists_nnNorm_coeff_eq_unitGaussValuation n K g
  set c : K := MvPowerSeries.coeff ν₀ (g : MvPowerSeries (Fin n) K)
  have hc0 : c ≠ 0 := nnNorm_ne_zero_iff.mp (hν₀.trans_ne hgv0)
  set u := weightedC (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight c⁻¹
  have hu_val : unitGaussValuation n K u = (unitGaussValuation n K g)⁻¹ := by
    rw [unitGaussValuation_weightedC, nnNorm_inv, hν₀]
  refine ⟨u, (IsUnit.mk0 c⁻¹ (inv_ne_zero hc0)).map _,
    by rw [map_mul, hu_val, mul_inv_cancel₀ hgv0], fun f hf ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
  rw [map_mul, hu_val]
  exact (mul_le_mul_of_nonneg_right ((unitGaussPoint_vle_iff n K t g).mp (hT t ht))
    zero_le).trans_eq (mul_inv_cancel₀ hgv0)

variable [CompleteSpace K]

/-- Evaluating a unit-bounded series at a power-bounded tuple yields a power-bounded element. -/
theorem evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring
    (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    evalAtHom a ha f.val ∈ powerBoundedSubring K := by
  rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one]
  refine (norm_evalAtHom_le ha (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i)) f.val).trans ?_
  rw [← coe_unitGaussValuation]
  exact_mod_cast (unitGaussValuation_le_one_iff_mem_weightedSubring n K).mpr f.property

/-- **Reduction commutes with evaluation at power-bounded tuples.** For `f ∈ K°⟨T₁, …, Tₙ⟩` and
`a ∈ (K°)ⁿ`, the residue class of `f(a)` in `K° ⧸ K°°` equals the value of `polydiscReduction n K f`
at the residue tuple `ā`. -/
theorem mk_evalAtHom_eq_eval_polydiscReduction (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
        ⟨evalAtHom a ha f.val, evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha f⟩ =
      MvPolynomial.eval
        (fun i ↦ Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
          ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩)
        (polydiscReduction n K f) := by
  have : CompleteSpace (powerBoundedSubring K) :=
    (coe_powerBoundedSubring_eq_closedBall K ▸ Metric.isClosed_closedBall).completeSpace_coe
  let b : Fin n → powerBoundedSubring K := fun i ↦ ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩
  have huniv : TauCeti.Huber.IsBounded (Set.univ : Set (powerBoundedSubring K)) := by
    rw [TauCeti.Huber.isBounded_iff]
    intro U hU
    rw [nhds_subtype, Filter.mem_comap] at hU
    obtain ⟨U', hU', hUU'⟩ := hU
    obtain ⟨V', hV', hV'U'⟩ := (TauCeti.Huber.isBounded_iff.mp
      (IsUniform.isBounded_powerBoundedSubring (A := K))) U' hU'
    refine ⟨Subtype.val ⁻¹' V', continuous_subtypeVal.continuousAt.preimage_mem_nhds
      (by simpa using hV'), fun _ hx ↦ ?_⟩
    obtain ⟨v, hv, w, _, rfl⟩ := hx
    exact hUU' (hV'U' (Set.mul_mem_mul hv w.property))
  have hb : IsWeightBounded (RingHom.id (powerBoundedSubring K))
      (fun _ : Fin n ↦ ({1} : Set (powerBoundedSubring K))) b :=
    (isWeightBounded_one_weight_iff _ _).mpr (huniv.subset (Set.subset_univ _))
  have hopen : IsOpen (topologicallyNilpotentIdeal K : Set (powerBoundedSubring K)) := by
    have heq : (topologicallyNilpotentIdeal K : Set (powerBoundedSubring K)) =
        (Subtype.val : powerBoundedSubring K → K) ⁻¹' Metric.ball 0 1 := by
      ext x
      simp only [SetLike.mem_coe, mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
        tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, Set.mem_preimage, mem_ball_zero_iff]
    rw [heq]
    exact Metric.isOpen_ball.preimage continuous_subtypeVal
  have hsub : Continuous (powerBoundedSubring K).subtype := continuous_subtypeVal
  have hext :
      (powerBoundedSubring K).subtype.comp
          (weightedEvalHom isWeightFamily_one_weight continuousAt_id hb) =
        (evalAtHom a ha).comp (weightedMap hsub isWeightFamily_one_weight isWeightFamily_one_weight
          (fun _ ↦ by simp)) := by
    refine weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (continuous_subtypeVal.comp (continuous_weightedEvalHom _ _ _))
      ((continuous_evalAtHom a ha).comp (continuous_weightedMap _ _ _ _))
      (fun c ↦ by simp) (fun i ↦ by simp [b])
  have heval :
      (⟨evalAtHom a ha f.val, evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha f⟩ :
          powerBoundedSubring K) =
        weightedEvalHom isWeightFamily_one_weight continuousAt_id hb
          (weightedRestrictedSubringEquivWeightedSubring.symm f) := by
    refine Subtype.ext ?_
    have h := DFunLike.congr_fun hext (weightedRestrictedSubringEquivWeightedSubring.symm f)
    have hval : weightedMap hsub isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ by simp) (weightedRestrictedSubringEquivWeightedSubring.symm f) = f.val :=
      congrArg Subtype.val (weightedRestrictedSubringEquivWeightedSubring.apply_symm_apply f)
    simpa [hval] using h.symm
  rw [heval, mk_weightedEvalHom_eq_eval₂_restrictedReduction continuousAt_id hb hopen hopen le_rfl]
  have hid : Ideal.quotientMap (I := topologicallyNilpotentIdeal K)
      (topologicallyNilpotentIdeal K) (RingHom.id (powerBoundedSubring K)) le_rfl =
      RingHom.id _ := RingHom.ext fun q ↦ by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl
  rw [hid, MvPolynomial.eval₂_id]
  rfl

/-- A unit-bounded series `f ∈ K°⟨T₁, …, Tₙ⟩` evaluates to an element of norm `1` at `a ∈ (K°)ⁿ`
if and only if its reduction does not vanish at the residue tuple `ā`. -/
theorem norm_evalAtHom_eq_one_iff_eval_polydiscReduction_ne_zero (a : Fin n → K)
    (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    ‖evalAtHom a ha f.val‖ = 1 ↔
      MvPolynomial.eval
        (fun i ↦ Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
          ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩)
        (polydiscReduction n K f) ≠ 0 := by
  have hle : ‖evalAtHom a ha f.val‖ ≤ 1 :=
    isPowerBounded_iff_norm_le_one.mp
      (mem_powerBoundedSubring.mp
        (evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha f))
  rw [← mk_evalAtHom_eq_eval_polydiscReduction a ha f, Ne, Ideal.Quotient.eq_zero_iff_mem,
    mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
    tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, not_lt]
  exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm hle h⟩

/-- **Normalized rational-neighbourhood criterion at the unit Gauss point.** If `g ∈ K°⟨T⟩` and
every `f ∈ T` has unit Gauss valuation at most `1`, then `R(T/g)` contains every classical point
`classicalPoint x a ha` whose residue tuple `ā` does not annihilate `polydiscReduction n K g`. -/
theorem classicalPoint_mem_rationalSubset_of_eval_polydiscReduction_ne_zero
    (x : spa (powerBoundedSubring K))
    {T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight)}
    {g : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)}
    (hT : ∀ f ∈ T, unitGaussValuation n K f ≤ 1)
    {a : Fin n → K} (ha : ∀ i, IsPowerBounded (a i))
    (hga : MvPolynomial.eval
      (fun i ↦ Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
        ⟨a i, mem_powerBoundedSubring.mpr (ha i)⟩)
      (polydiscReduction n K g) ≠ 0) :
    (classicalPoint x a ha).val ∈ rationalSubset (powerBoundedSubring _) T g.val := by
  have hg1 : ‖evalAtHom a ha g.val‖ = 1 :=
    (norm_evalAtHom_eq_one_iff_eval_polydiscReduction_ne_zero a ha g).mpr hga
  rw [classicalPoint_mem_rationalSubset_iff]
  refine ⟨fun f hf ↦ ?_, norm_pos_iff.mp (by linarith)⟩
  rw [hg1]
  refine (norm_evalAtHom_le ha (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i)) f).trans ?_
  rw [← coe_unitGaussValuation]
  exact_mod_cast hT f hf

open scoped Classical in
/-- Every basic open `Spv(K⟨T⟩)(T/g)` containing the unit Gauss point contains a classical point
when the residue field `K° ⧸ K°°` is infinite. -/
theorem exists_classicalPoint_mem_basicOpenFinset
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (x : spa (powerBoundedSubring K))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hη : (unitGaussPoint n K).val ∈ basicOpenFinset T g) :
    ∃ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)),
      (classicalPoint x a ha).val ∈ basicOpenFinset T g := by
  obtain ⟨u, hu, hg'_val, hT'_val⟩ := exists_unit_mul_unitGaussValuation_eq_one T g hη
  let g' : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K) :=
    ⟨g * u, (unitGaussValuation_le_one_iff_mem_weightedSubring n K).mp hg'_val.le⟩
  have hred_ne : polydiscReduction n K g' ≠ 0 := (polydiscReduction_ne_zero_iff g').mpr hg'_val
  have : (topologicallyNilpotentIdeal K).IsMaximal := isMaximal_topologicallyNilpotentIdeal
  let : Field (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K) :=
    Ideal.Quotient.field (topologicallyNilpotentIdeal K)
  have hex : ∃ ā : Fin n → (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K),
      MvPolynomial.eval ā (polydiscReduction n K g') ≠ 0 := by
    by_contra! hall
    exact hred_ne (MvPolynomial.funext fun ā ↦ by simpa using hall ā)
  obtain ⟨ā, hā⟩ := hex
  choose b hb using fun i ↦ Ideal.Quotient.mk_surjective (ā i)
  refine ⟨fun i ↦ (b i : K), fun i ↦ mem_powerBoundedSubring.mp (b i).property, ?_⟩
  have hmem := classicalPoint_mem_rationalSubset_of_eval_polydiscReduction_ne_zero x
    (T := T.image (· * u)) (g := g') hT'_val (fun i ↦ mem_powerBoundedSubring.mp (b i).property)
    (by
      have heq : (fun i ↦ Ideal.Quotient.mk (topologicallyNilpotentIdeal K)
          ⟨(b i : K), mem_powerBoundedSubring.mpr
            (mem_powerBoundedSubring.mp (b i).property)⟩) = ā :=
        funext fun i ↦ hb i
      rwa [heq])
  dsimp only [g'] at hmem
  rw [rationalSubset_def, Set.mem_inter_iff] at hmem
  rw [← basicOpenFinset_image_mul_right T g u hu]
  convert hmem.right

/-- Every rational subset `R(T/g)` of `closedPolydisc n K` containing the unit Gauss point contains
a classical point when `K° ⧸ K°°` is infinite. -/
theorem exists_classicalPoint_mem_rationalSubset
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (x : spa (powerBoundedSubring K))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hη : (unitGaussPoint n K).val ∈ rationalSubset (powerBoundedSubring _) T g) :
    ∃ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)),
      (classicalPoint x a ha).val ∈ rationalSubset (powerBoundedSubring _) T g := by
  rw [rationalSubset_def, Set.mem_inter_iff] at hη
  obtain ⟨a, ha, hmem⟩ := exists_classicalPoint_mem_basicOpenFinset x T g hη.right
  refine ⟨a, ha, ?_⟩
  rw [rationalSubset_def]
  exact ⟨closedPolydisc_def n K ▸ (classicalPoint x a ha).property, hmem⟩

/-- **Gauss-point closure.** Over a complete ultrametric normed field `K` whose residue field
`K° ⧸ K°°` is infinite, the unit Gauss point of `closedPolydisc n K` lies in the closure of the
classical points. -/
theorem unitGaussPoint_mem_closure_classicalPoint
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈ closure (Set.range
      (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property)) := by
  have : IsHuberRing K := by
    rcases NormedField.discreteTopology_or_nontriviallyNormedField K with _ | ⟨_, rfl⟩
    · infer_instance
    · exact (IsTateRing.of_nontriviallyNormedField K).toIsHuberRing
  rw [mem_closure_iff]
  intro U hU hηU
  let e : closedPolydisc n K ≃ₜ spa (powerBoundedSubring _) :=
    Homeomorph.setCongr (closedPolydisc_def n K)
  have hVopen : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hηV : e (unitGaussPoint n K) ∈ e.symm ⁻¹' U := by
    simpa [Set.mem_preimage] using hηU
  obtain ⟨_, hR, hηR, hRV⟩ :=
    (isTopologicalBasis_spaRationalFamily (powerBoundedSubring _)).exists_subset_of_mem_open
      hηV hVopen
  obtain ⟨T, g, -, rfl⟩ := mem_spaRationalFamily_iff.mp hR
  obtain ⟨a, ha, haMem⟩ := exists_classicalPoint_mem_rationalSubset x T g hηR
  refine ⟨classicalPoint x a ha, ?_, ⟨⟨a, ha⟩, rfl⟩⟩
  have hmem := hRV (a := e (classicalPoint x a ha)) haMem
  simpa [Set.mem_preimage] using hmem

/-- Every closed subset of `closedPolydisc n K` containing all classical points contains the unit
Gauss point, when `K° ⧸ K°°` is infinite. -/
theorem unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (x : spa (powerBoundedSubring K)) {Z : Set (closedPolydisc n K)} (hZ : IsClosed Z)
    (h : ∀ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)), classicalPoint x a ha ∈ Z) :
    unitGaussPoint n K ∈ Z :=
  hZ.closure_subset_iff.mpr (Set.range_subset_iff.mpr fun ⟨a, ha⟩ ↦ h a ha)
    (unitGaussPoint_mem_closure_classicalPoint x)

/-- **Gauss-point closure (existential form).** Over a complete ultrametric normed field `K` whose
residue field `K° ⧸ K°°` is infinite, the unit Gauss point exists on `closedPolydisc n K` and lies
in the closure of the evaluation points at tuples of power-bounded elements of `K`. -/
theorem gaussPoint_mem_closure_rationalPoints
    (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (n : ℕ) (x : spa (powerBoundedSubring K)) :
    ∃ η : closedPolydisc n K,
      IsUnitGaussPoint K n η ∧ η ∈ closure (Set.range
        (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
          classicalPoint x a.val a.property)) :=
  ⟨unitGaussPoint n K, isUnitGaussPoint_unitGaussPoint n K,
    unitGaussPoint_mem_closure_classicalPoint x⟩

/-- **Chartwise Gauss-point closure.** If `f : closedPolydisc n K → X` is any continuous map (for
instance a polydisc affinoid chart into a rigid space) and `Z ⊆ X` is a closed subset containing
the image of every classical point, then `Z` contains `f (unitGaussPoint n K)`. -/
theorem map_unitGaussPoint_mem_of_isClosed
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    {X : Type*} [TopologicalSpace X] (x : spa (powerBoundedSubring K))
    {f : closedPolydisc n K → X} (hf : Continuous f) {Z : Set X} (hZ : IsClosed Z)
    (h : ∀ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)), f (classicalPoint x a ha) ∈ Z) :
    f (unitGaussPoint n K) ∈ Z :=
  unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem x (hZ.preimage hf) h

/-- **In positive dimension with infinite residue field, the classical points do not form a closed
subset of `closedPolydisc n K`**: their closure contains the nonclassical unit Gauss point. -/
theorem not_isClosed_range_classicalPoint
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)] [NeZero n]
    (x : spa (powerBoundedSubring K)) :
    ¬ IsClosed (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.val a.property) := fun hclosed ↦ by
  obtain ⟨a, ha⟩ := unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem x hclosed
    fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩
  exact unitGaussPoint_ne_classicalPoint x a.val a.property ha.symm

end ReductionAndClosure

section FiniteResidue

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- For `q > 1`, the polynomial `T₀^q - T₀` has degree-`1` coefficient `-1`, hence unit Gauss
valuation at least `1`. -/
private theorem one_le_unitGaussValuation_weightedX_pow_sub [NeZero n] {q : ℕ} (hq : 1 < q) :
    1 ≤ unitGaussValuation n K
      (weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight 0 ^ q -
        weightedX _ isWeightFamily_one_weight 0) := by
  set X₀ : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedX _ isWeightFamily_one_weight 0
  have hne : Finsupp.single (0 : Fin n) 1 ≠ Finsupp.single (0 : Fin n) q := fun heq ↦ by
    have h1 := DFunLike.congr_fun heq 0
    simp at h1
    omega
  have h := nnNorm_coeff_le_unitGaussValuation n K (X₀ ^ q - X₀) (Finsupp.single 0 1)
  rw [AddSubgroupClass.coe_sub, map_sub, Subring.coe_pow, coe_weightedX,
    MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X] at h
  simpa only [hne, ↓reduceIte, zero_sub, nnNorm_neg, nnNorm_one] using h

variable [CompleteSpace K]

/-- **Failure of Gauss-point closure over finite residue fields.** When `K° ⧸ K°°` is finite of
cardinality `q` and `n ≥ 1`, the rational open `R({1} / (T₀^q - T₀))` separates
`unitGaussPoint n K` from all classical points. -/
theorem unitGaussPoint_notMem_closure_classicalPoint_of_finite
    [Finite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)] [NeZero n]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∉ closure (Set.range
      (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property)) := by
  let : Field (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K) :=
    Ideal.Quotient.field (topologicallyNilpotentIdeal K)
  let : Fintype (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K) := Fintype.ofFinite _
  set q := Fintype.card (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)
  set X₀ : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedX _ isWeightFamily_one_weight 0
  set g := X₀ ^ q - X₀
  set U : Set (closedPolydisc n K) := Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) {1} g
  have hg_ge : 1 ≤ unitGaussValuation n K g :=
    one_le_unitGaussValuation_weightedX_pow_sub Fintype.one_lt_card
  have hηU : unitGaussPoint n K ∈ U := by
    rw [Set.mem_preimage, mem_rationalSubset_singleton_one_iff
      (closedPolydisc_def n K ▸ (unitGaussPoint n K).property), unitGaussPoint_vle_iff, map_one]
    exact hg_ge
  have hU_open : IsOpen U := by
    dsimp only [U]
    rw [closedPolydisc_def]
    exact isOpen_val_preimage_rationalSubset _ _ _
  intro hmem
  obtain ⟨_, hpU, ⟨a, rfl⟩⟩ := mem_closure_iff.mp hmem U hU_open hηU
  rw [Set.mem_preimage, classicalPoint_mem_rationalSubset_iff] at hpU
  have hle := hpU.left 1 (Finset.mem_singleton_self 1)
  rw [map_one, norm_one] at hle
  -- Every power-bounded `a 0` satisfies `a 0 ^ q - a 0 ∈ K°°` by `FiniteField.pow_card`.
  let a₀ : powerBoundedSubring K := ⟨a.val 0, mem_powerBoundedSubring.mpr (a.property 0)⟩
  have hnil : a₀ ^ q - a₀ ∈ topologicallyNilpotentIdeal K := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero]
    exact FiniteField.pow_card (Ideal.Quotient.mk (topologicallyNilpotentIdeal K) a₀)
  have hlt : ‖evalAtHom a.val a.property g‖ < 1 := by
    have hlt' : ‖((a₀ ^ q - a₀ : powerBoundedSubring K) : K)‖ < 1 :=
      (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one).mp (mem_topologicallyNilpotentIdeal.mp hnil)
    simpa only [g, X₀, map_sub, map_pow, evalAtHom_weightedX, AddSubgroupClass.coe_sub,
      Subring.coe_pow] using hlt'
  exact hlt.not_ge hle

/-- **Characterization of Gauss-point closure in positive dimension.** Over a complete ultrametric
normed field `K` and for `n ≥ 1`, the unit Gauss point of `closedPolydisc n K` lies in the closure
of the classical points if and only if the residue field `K° ⧸ K°°` is infinite. -/
theorem unitGaussPoint_mem_closure_classicalPoint_iff [NeZero n]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈ closure (Set.range
        (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
          classicalPoint x a.val a.property)) ↔
      Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K) :=
  ⟨fun h ↦ not_finite_iff_infinite.mp fun _ ↦
      unitGaussPoint_notMem_closure_classicalPoint_of_finite x h,
    fun _ ↦ unitGaussPoint_mem_closure_classicalPoint x⟩

end FiniteResidue

end TauCeti.ValuationSpectrum
