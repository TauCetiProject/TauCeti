/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.PointTopology
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint
public import TauCeti.RingTheory.Huber.Restricted.UnitGaussValuation

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.RingTheory.Huber.Restricted.Comparison

/-!
# The unit Gauss point of a closed polydisc and rational-point closure

Let `K` be an ultrametric normed field and `D = closedPolydisc n K` the closed unit polydisc of
dimension `n` over `K`, whose coordinate ring is the trivial-weight restricted power series ring
`K⟨T₁, …, Tₙ⟩`. The unit-radius Gauss valuation `TauCeti.Huber.unitGaussValuation n K` is
continuous and bounded by `1` on `K⟨T₁, …, Tₙ⟩°`, so it defines the *unit Gauss point*
`unitGaussPoint n K : closedPolydisc n K`.

A point `η` of `closedPolydisc n K` satisfies the predicate `IsUnitGaussPoint K n η` when it
compares restricted power series by their unit Gauss norms; this uniquely characterizes
`unitGaussPoint n K`. In dimension `1` over a nontrivially normed field, `unitGaussPoint 1 K`
agrees with the radius-`1` Gauss point `TauCeti.ValuationSpectrum.gaussPoint zero_lt_one le_rfl`.
In dimension `0`, `closedPolydisc 0 K` is a subsingleton, so the unit Gauss point coincides with
the unique classical point without any residue-field assumption. In positive dimension over a
complete field, `unitGaussPoint n K` has trivial support and is therefore never classical.

To study the closure of the classical locus `classicalPoints n K`, we use coefficientwise reduction
`TauCeti.Huber.polydiscReduction n K : K°⟨T₁, …, Tₙ⟩ →+* (K° ⧸ K°°)[T₁, …, Tₙ]`. Given any basic
open `Spv(K⟨T⟩)(T/g)` containing `unitGaussPoint n K`, scaling by the inverse of a coefficient
attaining the Gauss norm of `g` normalizes `g` to unit Gauss norm and every numerator to Gauss norm
at most `1`. Every `a ∈ (K°)ⁿ` whose residue avoids the vanishing locus of the reduced denominator
then yields `normClassicalPoint a ha ∈ R(T/g)`.

When the residue field `K° ⧸ K°°` is infinite, `MvPolynomial.funext` provides such a tuple `a`, so
every rational open (and hence every open neighbourhood) of `unitGaussPoint n K` meets
`classicalPoints n K`. Thus `unitGaussPoint n K` lies in the closure of `classicalPoints n K`
(`TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_classicalPoints` and
`TauCeti.ValuationSpectrum.gaussPoint_mem_closure_rationalPoints`), and consequently every closed
subset of a topological space containing the image of `classicalPoints n K` under a continuous map
from `closedPolydisc n K` also contains the image of the unit Gauss point. In positive dimension
this implies that `classicalPoints n K` is not closed in `closedPolydisc n K`.

Conversely, when `K° ⧸ K°°` is finite of cardinality `q` and `n ≥ 1`, the rational open
`R({1} / (T₀^q - T₀))` contains `unitGaussPoint n K` but no point of `classicalPoints n K`, since
`‖a₀^q - a₀‖ < 1` for every `a₀ ∈ K°` by `FiniteField.pow_card`. Thus, in positive dimension,
membership of `unitGaussPoint n K` in `closure (classicalPoints n K)` is equivalent to infinitude
of `K° ⧸ K°°`.

All results above — other than the comparison with the one-variable `gaussPoint` — require only
`[NormedField K] [IsUltrametricDist K]` (plus `[CompleteSpace K]` for evaluation), and thus apply
both to nontrivially normed complete nonarchimedean fields and to trivially normed fields.

## Main definitions

* `TauCeti.ValuationSpectrum.IsUnitGaussPoint`: predicate characterizing the valuation class of
  the unit Gauss point of `closedPolydisc n K` via `MvPowerSeries.gaussNorm`.
* `TauCeti.ValuationSpectrum.unitGaussPoint`: the unit Gauss point of `closedPolydisc n K`.

## Main results

* `TauCeti.ValuationSpectrum.isUnitGaussPoint_iff_eq_unitGaussPoint`: `IsUnitGaussPoint K n η`
  holds if and only if `η = unitGaussPoint n K`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_one_eq_gaussPoint`: in dimension `1`,
  `unitGaussPoint 1 K` equals `gaussPoint zero_lt_one le_rfl`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_zero_eq_classicalPoint` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_zero_mem_closure_classicalPoints`: in dimension `0`, the
  unit Gauss point is classical and lies in `closure (classicalPoints 0 K)`.
* `normClassicalPoint_mem_rationalSubset_of_eval_polydiscReduction_ne_zero`: normalized rational
  neighbourhoods of `unitGaussPoint n K` contain every canonical classical point whose reduction
  does not kill the reduced denominator.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_classicalPoints` and
  `TauCeti.ValuationSpectrum.gaussPoint_mem_closure_rationalPoints`: over a complete ultrametric
  normed field with infinite residue field, the unit Gauss point lies in the closure of
  `classicalPoints n K`.
* `TauCeti.ValuationSpectrum.map_unitGaussPoint_mem_of_isClosed`: any closed set containing the
  image of `classicalPoints n K` under a continuous map out of `closedPolydisc n K` contains the
  image of the unit Gauss point.
* `TauCeti.ValuationSpectrum.not_isClosed_classicalPoints`: in positive dimension with infinite
  residue field, `classicalPoints n K` is not a closed subset of the polydisc.
* `TauCeti.ValuationSpectrum.unitGaussPoint_notMem_closure_classicalPoints_of_finite` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_classicalPoints_iff`: in positive dimension,
  membership of `unitGaussPoint n K` in `closure (classicalPoints n K)` is equivalent to infinitude
  of `K° ⧸ K°°`.

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
    ⟨(isContinuous_ofValuation_iff _).mpr <| by
        rw [unitGaussValuation_def]
        exact isContinuous_weightedGaussValuation (NormedField.isContinuous_valuation (K := K)),
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
    · rw [unitGaussValuation_def, weightedGaussValuation_le_iff]
      intro ν
      have hν : ν = Finsupp.single 0 (ν 0) := Finsupp.ext fun i ↦ by
        rw [Subsingleton.elim i 0, Finsupp.single_eq_same]
      have h := norm_coeff_mul_pow_le_closedDiscGaussValuation (R := K) zero_lt_one le_rfl f (ν 0)
      rw [one_pow, mul_one, ← hν] at h
      rw [NormedField.valuation_apply]
      exact_mod_cast h
    · refine NNReal.coe_le_coe.mp ?_
      refine closedDiscGaussValuation_le_of_forall_norm_coeff_le zero_lt_one le_rfl fun ν ↦ ?_
      have h := coeff_le_weightedGaussValuation (NormedField.isContinuous_valuation (K := K)) f ν
      rw [← unitGaussValuation_def, NormedField.valuation_apply] at h
      exact_mod_cast h
  refine Subtype.ext <| ext' fun f g ↦ ?_
  rw [unitGaussPoint_vle_iff, gaussPoint_vle_iff, hval f, hval g]

/-- **In dimension `0`, the unit Gauss point coincides with every classical point**, without any
residue-field assumption. -/
theorem unitGaussPoint_zero_eq_classicalPoint {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (x : spa (powerBoundedSubring K)) (a : Fin 0 → K)
    (ha : ∀ i, IsPowerBounded (a i)) :
    unitGaussPoint 0 K = classicalPoint x a ha :=
  @Subsingleton.elim _ subsingleton_closedPolydisc_zero _ _

/-- **In dimension `0`, the unit Gauss point lies in the closure of `classicalPoints 0 K`** over
every complete ultrametric normed field, with no residue-field infinitude hypothesis. -/
theorem unitGaussPoint_zero_mem_closure_classicalPoints {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] :
    unitGaussPoint 0 K ∈ closure (classicalPoints 0 K) := by
  rw [unitGaussPoint_zero_eq_classicalPoint (normSpaPoint K) Fin.elim0 fun i ↦ i.elim0]
  exact subset_closure (classicalPoint_mem_classicalPoints _ _ _)

end UnitGaussPoint

section ReductionAndClosure

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]

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
  obtain ⟨ν₀, hν₀⟩ :=
    exists_coeff_eq_weightedGaussValuation (NormedField.isContinuous_valuation (K := K)) (f := g)
  rw [← unitGaussValuation_def, NormedField.valuation_apply] at hν₀
  set c : K := MvPowerSeries.coeff ν₀ (g : MvPowerSeries (Fin n) K)
  have hc0 : c ≠ 0 := nnNorm_ne_zero_iff.mp (hν₀.trans_ne hgv0)
  set u := weightedC (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight c⁻¹
  have hu_val : unitGaussValuation n K u = (unitGaussValuation n K g)⁻¹ := by
    rw [← hν₀, unitGaussValuation_def, weightedGaussValuation_weightedC,
      NormedField.valuation_apply, nnNorm_inv]
  refine ⟨u, (IsUnit.mk0 c⁻¹ (inv_ne_zero hc0)).map _,
    by rw [map_mul, hu_val, mul_inv_cancel₀ hgv0], fun f hf ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
  rw [map_mul, hu_val]
  exact (mul_le_mul_of_nonneg_right ((unitGaussPoint_vle_iff n K t g).mp (hT t ht))
    zero_le).trans_eq (mul_inv_cancel₀ hgv0)

variable [CompleteSpace K]

/-- **Normalized rational-neighbourhood criterion at the unit Gauss point.** If `g ∈ K°⟨T⟩` and
every `f ∈ T` has unit Gauss valuation at most `1`, then `R(T/g)` contains `normClassicalPoint a ha`
whenever the residue tuple `ā` does not annihilate `polydiscReduction n K g`. -/
theorem normClassicalPoint_mem_rationalSubset_of_eval_polydiscReduction_ne_zero
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
    (normClassicalPoint a ha).val ∈ rationalSubset (powerBoundedSubring _) T g.val := by
  have hg1 : ‖evalAtHom a ha g.val‖ = 1 :=
    (norm_evalAtHom_eq_one_iff_eval_polydiscReduction_ne_zero a ha g).mpr hga
  rw [normClassicalPoint_mem_rationalSubset_iff]
  refine ⟨fun f hf ↦ ?_, norm_pos_iff.mp (by linarith)⟩
  rw [hg1, evalAtHom_def]
  refine (norm_weightedEvalHom_le continuousAt_id (C := 1) (fun r ↦ by simp)
    (fun i ↦ isPowerBounded_iff_norm_le_one.mp (ha i)) _ f).trans ?_
  rw [one_mul, MvPowerSeries.norm_eq_gaussNorm, coe_restrictedMvPowerSeriesGaussEquiv,
    ← coe_unitGaussValuation]
  exact_mod_cast hT f hf

open scoped Classical in
/-- Every basic open `Spv(K⟨T⟩)(T/g)` containing the unit Gauss point contains a canonical classical
point when the residue field `K° ⧸ K°°` is infinite. -/
theorem exists_normClassicalPoint_mem_basicOpenFinset
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hη : (unitGaussPoint n K).val ∈ basicOpenFinset T g) :
    ∃ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)),
      (normClassicalPoint a ha).val ∈ basicOpenFinset T g := by
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
  have hmem := normClassicalPoint_mem_rationalSubset_of_eval_polydiscReduction_ne_zero
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
a canonical classical point when `K° ⧸ K°°` is infinite. -/
theorem exists_normClassicalPoint_mem_rationalSubset
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hη : (unitGaussPoint n K).val ∈ rationalSubset (powerBoundedSubring _) T g) :
    ∃ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)),
      (normClassicalPoint a ha).val ∈ rationalSubset (powerBoundedSubring _) T g := by
  rw [rationalSubset_def, Set.mem_inter_iff] at hη
  obtain ⟨a, ha, hmem⟩ := exists_normClassicalPoint_mem_basicOpenFinset T g hη.right
  refine ⟨a, ha, ?_⟩
  rw [rationalSubset_def]
  exact ⟨closedPolydisc_def n K ▸ (normClassicalPoint a ha).property, hmem⟩

/-- **Gauss-point closure.** Over a complete ultrametric normed field `K` whose residue field
`K° ⧸ K°°` is infinite, the unit Gauss point of `closedPolydisc n K` lies in the closure of
`classicalPoints n K`. -/
theorem unitGaussPoint_mem_closure_classicalPoints
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)] :
    unitGaussPoint n K ∈ closure (classicalPoints n K) := by
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
  obtain ⟨a, ha, haMem⟩ := exists_normClassicalPoint_mem_rationalSubset T g hηR
  refine ⟨normClassicalPoint a ha, ?_, mem_classicalPoints_iff.mpr ⟨a, ha, rfl⟩⟩
  have hmem := hRV (a := e (normClassicalPoint a ha)) haMem
  simpa [Set.mem_preimage] using hmem

/-- Every closed subset of `closedPolydisc n K` containing `classicalPoints n K` contains the unit
Gauss point, when `K° ⧸ K°°` is infinite. -/
theorem unitGaussPoint_mem_of_isClosed_of_classicalPoints_subset
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    {Z : Set (closedPolydisc n K)} (hZ : IsClosed Z) (h : classicalPoints n K ⊆ Z) :
    unitGaussPoint n K ∈ Z :=
  hZ.closure_subset_iff.mpr h unitGaussPoint_mem_closure_classicalPoints

/-- **Gauss-point closure (existential form).** Over a complete ultrametric normed field `K` whose
residue field `K° ⧸ K°°` is infinite, the unit Gauss point exists on `closedPolydisc n K` and lies
in the closure of `classicalPoints n K`. -/
theorem gaussPoint_mem_closure_rationalPoints
    (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)] (n : ℕ) :
    ∃ η : closedPolydisc n K,
      IsUnitGaussPoint K n η ∧ η ∈ closure (classicalPoints n K) :=
  ⟨unitGaussPoint n K, isUnitGaussPoint_unitGaussPoint n K,
    unitGaussPoint_mem_closure_classicalPoints⟩

/-- **Chartwise Gauss-point closure.** If `f : closedPolydisc n K → X` is any continuous map (for
instance a polydisc affinoid chart into a rigid space) and `Z ⊆ X` is a closed subset containing
the image of `classicalPoints n K`, then `Z` contains `f (unitGaussPoint n K)`. -/
theorem map_unitGaussPoint_mem_of_isClosed
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    {X : Type*} [TopologicalSpace X] {f : closedPolydisc n K → X} (hf : Continuous f)
    {Z : Set X} (hZ : IsClosed Z) (h : ∀ p ∈ classicalPoints n K, f p ∈ Z) :
    f (unitGaussPoint n K) ∈ Z :=
  unitGaussPoint_mem_of_isClosed_of_classicalPoints_subset (hZ.preimage hf) h

/-- **In positive dimension with infinite residue field, `classicalPoints n K` is not a closed
subset of `closedPolydisc n K`**: its closure contains the nonclassical unit Gauss point. -/
theorem not_isClosed_classicalPoints
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)] [NeZero n] :
    ¬ IsClosed (classicalPoints n K) := fun hclosed ↦ by
  obtain ⟨a, ha, hmem⟩ := mem_classicalPoints_iff.mp
    (unitGaussPoint_mem_of_isClosed_of_classicalPoints_subset hclosed Set.Subset.rfl)
  rw [normClassicalPoint_def] at hmem
  exact unitGaussPoint_ne_classicalPoint (normSpaPoint K) a ha hmem.symm

end ReductionAndClosure

section FiniteResidue

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Failure of Gauss-point closure over finite residue fields.** When `K° ⧸ K°°` is finite of
cardinality `q` and `n ≥ 1`, the rational open `R({1} / (T₀^q - T₀))` separates
`unitGaussPoint n K` from `classicalPoints n K`. -/
theorem unitGaussPoint_notMem_closure_classicalPoints_of_finite
    [Finite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)] [NeZero n] :
    unitGaussPoint n K ∉ closure (classicalPoints n K) := by
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
  obtain ⟨_, hpU, hp⟩ := mem_closure_iff.mp hmem U hU_open hηU
  obtain ⟨a, ha, rfl⟩ := mem_classicalPoints_iff.mp hp
  rw [Set.mem_preimage, normClassicalPoint_mem_rationalSubset_iff] at hpU
  have hle := hpU.left 1 (Finset.mem_singleton_self 1)
  rw [map_one, norm_one] at hle
  -- Every power-bounded `a 0` satisfies `a 0 ^ q - a 0 ∈ K°°` by `FiniteField.pow_card`.
  let a₀ : powerBoundedSubring K := ⟨a 0, mem_powerBoundedSubring.mpr (ha 0)⟩
  have hnil : a₀ ^ q - a₀ ∈ topologicallyNilpotentIdeal K := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero]
    exact FiniteField.pow_card (Ideal.Quotient.mk (topologicallyNilpotentIdeal K) a₀)
  have hlt : ‖evalAtHom a ha g‖ < 1 := by
    have hlt' : ‖((a₀ ^ q - a₀ : powerBoundedSubring K) : K)‖ < 1 :=
      (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one).mp (mem_topologicallyNilpotentIdeal.mp hnil)
    simpa only [g, X₀, map_sub, map_pow, evalAtHom_weightedX, AddSubgroupClass.coe_sub,
      Subring.coe_pow] using hlt'
  exact hlt.not_ge hle

/-- **Characterization of Gauss-point closure in positive dimension.** Over a complete ultrametric
normed field `K` and for `n ≥ 1`, the unit Gauss point of `closedPolydisc n K` lies in the closure
of `classicalPoints n K` if and only if the residue field `K° ⧸ K°°` is infinite. -/
theorem unitGaussPoint_mem_closure_classicalPoints_iff [NeZero n] :
    unitGaussPoint n K ∈ closure (classicalPoints n K) ↔
      Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K) :=
  ⟨fun h ↦ not_finite_iff_infinite.mp fun _ ↦
      unitGaussPoint_notMem_closure_classicalPoints_of_finite h,
    fun _ ↦ unitGaussPoint_mem_closure_classicalPoints⟩

end FiniteResidue

end TauCeti.ValuationSpectrum
