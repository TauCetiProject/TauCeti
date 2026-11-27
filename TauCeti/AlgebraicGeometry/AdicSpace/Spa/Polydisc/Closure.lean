/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Reduction
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.UnitGaussPoint

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis

/-!
# Closure of the classical locus of a closed polydisc

Let `K` be a complete ultrametric normed field and `D = closedPolydisc n K` the closed unit
polydisc of dimension `n` over `K`. This file determines when the unit Gauss point
`TauCeti.ValuationSpectrum.unitGaussPoint n K` lies in the closure of the classical locus
`TauCeti.ValuationSpectrum.classicalPoints n K`.

In dimension `0`, `unitGaussPoint 0 K` already belongs to `classicalPoints 0 K` and hence to its
closure without any residue-field assumption. In positive dimension, we use coefficientwise residue
reduction `TauCeti.Huber.polydiscReduction n K` into polynomials over the residue field `𝓀[K]`:
* Given any basic open `Spv(K⟨T⟩)(T/g)` containing `unitGaussPoint n K`, scaling by the inverse of
  a coefficient attaining the Gauss norm of `g` normalizes `g` to unit Gauss norm and every
  numerator to Gauss norm at most `1`. Every `a ∈ (K°)ⁿ` whose residue avoids the vanishing locus of
  the reduced denominator then yields `normClassicalPoint a ha ∈ R(T/g)`.
* When `𝓀[K]` is infinite, `MvPolynomial.funext` provides such a tuple `a`, so
  `unitGaussPoint n K ∈ closure (classicalPoints n K)` and `classicalPoints n K` is not closed in
  positive dimension.
* Conversely, when `𝓀[K]` is finite of cardinality `q` and `n ≥ 1`, the rational open
  `R({1} / (T₀^q - T₀))` separates `unitGaussPoint n K` from `classicalPoints n K` by
  `FiniteField.pow_card`.

## Main results

* `TauCeti.ValuationSpectrum.unitGaussPoint_zero_mem_closure_classicalPoints`: in dimension `0`,
  `unitGaussPoint 0 K ∈ closure (classicalPoints 0 K)`.
* `normClassicalPoint_mem_rationalSubset_of_eval_polydiscReduction_ne_zero`:
  normalized rational neighbourhoods of `unitGaussPoint n K` contain every canonical classical
  point whose reduction does not kill the reduced denominator.
* `TauCeti.ValuationSpectrum.exists_normClassicalPoint_mem_basicOpenFinset` and
  `TauCeti.ValuationSpectrum.exists_normClassicalPoint_mem_rationalSubset`: every rational
  neighbourhood of `unitGaussPoint n K` meets `classicalPoints n K` when `𝓀[K]` is infinite.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_classicalPoints` and
  `TauCeti.ValuationSpectrum.gaussPoint_mem_closure_rationalPoints`: over a complete ultrametric
  normed field with infinite residue field, the unit Gauss point lies in the closure of
  `classicalPoints n K`.
* `TauCeti.ValuationSpectrum.not_isClosed_classicalPoints`: in positive dimension with infinite
  residue field, `classicalPoints n K` is not a closed subset of the polydisc.
* `TauCeti.ValuationSpectrum.unitGaussPoint_notMem_closure_classicalPoints_of_finite` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_classicalPoints_iff`: in positive dimension,
  membership of `unitGaussPoint n K` in `closure (classicalPoints n K)` is equivalent to infinitude
  of `𝓀[K]`.

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
open scoped NNReal NormedField Valued

section Closure

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **In dimension `0`, the unit Gauss point lies in the closure of `classicalPoints 0 K`** over
every complete ultrametric normed field, with no residue-field infinitude hypothesis. -/
theorem unitGaussPoint_zero_mem_closure_classicalPoints [CompleteSpace K] :
    unitGaussPoint 0 K ∈ closure (classicalPoints 0 K) :=
  subset_closure unitGaussPoint_zero_mem_classicalPoints

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
    rw [← hν₀, unitGaussValuation_weightedC, nnNorm_inv]
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
      (fun i ↦ IsLocalRing.residue 𝒪[K]
        ⟨a i, (powerBoundedSubring_eq_integer (K := K)).le
          (mem_powerBoundedSubring.mpr (ha i))⟩)
      (polydiscReduction n K g) ≠ 0) :
    (normClassicalPoint a ha).val ∈ rationalSubset (powerBoundedSubring _) T g.val := by
  have hg1 : ‖evalAtHom a ha g.val‖ = 1 :=
    (norm_evalAtHom_eq_one_iff_eval_polydiscReduction_ne_zero a ha g).mpr hga
  rw [normClassicalPoint_mem_rationalSubset_iff]
  refine ⟨fun f hf ↦ ?_, norm_pos_iff.mp (by linarith)⟩
  rw [hg1]
  let f' : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K) :=
    ⟨f, (unitGaussValuation_le_one_iff_mem_weightedSubring n K).mp (hT f hf)⟩
  exact isPowerBounded_iff_norm_le_one.mp
    (mem_powerBoundedSubring.mp (evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha f'))

open scoped Classical in
/-- Every basic open `Spv(K⟨T⟩)(T/g)` containing the unit Gauss point contains a canonical classical
point when the residue field `𝓀[K]` is infinite. -/
theorem exists_normClassicalPoint_mem_basicOpenFinset [Infinite 𝓀[K]]
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
  have hex : ∃ ā : Fin n → 𝓀[K], MvPolynomial.eval ā (polydiscReduction n K g') ≠ 0 := by
    by_contra! hall
    exact hred_ne (MvPolynomial.funext fun ā ↦ by simpa using hall ā)
  obtain ⟨ā, hā⟩ := hex
  choose b hb using fun i ↦ IsLocalRing.residue_surjective (ā i)
  have hba : ∀ i, IsPowerBounded (b i : K) := fun i ↦
    mem_powerBoundedSubring.mp ((powerBoundedSubring_eq_integer (K := K)).ge (b i).property)
  refine ⟨fun i ↦ (b i : K), hba, ?_⟩
  have hmem := normClassicalPoint_mem_rationalSubset_of_eval_polydiscReduction_ne_zero
    (T := T.image (· * u)) (g := g') hT'_val hba
    (by
      have heq : (fun i ↦ IsLocalRing.residue 𝒪[K]
          ⟨(b i : K), (powerBoundedSubring_eq_integer (K := K)).le
            (mem_powerBoundedSubring.mpr (hba i))⟩) = ā :=
        funext fun i ↦ hb i
      rwa [heq])
  dsimp only [g'] at hmem
  rw [rationalSubset_def, Set.mem_inter_iff] at hmem
  rw [← basicOpenFinset_image_mul_right T g u hu]
  convert hmem.right

/-- Every rational subset `R(T/g)` of `closedPolydisc n K` containing the unit Gauss point contains
a canonical classical point when `𝓀[K]` is infinite. -/
theorem exists_normClassicalPoint_mem_rationalSubset [Infinite 𝓀[K]]
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

/-- **Gauss-point closure.** Over a complete ultrametric normed field `K` whose residue field `𝓀[K]`
is infinite, the unit Gauss point of `closedPolydisc n K` lies in the closure of
`classicalPoints n K`. -/
theorem unitGaussPoint_mem_closure_classicalPoints [Infinite 𝓀[K]] :
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
  refine ⟨normClassicalPoint a ha, ?_, normClassicalPoint_mem_classicalPoints a ha⟩
  have hmem := hRV (a := e (normClassicalPoint a ha)) haMem
  simpa [Set.mem_preimage] using hmem

/-- **Gauss-point closure (existential form).** Over a complete ultrametric normed field `K` whose
residue field `K° ⧸ K°°` is infinite, the unit Gauss point exists on `closedPolydisc n K` and
lies in the closure of the evaluation points `classicalPoint x` at tuples of power-bounded
elements of `K`. -/
theorem gaussPoint_mem_closure_rationalPoints
    (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Infinite (powerBoundedSubring K ⧸ topologicallyNilpotentIdeal K)]
    (n : ℕ) (x : spa (powerBoundedSubring K)) :
    ∃ η : closedPolydisc n K,
      IsUnitGaussPoint K n η ∧
      η ∈ closure (Set.range fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property) :=
  ⟨unitGaussPoint n K, isUnitGaussPoint_unitGaussPoint n K, by
    have : Infinite 𝓀[K] :=
      canonicalReductionRingEquivResidueField.toEquiv.infinite_iff.mp ‹_›
    rw [range_classicalPoint_eq_classicalPoints]
    exact unitGaussPoint_mem_closure_classicalPoints⟩

/-- **In positive dimension with infinite residue field, `classicalPoints n K` is not a closed
subset of `closedPolydisc n K`**: its closure contains the nonclassical unit Gauss point. -/
theorem not_isClosed_classicalPoints [Infinite 𝓀[K]] [NeZero n] :
    ¬ IsClosed (classicalPoints n K) := fun hclosed ↦
  unitGaussPoint_notMem_classicalPoints
    (closure_minimal Set.Subset.rfl hclosed unitGaussPoint_mem_closure_classicalPoints)

end Closure

section FiniteResidue

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Failure of Gauss-point closure over finite residue fields.** When `𝓀[K]` is finite of
cardinality `q` and `n ≥ 1`, the rational open `R({1} / (T₀^q - T₀))` separates
`unitGaussPoint n K` from `classicalPoints n K`. -/
theorem unitGaussPoint_notMem_closure_classicalPoints_of_finite [Finite 𝓀[K]] [NeZero n] :
    unitGaussPoint n K ∉ closure (classicalPoints n K) := by
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  set q := Fintype.card 𝓀[K]
  set X₀ : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedX _ isWeightFamily_one_weight 0
  set g := X₀ ^ q - X₀
  set U : Set (closedPolydisc n K) := Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) {1} g
  have hg_ge : 1 ≤ unitGaussValuation n K g := by
    have hcoeff := coeff_le_weightedGaussValuation (NormedField.isContinuous_valuation (K := K))
      g (Finsupp.single 0 q)
    have hne : Finsupp.single (0 : Fin n) q ≠ Finsupp.single 0 1 :=
      (Finsupp.single_injective (0 : Fin n)).ne Fintype.one_lt_card.ne'
    have hg_coeff :
        MvPowerSeries.coeff (Finsupp.single 0 q) (g : MvPowerSeries (Fin n) K) = 1 := by
      simp [g, X₀, MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X, hne]
    rw [hg_coeff, map_one, ← unitGaussValuation_def] at hcoeff
    exact hcoeff
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
    rw [← Ideal.Quotient.eq_zero_iff_mem,
      ← map_eq_zero_iff _ canonicalReductionRingEquivResidueField.injective]
    simp only [map_sub, map_pow, sub_eq_zero]
    exact FiniteField.pow_card _
  have hlt : ‖evalAtHom a ha g‖ < 1 := by
    have hlt' : ‖((a₀ ^ q - a₀ : powerBoundedSubring K) : K)‖ < 1 :=
      (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one).mp (mem_topologicallyNilpotentIdeal.mp hnil)
    simpa only [g, X₀, map_sub, map_pow, evalAtHom_weightedX, AddSubgroupClass.coe_sub,
      Subring.coe_pow] using hlt'
  exact hlt.not_ge hle

/-- **Characterization of Gauss-point closure in positive dimension.** Over a complete ultrametric
normed field `K` and for `n ≥ 1`, the unit Gauss point of `closedPolydisc n K` lies in the closure
of `classicalPoints n K` if and only if the residue field `𝓀[K]` is infinite. -/
theorem unitGaussPoint_mem_closure_classicalPoints_iff [NeZero n] :
    unitGaussPoint n K ∈ closure (classicalPoints n K) ↔ Infinite 𝓀[K] :=
  ⟨fun h ↦ not_finite_iff_infinite.mp fun _ ↦
      unitGaussPoint_notMem_closure_classicalPoints_of_finite h,
    fun _ ↦ unitGaussPoint_mem_closure_classicalPoints⟩

end FiniteResidue

end TauCeti.ValuationSpectrum
