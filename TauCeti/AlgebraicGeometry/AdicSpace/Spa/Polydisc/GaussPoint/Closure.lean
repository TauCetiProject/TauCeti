/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Eval
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint.Unit
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Reduction
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# Closure of rational points and the unit Gauss point

Let `K` be a complete ultrametric normed field and `D = closedPolydisc n K` the closed unit
polydisc `Spa (K⟨T₁, …, Tₙ⟩, K⟨T₁, …, Tₙ⟩°)` of dimension `n`, with unit Gauss point
`unitGaussPoint n K : closedPolydisc n K` defined in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint.Unit`, and classical locus
`classicalPoints n K : Set (closedPolydisc n K)` defined in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic`.

For any complete ultrametric normed field `K` (including trivially normed fields), every rational
neighbourhood `R(T/s)` of `unitGaussPoint n K` can be rescaled by a scalar unit dividing a
coefficient attaining `unitGaussValuation n K s` so that `unitGaussValuation n K s = 1` and
`unitGaussValuation n K f ≤ 1` for all `f ∈ T`. Then `s` has a nonzero polynomial reduction
`p = polydiscReduction n K s ∈ 𝓀[K][T₁, …, Tₙ]`, and every integral tuple `a ∈ 𝒪[K]ⁿ` whose
residue `ā` satisfies `p(ā) ≠ 0` gives a classical point `normClassicalPoint a ha ∈ R(T/s)`. When
the residue field `𝓀[K]` is infinite, `MvPolynomial.funext` provides such a tuple `ā`, which lifts
to `𝒪[K]ⁿ`. Since rational subsets form a basis of `closedPolydisc n K`, every open neighbourhood
of `unitGaussPoint n K` meets `classicalPoints n K`, so `unitGaussPoint n K` lies in its closure.

In particular, under those hypotheses (complete ultrametric normed field with infinite residue field
`𝓀[K]`), any closed subset of `closedPolydisc n K` (or of any topological space receiving a
continuous map from `closedPolydisc n K`) containing `classicalPoints n K` (or its image) also
contains `unitGaussPoint n K` (or its image), and for `n ≥ 1` `classicalPoints n K` is therefore not
closed.

Conversely, for any complete ultrametric normed field `K` whose residue field `𝓀[K]` is finite of
cardinality `q` and `n ≥ 1`, the rational open `R({1} / (T₀^q - T₀))` contains `unitGaussPoint n K`
(since the coefficient of `T₀` is `-1`) but no `K`-rational point (since `a₀^q - a₀` has zero
residue and hence norm strictly less than `1`). Thus, for every complete ultrametric normed field
`K` and `n ≥ 1`, `unitGaussPoint n K` lies in the closure of `classicalPoints n K` if and only if
the residue field `𝓀[K]` is infinite. Independently, in dimension `0`, membership in the closure
holds unconditionally for every complete ultrametric normed field `K`.

## Main results

* `TauCeti.ValuationSpectrum.unitGaussPoint_zero_mem_closure_classicalPoints`: in dimension `0`,
  `unitGaussPoint 0 K` lies in the closure of `classicalPoints 0 K` unconditionally for any
  complete ultrametric normed field `K`.
* `normClassicalPoint_mem_rationalSubset_of_eval_polydiscReduction_ne_zero`:
  for any complete ultrametric normed field `K`, normalized basic opens `R(T/g)` around
  `unitGaussPoint n K` contain `normClassicalPoint a ha` whenever `ā` does not vanish on
  `polydiscReduction n K g`.
* `TauCeti.ValuationSpectrum.exists_classicalPoint_mem_rationalSubset_of_unitGaussPoint_mem`:
  over a complete ultrametric normed field with infinite residue field `𝓀[K]`, every rational
  neighbourhood of `unitGaussPoint n K` meets `classicalPoints n K`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_classicalPoints` and
  `TauCeti.ValuationSpectrum.gaussPoint_mem_closure_rationalPoints`: over a complete ultrametric
  normed field with infinite residue field `𝓀[K]`, `unitGaussPoint n K` lies in the closure of
  `classicalPoints n K`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem`,
  `TauCeti.ValuationSpectrum.map_unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem`, and
  `TauCeti.ValuationSpectrum.not_isClosed_classicalPoints`: over a complete ultrametric normed
  field with infinite residue field `𝓀[K]`, closed subsets containing `classicalPoints n K` (or its
  image under a continuous map) contain the unit Gauss point (or its image), and for `n ≥ 1`
  `classicalPoints n K` is not closed.
* `TauCeti.ValuationSpectrum.unitGaussPoint_notMem_closure_classicalPoints_of_finite`: for any
  complete ultrametric normed field with finite residue field `𝓀[K]` and `n ≥ 1`,
  `unitGaussPoint n K` does not lie in the closure of `classicalPoints n K`.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_classicalPoints_iff`: over a complete
  ultrametric normed field, for `n ≥ 1`, `unitGaussPoint n K` lies in the closure of
  `classicalPoints n K` if and only if the residue field `𝓀[K]` is infinite.

## References

* S. Howe and C. Klevdal, *Admissible pairs and p-adic Hodge structures II: the bi-analytic
  Ax–Lindemann theorem*, arXiv:2308.11064v2, proof of Lemma 9.3.5, p. 60.
* B. Bhatt and D. Hansen, *The six functors for Zariski-constructible sheaves in rigid geometry*,
  arXiv:2101.09759v2, Example 2.1, p. 6.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

section DimensionZero

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **In dimension `0`, the unit Gauss point lies in the closure of `classicalPoints 0 K`
unconditionally**, without any hypothesis on the residue field. -/
theorem unitGaussPoint_zero_mem_closure_classicalPoints :
    unitGaussPoint 0 K ∈ closure (classicalPoints 0 K) :=
  subset_closure unitGaussPoint_zero_mem_classicalPoints

end DimensionZero

section Closure

open scoped NormedField

section InfiniteResidueField

open scoped Valued

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
    hg0 ((unitGaussPoint_vle_zero_iff n g).mpr ((unitGaussValuation_eq_zero_iff n K).mp h0))
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
  have hle : unitGaussValuation n K t ≤ unitGaussValuation n K g := by
    rw [← NNReal.coe_le_coe, coe_unitGaussValuation, coe_unitGaussValuation]
    exact (unitGaussPoint_vle_iff n t g).mp (hT t ht)
  exact (mul_le_mul_of_nonneg_right hle zero_le).trans_eq (mul_inv_cancel₀ hgv0)

variable [CompleteSpace K]

/-- **Normalized rational-neighbourhood criterion at the unit Gauss point.** Over any complete
ultrametric normed field `K`, if `g ∈ K°⟨T⟩` and every `f ∈ T` has unit Gauss valuation at most
`1`, then `R(T/g)` contains `normClassicalPoint a ha` whenever the residue tuple `ā` does not
annihilate `polydiscReduction n K g`. -/
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
/-- **Every rational neighbourhood of the unit Gauss point meets `classicalPoints n K`**, over a
complete ultrametric normed field `K` whose residue field `𝓀[K]` is infinite. Rescaling by a
coefficient attaining `unitGaussValuation n K s` reduces to `unitGaussValuation n K g = 1` and
`unitGaussValuation n K f ≤ 1` for all `f ∈ T`, and `MvPolynomial.funext` over the infinite residue
field `𝓀[K]` produces a non-root of `polydiscReduction n K g`. -/
theorem exists_classicalPoint_mem_rationalSubset_of_unitGaussPoint_mem
    [Infinite 𝓀[K]]
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (s : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hs : unitGaussPoint n K ∈ Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s) :
    ∃ p ∈ classicalPoints n K,
      p ∈ Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s := by
  rw [Set.mem_preimage, rationalSubset_def, Set.mem_inter_iff] at hs
  obtain ⟨u, hu_unit, hg_val, hT_val⟩ := exists_unit_mul_unitGaussValuation_eq_one T s hs.right
  let g : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K) :=
    ⟨s * u, (unitGaussValuation_le_one_iff_mem_weightedSubring n K).mp hg_val.le⟩
  have hred_ne : polydiscReduction n K g ≠ 0 := (polydiscReduction_ne_zero_iff g).mpr hg_val
  have hex : ∃ ā : Fin n → 𝓀[K], MvPolynomial.eval ā (polydiscReduction n K g) ≠ 0 := by
    by_contra! hall
    exact hred_ne (MvPolynomial.funext fun ā ↦ by simpa using hall ā)
  obtain ⟨ā, hā⟩ := hex
  choose b hb using fun i ↦ IsLocalRing.residue_surjective (ā i)
  have hba : ∀ i, IsPowerBounded (b i : K) := fun i ↦
    mem_powerBoundedSubring.mp ((powerBoundedSubring_eq_integer (K := K)).ge (b i).property)
  have hmem := normClassicalPoint_mem_rationalSubset_of_eval_polydiscReduction_ne_zero
    hT_val hba (by
      have heq : (fun i ↦ IsLocalRing.residue 𝒪[K]
          ⟨(b i : K), (powerBoundedSubring_eq_integer (K := K)).le
            (mem_powerBoundedSubring.mpr (hba i))⟩) = ā :=
        funext fun i ↦ hb i
      rwa [heq])
  have hrat : rationalSubset (powerBoundedSubring _) (T.image (· * u)) (s * u) =
      rationalSubset (powerBoundedSubring _) T s := by
    convert rationalSubset_image_mul_right (powerBoundedSubring _) T s u hu_unit
  rw [show g.val = s * u from rfl, hrat] at hmem
  exact ⟨normClassicalPoint (fun i ↦ (b i : K)) hba,
    normClassicalPoint_mem_classicalPoints _ hba, hmem⟩

/-- **Gauss-point closure.** Over a complete ultrametric normed field `K` whose residue field `𝓀[K]`
is infinite, the unit Gauss point of `closedPolydisc n K` lies in the closure of
`classicalPoints n K`. -/
theorem unitGaussPoint_mem_closure_classicalPoints [Infinite 𝓀[K]] :
    unitGaussPoint n K ∈ closure (classicalPoints n K) := by
  rw [mem_closure_iff]
  intro U hU hηU
  have : IsHuberRing K := IsHuberRing.of_normedField K
  have : IsHuberRing (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight) :=
    isHuberRing_weightedRestrictedSubring
  let e := Homeomorph.setCongr (closedPolydisc_def n K)
  have hbasis := isTopologicalBasis_spaRationalFamily (powerBoundedSubring
    (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight))
  have heU : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hηeU : e (unitGaussPoint n K) ∈ e.symm ⁻¹' U := by
    simpa only [Set.mem_preimage, e.symm_apply_apply] using hηU
  obtain ⟨V, hVmem, hηV, hVU⟩ := hbasis.exists_subset_of_mem_open hηeU heU
  obtain ⟨T, s, -, rfl⟩ := mem_spaRationalFamily_iff.mp hVmem
  have hmem_iff (p : closedPolydisc n K) :
      e p ∈ Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s ↔
        p ∈ Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s := by
    simp only [Set.mem_preimage, e, Homeomorph.setCongr_apply]
  obtain ⟨p, hp_cl, hpV⟩ :=
    exists_classicalPoint_mem_rationalSubset_of_unitGaussPoint_mem T s ((hmem_iff _).mp hηV)
  have hpU : p ∈ U := by
    simpa only [Set.mem_preimage, e.symm_apply_apply] using hVU ((hmem_iff _).mpr hpV)
  exact ⟨p, hpU, hp_cl⟩

/-- **Over a complete ultrametric normed field `K` with infinite residue field `𝓀[K]`, a closed
subset of `closedPolydisc n K` containing `classicalPoints n K` contains the unit Gauss point.** -/
theorem unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem
    [Infinite 𝓀[K]] {Z : Set (closedPolydisc n K)} (hZ : IsClosed Z)
    (hmem : ∀ p ∈ classicalPoints n K, p ∈ Z) :
    unitGaussPoint n K ∈ Z :=
  hZ.closure_subset_iff.mpr (fun _ hp ↦ hmem _ hp) unitGaussPoint_mem_closure_classicalPoints

/-- **Closed-set propagation along a continuous map from a closed polydisc.** Over a complete
ultrametric normed field `K` with infinite residue field `𝓀[K]`, if `φ` maps `closedPolydisc n K`
continuously into a topological space `X` (for instance an affinoid open chart of an adic space)
and a closed subset `Z ⊆ X` contains `φ p` for all `p ∈ classicalPoints n K`, then `Z` contains
`φ (unitGaussPoint n K)`. -/
theorem map_unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem
    [Infinite 𝓀[K]] {X : Type*} [TopologicalSpace X]
    {φ : closedPolydisc n K → X} (hφ : Continuous φ)
    {Z : Set X} (hZ : IsClosed Z)
    (hmem : ∀ p ∈ classicalPoints n K, φ p ∈ Z) :
    φ (unitGaussPoint n K) ∈ Z :=
  unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem (hZ.preimage hφ) hmem

/-- **In positive dimension with infinite residue field `𝓀[K]`, `classicalPoints n K` is not a
closed subset of `closedPolydisc n K`**: its closure contains the nonclassical unit Gauss point. -/
theorem not_isClosed_classicalPoints [Infinite 𝓀[K]] [NeZero n] :
    ¬ IsClosed (classicalPoints n K) := fun hclosed ↦
  unitGaussPoint_notMem_classicalPoints
    (closure_minimal Set.Subset.rfl hclosed unitGaussPoint_mem_closure_classicalPoints)

end InfiniteResidueField

section FiniteResidueField

open scoped Valued

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Failure of Gauss-point closure over finite residue fields.** Over any complete ultrametric
normed field `K` whose residue field `𝓀[K]` is finite of cardinality `q` and `n ≥ 1`, the rational
open `R({1} / (T₀^q - T₀))` is a neighbourhood of `unitGaussPoint n K` disjoint from
`classicalPoints n K`, because `a₀^q - a₀` reduces to `0` in the residue field and therefore has
norm strictly less than `1`. -/
theorem unitGaussPoint_notMem_closure_classicalPoints_of_finite
    [Finite 𝓀[K]] [NeZero n] :
    unitGaussPoint n K ∉ closure (classicalPoints n K) := by
  let : Fintype 𝓀[K] := Fintype.ofFinite 𝓀[K]
  set q : ℕ := Fintype.card 𝓀[K]
  set T₀ : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedX _ isWeightFamily_one_weight 0
  set s := T₀ ^ q - T₀
  set U : Set (closedPolydisc n K) :=
    Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) {1} s
  have hUopen : IsOpen U := isOpen_val_preimage_rationalSubset_closedPolydisc {1} s
  have hs_norm_ge : 1 ≤ ‖restrictedMvPowerSeriesGaussEquiv s‖ :=
    one_le_norm_weightedX_pow_sub_weightedX 0 Fintype.one_lt_card
  have hηU : unitGaussPoint n K ∈ U := by
    rw [Set.mem_preimage, mem_rationalSubset_iff, ← closedPolydisc_def]
    refine ⟨(unitGaussPoint n K).property, ?_, ?_⟩
    · intro f hf
      rw [Finset.mem_singleton.mp hf, unitGaussPoint_vle_iff_norm, map_one, norm_one]
      exact hs_norm_ge
    · rw [unitGaussPoint_vle_zero_iff]
      intro hs0
      have : (1 : ℝ) ≤ 0 := by simpa [hs0] using hs_norm_ge
      linarith
  intro hcl
  obtain ⟨p, hpU, hp_cl⟩ := mem_closure_iff.mp hcl U hUopen hηU
  obtain ⟨a, ha, rfl⟩ := mem_classicalPoints_iff.mp hp_cl
  rw [Set.mem_preimage, normClassicalPoint_mem_rationalSubset_iff] at hpU
  have h1le := hpU.1 1 (Finset.mem_singleton_self 1)
  rw [map_one, norm_one] at h1le
  -- Every `a₀ ∈ 𝒪[K]` satisfies `a₀^q - a₀ ∈ 𝓂[K]`, so `‖a₀^q - a₀‖ < 1`.
  have heval_s : evalAtHom a ha s = a 0 ^ q - a 0 := by simp [s, T₀]
  let b : 𝒪[K] := powerBoundedSubringEquivInteger ⟨a 0, mem_powerBoundedSubring.mpr (ha 0)⟩
  have hres : IsLocalRing.residue 𝒪[K] (b ^ q - b) = 0 := by
    rw [map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hlt : ‖evalAtHom a ha s‖ < 1 := by
    simpa only [heval_s, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, b,
      coe_powerBoundedSubringEquivInteger] using
      Valued.integer.residue_eq_zero_iff_norm_lt_one.mp hres
  exact hlt.not_ge h1le

end FiniteResidueField

section EquivalenceAndHeadline

open scoped Valued

/-- **Characterization of Gauss-point closure in positive dimension.** Over a complete ultrametric
normed field `K` and for `n ≥ 1`, the unit Gauss point of `closedPolydisc n K` lies in the closure
of `classicalPoints n K` if and only if the residue field `𝓀[K]` is infinite. -/
theorem unitGaussPoint_mem_closure_classicalPoints_iff {n : ℕ} [NeZero n]
    {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    unitGaussPoint n K ∈ closure (classicalPoints n K) ↔ Infinite 𝓀[K] :=
  ⟨fun h ↦ not_finite_iff_infinite.mp fun _ ↦
      unitGaussPoint_notMem_closure_classicalPoints_of_finite h,
    fun _ ↦ unitGaussPoint_mem_closure_classicalPoints⟩

/-- **Gauss-point closure.** Over a complete ultrametric normed field `K` whose residue field `𝓀[K]`
is infinite, the unit Gauss point exists on the closed unit polydisc of every dimension `n` and
lies in the closure of `classicalPoints n K`. -/
theorem gaussPoint_mem_closure_rationalPoints
    (K : Type*) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Infinite 𝓀[K]] (n : ℕ) :
    ∃ η : closedPolydisc n K,
      IsUnitGaussPoint K n η ∧ η ∈ closure (classicalPoints n K) :=
  ⟨unitGaussPoint n K, isUnitGaussPoint_unitGaussPoint n K,
    unitGaussPoint_mem_closure_classicalPoints⟩

end EquivalenceAndHeadline

end Closure

end TauCeti.ValuationSpectrum
