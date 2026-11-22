/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Eval
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint.Unit
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis

/-!
# Closure of rational points and the unit Gauss point

Let `K` be a complete ultrametric normed field and `D = closedPolydisc n K` the closed unit
polydisc `Spa (K⟨T₁, …, Tₙ⟩, K⟨T₁, …, Tₙ⟩°)` of dimension `n`, with unit Gauss point
`unitGaussPoint n K : closedPolydisc n K` defined in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.GaussPoint.Unit`.

When `K` is nontrivially normed, every rational neighbourhood `R(T/s)` of `unitGaussPoint n K` can
be rescaled by a scalar unit (`TauCeti.Huber.exists_units_norm_mul_weightedC_eq_one`) so that
`‖s‖ = 1` and `‖f‖ ≤ 1` for all `f ∈ T`. Then `s` has a nonzero polynomial reduction
`p ∈ 𝓀[K][T₁, …, Tₙ]`, and every integral tuple `a ∈ 𝒪[K]ⁿ` whose residue `ā` satisfies
`p(ā) ≠ 0` gives a classical point `classicalPoint x a ha ∈ R(T/s)`. When the canonical reduction
`K° / K°° ≃+* 𝓀[K]` is infinite, `MvPolynomial.funext` provides such a tuple `ā`, which lifts to
`𝒪[K]ⁿ`. Since rational subsets form a basis of `closedPolydisc n K`, every open neighbourhood of
`unitGaussPoint n K` meets the `K`-rational points, so `unitGaussPoint n K` lies in their closure.

In particular, any closed subset of `closedPolydisc n K` (or of any topological space receiving a
continuous map from `closedPolydisc n K`) containing the images of all `K`-rational points also
contains the image of `unitGaussPoint n K`. For `n ≥ 1`, the rational points are therefore not
closed when `K° / K°°` is infinite.

Conversely, when `K° / K°° ≃+* 𝓀[K]` is finite of cardinality `q` and `n ≥ 1`, the rational open
`R({1} / (T₀^q - T₀))` contains `unitGaussPoint n K` (since the coefficient of `T₀` is `-1`) but
no `K`-rational point (since `a₀^q - a₀` has zero residue and hence norm strictly less than `1`).
Thus for `n ≥ 1`, `unitGaussPoint n K` lies in the closure of the `K`-rational points if and only
if the residue field `K° / K°°` is infinite. In dimension `0`, membership in the closure holds
unconditionally.

## Main results

* `TauCeti.ValuationSpectrum.unitGaussPoint_zero_mem_closure_range_classicalPoint`: in dimension
  `0`, `unitGaussPoint 0 K` lies in the closure of the `K`-rational points unconditionally.
* `TauCeti.ValuationSpectrum.classicalPoint_mem_rationalSubset_of_eval_restrictedReduction_ne_zero`:
  normalized rational neighbourhoods of `unitGaussPoint n K` contain every classical point whose
  reduction does not vanish on the reduced denominator.
* `TauCeti.ValuationSpectrum.exists_classicalPoint_mem_rationalSubset_of_unitGaussPoint_mem`:
  over a complete nontrivially normed field with infinite residue field, every rational
  neighbourhood of `unitGaussPoint n K` contains a `K`-rational classical point.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_range_classicalPoint` and
  `TauCeti.ValuationSpectrum.gaussPoint_mem_closure_rationalPoints`: `unitGaussPoint n K` lies in
  the closure of the `K`-rational points.
* `TauCeti.ValuationSpectrum.unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem` and
  `TauCeti.ValuationSpectrum.map_unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem`:
  closed subsets containing the `K`-rational points (or their images under a continuous map) contain
  the unit Gauss point (or its image).
* `TauCeti.ValuationSpectrum.unitGaussPoint_notMem_closure_range_classicalPoint_of_finite` and
  `TauCeti.ValuationSpectrum.unitGaussPoint_mem_closure_range_classicalPoint_iff`: for `n ≥ 1`,
  `unitGaussPoint n K` lies in the closure of the `K`-rational points if and only if the residue
  field is infinite.

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

section DimensionZero

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **In dimension `0`, the unit Gauss point lies in the closure of the `K`-rational points
unconditionally**, without any hypothesis on the residue field. -/
theorem unitGaussPoint_zero_mem_closure_range_classicalPoint
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint 0 K ∈ closure (Set.range
      (fun a : {a : Fin 0 → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property)) :=
  subset_closure ⟨⟨Fin.elim0, fun i ↦ i.elim0⟩, (unitGaussPoint_zero_eq_classicalPoint x).symm⟩

end DimensionZero

section Closure

open scoped NormedField

section InfiniteResidueField

variable {n : ℕ} {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Normalized rational-neighbourhood containment.** Let `R(T/g)` be a rational subset of
`closedPolydisc n K` whose denominator `g` has unit Gauss norm `1` and whose numerators `f ∈ T`
all have unit Gauss norm at most `1`. Then every integral tuple `a ∈ 𝒪[K]ⁿ` whose residue does not
annihilate the polynomial reduction of `g` in `𝓀[K][T₁, …, Tₙ]` produces a classical point lying in
`R(T/g)`. -/
theorem classicalPoint_mem_rationalSubset_of_eval_restrictedReduction_ne_zero
    (x : spa (powerBoundedSubring K))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (g : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hg : ‖restrictedMvPowerSeriesGaussEquiv g‖ = 1)
    (hT : ∀ f ∈ T, ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ 1)
    (a : Fin n → Valued.integer K)
    (heval : MvPolynomial.eval (fun i ↦ IsLocalRing.residue (Valued.integer K) (a i))
      (TauCeti.MvPowerSeries.restrictedReduction
        ⟨restrictedMvPowerSeriesGaussEquiv g, Subring.mem_unitClosedBall.mpr hg.le⟩) ≠ 0) :
    classicalPoint x (fun i ↦ (a i : K))
        (fun i ↦ isPowerBounded_iff_norm_le_one.mpr (Valued.integer.mem_iff.mp (a i).property)) ∈
      Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T g := by
  set a' : Fin n → K := fun i ↦ (a i : K)
  set ha' : ∀ i, IsPowerBounded (a' i) :=
    fun i ↦ isPowerBounded_iff_norm_le_one.mpr (Valued.integer.mem_iff.mp (a i).property)
  have ha_norm : ∀ i, ‖a' i‖ ≤ 1 := fun i ↦ Valued.integer.mem_iff.mp (a i).property
  set gball : Subring.unitClosedBall
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :=
    ⟨restrictedMvPowerSeriesGaussEquiv g, Subring.mem_unitClosedBall.mpr hg.le⟩
  have hg_not_lt : ¬ ‖evalAtHom a' ha' g‖ < 1 := by
    rw [evalAtHom_eq_restrictedEval₂ a' ha' ha_norm g]
    have hiff := TauCeti.MvPowerSeries.norm_restrictedEval₂_lt_one_iff (RingHom.id K)
      (fun _ ↦ le_rfl) a gball
    simp only [RingHom.integerRestrict_id, IsLocalRing.ResidueField.map_id,
      MvPolynomial.eval₂_id] at hiff
    exact hiff.not.mpr heval
  have hg_ge : 1 ≤ ‖evalAtHom a' ha' g‖ := le_of_not_gt hg_not_lt
  rw [Set.mem_preimage, mem_rationalSubset_iff, ← closedPolydisc_def]
  refine ⟨(classicalPoint x a' ha').property, fun f hf ↦ ?_, ?_⟩
  · rw [classicalPoint_vle, vle_iff_norm_le_of_mem_spa x.property]
    exact (norm_evalAtHom_le a' ha' ha_norm f).trans ((hT f hf).trans hg_ge)
  · rw [classicalPoint_vle, map_zero, vle_iff_norm_le_of_mem_spa x.property, norm_zero, not_le]
    exact zero_lt_one.trans_le hg_ge

open scoped Classical in
/-- **Every rational neighbourhood of the unit Gauss point contains a `K`-rational point**, when
the canonical reduction `K° / K°°` is infinite. Rescaling by a coefficient attaining the Gauss norm
of `s` reduces to `‖s‖ = 1` and `‖f‖ ≤ 1` for all `f ∈ T`, and `MvPolynomial.funext` over the
infinite residue field `𝓀[K]` produces a non-root of the nonzero polynomial reduction. -/
theorem exists_classicalPoint_mem_rationalSubset_of_unitGaussPoint_mem
    [Infinite (CanonicalReduction K)] (x : spa (powerBoundedSubring K))
    (T : Finset (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight))
    (s : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (hs : unitGaussPoint n K ∈ Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s) :
    ∃ a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)},
      classicalPoint x a.val a.property ∈
        Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s := by
  rw [Set.mem_preimage, mem_rationalSubset_iff] at hs
  obtain ⟨-, hTle, hs_ne⟩ := hs
  have hs0 : s ≠ 0 := fun h ↦ hs_ne (by simp [h])
  obtain ⟨c, hg_norm, hscale⟩ := exists_units_norm_mul_weightedC_eq_one hs0
  set u : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight :=
    weightedC _ isWeightFamily_one_weight (c : K)
  have hu_unit : IsUnit u := c.isUnit.map _
  set g := s * u
  set T' := T.image fun t ↦ t * u
  have hT'_norm : ∀ f ∈ T', ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ 1 := by
    rintro _ hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    have hle := (unitGaussPoint_vle_iff_norm n t s).mp (hTle t ht)
    rw [hscale t]
    exact div_le_one_of_le₀ hle (norm_nonneg _)
  -- The reduced denominator is nonzero; over the infinite residue field it is nonvanishing.
  set gball : Subring.unitClosedBall
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) :=
    ⟨restrictedMvPowerSeriesGaussEquiv g, Subring.mem_unitClosedBall.mpr hg_norm.le⟩
  have hred_ne : TauCeti.MvPowerSeries.restrictedReduction gball ≠ 0 :=
    TauCeti.MvPowerSeries.restrictedReduction_ne_zero_iff.mpr hg_norm
  have : Infinite (Valued.ResidueField K) :=
    (canonicalReductionRingEquivResidueField (K := K)).toEquiv.infinite_iff.mp ‹_›
  have hex : ∃ ā : Fin n → Valued.ResidueField K,
      MvPolynomial.eval ā (TauCeti.MvPowerSeries.restrictedReduction gball) ≠ 0 := by
    by_contra! hall
    exact hred_ne (MvPolynomial.funext fun ā ↦ by simpa using hall ā)
  obtain ⟨ā, hā⟩ := hex
  choose a ha_res using fun i ↦ IsLocalRing.residue_surjective (ā i)
  have hmem := classicalPoint_mem_rationalSubset_of_eval_restrictedReduction_ne_zero x T' g
    hg_norm hT'_norm a (by simpa [ha_res] using hā)
  have hrat : rationalSubset (powerBoundedSubring _) T' g =
      rationalSubset (powerBoundedSubring _) T s := by
    convert rationalSubset_image_mul_right (powerBoundedSubring _) T s u hu_unit
  rw [hrat] at hmem
  exact ⟨⟨fun i ↦ (a i : K),
    fun i ↦ isPowerBounded_iff_norm_le_one.mpr (Valued.integer.mem_iff.mp (a i).property)⟩, hmem⟩

/-- **Gauss-point closure.** Over a complete nontrivially normed ultrametric field `K` whose
canonical reduction `K° / K°°` is infinite, the unit Gauss point `unitGaussPoint n K` lies in the
closure of the `K`-rational evaluation points of `closedPolydisc n K`. -/
theorem unitGaussPoint_mem_closure_range_classicalPoint [Infinite (CanonicalReduction K)]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈ closure (Set.range
      (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property)) := by
  rw [mem_closure_iff]
  intro U hU hηU
  have : IsHuberRing (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
      isWeightFamily_one_weight) :=
    isHuberRing_weightedRestrictedSubring
  let e := Homeomorph.setCongr (closedPolydisc_def n K)
  have hbasis := isTopologicalBasis_spaRationalFamily (powerBoundedSubring
    (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight))
  have heU : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hηeU : e (unitGaussPoint n K) ∈ e.symm ⁻¹' U := by simpa [e] using hηU
  obtain ⟨V, hVmem, hηV, hVU⟩ := hbasis.exists_subset_of_mem_open hηeU heU
  obtain ⟨T, s, -, rfl⟩ := mem_spaRationalFamily_iff.mp hVmem
  have hηV' : unitGaussPoint n K ∈ Subtype.val ⁻¹' rationalSubset (powerBoundedSubring _) T s := by
    simpa only [Set.mem_preimage, e, Homeomorph.setCongr, Homeomorph.homeomorph_mk_coe,
      Set.equivOfEq_apply] using hηV
  obtain ⟨a, ha⟩ := exists_classicalPoint_mem_rationalSubset_of_unitGaussPoint_mem x T s hηV'
  have haU : classicalPoint x a.val a.property ∈ U := by
    have : e (classicalPoint x a.val a.property) ∈ e.symm ⁻¹' U := hVU ha
    simpa [e] using this
  exact ⟨classicalPoint x a.val a.property, haU, ⟨a, rfl⟩⟩

/-- **A closed subset of `closedPolydisc n K` containing all `K`-rational points contains the unit
Gauss point**, when the residue field `K° / K°°` is infinite. -/
theorem unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem
    [Infinite (CanonicalReduction K)] (x : spa (powerBoundedSubring K))
    {Z : Set (closedPolydisc n K)} (hZ : IsClosed Z)
    (hmem : ∀ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)), classicalPoint x a ha ∈ Z) :
    unitGaussPoint n K ∈ Z :=
  hZ.closure_subset_iff.mpr
    (Set.range_subset_iff.mpr fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      hmem a.val a.property)
    (unitGaussPoint_mem_closure_range_classicalPoint x)

/-- **Closed-set propagation along a continuous map from a closed polydisc.** If `φ` maps
`closedPolydisc n K` continuously into a topological space `X` (for instance an affinoid open
chart of an adic space) and a closed subset `Z ⊆ X` contains `φ (classicalPoint x a ha)` for all
`a ∈ (K°)ⁿ`, then `Z` contains `φ (unitGaussPoint n K)`. -/
theorem map_unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem
    [Infinite (CanonicalReduction K)] {X : Type*} [TopologicalSpace X]
    {φ : closedPolydisc n K → X} (hφ : Continuous φ) (x : spa (powerBoundedSubring K))
    {Z : Set X} (hZ : IsClosed Z)
    (hmem : ∀ (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i)), φ (classicalPoint x a ha) ∈ Z) :
    φ (unitGaussPoint n K) ∈ Z :=
  unitGaussPoint_mem_of_isClosed_of_forall_classicalPoint_mem x (hZ.preimage hφ) hmem

/-- **In positive dimension over a field with infinite residue field, the `K`-rational points of a
closed polydisc do not form a closed subset**: their closure contains the non-classical unit Gauss
point. -/
theorem not_isClosed_range_classicalPoint [Infinite (CanonicalReduction K)] [NeZero n]
    (x : spa (powerBoundedSubring K)) :
    ¬ IsClosed (Set.range (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.val a.property)) := fun hclosed ↦ by
  obtain ⟨a, ha⟩ := hclosed.closure_eq ▸ unitGaussPoint_mem_closure_range_classicalPoint (n := n) x
  exact unitGaussPoint_ne_classicalPoint x a.val a.property ha.symm

end InfiniteResidueField

section FiniteResidueField

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Failure of Gauss-point closure for finite residue fields.** When `K° / K°°` is finite of
cardinality `q` and `n ≥ 1`, the rational open `R({1} / (T₀^q - T₀))` is a neighbourhood of
`unitGaussPoint n K` disjoint from all `K`-rational points, because `a₀^q - a₀` reduces to `0` in
the residue field and therefore has norm strictly less than `1`. -/
theorem unitGaussPoint_notMem_closure_range_classicalPoint_of_finite
    [Finite (CanonicalReduction K)] [NeZero n] (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∉ closure (Set.range
      (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
        classicalPoint x a.val a.property)) := by
  have hfin_res : Finite (Valued.ResidueField K) :=
    (canonicalReductionRingEquivResidueField (K := K)).toEquiv.finite_iff.mp ‹_›
  let : Fintype (Valued.ResidueField K) := Fintype.ofFinite (Valued.ResidueField K)
  set q : ℕ := Fintype.card (Valued.ResidueField K)
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
  obtain ⟨_, hpU, ⟨a, rfl⟩⟩ := mem_closure_iff.mp hcl U hUopen hηU
  rw [Set.mem_preimage, mem_rationalSubset_iff] at hpU
  have h1le := hpU.right.left 1 (Finset.mem_singleton_self 1)
  rw [classicalPoint_vle, map_one, vle_iff_norm_le_of_mem_spa x.property, norm_one] at h1le
  -- Every `a₀ ∈ 𝒪[K]` satisfies `a₀^q - a₀ ∈ 𝓂[K]`, so `‖a₀^q - a₀‖ < 1`.
  have heval_s : evalAtHom a.val a.property s = a.val 0 ^ q - a.val 0 := by simp [s, T₀]
  let b : Valued.integer K :=
    powerBoundedSubringEquivInteger ⟨a.val 0, mem_powerBoundedSubring.mpr (a.property 0)⟩
  have hres : IsLocalRing.residue (Valued.integer K) (b ^ q - b) = 0 := by
    rw [map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hlt : ‖evalAtHom a.val a.property s‖ < 1 := by
    simpa only [heval_s, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, b,
      coe_powerBoundedSubringEquivInteger] using
      Valued.integer.residue_eq_zero_iff_norm_lt_one.mp hres
  exact hlt.not_ge h1le

end FiniteResidueField

section EquivalenceAndHeadline

/-- **Exact characterization of Gauss-point closure in positive dimension.** Over a complete
nontrivially normed ultrametric field `K`, for `n ≥ 1`, the unit Gauss point of `closedPolydisc n K`
lies in the closure of the `K`-rational evaluation points if and only if the canonical reduction
`K° / K°°` is infinite. -/
theorem unitGaussPoint_mem_closure_range_classicalPoint_iff {n : ℕ} [NeZero n]
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (x : spa (powerBoundedSubring K)) :
    unitGaussPoint n K ∈ closure (Set.range
        (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
          classicalPoint x a.val a.property)) ↔
      Infinite (CanonicalReduction K) := by
  refine ⟨fun h ↦ ?_, fun h ↦ unitGaussPoint_mem_closure_range_classicalPoint x⟩
  by_contra hnot
  have : Finite (CanonicalReduction K) := not_infinite_iff_finite.mp hnot
  exact unitGaussPoint_notMem_closure_range_classicalPoint_of_finite x h

/-- **Gauss-point closure.** Over a complete nontrivially normed ultrametric field `K` whose
canonical reduction `K° / K°°` is infinite, the unit Gauss point exists on the closed unit polydisc
of every dimension `n` and lies in the closure of the evaluation points at tuples of power-bounded
elements of `K`. -/
theorem gaussPoint_mem_closure_rationalPoints
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Infinite (CanonicalReduction K)] (n : ℕ) (x : spa (powerBoundedSubring K)) :
    ∃ η : closedPolydisc n K,
      IsUnitGaussPoint K n η ∧ η ∈ closure (Set.range
        (fun a : {a : Fin n → K // ∀ i, IsPowerBounded (a i)} ↦
          classicalPoint x a.val a.property)) :=
  ⟨unitGaussPoint n K, isUnitGaussPoint_unitGaussPoint n K,
    unitGaussPoint_mem_closure_range_classicalPoint x⟩

end EquivalenceAndHeadline

end Closure

end TauCeti.ValuationSpectrum
