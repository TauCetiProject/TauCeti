/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import TauCeti.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Regularity under almost everywhere continuous maps, finite sums and absolute continuity

An almost everywhere measurable map that is continuous on a set of full measure sends an inner
regular measure to an inner regular measure. Global continuity is unnecessary: compact approximation
can be performed inside the set where the map is continuous. This applies, for example, to
spectral character assignments whose exceptional set has measure zero.

Outer regularity and weak regularity are preserved by finite sums of measures, complementing
Mathlib's finite-sum instances for inner regularity. An open set approximating a sum from outside
is the intersection of open sets approximating the summands, and a set approximating it from
inside is the union of sets approximating the summands. Weak regularity of a finite sum is what
lets one approximate a function in `L¹` of several finite measures at once by approximating it in
`L¹` of their sum.

For a σ-finite measure that is inner regular for compact sets on sets of finite measure, such as
an additive Haar measure, every null measurable set contains a σ-compact subset of full measure
(`MeasureTheory.NullMeasurableSet.exists_isSigmaCompact_subset_ae_eq`). This reduces statements
about measurable sets to statements about compact sets, up to a null set.

For a weakly regular finite measure, the atoms of a measurable label with finitely many values
contain closed sets whose union has complement of arbitrarily small measure
(`Measurable.exists_isClosed_measure_compl_iUnion_le`). This is the closed approximation of a
finite partition used in the proof of Goodwyn's inequality between measure-theoretic and
topological entropy.

A finite measure `ν` absolutely continuous with respect to a finite measure `μ` inherits the
regularity of `μ`. By the `ε`–`δ` form of absolute continuity
(`MeasureTheory.Measure.AbsolutelyContinuous.exists_pos_measure_lt_of_measure_lt`), a set `K ⊆ U`
or `U ⊇ A` approximating in `μ`-measure leaves a difference of small `ν`-measure. So every
compact or closed inner approximation, and every open outer approximation, for `μ` is one for
`ν`. In particular, on a compact Hausdorff space with its Borel σ-algebra, a finite measure
absolutely continuous with respect to a finite regular measure is regular. Since `ν ≤ c • μ`
implies `ν ≪ μ` (`MeasureTheory.Measure.absolutelyContinuous_of_le_smul`), the same holds for a
measure dominated by a multiple of a finite regular measure. This is how regularity is checked for
measures given only through a domination bound, such as the variation of a sum of scalar measures.

## Main results

* `MeasureTheory.Measure.InnerRegular.map_of_continuousOn`: pushforward of an inner regular
  measure along an almost everywhere measurable map continuous on a set of full measure.
* `MeasureTheory.Measure.AbsolutelyContinuous.innerRegularWRT`: transfer of inner regularity with
  respect to measurable approximating sets.
* `MeasureTheory.Measure.AbsolutelyContinuous.outerRegular`,
  `MeasureTheory.Measure.AbsolutelyContinuous.weaklyRegular`,
  `MeasureTheory.Measure.AbsolutelyContinuous.innerRegularCompactLTTop`,
  `MeasureTheory.Measure.AbsolutelyContinuous.innerRegular`,
  `MeasureTheory.Measure.AbsolutelyContinuous.regular`: a finite measure absolutely continuous
  with respect to a finite measure inherits each regularity property.
* `MeasureTheory.Measure.OuterRegular.finsetSum`, `MeasureTheory.Measure.WeaklyRegular.finsetSum`:
  a finite sum of outer (weakly) regular measures is outer (weakly) regular.
* `MeasureTheory.Measure.InnerRegularCompactLTTop.comap'`: compact inner regularity on sets of
  finite measure pulls back along an open embedding between Borel spaces.
* `MeasureTheory.Measure.InnerRegularCompactLTTop.map_ofMul`: compact inner regularity on sets of
  finite measure transfers to `Additive α` for Borel spaces.
* `MeasureTheory.NullMeasurableSet.exists_isSigmaCompact_subset_ae_eq`: a null measurable set
  contains a σ-compact subset of full measure.
* `MeasureTheory.Measure.dirac.innerRegular`: a Dirac measure is inner regular; on an `R₁` space
  with its Borel σ-algebra it is therefore regular.
* `MeasureTheory.Measure.lintegral_lintegral_le_of_isOpen`: passage from open-set domination
  against an outer regular measure to Borel-weight domination.
* `Measurable.exists_isClosed_measure_compl_iUnion_le`: for a weakly regular finite measure, every
  atom `a ⁻¹' {i}` of a measurable label `a` into a finite type contains a closed set `F i`, with
  `μ (⋃ i, F i)ᶜ` arbitrarily small.

## Provenance

The proof of `MeasureTheory.Measure.InnerRegularWRT.add` is adapted from the anonymous
`InnerRegular (μ + ν)` instance in Mathlib's `Mathlib/MeasureTheory/Measure/Regular.lean`,
generalized from compact sets to any property of sets stable under binary unions.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill (1987), §2.18 and Theorem 6.11.
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley
  (1999), Theorem 3.5 and §7.1.
* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, §4.6.3, pp. 122–123.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- An almost everywhere measurable map that is continuous on a set of full measure preserves
inner regularity. Unlike `Measure.InnerRegular.map_of_continuous`, no Borel, separation,
countability or finiteness assumption is required. -/
protected theorem InnerRegular.map_of_continuousOn [TopologicalSpace α] {β : Type*}
    [MeasurableSpace β] [TopologicalSpace β] [μ.InnerRegular] {f : α → β} {s : Set α}
    (hf : AEMeasurable f μ) (hcont : ContinuousOn f s) (hmem : ∀ᵐ x ∂μ, x ∈ s) :
    (μ.map f).InnerRegular := by
  have hreg : μ.InnerRegularWRT (fun K ↦ IsCompact K ∧ K ⊆ s) (NullMeasurableSet · μ) := by
    intro t ht r hr
    have hs : NullMeasurableSet s μ := (NullMeasurableSet.of_null hmem).of_compl
    obtain ⟨u, hut, hu, hμu⟩ := (ht.inter hs).exists_measurable_subset_ae_eq
    rw [← μ.measure_inter_eq_of_ae hmem, inter_comm, ← measure_congr hμu] at hr
    obtain ⟨K, hKu, hK, hrK⟩ := hu.exists_lt_isCompact hr
    exact ⟨K, (hKu.trans hut).trans inter_subset_left,
      ⟨hK, (hKu.trans hut).trans inter_subset_right⟩, hrK⟩
  exact ⟨hreg.map hf (fun _ ht ↦ hf.nullMeasurableSet_preimage ht)
    (fun _ hK ↦ hK.1.image_of_continuousOn (hcont.mono hK.2)) (fun _ ht ↦ ht)⟩

/-- If two measures are inner regular for a property `p` of sets stable under binary unions, then
so is their sum. The proof is adapted from Mathlib's `InnerRegular (μ + ν)` instance. -/
theorem InnerRegularWRT.add {p q : Set α → Prop} (hp : ∀ s t, p s → p t → p (s ∪ t))
    (hμ : μ.InnerRegularWRT p q) (hν : ν.InnerRegularWRT p q) : (μ + ν).InnerRegularWRT p q := by
  intro U hU r hr
  rw [add_apply] at hr
  rcases eq_or_ne (μ U) 0 with h | h
  · rw [h, zero_add] at hr
    obtain ⟨K, hKU, hK, hrK⟩ := hν hU r hr
    exact ⟨K, hKU, hK, hrK.trans_le (by simp)⟩
  rcases eq_or_ne (ν U) 0 with h' | h'
  · rw [h', add_zero] at hr
    obtain ⟨K, hKU, hK, hrK⟩ := hμ hU r hr
    exact ⟨K, hKU, hK, hrK.trans_le (by simp)⟩
  obtain ⟨a, ha, b, hb, hab⟩ := ENNReal.exists_lt_add_of_lt_add hr h h'
  obtain ⟨K, hKU, hK, haK⟩ := hμ hU a ha
  obtain ⟨L, hLU, hL, hbL⟩ := hν hU b hb
  refine ⟨K ∪ L, union_subset hKU hLU, hp K L hK hL, hab.trans_le ?_⟩
  rw [add_apply]
  calc a + b ≤ μ K + ν L := add_le_add haK.le hbL.le
    _ ≤ μ (K ∪ L) + ν (K ∪ L) := by gcongr <;> simp

private theorem eapproxDiff_eq_tsum_indicator {w : α → ℝ≥0∞} (hw : Measurable w) (x : α) :
    w x = ∑' p : Σ n : ℕ, {r : ℝ≥0 // r ∈ (SimpleFunc.eapproxDiff w n).range.erase 0},
      (p.snd.val : ℝ≥0∞) * (SimpleFunc.eapproxDiff w p.fst ⁻¹' {p.snd.val}).indicator 1 x := by
  rw [tsum_sigma', ← SimpleFunc.tsum_eapproxDiff w hw x]
  refine tsum_congr fun n => ?_
  have hsum : ((SimpleFunc.eapproxDiff w n) x : ℝ≥0∞) =
      ∑ r ∈ (SimpleFunc.eapproxDiff w n).range.erase 0,
        (r : ℝ≥0∞) * (SimpleFunc.eapproxDiff w n ⁻¹' {r}).indicator 1 x := by
    by_cases h0 : SimpleFunc.eapproxDiff w n x = 0
    · rw [h0, ENNReal.coe_zero, eq_comm]
      exact Finset.sum_eq_zero fun r hr => by
        simp [(Finset.ne_of_mem_erase hr).symm, h0]
    · have hmem : SimpleFunc.eapproxDiff w n x ∈ (SimpleFunc.eapproxDiff w n).range.erase 0 :=
        Finset.mem_erase.2 ⟨h0, SimpleFunc.mem_range_self _ x⟩
      rw [Finset.sum_eq_single_of_mem (SimpleFunc.eapproxDiff w n x) hmem]
      · simp
      · intro r _ hne
        simp [Ne.symm hne]
  rw [hsum, ← Finset.tsum_subtype' ((SimpleFunc.eapproxDiff w n).range.erase 0) fun r =>
    (r : ℝ≥0∞) * (SimpleFunc.eapproxDiff w n ⁻¹' {r}).indicator 1 x]
  -- `Finset.tsum_subtype'` uses `Coe.coe` on the subtype while `tsum_sigma'` uses `.val`.
  rfl

private theorem lintegral_eq_tsum_eapproxDiff_fibre (ρ : Measure α) {w : α → ℝ≥0∞}
    (hw : Measurable w) :
    ∫⁻ x, w x ∂ρ =
      ∑' p : Σ n : ℕ, {r : ℝ≥0 // r ∈ (SimpleFunc.eapproxDiff w n).range.erase 0},
        (p.snd.val : ℝ≥0∞) * ρ (SimpleFunc.eapproxDiff w p.fst ⁻¹' {p.snd.val}) := by
  rw [lintegral_congr (eapproxDiff_eq_tsum_indicator hw)]
  have hmeas (p : Σ n : ℕ, {r : ℝ≥0 // r ∈ (SimpleFunc.eapproxDiff w n).range.erase 0}) :
      MeasurableSet (SimpleFunc.eapproxDiff w p.fst ⁻¹' {p.snd.val}) :=
    (SimpleFunc.eapproxDiff w p.fst).measurableSet_fiber p.snd.val
  rw [lintegral_tsum fun p =>
    ((measurable_one.indicator (hmeas p)).const_mul (p.snd.val : ℝ≥0∞)).aemeasurable]
  refine tsum_congr fun p => ?_
  rw [lintegral_const_mul _ (measurable_one.indicator (hmeas p)),
    lintegral_indicator_one (hmeas p)]

private theorem tsum_eapproxDiff_weight_le_one (d : ℕ → SimpleFunc α ℝ≥0) :
    ∑' p : Σ n : ℕ, {r : ℝ≥0 // r ∈ (d n).range.erase 0},
      (2⁻¹ : ℝ≥0∞) ^ (p.fst + 1) * ((d p.fst).range.card + 1 : ℝ≥0∞)⁻¹ ≤ 1 := by
  rw [tsum_sigma']
  calc ∑' n : ℕ, ∑' _ : {r : ℝ≥0 // r ∈ (d n).range.erase 0},
          (2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((d n).range.card + 1 : ℝ≥0∞)⁻¹
      = ∑' n : ℕ, ((d n).range.erase 0).card *
          ((2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((d n).range.card + 1 : ℝ≥0∞)⁻¹) := by
        refine tsum_congr fun n => ?_
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
        refine tsum_le_tsum fun n => ?_
        have hcard : (((d n).range.erase 0).card : ℝ≥0∞) ≤ ((d n).range.card + 1 : ℝ≥0∞) := by
          exact_mod_cast (Finset.card_erase_le.trans (Nat.le_succ _))
        calc (((d n).range.erase 0).card : ℝ≥0∞) *
                ((2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((d n).range.card + 1 : ℝ≥0∞)⁻¹)
            ≤ ((d n).range.card + 1 : ℝ≥0∞) *
                ((2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((d n).range.card + 1 : ℝ≥0∞)⁻¹) := by gcongr
          _ = ((d n).range.card + 1 : ℝ≥0∞) * ((d n).range.card + 1 : ℝ≥0∞)⁻¹ *
                (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by ring
          _ = (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
              rw [ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]
    _ = 1 := by
        simp_rw [pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        norm_num
        exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

variable [TopologicalSpace α]

/-- The sum of two outer regular measures is outer regular. -/
instance OuterRegular.add [OuterRegular μ] [OuterRegular ν] : OuterRegular (μ + ν) where
  outerRegular s _ r hr := by
    rw [gt_iff_lt, add_apply] at hr
    obtain ⟨a, ha, b, hb, hab⟩ := ENNReal.exists_add_lt_of_add_lt hr
    obtain ⟨U, hsU, hU, hμU⟩ := s.exists_isOpen_lt_of_lt a ha
    obtain ⟨V, hsV, hV, hνV⟩ := s.exists_isOpen_lt_of_lt b hb
    refine ⟨U ∩ V, subset_inter hsU hsV, hU.inter hV, ?_⟩
    rw [add_apply]
    calc μ (U ∩ V) + ν (U ∩ V) ≤ μ U + ν V := by gcongr <;> simp
      _ < r := (ENNReal.add_lt_add hμU hνV).trans hab

/-- The sum of two weakly regular measures is weakly regular. -/
instance WeaklyRegular.add [WeaklyRegular μ] [WeaklyRegular ν] : WeaklyRegular (μ + ν) where
  innerRegular := WeaklyRegular.innerRegular.add (fun _ _ ↦ IsClosed.union)
    WeaklyRegular.innerRegular

/-- A finite sum of outer regular measures is outer regular. -/
instance OuterRegular.finsetSum {ι : Type*} {μ : ι → Measure α} [∀ i, OuterRegular (μ i)]
    (s : Finset ι) : OuterRegular (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert a s ha ih => rw [Finset.sum_insert ha]; infer_instance

/-- A finite sum of weakly regular measures is weakly regular. -/
instance WeaklyRegular.finsetSum {ι : Type*} {μ : ι → Measure α} [∀ i, WeaklyRegular (μ i)]
    (s : Finset ι) : WeaklyRegular (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert a s ha ih => rw [Finset.sum_insert ha]; infer_instance

/-- Compact inner regularity on measurable sets of finite measure pulls back along an open
embedding between Borel spaces, complementing `Measure.InnerRegular.comap'` and
`Measure.Regular.comap'`. -/
protected theorem InnerRegularCompactLTTop.comap' {β : Type*} [BorelSpace α]
    {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β] (μ : Measure β)
    [hμ : μ.InnerRegularCompactLTTop] {f : α → β} (hf : Topology.IsOpenEmbedding f) :
    (μ.comap f).InnerRegularCompactLTTop where
  innerRegular :=
    hμ.innerRegular.comap hf.measurableEmbedding
      (fun s ⟨hs, htop⟩ ↦ ⟨hf.measurableEmbedding.measurableSet_image' hs, by
        rwa [← hf.measurableEmbedding.comap_apply]⟩)
      (fun _ hKrange hK ↦ hf.isInducing.isCompact_preimage' hK hKrange)

/-- Pushing forward a compactly inner regular measure on a Borel space to `Additive α` preserves
compact inner regularity on sets of finite measure. -/
instance InnerRegularCompactLTTop.map_ofMul [BorelSpace α] [μ.InnerRegularCompactLTTop] :
    (μ.map Additive.ofMul).InnerRegularCompactLTTop :=
  .map_of_continuous continuous_ofMul

/-- A Dirac measure is inner regular: a measurable set containing the point contains the compact
singleton, which carries the full mass. On an `R₁` space with its Borel σ-algebra, Mathlib's
instances upgrade this to regularity of the finite measure `dirac x`. -/
instance dirac.innerRegular (x : α) : (dirac x).InnerRegular where
  innerRegular U hU r hr := by
    by_cases hx : x ∈ U
    · exact ⟨{x}, singleton_subset_iff.2 hx, isCompact_singleton,
        by rwa [dirac_apply_of_mem (mem_singleton x), ← dirac_apply_of_mem hx]⟩
    · simp [dirac_apply' x hU, hx] at hr

/-- **Passage from open-set domination to Borel-weight domination.** If a family of measures `μ t`
on `α` is dominated on every open set `U` by a measurable majorant `m` with
`∫⁻ t, m t ∂ν ≤ c₀ * ρ U` for an outer regular measure `ρ`, then for every measurable weight
`w : α → ℝ≥0∞`, `∫⁻ t, ∫⁻ x, w x ∂μ t ∂ν ≤ c₀ * ∫⁻ x, w x ∂ρ`. -/
theorem lintegral_lintegral_le_of_isOpen {β : Type*} [MeasurableSpace β] [OpensMeasurableSpace α]
    {ν : Measure β} {μ : β → Measure α} {ρ : Measure α} [ρ.OuterRegular] {c₀ : ℝ≥0∞}
    (hc₀top : c₀ ≠ ⊤)
    (hmaj : ∀ U : Set α, IsOpen U → ∃ m : β → ℝ≥0∞, Measurable m ∧
      (∀ᵐ t ∂ν, μ t U ≤ m t) ∧ ∫⁻ t, m t ∂ν ≤ c₀ * ρ U)
    {w : α → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ t, ∫⁻ x, w x ∂μ t ∂ν ≤ c₀ * ∫⁻ x, w x ∂ρ := by
  by_cases hc₀0 : c₀ = 0
  · subst hc₀0
    obtain ⟨m, hm_meas, hm_le, hm_int⟩ := hmaj univ isOpen_univ
    have hm0 : ∀ᵐ t ∂ν, m t = 0 :=
      (lintegral_eq_zero_iff hm_meas).1 (nonpos_iff_eq_zero.1 (by simpa using hm_int))
    have hae : ∀ᵐ t ∂ν, ∫⁻ x, w x ∂μ t = 0 := by
      filter_upwards [hm_le, hm0] with t hle hmt
      have hμ0 : μ t = 0 :=
        Measure.measure_univ_eq_zero.1 (nonpos_iff_eq_zero.1 (hle.trans_eq hmt))
      simp [hμ0]
    simp [lintegral_congr_ae hae]
  by_cases hwint : ∫⁻ x, w x ∂ρ = ⊤
  · rw [hwint, ENNReal.mul_top hc₀0]
    exact le_top
  -- Approximate `w` by the indicator sum `∑' p, c p * 1_{A p}` over the nonzero fibres of
  -- `SimpleFunc.eapproxDiff w`, thicken each fibre `A p` to an open set `U p` with `ρ`-error
  -- at most `δ p`, apply the open-set majorant hypothesis to each `U p`, and sum the errors.
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : 0 < (ε : ℝ≥0∞) / c₀ :=
    ENNReal.div_pos (ENNReal.coe_pos.2 hε).ne' hc₀top
  let d : ℕ → SimpleFunc α ℝ≥0 := SimpleFunc.eapproxDiff w
  let ι := Σ n : ℕ, {r : ℝ≥0 // r ∈ (d n).range.erase 0}
  let c (p : ι) : ℝ≥0∞ := (p.snd.val : ℝ≥0∞)
  let A (p : ι) : Set α := (d p.fst) ⁻¹' {p.snd.val}
  have hc_pos (p : ι) : c p ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Finset.mem_erase.1 p.snd.property).1
  have hw_eq := eapproxDiff_eq_tsum_indicator hw
  have hw_int_eq := lintegral_eq_tsum_eapproxDiff_fibre ρ hw
  have hA_fin (p : ι) : ρ (A p) ≠ ⊤ := by
    have hle : c p * ρ (A p) ≤ ∫⁻ x, w x ∂ρ := by
      rw [hw_int_eq]
      exact le_tsum (fun p => c p * ρ (A p)) p
    exact fun htop => hwint (top_le_iff.1 (by rw [← ENNReal.mul_top (hc_pos p), ← htop]; exact hle))
  -- Thicken each fibre `A p` to an open set `U p` with `ρ (U p) < ρ (A p) + δ p`.
  let δ (p : ι) : ℝ≥0∞ :=
    ((ε : ℝ≥0∞) / c₀) / (c p * 2 ^ (p.fst + 1) * ((d p.fst).range.card + 1 : ℝ≥0∞))
  have hδ_pos (p : ι) : δ p ≠ 0 :=
    ENNReal.div_ne_zero.2 ⟨hε'.ne', by finiteness⟩
  have hU_ex (p : ι) : ∃ U : Set α, A p ⊆ U ∧ IsOpen U ∧ ρ U < ρ (A p) + δ p :=
    (A p).exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right (hA_fin p) (hδ_pos p))
  choose U hAU hUo hU_lt using hU_ex
  choose m hm_meas hm_le hm_int using fun p : ι => hmaj (U p) (hUo p)
  -- Bound `∫⁻ x, w x ∂μ t` by `∑' p, c p * m p t` a.e., then integrate and sum the `δ p` errors.
  have hstep1 (t : β) : ∫⁻ x, w x ∂μ t ≤ ∑' p : ι, c p * μ t (U p) := by
    calc ∫⁻ x, w x ∂μ t
        ≤ ∫⁻ x, ∑' p : ι, c p * (U p).indicator 1 x ∂μ t := by
          refine lintegral_mono fun x => ?_
          rw [hw_eq]
          refine tsum_le_tsum fun p => ?_
          gcongr
          exact hAU p
      _ = ∑' p : ι, c p * μ t (U p) := by
          rw [lintegral_tsum fun p =>
            ((measurable_one.indicator (hUo p).measurableSet).const_mul (c p)).aemeasurable]
          refine tsum_congr fun p => ?_
          rw [lintegral_const_mul _ (measurable_one.indicator (hUo p).measurableSet),
            lintegral_indicator_one (hUo p).measurableSet]
  have hae_le : ∀ᵐ t ∂ν, ∫⁻ x, w x ∂μ t ≤ ∑' p : ι, c p * m p t := by
    filter_upwards [ae_all_iff.2 hm_le] with t ht
    refine (hstep1 t).trans (tsum_le_tsum fun p => ?_)
    gcongr
    exact ht p
  calc ∫⁻ t, ∫⁻ x, w x ∂μ t ∂ν
      ≤ ∫⁻ t, ∑' p : ι, c p * m p t ∂ν := lintegral_mono_ae hae_le
    _ = ∑' p : ι, c p * ∫⁻ t, m p t ∂ν := by
        rw [lintegral_tsum fun p => ((hm_meas p).const_mul (c p)).aemeasurable]
        refine tsum_congr fun p => ?_
        rw [lintegral_const_mul _ (hm_meas p)]
    _ ≤ ∑' p : ι, c p * (c₀ * ρ (U p)) :=
        tsum_le_tsum fun p => by gcongr; exact hm_int p
    _ = c₀ * ∑' p : ι, c p * ρ (U p) := by
        simp_rw [← mul_assoc, mul_comm (c _) c₀, mul_assoc, ENNReal.tsum_mul_left]
    _ ≤ c₀ * ∑' p : ι, c p * (ρ (A p) + δ p) := by
        gcongr with p
        exact (hU_lt p).le
    _ = c₀ * (∫⁻ x, w x ∂ρ + ∑' p : ι, c p * δ p) := by
        congr 1
        rw [tsum_congr fun p => mul_add (c p) _ _,
          Summable.tsum_add CompleteLattice.summable CompleteLattice.summable, hw_int_eq]
    _ ≤ c₀ * (∫⁻ x, w x ∂ρ + (ε : ℝ≥0∞) / c₀) := by
        gcongr
        have hterm (p : ι) : c p * δ p = ((ε : ℝ≥0∞) / c₀) *
            ((2⁻¹ : ℝ≥0∞) ^ (p.fst + 1) * ((d p.fst).range.card + 1 : ℝ≥0∞)⁻¹) := by
          calc c p * δ p
              = ((ε : ℝ≥0∞) / c₀) * ((c p * (c p)⁻¹) *
                  ((2 ^ (p.fst + 1) : ℝ≥0∞)⁻¹ * ((d p.fst).range.card + 1 : ℝ≥0∞)⁻¹)) := by
                dsimp [δ]
                rw [div_eq_mul_inv,
                  ENNReal.mul_inv (Or.inl (mul_ne_zero (hc_pos p) (by positivity)))
                    (Or.inl (by finiteness)),
                  ENNReal.mul_inv (Or.inl (hc_pos p)) (Or.inl ENNReal.coe_ne_top)]
                ring
            _ = ((ε : ℝ≥0∞) / c₀) *
                  ((2⁻¹ : ℝ≥0∞) ^ (p.fst + 1) * ((d p.fst).range.card + 1 : ℝ≥0∞)⁻¹) := by
                rw [ENNReal.mul_inv_cancel (hc_pos p) ENNReal.coe_ne_top, one_mul,
                  ENNReal.inv_pow]
        simp_rw [hterm, ENNReal.tsum_mul_left]
        calc ((ε : ℝ≥0∞) / c₀) *
                ∑' p : ι, (2⁻¹ : ℝ≥0∞) ^ (p.fst + 1) * ((d p.fst).range.card + 1 : ℝ≥0∞)⁻¹
            ≤ ((ε : ℝ≥0∞) / c₀) * 1 := by gcongr; exact tsum_eapproxDiff_weight_le_one d
          _ = (ε : ℝ≥0∞) / c₀ := mul_one _
    _ = c₀ * ∫⁻ x, w x ∂ρ + (ε : ℝ≥0∞) := by
        rw [mul_add, ENNReal.mul_div_cancel hc₀0 hc₀top]

end MeasureTheory.Measure

namespace MeasureTheory.Measure.AbsolutelyContinuous

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- A finite measure absolutely continuous with respect to `μ` inherits inner regularity of `μ`
with respect to `p` on sets satisfying `q`, provided the approximating `p`-sets are `μ`-null
measurable and `q`-sets have finite `μ`-measure. -/
theorem innerRegularWRT [IsFiniteMeasure ν] (h : ν ≪ μ) {p q : Set α → Prop}
    (H : μ.InnerRegularWRT p q) (hp : ∀ K, p K → NullMeasurableSet K μ)
    (hq : ∀ U, q U → μ U ≠ ∞) : ν.InnerRegularWRT p q := by
  intro U hU r hr
  obtain ⟨δ, hδ, hδν⟩ := h.exists_pos_measure_lt_of_measure_lt (tsub_pos_of_lt hr).ne'
  have hμU : μ U ≠ 0 := fun h0 ↦ (pos_of_gt hr).ne' (h h0)
  obtain ⟨K, hKU, hpK, hK⟩ := H hU _ (ENNReal.sub_lt_self (hq U hU) hμU hδ.ne')
  refine ⟨K, hKU, hpK, lt_of_tsub_lt_tsub_left (le_measure_sdiff.trans_lt (hδν _ ?_))⟩
  exact measure_sdiff_lt_of_lt_add (hp K hpK) hKU
    (ne_top_of_le_ne_top (hq U hU) (measure_mono hKU))
    (ENNReal.lt_add_of_sub_lt_right (Or.inl (hq U hU)) hK)

variable [TopologicalSpace α] [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- A finite measure absolutely continuous with respect to a finite outer regular measure is
outer regular. -/
theorem outerRegular [μ.OuterRegular] (h : ν ≪ μ) : ν.OuterRegular := by
  refine ⟨fun A hA r hr ↦ ?_⟩
  obtain ⟨δ, hδ, hδν⟩ := h.exists_pos_measure_lt_of_measure_lt (tsub_pos_of_lt hr).ne'
  obtain ⟨U, hAU, hU, -, hμU⟩ := hA.exists_isOpen_sdiff_lt (measure_ne_top μ A) hδ.ne'
  exact ⟨U, hAU, hU, lt_of_tsub_lt_tsub_right (le_measure_sdiff.trans_lt (hδν _ hμU))⟩

/-- A finite measure absolutely continuous with respect to a finite weakly regular measure is
weakly regular. -/
theorem weaklyRegular [OpensMeasurableSpace α] [μ.WeaklyRegular] (h : ν ≪ μ) :
    ν.WeaklyRegular where
  __ := h.outerRegular
  innerRegular := h.innerRegularWRT WeaklyRegular.innerRegular
    (fun _ hK ↦ hK.measurableSet.nullMeasurableSet) fun U _ ↦ measure_ne_top μ U

omit [IsFiniteMeasure ν] in
/-- On an `R₁` space with its Borel σ-algebra, a measure absolutely continuous with
respect to a finite measure that is inner regular for compact sets is inner regular for compact
sets. Compact inner approximation holds on every measurable set of finite measure. -/
theorem innerRegularCompactLTTop [BorelSpace α] [R1Space α] [μ.InnerRegularCompactLTTop]
    (h : ν ≪ μ) : ν.InnerRegularCompactLTTop := by
  -- Closures of compact sets are compact and closed, so measurable, approximating sets.
  have H : μ.InnerRegularWRT (fun K ↦ IsCompact K ∧ IsClosed K) MeasurableSet :=
    fun U hU _ hr ↦
      let ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact_of_ne_top (measure_ne_top μ U) hr
      ⟨closure K, hK.closure_subset_measurableSet hU hKU, ⟨hK.closure, isClosed_closure⟩,
        hrK.trans_le (measure_mono subset_closure)⟩
  refine ⟨fun U ⟨hU, hUtop⟩ r hr ↦ ?_⟩
  have : IsFiniteMeasure (ν.restrict U) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hUtop.lt_top⟩
  have hac : ν.restrict U ≪ μ :=
    (Measure.restrict_le_self (μ := ν) (s := U)).absolutelyContinuous.trans h
  obtain ⟨K, hKU, ⟨hK, -⟩, hrK⟩ := (hac.innerRegularWRT H
    (fun _ hK ↦ hK.2.measurableSet.nullMeasurableSet) fun V _ ↦ measure_ne_top μ V)
    hU r (by rwa [restrict_apply_self])
  exact ⟨K, hKU, hK, by rwa [restrict_eq_self _ hKU] at hrK⟩

/-- On an `R₁` space with its Borel σ-algebra, a finite measure absolutely continuous with
respect to a finite inner regular measure is inner regular. -/
theorem innerRegular [BorelSpace α] [R1Space α] [μ.InnerRegular] (h : ν ≪ μ) :
    ν.InnerRegular :=
  have := h.innerRegularCompactLTTop
  inferInstance

/-- On an `R₁` space with its Borel σ-algebra, for example a compact Hausdorff space, a finite
measure absolutely continuous with respect to a finite regular measure is regular. -/
theorem regular [BorelSpace α] [R1Space α] [μ.Regular] (h : ν ≪ μ) : ν.Regular :=
  have := h.innerRegularCompactLTTop
  inferInstance

end MeasureTheory.Measure.AbsolutelyContinuous

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]

/-- **Null measurable sets are σ-compact up to a null set.** For a σ-finite measure that is inner
regular for compact sets on sets of finite measure, every null measurable set `s` contains a
σ-compact set `t` that is almost everywhere equal to `s`. -/
theorem NullMeasurableSet.exists_isSigmaCompact_subset_ae_eq [OpensMeasurableSpace α] [T2Space α]
    {μ : Measure α} [SigmaFinite μ] [μ.InnerRegularCompactLTTop] {s : Set α}
    (hs : NullMeasurableSet s μ) : ∃ t ⊆ s, IsSigmaCompact t ∧ t =ᵐ[μ] s := by
  obtain ⟨u, hus, hu, hsu⟩ := hs.exists_measurable_subset_ae_eq
  -- Approximate `u ∩ spanningSets μ n` from inside by a compact set up to measure `k⁻¹`.
  have h (n k : ℕ) : ∃ K ⊆ u ∩ spanningSets μ n, IsCompact K ∧
      μ ((u ∩ spanningSets μ n) \ K) < (k : ℝ≥0∞)⁻¹ :=
    (hu.inter (measurableSet_spanningSets μ n)).exists_isCompact_sdiff_lt
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top k))
  choose K hKu hK hKμ using h
  set t := ⋃ p : ℕ × ℕ, K p.1 p.2
  have htu : t ⊆ u := iUnion_subset fun p ↦ (hKu p.1 p.2).trans inter_subset_left
  have hnull : μ (u \ t) = 0 := by
    refine measure_mono_null (t := ⋃ n, (u ∩ spanningSets μ n) \ t) (fun x hx ↦ ?_)
      (measure_iUnion_null fun n ↦ ?_)
    · obtain ⟨n, hn⟩ := mem_iUnion.1 ((iUnion_spanningSets μ).symm ▸ mem_univ x)
      exact mem_iUnion.2 ⟨n, ⟨hx.1, hn⟩, hx.2⟩
    · refine nonpos_iff_eq_zero.1 (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun k ↦ ?_)
      exact (measure_mono (sdiff_subset_sdiff_right
        (subset_iUnion (fun p : ℕ × ℕ ↦ K p.1 p.2) (n, k)))).trans (hKμ n k).le
  refine ⟨t, htu.trans hus, isSigmaCompact_iUnion_of_isCompact _ fun p ↦ hK p.1 p.2, ?_⟩
  exact (ae_eq_set.2 ⟨by simp [sdiff_eq_empty.2 htu], hnull⟩).trans hsu

end MeasureTheory

namespace Measurable

variable {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}

/-- **Closed approximation of a finite partition.** For a weakly regular finite measure on a
topological space with measurable open sets and a measurable label `a` into a finite type, every
`δ > 0` admits closed sets `F i ⊆ a ⁻¹' {i}` whose union misses a set of measure at most `δ`. -/
theorem exists_isClosed_measure_compl_iUnion_le [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    [μ.WeaklyRegular] [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {a : X → ι}
    (ha : Measurable a) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ F : ι → Set X, (∀ i, IsClosed (F i)) ∧ (∀ i, F i ⊆ a ⁻¹' {i}) ∧
      μ (⋃ i, F i)ᶜ ≤ δ := by
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun _ ↦ ∅, fun _ ↦ isClosed_empty, fun _ ↦ empty_subset _, ?_⟩
    have : IsEmpty X := ⟨fun x ↦ hι.false (a x)⟩
    simp [Set.univ_eq_empty_iff.2 this]
  have hcard : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by simp
  have hε : δ / Fintype.card ι ≠ 0 := ENNReal.div_ne_zero.2 ⟨hδ, by simp⟩
  choose F hFsub hFc hF using fun i : ι ↦
    (ha (measurableSet_singleton i)).exists_isClosed_sdiff_lt (measure_ne_top μ _) hε
  refine ⟨F, hFc, hFsub, ?_⟩
  have hcover : (⋃ i, F i)ᶜ ⊆ ⋃ i, a ⁻¹' {i} \ F i := fun x hx ↦
    mem_iUnion.2 ⟨a x, rfl, fun h ↦ hx (mem_iUnion.2 ⟨a x, h⟩)⟩
  calc μ (⋃ i, F i)ᶜ ≤ ∑ i, μ (a ⁻¹' {i} \ F i) :=
        (measure_mono hcover).trans (measure_iUnion_fintype_le μ _)
    _ ≤ ∑ _i : ι, δ / Fintype.card ι := Finset.sum_le_sum fun i _ ↦ (hF i).le
    _ = δ := by simp [ENNReal.mul_div_cancel hcard (ENNReal.natCast_ne_top _)]

end Measurable
