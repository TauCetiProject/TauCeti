/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.BoundedVariation.Space
public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Basic
import TauCeti.Analysis.BoundedVariation.Isometry
import TauCeti.Analysis.BoundedVariation.W1p
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.Basic
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
import TauCeti.Analysis.Sobolev.W1p.LocalCompactness

/-!
# Global `L¹` compactness of BV functions and sets of finite perimeter on bounded Lipschitz domains

Local compactness in `L¹_loc(Ω)` (`TauCeti.Analysis.BoundedVariation.Compactness`) holds on every
open subset `Ω` of a finite-dimensional real inner product space, without any assumption on the
boundary of `Ω`. Global compactness in `L¹(Ω)` fails on arbitrary bounded open sets (for instance on
a countable union of disjoint open intervals accumulating at `0`), because variations can vanish
while values jump freely across components.

On a bounded Lipschitz domain `Ω`, however, the Rellich–Kondrachov theorem makes the Sobolev value
projection `W^{1,1}(Ω) → L¹(Ω)` a compact operator
(`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`), and strict `W^{1,1}`
approximation transfers compactness from `W^{1,1}(Ω)` to `BV(Ω)`
(`TauCeti.BV.isCompactOperator_toL1CLM_iff`).

This file develops:

* **Abstract consequences of compactness of `BV.toL1CLM`.** Whenever
  `BV.toL1CLM : BV μ Ω →L[ℝ] (E →₁[μ.restrict Ω] ℝ)` is a compact operator (for any measure `μ` on
  an open set `Ω`), every norm-bounded sequence in `BV μ Ω` has an `L¹(Ω)`-convergent subsequence
  whose limit stays in the same closed BV ball and satisfies lower semicontinuity of variation;
  families bounded in `L¹(Ω)` and in variation on `Ω` are totally bounded and have compact closure
  in `L¹(Ω)`; and on finite-measure domains (`μ Ω ≠ ∞`), sequences of null-measurable sets of
  uniformly bounded perimeter have subsequences converging globally in measure on `Ω`, with lower
  semicontinuity of perimeter.
* **Invariance under linear and affine isometry equivalences.** Compactness of `BV.toL1CLM` is
  preserved and reflected along measure-preserving `LinearIsometryEquiv`s and
  `AffineIsometryEquiv`s.
* **Global `L¹` compactness on bounded Lipschitz domains.** Compactness of `BV.toL1CLM` holds for
  bounded `IsLipschitzDomainWith` domains in the model space `WithLp 2 (ℝ × E)`, for bounded open
  sets in any finite-dimensional real inner product space `F` whose isometric image in the model
  space is `IsLipschitzDomainWith`, and intrinsically for any bounded `(Ω : Set F).IsLipschitzDomain
  E`, together with the resulting global sequential compactness theorems for BV functions and sets
  of finite perimeter, and concrete specializations to Euclidean balls and the planar half-disc.

## Main declarations

* `TauCeti.BV.exists_subseq_tendsto_toL1_of_isCompactOperator`: sequential `L¹` compactness of
  norm-bounded sequences in `BV μ Ω`, with norm and lower-semicontinuity bounds on the limit.
* `TauCeti.totallyBounded_of_isCompactOperator_toL1CLM` and
  `TauCeti.isCompact_closure_of_isCompactOperator_toL1CLM`: total boundedness and relative
  compactness in `L¹(Ω)` of families bounded in `L¹(Ω)` and in variation.
* `TauCeti.exists_subseq_tendsto_setLIntegral_enorm_sub_of_isCompactOperator_toL1CLM` and
  `TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_of_isCompactOperator_toL1CLM`: global
  sequential compactness for unbundled BV sequences and sets of bounded perimeter.
* `TauCeti.BV.isCompactOperator_toL1CLM_iff_of_linearIsometryEquiv` and
  `TauCeti.BV.isCompactOperator_toL1CLM_iff_of_affineIsometryEquiv`: invariance of compactness of
  `BV.toL1CLM` under linear and affine isometries.
* `TauCeti.BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith`,
  `TauCeti.BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith_image`, and
  `TauCeti.BV.isCompactOperator_toL1CLM_of_isLipschitzDomain`: global `L¹` compactness of `BV` on
  bounded Lipschitz domains.
* `TauCeti.BV.exists_subseq_tendsto_toL1_of_isLipschitzDomain`,
  `TauCeti.totallyBounded_of_setLIntegral_le_of_totalVariationOn_le_of_isLipschitzDomain`,
  `TauCeti.isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le_of_isLipschitzDomain`,
  `TauCeti.exists_subseq_tendsto_setLIntegral_enorm_sub_of_isLipschitzDomain`, and
  `TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_of_isLipschitzDomain`: global compactness
  corollaries on bounded Lipschitz domains.
* `TauCeti.BV.isCompactOperator_toL1CLM_ball` and
  `TauCeti.BV.isCompactOperator_toL1CLM_halfDisc`: compactness of `BV.toL1CLM` on Euclidean balls
  and on the open half-disc.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.23 and Remark 3.24.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2.3,
  Theorem 4.
* W. P. Ziemer, *Weakly Differentiable Functions*, Corollary 5.3.4.
-/

public section

namespace TauCeti

open Bornology Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology symmDiff

section CompactOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E}

/-- Lower semicontinuity of total variation on `Ω` under `L¹(Ω)` convergence. -/
private theorem totalVariationOn_le_liminf_of_tendsto_L1 {ι : Type*} {l : Filter ι}
    {u : ι → E →₁[μ.restrict Ω] ℝ} {v : E →₁[μ.restrict Ω] ℝ} (h : Tendsto u l (𝓝 v)) :
    totalVariationOn μ Ω v ≤ liminf (fun i => totalVariationOn μ Ω (u i)) l := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  exact le_of_forall_gt_imp_ge_of_dense fun _ hc => totalVariationOn_le_of_tendsto_L1 h
    ((frequently_lt_of_liminf_lt (h := hc)).mono fun _ hi => hi.le)

/-- **Sequential `L¹` compactness for bounded sequences in `BV`.** If `BV.toL1CLM` is a compact
operator on `Ω`, every sequence `u` in `BV μ Ω` with `‖u n‖ ≤ R` has a subsequence whose `L¹(Ω)`
classes converge to `v.toL1` for some `v : BV μ Ω` satisfying lower semicontinuity of total
variation and `‖v‖ ≤ R`. -/
theorem BV.exists_subseq_tendsto_toL1_of_isCompactOperator
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ Ω →L[ℝ] _))
    {u : ℕ → BV μ Ω} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : BV μ Ω) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => (u (φ k)).toL1) atTop (𝓝 v.toL1) ∧
      totalVariationOn μ Ω v ≤ liminf (fun k => totalVariationOn μ Ω (u (φ k))) atTop ∧
      ‖v‖ ≤ R := by
  obtain ⟨w, φ, hφ, hw⟩ := hcpt.exists_subseq_tendsto hu
  have hw' : Tendsto (fun k => (u (φ k)).toL1) atTop (𝓝 w) := by
    simpa only [ContinuousLinearMap.coe_coe, BV.toL1CLM_apply] using hw
  have hw_norm : ‖w‖ ≤ R :=
    le_of_tendsto hw'.norm (.of_forall fun k => (BV.norm_toL1_le _).trans (hu _))
  have hstep (k : ℕ) :
      totalVariationOn μ Ω (u (φ k)) ≤ ENNReal.ofReal (R - ‖(u (φ k)).toL1‖) := by
    have hsub : 0 ≤ R - ‖(u (φ k)).toL1‖ :=
      sub_nonneg.mpr ((BV.norm_toL1_le _).trans (hu _))
    refine (ENNReal.le_ofReal_iff_toReal_le (u (φ k)).totalVariationOn_lt_top.ne hsub).mpr ?_
    linarith [BV.norm_def (u (φ k)), hu (φ k)]
  have hlim :
      Tendsto (fun k => ENNReal.ofReal (R - ‖(u (φ k)).toL1‖)) atTop
        (𝓝 (ENNReal.ofReal (R - ‖w‖))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hw'.norm)
  have hlsc : totalVariationOn μ Ω w ≤ liminf (fun k => totalVariationOn μ Ω (u (φ k))) atTop :=
    totalVariationOn_le_liminf_of_tendsto_L1 hw'
  have htvR : totalVariationOn μ Ω w ≤ ENNReal.ofReal (R - ‖w‖) :=
    hlsc.trans ((liminf_le_liminf (.of_forall hstep)).trans_eq hlim.liminf_eq)
  have hwBV : MemBV μ Ω w :=
    memBV_iff.mpr ⟨L1.integrable_coeFn w, htvR.trans_lt ENNReal.ofReal_lt_top⟩
  let v : BV μ Ω := BV.ofFunction w hwBV
  have hv_toL1 : v.toL1 = w :=
    (BV.toL1_ofFunction w hwBV).trans (Integrable.toL1_coeFn w (L1.integrable_coeFn w))
  refine ⟨v, φ, hφ, hv_toL1.symm ▸ hw', ?_, ?_⟩
  · rwa [BV.totalVariationOn_ofFunction]
  · rw [BV.norm_def, hv_toL1]
    linarith [ENNReal.toReal_le_of_le_ofReal (sub_nonneg.mpr hw_norm) htvR]

/-- **Total boundedness in `L¹(Ω)` from compactness of `BV.toL1CLM`.** If `BV.toL1CLM` is a compact
operator on `Ω`, any family `S` of functions on `Ω` with `∫_Ω |u| ≤ M` and `|Du|(Ω) ≤ M` (`M < ∞`)
gives a totally bounded set of classes in `L¹(Ω)`. Unlike the local criterion on compact subsets,
no separate measurability assumption on `S` is required: any `f : Lp ℝ 1 (μ.restrict Ω)` agreeing
almost everywhere with `u ∈ S` is already measurable. -/
theorem totallyBounded_of_isCompactOperator_toL1CLM
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ Ω →L[ℝ] _))
    {S : Set (E → ℝ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ∂μ ≤ M)
    (hvar : ∀ u ∈ S, totalVariationOn μ Ω u ≤ M) :
    TotallyBounded {f : Lp ℝ 1 (μ.restrict Ω) | ∃ u ∈ S, f =ᵐ[μ.restrict Ω] u} := by
  refine (hcpt.totallyBounded_image_closedBall (2 * M.toReal)).subset ?_
  rintro f ⟨u, hu, hf⟩
  have hfe : ‖f‖ₑ ≤ M := by
    rw [Lp.eNorm_def, eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable f),
      lintegral_congr_ae (hf.mono fun x hx => by rw [hx])]
    exact hbdd u hu
  have hftv : totalVariationOn μ Ω f ≤ M :=
    (totalVariationOn_congr_ae hf).trans_le (hvar u hu)
  have hfBV : MemBV μ Ω f := memBV_iff.mpr ⟨L1.integrable_coeFn f, hftv.trans_lt hM.lt_top⟩
  refine ⟨BV.ofFunction f hfBV, mem_closedBall_zero_iff.mpr ?_, ?_⟩
  · have h₁ : ‖(BV.ofFunction f hfBV).toL1‖ ≤ M.toReal := by
      rw [BV.toL1_ofFunction, Integrable.toL1_coeFn f (L1.integrable_coeFn f), ← toReal_eNorm]
      exact ENNReal.toReal_mono hM hfe
    have h₂ : (totalVariationOn μ Ω (BV.ofFunction f hfBV)).toReal ≤ M.toReal := by
      rw [BV.totalVariationOn_ofFunction]
      exact ENNReal.toReal_mono hM hftv
    rw [BV.norm_def]
    linarith
  · rw [ContinuousLinearMap.coe_coe, BV.toL1CLM_apply, BV.toL1_ofFunction]
    exact Integrable.toL1_coeFn f (L1.integrable_coeFn f)

/-- **Relative compactness in `L¹(Ω)` from compactness of `BV.toL1CLM`.** Under the hypotheses of
`TauCeti.totallyBounded_of_isCompactOperator_toL1CLM`, the closure in `L¹(Ω)` of the classes of
members of `S` is compact. -/
theorem isCompact_closure_of_isCompactOperator_toL1CLM
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ Ω →L[ℝ] _))
    {S : Set (E → ℝ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ∂μ ≤ M)
    (hvar : ∀ u ∈ S, totalVariationOn μ Ω u ≤ M) :
    IsCompact (closure {f : Lp ℝ 1 (μ.restrict Ω) | ∃ u ∈ S, f =ᵐ[μ.restrict Ω] u}) :=
  (totallyBounded_of_isCompactOperator_toL1CLM hcpt hM hbdd hvar).closure.isCompact_of_isClosed
    isClosed_closure

/-- **Global `L¹(Ω)` sequential compactness of unbundled BV sequences.** If `BV.toL1CLM` is a
compact operator on `Ω` and `u : ℕ → E → ℝ` is a sequence of `μ.restrict Ω`-almost-everywhere
measurable functions bounded in `L¹(Ω)` and in total variation on `Ω` by `M < ∞`, then a
subsequence converges globally in `L¹(Ω)` to a function `v` belonging to `MemBV μ Ω`, with
`totalVariationOn μ Ω v ≤ liminf_j totalVariationOn μ Ω (u (φ j))`. -/
theorem exists_subseq_tendsto_setLIntegral_enorm_sub_of_isCompactOperator_toL1CLM
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ Ω →L[ℝ] _))
    {u : ℕ → E → ℝ} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hmeas : ∀ n, AEStronglyMeasurable (u n) (μ.restrict Ω))
    (hbdd : ∀ n, ∫⁻ x in Ω, ‖u n x‖ₑ ∂μ ≤ M)
    (hvar : ∀ n, totalVariationOn μ Ω (u n) ≤ M) :
    ∃ v : E → ℝ, MemBV μ Ω v ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => ∫⁻ x in Ω, ‖u (φ j) x - v x‖ₑ ∂μ) atTop (𝓝 0) ∧
      totalVariationOn μ Ω v ≤ liminf (fun j => totalVariationOn μ Ω (u (φ j))) atTop := by
  have huBV (n : ℕ) : MemBV μ Ω (u n) :=
    memBV_iff.mpr ⟨⟨hmeas n, (hbdd n).trans_lt hM.lt_top⟩, (hvar n).trans_lt hM.lt_top⟩
  let b : ℕ → BV μ Ω := fun n => BV.ofFunction (u n) (huBV n)
  have hb_norm (n : ℕ) : ‖b n‖ ≤ 2 * M.toReal := by
    have h₁ : ‖(b n).toL1‖ ≤ M.toReal := by
      rw [← toReal_eNorm, Lp.eNorm_def, eLpNorm_congr_ae (BV.coeFn_ofFunction (u n) (huBV n)),
        eLpNorm_one_eq_lintegral_eNorm (hmeas n)]
      exact ENNReal.toReal_mono hM (hbdd n)
    have h₂ : (totalVariationOn μ Ω (b n)).toReal ≤ M.toReal := by
      rw [BV.totalVariationOn_ofFunction]
      exact ENNReal.toReal_mono hM (hvar n)
    rw [BV.norm_def]
    linarith
  obtain ⟨v, φ, hφ, hv, hlsc, -⟩ :=
    BV.exists_subseq_tendsto_toL1_of_isCompactOperator hcpt hb_norm
  refine ⟨v, v.memBV, φ, hφ, ?_, ?_⟩
  · refine (tendsto_iff_edist_tendsto_0.mp hv).congr fun j => ?_
    rw [L1.edist_def]
    refine lintegral_congr_ae ?_
    filter_upwards [BV.coeFn_ofFunction (u (φ j)) (huBV (φ j))] with x hx
    simp [b, hx, eDist_eq_eNorm_sub]
  · simpa only [b, BV.totalVariationOn_ofFunction] using hlsc

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- Pointwise bound `1_{A ∆ {1/2 < w}} ≤ 2 ‖1_A - w‖ₑ` used to extract a measurable set limit from
an `L¹` limit of indicators. -/
private theorem indicator_symmDiff_le_two_mul_enorm_sub (A : Set E) (w : E → ℝ) (x : E) :
    (A ∆ {y | 1 / 2 < w y}).indicator (1 : E → ℝ≥0∞) x ≤
      2 * ‖A.indicator (1 : E → ℝ) x - w x‖ₑ := by
  have key {r : ℝ} (hr : 1 / 2 ≤ |r|) : (1 : ℝ≥0∞) ≤ 2 * ‖r‖ₑ := by
    rw [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ENNReal.one_le_ofReal]
    linarith
  by_cases h₁ : x ∈ A <;> by_cases h₂ : 1 / 2 < w x
  · rw [indicator_of_notMem (by simp [mem_symmDiff, h₁]; linarith)]
    exact zero_le
  · rw [indicator_of_mem (by simp [mem_symmDiff, h₁]; linarith), indicator_of_mem h₁,
      Pi.one_apply, Pi.one_apply]
    exact key (by rw [abs_of_nonneg (by linarith)]; linarith)
  · rw [indicator_of_mem (by simp [mem_symmDiff, h₁]; linarith), indicator_of_notMem h₁,
      Pi.one_apply]
    exact key (by rw [zero_sub, abs_neg, abs_of_pos (by linarith)]; linarith)
  · rw [indicator_of_notMem (by simp [mem_symmDiff, h₁]; linarith)]
    exact zero_le

/-- **Global compactness for sets of bounded perimeter.** If `BV.toL1CLM` is a compact operator on
`Ω`, `μ Ω ≠ ∞`, and `s : ℕ → Set E` is a sequence of `μ.restrict Ω`-null-measurable sets with
`perimeter μ Ω (s n) ≤ M` (`M < ∞`), then a subsequence converges globally in measure on `Ω` to a
measurable set `t`, that is `μ ((s (φ j) ∆ t) ∩ Ω) → 0`, with
`perimeter μ Ω t ≤ liminf_j perimeter μ Ω (s (φ j))`. -/
theorem exists_subseq_tendsto_measure_symmDiff_inter_of_isCompactOperator_toL1CLM
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ Ω →L[ℝ] _)) (hμΩ : μ Ω ≠ ∞)
    {s : ℕ → Set E} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hs : ∀ n, NullMeasurableSet (s n) (μ.restrict Ω))
    (hP : ∀ n, perimeter μ Ω (s n) ≤ M) :
    ∃ t : Set E, MeasurableSet t ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => μ ((s (φ j) ∆ t) ∩ Ω)) atTop (𝓝 0) ∧
      perimeter μ Ω t ≤ liminf (fun j => perimeter μ Ω (s (φ j))) atTop := by
  have hB : max (μ Ω) M ≠ ⊤ := (max_lt_iff.mpr ⟨hμΩ.lt_top, hM.lt_top⟩).ne
  have hind (A : Set E) : ∫⁻ x in Ω, ‖A.indicator (1 : E → ℝ) x‖ₑ ∂μ ≤ μ Ω :=
    (lintegral_mono (g := fun _ => (1 : ℝ≥0∞)) fun x =>
      (eNorm_indicator_le_eNorm_self _ x).trans (by simp)).trans_eq (by simp)
  obtain ⟨v, hv, φ, hφ, hlim, -⟩ :=
    exists_subseq_tendsto_setLIntegral_enorm_sub_of_isCompactOperator_toL1CLM
      (u := fun n => (s n).indicator 1) hcpt hB
      (fun n => aestronglyMeasurable_const.indicator₀ (hs n))
      (fun n => (hind (s n)).trans (le_max_left _ _))
      fun n => by simpa [perimeter_def] using (hP n).trans (le_max_right _ _)
  let w := hv.integrableOn.aestronglyMeasurable.mk v
  have hw : Measurable w := hv.integrableOn.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  let t : Set E := {x | 1 / 2 < w x}
  have ht : MeasurableSet t := measurableSet_lt measurable_const hw
  have hsymm : Tendsto (fun j => μ ((s (φ j) ∆ t) ∩ Ω)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using ENNReal.Tendsto.const_mul (a := 2) hlim (.inr (by simp)))
      (fun _ => zero_le) fun j => ?_
    calc μ ((s (φ j) ∆ t) ∩ Ω)
        = ∫⁻ x in Ω, (s (φ j) ∆ t).indicator 1 x ∂μ := by
          rw [lintegral_indicator_one₀ ((hs _).symmDiff ht.nullMeasurableSet),
            Measure.restrict_apply' Ω.isOpen.measurableSet]
      _ ≤ ∫⁻ x in Ω, 2 * ‖(s (φ j)).indicator (1 : E → ℝ) x - v x‖ₑ ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hv.integrableOn.aestronglyMeasurable.ae_eq_mk] with x hx
          rw [hx]
          exact indicator_symmDiff_le_two_mul_enorm_sub (s (φ j)) w x
      _ = 2 * ∫⁻ x in Ω, ‖(s (φ j)).indicator (1 : E → ℝ) x - v x‖ₑ ∂μ :=
          lintegral_const_mul' _ _ (by simp)
  refine ⟨t, ht, φ, hφ, hsymm, ?_⟩
  have : IsFiniteMeasure (μ.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμΩ.lt_top⟩
  have hper (A : Set E) : perimeter (μ.restrict Ω) Ω A = perimeter μ Ω A := by
    rw [← perimeter_congr_of_inter_eq (s := A ∩ Ω) (t := A) (by simp),
      perimeter_restrict_of_subset inter_subset_right,
      perimeter_congr_of_inter_eq (s := A ∩ Ω) (t := A) (by simp)]
  simp_rw [← hper]
  refine perimeter_le_liminf (.of_forall fun j => hs (φ j)) ht.nullMeasurableSet fun K _ _ => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsymm
    (fun _ => zero_le) fun j => ?_
  rw [Measure.restrict_apply' Ω.isOpen.measurableSet]
  exact measure_mono (inter_subset_inter_left _ inter_subset_left)

end CompactOperator

section Isometry

/-- Factoring `BV.toL1CLM` through a linear isometry equivalence `L : BV μ₁ Ω₁ ≃ₗᵢ[ℝ] BV μ₂ Ω₂`
and a measure-preserving pullback `f` transports compactness of `BV.toL1CLM`. -/
private theorem isCompactOperator_toL1CLM_of_compEquiv
    {α₁ α₂ : Type*} [NormedAddCommGroup α₁] [InnerProductSpace ℝ α₁] [FiniteDimensional ℝ α₁]
    [NormedAddCommGroup α₂] [InnerProductSpace ℝ α₂] [FiniteDimensional ℝ α₂]
    [MeasurableSpace α₁] [OpensMeasurableSpace α₁] [MeasurableSpace α₂] [OpensMeasurableSpace α₂]
    {μ₁ : Measure α₁} {μ₂ : Measure α₂} {Ω₁ : Opens α₁} {Ω₂ : Opens α₂}
    {f : α₂ → α₁} (hf : MeasurePreserving f (μ₂.restrict Ω₂) (μ₁.restrict Ω₁))
    (L : BV μ₁ Ω₁ ≃ₗᵢ[ℝ] BV μ₂ Ω₂)
    (hcomm : ∀ x : BV μ₁ Ω₁, (L x).toL1 = Lp.compMeasurePreserving f hf x.toL1)
    (hcpt : IsCompactOperator (BV.toL1CLM : BV μ₁ Ω₁ →L[ℝ] _)) :
    IsCompactOperator (BV.toL1CLM : BV μ₂ Ω₂ →L[ℝ] _) := by
  let S : (α₁ →₁[μ₁.restrict Ω₁] ℝ) →L[ℝ] (α₂ →₁[μ₂.restrict Ω₂] ℝ) :=
    (Lp.compMeasurePreservingₗᵢ ℝ f hf).toContinuousLinearMap
  have hfac : (BV.toL1CLM : BV μ₂ Ω₂ →L[ℝ] _) = S.comp ((BV.toL1CLM : BV μ₁ Ω₁ →L[ℝ] _).comp
      L.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
    ext1 y
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      BV.toL1CLM_apply, BV.toL1CLM_apply]
    simpa only [S, LinearIsometry.coe_toContinuousLinearMap, Lp.compMeasurePreservingₗᵢ_apply,
      ← hcomm (L.symm y)] using congrArg BV.toL1 (L.apply_symm_apply y).symm
  rw [hfac]
  exact (hcpt.comp_clm _).clm_comp S

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [OpensMeasurableSpace E']
  {μ : Measure E} {ν : Measure E'} {V : Opens E} {Ω : Opens E'}

/-- Pulling `BV` back along a measure-preserving linear isometry equivalence `e` with `V = e ⁻¹' Ω`
transports compactness of `BV.toL1CLM` from `Ω` to `V`. -/
theorem BV.isCompactOperator_toL1CLM_of_linearIsometryEquiv {e : E ≃ₗᵢ[ℝ] E'}
    (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω)
    (hcpt : IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _)) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) :=
  isCompactOperator_toL1CLM_of_compEquiv
    (hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet)
    (BV.compLinearIsometryEquiv he hVO) (BV.toL1_compLinearIsometryEquiv he hVO) hcpt

/-- **Invariance of compactness of `BV.toL1CLM` under linear isometry equivalences.** -/
theorem BV.isCompactOperator_toL1CLM_iff_of_linearIsometryEquiv {e : E ≃ₗᵢ[ℝ] E'}
    (he : MeasurePreserving e μ ν) (hVO : (V : Set E) = e ⁻¹' Ω) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) ↔
      IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _) := by
  refine ⟨?_, BV.isCompactOperator_toL1CLM_of_linearIsometryEquiv he hVO⟩
  have hres : MeasurePreserving e (μ.restrict V) (ν.restrict Ω) :=
    hVO ▸ he.restrict_preimage Ω.isOpen.measurableSet
  have hsymm : MeasurePreserving e.symm (ν.restrict Ω) (μ.restrict V) :=
    MeasurePreserving.symm ⟨e.toEquiv, he.measurable, e.symm.continuous.measurable⟩ hres
  exact isCompactOperator_toL1CLM_of_compEquiv hsymm (BV.compLinearIsometryEquiv he hVO).symm
    fun v => Lp.ext <| (BV.coeFn_compLinearIsometryEquiv_symm he hVO v).trans
      (Lp.coeFn_compMeasurePreserving v.toL1 hsymm).symm

/-- Pulling `BV` back along a measure-preserving affine isometry equivalence `f` with `V = f ⁻¹' Ω`
transports compactness of `BV.toL1CLM` from `Ω` to `V`. -/
theorem BV.isCompactOperator_toL1CLM_of_affineIsometryEquiv {f : E ≃ᵃⁱ[ℝ] E'}
    (hf : MeasurePreserving f μ ν) (hVO : (V : Set E) = f ⁻¹' Ω)
    (hcpt : IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _)) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) :=
  isCompactOperator_toL1CLM_of_compEquiv
    (hVO ▸ hf.restrict_preimage Ω.isOpen.measurableSet)
    (BV.compAffineIsometryEquiv hf hVO) (BV.toL1_compAffineIsometryEquiv hf hVO) hcpt

/-- **Invariance of compactness of `BV.toL1CLM` under affine isometry equivalences.** -/
theorem BV.isCompactOperator_toL1CLM_iff_of_affineIsometryEquiv {f : E ≃ᵃⁱ[ℝ] E'}
    (hf : MeasurePreserving f μ ν) (hVO : (V : Set E) = f ⁻¹' Ω) :
    IsCompactOperator (BV.toL1CLM : BV μ V →L[ℝ] _) ↔
      IsCompactOperator (BV.toL1CLM : BV ν Ω →L[ℝ] _) := by
  refine ⟨?_, BV.isCompactOperator_toL1CLM_of_affineIsometryEquiv hf hVO⟩
  have hres : MeasurePreserving f (μ.restrict V) (ν.restrict Ω) :=
    hVO ▸ hf.restrict_preimage Ω.isOpen.measurableSet
  have hsymm : MeasurePreserving f.symm (ν.restrict Ω) (μ.restrict V) :=
    MeasurePreserving.symm ⟨f.toEquiv, hf.measurable, f.symm.continuous.measurable⟩ hres
  exact isCompactOperator_toL1CLM_of_compEquiv hsymm (BV.compAffineIsometryEquiv hf hVO).symm
    fun v => Lp.ext <| (BV.coeFn_compAffineIsometryEquiv_symm hf hVO v).trans
      (Lp.coeFn_compMeasurePreserving v.toL1 hsymm).symm

end Isometry

section LipschitzDomain

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {L : ℝ≥0}

/-- **Global `L¹` compactness of `BV` on bounded Lipschitz domains of the model space.** If
`Ω ⊆ WithLp 2 (ℝ × E)` is a bounded Lipschitz domain with constant `L`, the inclusion
`BV.toL1CLM : BV volume Ω →L[ℝ] _` is a compact operator. -/
theorem BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith
    {Ω : Opens (WithLp 2 (ℝ × E))}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    IsCompactOperator (BV.toL1CLM (μ := volume) (Ω := Ω)) :=
  BV.isCompactOperator_toL1CLM_iff.mpr (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb)

end ModelSpace

section Intrinsic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Opens F}

/-- **Global `L¹` compactness of `BV` on isometric copies of bounded Lipschitz domains.** Let
`e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)` be a linear isometry equivalence and `Ω ⊆ F` a bounded open set
whose image `e '' Ω` is a Lipschitz domain with constant `L`. Then `BV.toL1CLM` on `Ω` is a
compact operator. No inner-product, finite-dimensionality, or measurability instances are assumed
on `E`, as `e.symm` embeds `E` linearly and isometrically into `F`. -/
theorem BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith_image {L : ℝ≥0}
    (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E))
    (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F)) :
    IsCompactOperator (BV.toL1CLM (μ := volume) (Ω := Ω)) := by
  let ι : E →ₗᵢ[ℝ] F :=
    { toLinearMap := e.symm.toLinearEquiv.toLinearMap.comp
        ((WithLp.linearEquiv 2 ℝ (ℝ × E)).symm.toLinearMap.comp (LinearMap.inr ℝ ℝ E))
      norm_map' y := by simp }
  let _ : InnerProductSpace ℝ E :=
    { inner x y := inner ℝ (ι x) (ι y)
      norm_sq_eq_re_inner x := by simp
      conj_inner_symm x y := by simp [real_inner_comm]
      add_left x y z := by simp [inner_add_left]
      smul_left x y r := by simp [inner_smul_left] }
  have _ : FiniteDimensional ℝ E := Module.Finite.of_injective ι.toLinearMap ι.injective
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨e '' (Ω : Set F), ((isLipschitzDomainWith_iff _ _).1 hΩ).1⟩
  have hOW : (Ω : Set F) = e ⁻¹' W := (e.toEquiv.preimage_image _).symm
  exact BV.isCompactOperator_toL1CLM_of_linearIsometryEquiv e.measurePreserving hOW
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith hΩ (e.lipschitzWith.isBounded_image hb))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- On a bounded open set with empty frontier (`Ω = ∅`, or `Ω = univ` when `F` is zero-dimensional),
`closure Ω ⊆ Ω` is compact, so local Rellich–Kondrachov compactness makes `BV.toL1CLM` compact. -/
private theorem isCompactOperator_toL1CLM_of_frontier_eq_empty
    (hb : IsBounded (Ω : Set F)) (hfr : frontier (Ω : Set F) = ∅) :
    IsCompactOperator (BV.toL1CLM (μ := volume) (Ω := Ω)) := by
  have hcl : closure (Ω : Set F) ⊆ (Ω : Set F) :=
    (isClopen_iff_frontier_eq_empty.mpr hfr).isClosed.closure_subset
  have hW1 : IsCompactOperator
      ((W1p.valueL (mu := volume) (Omega := Ω) (p := 1)).comp (W1p.restrictL le_rfl)) :=
    W1p.isCompactOperator_valueL_restrictL hb.isCompact_closure hcl
  have heq : W1p.valueL (mu := volume) (Omega := Ω) (p := 1) =
      (W1p.valueL (mu := volume) (Omega := Ω) (p := 1)).comp (W1p.restrictL le_rfl) := by
    ext1 u
    rw [ContinuousLinearMap.comp_apply, W1p.valueL_apply, W1p.valueL_apply]
    exact (Lp.ext (W1p.value_restrictL_ae le_rfl u)).symm
  exact BV.isCompactOperator_toL1CLM_iff.mpr (heq ▸ hW1)

/-- **Global `L¹` compactness of `BV` on bounded Lipschitz domains.** Let `F` be a
finite-dimensional real inner product space and `Ω ⊆ F` a bounded open set satisfying the intrinsic
Lipschitz-domain condition `(Ω : Set F).IsLipschitzDomain E` for some normed tangential model space
`E`. Then `BV.toL1CLM : BV volume Ω →L[ℝ] _` is a compact operator.

No inner-product, finite-dimensionality, or measurability instances are assumed on `E`: when
`frontier Ω` is empty `closure Ω ⊆ Ω` is already compact, and when `frontier Ω` is nonempty any
boundary chart embeds `E` linearly and isometrically into `F`. -/
theorem BV.isCompactOperator_toL1CLM_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F)) :
    IsCompactOperator (BV.toL1CLM (μ := volume) (Ω := Ω)) := by
  rcases (frontier (Ω : Set F)).eq_empty_or_nonempty with hfr | ⟨x₀, hx₀⟩
  · exact isCompactOperator_toL1CLM_of_frontier_eq_empty hb hfr
  obtain ⟨g, -, -, -, -, -, -⟩ := isLipschitzDomain_iff_exists_mem_normalCylinder.mp hΩ x₀ hx₀
  let e₀ : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E) := g.linearIsometryEquiv
  have hfr_cpt : IsCompact (frontier (e₀ '' (Ω : Set F))) := by
    change IsCompact (frontier (e₀.toHomeomorph '' (Ω : Set F)))
    rw [← e₀.toHomeomorph.image_frontier]
    exact (hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure).image
      e₀.continuous
  have hdom : (e₀ '' (Ω : Set F)).IsLipschitzDomain E := by
    simpa only [LinearIsometryEquiv.coe_toAffineIsometryEquiv] using
      hΩ.image e₀.toAffineIsometryEquiv
  obtain ⟨L, hL⟩ := hdom.exists_isLipschitzDomainWith hfr_cpt
  exact BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith_image e₀ hL hb

/-- **Sequential `L¹` compactness for bounded sequences in `BV` on a bounded Lipschitz domain.** -/
theorem BV.exists_subseq_tendsto_toL1_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    {u : ℕ → BV volume Ω} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : BV volume Ω) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => (u (φ k)).toL1) atTop (𝓝 v.toL1) ∧
      totalVariationOn volume Ω v ≤ liminf (fun k => totalVariationOn volume Ω (u (φ k))) atTop ∧
      ‖v‖ ≤ R :=
  BV.exists_subseq_tendsto_toL1_of_isCompactOperator
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomain hΩ hb) hu

/-- **Global total boundedness in `L¹(Ω)` on a bounded Lipschitz domain.** A family `S` of
functions on a bounded Lipschitz domain `Ω` with `∫_Ω |u| ≤ M` and `|Du|(Ω) ≤ M` (`M < ∞`) gives a
totally bounded subset of `L¹(Ω)`. -/
theorem totallyBounded_of_setLIntegral_le_of_totalVariationOn_le_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    {S : Set (F → ℝ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ≤ M)
    (hvar : ∀ u ∈ S, totalVariationOn volume Ω u ≤ M) :
    TotallyBounded {f : Lp ℝ 1 (volume.restrict (Ω : Set F)) |
      ∃ u ∈ S, f =ᵐ[volume.restrict (Ω : Set F)] u} :=
  totallyBounded_of_isCompactOperator_toL1CLM
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomain hΩ hb) hM hbdd hvar

/-- **Global relative compactness in `L¹(Ω)` on a bounded Lipschitz domain.** -/
theorem isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    {S : Set (F → ℝ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ≤ M)
    (hvar : ∀ u ∈ S, totalVariationOn volume Ω u ≤ M) :
    IsCompact (closure {f : Lp ℝ 1 (volume.restrict (Ω : Set F)) |
      ∃ u ∈ S, f =ᵐ[volume.restrict (Ω : Set F)] u}) :=
  isCompact_closure_of_isCompactOperator_toL1CLM
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomain hΩ hb) hM hbdd hvar

/-- **Global `L¹(Ω)` sequential compactness of unbundled BV sequences on a bounded Lipschitz
domain.** -/
theorem exists_subseq_tendsto_setLIntegral_enorm_sub_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    {u : ℕ → F → ℝ} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hmeas : ∀ n, AEStronglyMeasurable (u n) (volume.restrict (Ω : Set F)))
    (hbdd : ∀ n, ∫⁻ x in Ω, ‖u n x‖ₑ ≤ M)
    (hvar : ∀ n, totalVariationOn volume Ω (u n) ≤ M) :
    ∃ v : F → ℝ, MemBV volume Ω v ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => ∫⁻ x in Ω, ‖u (φ j) x - v x‖ₑ) atTop (𝓝 0) ∧
      totalVariationOn volume Ω v ≤ liminf (fun j => totalVariationOn volume Ω (u (φ j))) atTop :=
  exists_subseq_tendsto_setLIntegral_enorm_sub_of_isCompactOperator_toL1CLM
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomain hΩ hb) hM hmeas hbdd hvar

/-- **Global compactness for sets of bounded perimeter on a bounded Lipschitz domain.** Every
sequence of null-measurable sets with uniformly bounded perimeter in a bounded Lipschitz domain `Ω`
has a subsequence converging globally in measure on `Ω` to a measurable set `t` with
`perimeter volume Ω t ≤ liminf_j perimeter volume Ω (s (φ j))`. -/
theorem exists_subseq_tendsto_measure_symmDiff_inter_of_isLipschitzDomain
    (hΩ : (Ω : Set F).IsLipschitzDomain E) (hb : IsBounded (Ω : Set F))
    {s : ℕ → Set F} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hs : ∀ n, NullMeasurableSet (s n) (volume.restrict (Ω : Set F)))
    (hP : ∀ n, perimeter volume Ω (s n) ≤ M) :
    ∃ t : Set F, MeasurableSet t ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => volume ((s (φ j) ∆ t) ∩ Ω)) atTop (𝓝 0) ∧
      perimeter volume Ω t ≤ liminf (fun j => perimeter volume Ω (s (φ j))) atTop :=
  exists_subseq_tendsto_measure_symmDiff_inter_of_isCompactOperator_toL1CLM
    (BV.isCompactOperator_toL1CLM_of_isLipschitzDomain hΩ hb) hb.measure_lt_top.ne hM hs hP

/-- **Global `L¹` compactness of `BV` on an open Euclidean ball.** On any open ball
`Metric.ball c r` of a finite-dimensional real inner product space `F`, `BV.toL1CLM` is a compact
operator. -/
theorem BV.isCompactOperator_toL1CLM_ball (c : F) (r : ℝ) :
    IsCompactOperator (BV.toL1CLM (μ := volume) (Ω := ⟨ball c r, isOpen_ball⟩)) := by
  rcases le_or_gt r 0 with hr | hr
  · exact isCompactOperator_toL1CLM_of_frontier_eq_empty isBounded_ball
      (by simp [ball_eq_empty.mpr hr])
  rcases subsingleton_or_nontrivial F with hsub | _
  · exact isCompactOperator_toL1CLM_of_frontier_eq_empty isBounded_ball
      (by simp [Subsingleton.eq_univ_of_nonempty (nonempty_ball.mpr hr)])
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  let ν : F := ‖v‖⁻¹ • v
  have hν : ‖ν‖ = 1 := by simp [ν, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  let e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ) := (ℝ ∙ ν).orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2
      (LinearIsometryEquiv.toSpanUnitSingleton ν hν).symm
      (LinearIsometryEquiv.refl ℝ (ℝ ∙ ν)ᗮ))
  have hball : (e '' (⟨ball c r, isOpen_ball⟩ : Opens F)).IsLipschitzDomainWith 1 := by
    change (e '' ball c r).IsLipschitzDomainWith 1
    rw [e.image_ball]
    exact isLipschitzDomainWith_ball (e c) hr one_pos
  exact BV.isCompactOperator_toL1CLM_of_isLipschitzDomainWith_image e hball isBounded_ball

/-- **Global `L¹` compactness of `BV` on the open half-disc.** -/
theorem BV.isCompactOperator_toL1CLM_halfDisc (r : ℝ) :
    IsCompactOperator (BV.toL1CLM (μ := volume) (Ω := halfDisc r)) :=
  BV.isCompactOperator_toL1CLM_of_isLipschitzDomain (isLipschitzDomain_halfDisc r)
    (isBounded_ball.subset (by rw [coe_halfDisc]; exact inter_subset_left))

end Intrinsic

end LipschitzDomain

end TauCeti
