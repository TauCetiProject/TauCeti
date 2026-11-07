/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Normed.Module.WeakSpace.Approximation
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
import TauCeti.Analysis.Normed.Module.WeakSpace.SeqCompact
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.Lp.UniformConvex
import TauCeti.MeasureTheory.Integral.Bochner.DisjointSequence
import TauCeti.MeasureTheory.Integral.Lebesgue.DisjointSequence
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# The Dunford–Pettis weak compactness criterion in `L¹`

For a finite measure `μ`, a subset `A` of scalar `L¹(μ)` is relatively weakly compact exactly when
it is norm bounded and uniformly integrable: for every `ε > 0` there is `δ > 0` such that
`∫ x in s, ‖f x‖ ∂μ ≤ ε` for all `f ∈ A` and all measurable `s` with `μ s ≤ δ`. Here relative
weak compactness means compactness of the weak closure of `A`, and uniform integrability is
Mathlib's `MeasureTheory.UnifIntegrable` at exponent `1` for the representatives of the classes
in `A`; together with the norm bound it is `MeasureTheory.UniformIntegrable`. By
`MeasureTheory.uniformIntegrable_iff`, the latter is also the uniform tail-integral condition.

If `A` is uniformly integrable, then for each `ε > 0` a truncation level `C` exists such that each
`f ∈ A` lies within `ε` of its truncation `f · 1_{‖f‖ < C}`. The truncations lie in the image of a
ball of `L²(μ)` under the inclusion `L² → L¹`, which is weakly compact because `L²` is reflexive.
Grothendieck's lemma (`TauCeti.isCompact_closure_toWeakSpace_of_forall_exists_isCompact`) then
makes `A` relatively weakly compact.

Conversely, a relatively weakly compact set is bounded. If it were not uniformly integrable, there
would be `fₙ ∈ A` and measurable sets of measure tending to zero on which the integrals of `‖fₙ‖`
stay above some `ε > 0`. By Šmulian's theorem a subsequence converges weakly to some `f`, so the
integrals of `fₙ - f` over each fixed measurable set tend to zero. Shrinking the sets to disjoint
ones and applying the gliding hump lemma
`MeasureTheory.tendsto_setIntegral_norm_of_pairwise_disjoint` gives a contradiction.

## Main statements

* `MeasureTheory.Lp.isCompact_closure_toWeakSpace_of_uniformIntegrable`: uniformly integrable
  bounded subsets of `L¹(μ)` are relatively weakly compact.
* `MeasureTheory.Lp.uniformIntegrable_of_isCompact_closure_toWeakSpace`: relatively weakly compact
  subsets of `L¹(μ)` are bounded and uniformly integrable.
* `MeasureTheory.Lp.isCompact_closure_toWeakSpace_iff_uniformIntegrable` and
  `MeasureTheory.Lp.isCompact_closure_toWeakSpace_iff_isBounded_and_unifIntegrable`: the
  **Dunford–Pettis theorem**, with and without the bound bundled into uniform integrability.
* `MeasureTheory.Lp.isCompact_closure_toWeakSpace_iff_isBounded_and_forall_setIntegral_le`: the
  same with the uniform absolute continuity of the integrals `∫ x in s, ‖f x‖ ∂μ` spelled out.

## References

* N. Dunford and B. J. Pettis, *Linear operations on summable functions*, Trans. Amer. Math. Soc.
  **47** (1940), 323–392.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §5.2.
-/

public section

open Bornology Filter Metric Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} [RCLike 𝕜] {m : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]

/-- **Dunford–Pettis theorem**, sufficiency: for a finite measure, a bounded uniformly integrable
subset of scalar `L¹` has weakly compact closure. -/
theorem isCompact_closure_toWeakSpace_of_uniformIntegrable {A : Set (Lp 𝕜 1 μ)}
    (hA : UniformIntegrable (fun f : A ↦ (f : α → 𝕜)) 1 μ) :
    IsCompact (closure (toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' A)) := by
  refine TauCeti.isCompact_closure_toWeakSpace_of_forall_exists_isCompact fun ε hε ↦ ?_
  obtain ⟨C, hC⟩ := hA.spec one_ne_zero ENNReal.one_ne_top (ENNReal.ofReal_pos.2 hε)
  set R : ℝ := measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ * C
  set ι : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 1 μ := Measure.LpToL1CLM μ 2
  refine ⟨ι '' closedBall 0 R, ?_, fun f hf ↦ ?_⟩
  · -- The image of a ball of the reflexive space `L²` is weakly compact.
    have hcomp : toWeakSpace 𝕜 (Lp 𝕜 1 μ) ∘ ι = WeakSpace.map ι ∘ toWeakSpace 𝕜 (Lp 𝕜 2 μ) :=
      funext fun g ↦ (WeakSpace.map_apply ι g).symm
    rw [← image_comp, hcomp, image_comp]
    exact (TauCeti.isCompact_toWeakSpace_closedBall
      (surjective_inclusionInDoubleDual (by norm_num) (by norm_num)) 0 R).image
        (WeakSpace.map ι).continuous
  · -- The truncation of `f` at level `C` is bounded by `C`, hence lies in this ball.
    set s := {x | C ≤ ‖(f : α → 𝕜) x‖₊}
    have hs : MeasurableSet s :=
      measurableSet_le measurable_const (Lp.stronglyMeasurable f).measurable.nnnorm
    set g := sᶜ.indicator (f : α → 𝕜)
    have hgC (x : α) : ‖g x‖ ≤ C := by
      by_cases hx : x ∈ s
      · simp [g, hx]
      · have hgx : g x = (f : α → 𝕜) x := indicator_of_mem (mem_compl hx) _
        rw [hgx]
        exact_mod_cast (not_le.1 hx).le
    have hg : MemLp g 2 μ :=
      MemLp.of_bound ((Lp.aestronglyMeasurable f).indicator hs.compl) C (.of_forall hgC)
    refine ⟨ι (hg.toLp g), mem_image_of_mem _ ?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact Lp.norm_le_of_ae_bound C.coe_nonneg (hg.coeFn_toLp.mono fun x hx ↦ hx ▸ hgC x)
    · have hae : ⇑(f - ι (hg.toLp g)) =ᵐ[μ] s.indicator f := by
        filter_upwards [Lp.coeFn_sub f (ι (hg.toLp g)),
          Measure.LpToL1CLM_coeFn (𝕜 := 𝕜) μ 2 (hg.toLp g), hg.coeFn_toLp] with x h₁ h₂ h₃
        rw [h₁, Pi.sub_apply, h₂, h₃]
        simp [g, indicator_compl]
      rw [Lp.norm_def, eLpNorm_congr_ae hae]
      exact ENNReal.toReal_le_of_le_ofReal hε.le (hC ⟨f, hf⟩)

omit [IsFiniteMeasure μ] in
/-- The measurable hulls of sets of measure at most `(n + 1)⁻¹` have measure tending to zero. -/
theorem tendsto_measure_toMeasurable_of_le_inv {t : ℕ → Set α}
    (ht : ∀ n : ℕ, μ (t n) ≤ ((n : ℝ≥0∞) + 1)⁻¹) :
    Tendsto (fun n ↦ μ (toMeasurable μ (t n))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    refine (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
    simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun _ ↦ zero_le)
    fun n ↦ ?_
  simpa only [measure_toMeasurable] using ht n

/-- If `u n` tends weakly to `f` in `L¹`, the integrals of `u n - f` over every set tend to
zero. -/
theorem tendsto_setIntegral_sub_of_tendsto_toWeakSpace {ι : Type*} {l : Filter ι}
    {u : ι → Lp 𝕜 1 μ} {f : Lp 𝕜 1 μ}
    (hlim : Tendsto (fun n ↦ toWeakSpace 𝕜 (Lp 𝕜 1 μ) (u n)) l
      (𝓝 (toWeakSpace 𝕜 (Lp 𝕜 1 μ) f)))
    (S : Set α) :
    Tendsto (fun k ↦ ∫ x in S, ((u k : α → 𝕜) x - (f : α → 𝕜) x) ∂μ) l (𝓝 0) := by
  have hS' := TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.1 hlim
    (Set.setIntegralLp (𝕜 := 𝕜) S (measure_lt_top μ S))
  simp only [Set.setIntegralLp_apply] at hS'
  refine (tendsto_sub_nhds_zero_iff.2 hS').congr fun k ↦ ?_
  exact (integral_sub (L1.integrable_coeFn _).integrableOn
    (L1.integrable_coeFn f).integrableOn).symm

omit [IsFiniteMeasure μ] in
/-- If `g` has `L¹` mass more than `ε` on a set `S` and `f` has mass at most `ε / 2` there, then
`g - f` has mass more than `ε / 2` on `S`. -/
theorem half_lt_lintegral_enorm_sub {f g : α → 𝕜} (hf : AEStronglyMeasurable f μ) {S : Set α}
    {ε : ℝ≥0∞} (hg : ε < ∫⁻ x in S, ‖g x‖ₑ ∂μ) (hfS : ∫⁻ x in S, ‖f x‖ₑ ∂μ ≤ ε / 2) :
    ε / 2 < ∫⁻ x in S, ‖g x - f x‖ₑ ∂μ := by
  by_contra! hle
  have hsplit : ∫⁻ x in S, ‖g x‖ₑ ∂μ ≤
      ∫⁻ x in S, ‖g x - f x‖ₑ ∂μ + ∫⁻ x in S, ‖f x‖ₑ ∂μ := by
    rw [← lintegral_add_right' _ hf.enorm.restrict]
    refine lintegral_mono fun x ↦ ?_
    calc ‖g x‖ₑ = ‖(g x - f x) + f x‖ₑ := by simp
      _ ≤ ‖g x - f x‖ₑ + ‖f x‖ₑ := enorm_add_le _ _
  have := hg.trans_le (hsplit.trans (add_le_add hle hfS))
  rw [ENNReal.add_halves] at this
  exact lt_irrefl _ this

omit [IsFiniteMeasure μ] in
/-- If the integrals of `‖f j‖` over the sets `B j` tend to zero, so do the lower Lebesgue
integrals of `‖f j‖ₑ`. -/
theorem tendsto_lintegral_enorm_of_tendsto_integral_norm {ι : Type*} {l : Filter ι}
    {f : ι → α → 𝕜} {B : ι → Set α} (hf : ∀ j, Integrable (f j) μ)
    (h : Tendsto (fun j ↦ ∫ x in B j, ‖f j x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun j ↦ ∫⁻ x in B j, ‖f j x‖ₑ ∂μ) l (𝓝 0) := by
  refine (ENNReal.tendsto_ofReal h).congr' (.of_forall fun j ↦ ?_) |>.trans ?_
  · exact ofReal_integral_norm_eq_lintegral_enorm (hf j).integrableOn
  · rw [ENNReal.ofReal_zero]

/-- **Dunford–Pettis theorem**, necessity: for a finite measure, a subset of scalar `L¹` with
weakly compact closure is bounded and uniformly integrable. -/
theorem uniformIntegrable_of_isCompact_closure_toWeakSpace {A : Set (Lp 𝕜 1 μ)}
    (hA : IsCompact (closure (toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' A))) :
    UniformIntegrable (fun f : A ↦ (f : α → 𝕜)) 1 μ := by
  refine ⟨?_, ?_⟩
  swap
  · -- Weakly compact sets are bounded.
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hA.isBounded_toWeakSpace_preimage
    refine ⟨R.toNNReal, fun f ↦ ?_⟩
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      (hR f (subset_closure (s := toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' A) (mem_image_of_mem _ f.2)))
  by_contra hne
  rw [unifIntegrable_iff] at hne
  push Not at hne
  obtain ⟨ε, hε, hbad⟩ := hne
  choose i t ht hit using fun n : ℕ ↦ hbad ((n : ℝ≥0∞) + 1)⁻¹ (by simp)
  -- Replace the sets by measurable supersets of the same measure.
  set s : ℕ → Set α := fun n ↦ toMeasurable μ (t n)
  have hsm (n : ℕ) : MeasurableSet (s n) := measurableSet_toMeasurable _ _
  have hμs : Tendsto (fun n ↦ μ (s n)) atTop (𝓝 0) :=
    tendsto_measure_toMeasurable_of_le_inv ht
  have hbig (n : ℕ) : ε < ∫⁻ x in s n, ‖(i n : α → 𝕜) x‖ₑ ∂μ := by
    rw [← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _).restrict]
    exact (hit n).trans_le
      (eLpNorm_mono_measure _ (Measure.restrict_mono (subset_toMeasurable _ _) le_rfl))
  -- By Šmulian's theorem, a subsequence converges weakly.
  obtain ⟨f, τ, hτ, hlim⟩ := TauCeti.tendsto_subseq_toWeakSpace_of_isCompact_closure hA
    (u := fun n ↦ (i n : Lp 𝕜 1 μ)) fun n ↦ (i n).2
  set h : ℕ → α → 𝕜 := fun k x ↦ (i (τ k) : α → 𝕜) x - (f : α → 𝕜) x
  have hh (k : ℕ) : Integrable (h k) μ := (L1.integrable_coeFn _).sub (L1.integrable_coeFn f)
  have hset (S : Set α) (_ : MeasurableSet S) :
      Tendsto (fun k ↦ ∫ x in S, h k x ∂μ) atTop (𝓝 0) :=
    tendsto_setIntegral_sub_of_tendsto_toWeakSpace (u := fun k ↦ (i (τ k) : Lp 𝕜 1 μ)) hlim S
  -- Along the subsequence, the integrals of `‖h k‖` over the small sets stay above `ε / 2`.
  have hμsτ : Tendsto (fun k ↦ μ (s (τ k))) atTop (𝓝 0) := hμs.comp hτ.tendsto_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1
    (tendsto_setLIntegral_zero (L1.integrable_coeFn f).2.ne hμsτ) (ε / 2)
      (ENNReal.half_pos hε.ne'))
  have hbig' (k : ℕ) (hk : K ≤ k) : ε / 2 < ∫⁻ x in s (τ k), ‖h k x‖ₑ ∂μ :=
    half_lt_lintegral_enorm_sub (L1.integrable_coeFn f).1 (hbig (τ k)) (hK k hk)
  -- Shrink the small sets to disjoint ones and apply the gliding hump lemma.
  obtain ⟨σ, hσ, B, hBm, hB, -, hσB⟩ := exists_strictMono_pairwise_disjoint_lintegral_le
    (f := fun j x ↦ ‖h (j + K) x‖ₑ) (s := fun j ↦ s (τ (j + K)))
    (fun j ↦ (hh (j + K)).2.ne) (fun j ↦ hsm _)
    (hμsτ.comp (tendsto_add_atTop_nat K)) (ENNReal.half_pos (ENNReal.half_pos hε.ne').ne').ne'
  have hlow (j : ℕ) : ε / 2 / 2 < ∫⁻ x in B j, ‖h (σ j + K) x‖ₑ ∂μ := by
    by_contra! hle
    have := (hbig' (σ j + K) (by omega)).trans_le ((hσB j).trans (add_le_add_left hle _))
    rw [ENNReal.add_halves] at this
    exact lt_irrefl _ this
  have hzero := tendsto_setIntegral_norm_of_pairwise_disjoint (fun j ↦ hh (σ j + K))
    (fun S hS ↦ (hset S hS).comp ((tendsto_add_atTop_nat K).comp hσ.tendsto_atTop)) hBm hB
  have hzero' := tendsto_lintegral_enorm_of_tendsto_integral_norm (fun j ↦ hh (σ j + K)) hzero
  obtain ⟨j, hj⟩ := (ENNReal.tendsto_nhds_zero.1 hzero' (ε / 2 / 2)
    (ENNReal.half_pos (ENNReal.half_pos hε.ne').ne')).exists
  exact (hlow j).not_ge hj

/-- **Dunford–Pettis theorem.** For a finite measure, a subset of scalar `L¹` has weakly compact
closure exactly when it is uniformly integrable together with a uniform norm bound. -/
theorem isCompact_closure_toWeakSpace_iff_uniformIntegrable {A : Set (Lp 𝕜 1 μ)} :
    IsCompact (closure (toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' A)) ↔
      UniformIntegrable (fun f : A ↦ (f : α → 𝕜)) 1 μ :=
  ⟨uniformIntegrable_of_isCompact_closure_toWeakSpace,
    isCompact_closure_toWeakSpace_of_uniformIntegrable⟩

/-- **Dunford–Pettis theorem.** For a finite measure, a subset of scalar `L¹` has weakly compact
closure exactly when it is norm bounded and uniformly integrable. -/
theorem isCompact_closure_toWeakSpace_iff_isBounded_and_unifIntegrable {A : Set (Lp 𝕜 1 μ)} :
    IsCompact (closure (toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' A)) ↔
      IsBounded A ∧ UnifIntegrable (fun f : A ↦ (f : α → 𝕜)) 1 μ := by
  rw [isCompact_closure_toWeakSpace_iff_uniformIntegrable, UniformIntegrable, and_comm]
  refine and_congr_left' ⟨fun ⟨C, hC⟩ ↦ ?_, fun hA ↦ ?_⟩
  · refine isBounded_iff_forall_norm_le.2 ⟨C, fun f hf ↦ ?_⟩
    rw [Lp.norm_def]
    exact ENNReal.toReal_le_of_le_ofReal C.coe_nonneg (by simpa using hC ⟨f, hf⟩)
  · obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hA
    refine ⟨R.toNNReal, fun f ↦ ?_⟩
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hR f f.2)

/-- **Dunford–Pettis theorem**, classical form. For a finite measure, a subset `A` of scalar `L¹`
has weakly compact closure exactly when it is norm bounded and the integrals of `‖f‖` are
uniformly absolutely continuous: for every `ε > 0` there is `δ > 0` such that
`∫ x in s, ‖f x‖ ∂μ ≤ ε` for all `f ∈ A` and all measurable `s` with `μ s ≤ δ`. -/
theorem isCompact_closure_toWeakSpace_iff_isBounded_and_forall_setIntegral_le
    {A : Set (Lp 𝕜 1 μ)} :
    IsCompact (closure (toWeakSpace 𝕜 (Lp 𝕜 1 μ) '' A)) ↔
      IsBounded A ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f ∈ A, ∀ s, MeasurableSet s →
        μ s ≤ ENNReal.ofReal δ → ∫ x in s, ‖(f : α → 𝕜) x‖ ∂μ ≤ ε := by
  rw [isCompact_closure_toWeakSpace_iff_isBounded_and_unifIntegrable]
  refine and_congr_right' ?_
  -- On a measurable set, the restricted `L¹` seminorm is the integral of the norm.
  have heq (f : Lp 𝕜 1 μ) (s : Set α) :
      eLpNorm (f : α → 𝕜) 1 (μ.restrict s) = ENNReal.ofReal (∫ x in s, ‖(f : α → 𝕜) x‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f).restrict,
      ofReal_integral_norm_eq_lintegral_enorm (L1.integrable_coeFn f).integrableOn]
  rw [unifIntegrable_iff']
  constructor
  · intro hA ε hε
    obtain ⟨δ, hδ, hδA⟩ := hA (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    obtain ⟨δ', hδ'pos, hδ'⟩ : ∃ δ' : ℝ, 0 < δ' ∧ ENNReal.ofReal δ' ≤ δ := by
      rcases eq_or_ne δ ∞ with rfl | hδtop
      · exact ⟨1, one_pos, le_top⟩
      · exact ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' hδtop, (ENNReal.ofReal_toReal hδtop).le⟩
    refine ⟨δ', hδ'pos, fun f hf s hs hμs ↦ ?_⟩
    have := hδA ⟨f, hf⟩ s hs (hμs.trans hδ')
    rw [heq] at this
    exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 this
  · intro hA ε hε
    obtain ⟨ε', hε'pos, hε'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ENNReal.ofReal ε' ≤ ε := by
      rcases eq_or_ne ε ∞ with rfl | hεtop
      · exact ⟨1, one_pos, le_top⟩
      · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hεtop, (ENNReal.ofReal_toReal hεtop).le⟩
    obtain ⟨δ, hδ, hδA⟩ := hA ε' hε'pos
    refine ⟨ENNReal.ofReal δ, ENNReal.ofReal_pos.2 hδ, fun f s hs hμs ↦ ?_⟩
    rw [heq]
    exact (ENNReal.ofReal_le_ofReal (hδA f f.2 s hs hμs)).trans hε'

end MeasureTheory.Lp
