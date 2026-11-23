/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.RCLike.Basic
import TauCeti.Data.Set.Lattice
import TauCeti.MeasureTheory.Function.L1Space.HasFiniteIntegral
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.Lebesgue.DisjointSequence

/-!
# Set integrals of a sequence along disjoint sets

Let `h n` be integrable functions such that `∫ x in s, h n x ∂μ → 0` for every measurable set `s`,
as happens for a weakly null sequence in `L¹`. If the measurable sets `B n` are pairwise
disjoint, then also `∫ x in B n, h n x ∂μ → 0`, although the set of integration moves with `n`.
For real or complex functions the conclusion improves to `∫ x in B n, ‖h n x‖ ∂μ → 0`, by
splitting `B n` into the sets where the real and imaginary parts of `h n` have a fixed sign.

The proof is a gliding hump argument. If the conclusion fails, choose indices `n₀ < n₁ < ⋯` along
which `‖∫ x in B nⱼ, h nⱼ x ∂μ‖ ≥ ε`, the integral of `h nⱼ` over the union of the earlier sets
`B nᵢ` is small, and the integral of `‖h nⱼ‖` over all later sets `B m` is small. Then the
integrals of `h nⱼ` over the single set `⋃ j, B nⱼ` stay away from zero.

Together with `MeasureTheory.exists_strictMono_pairwise_disjoint_lintegral_le`, which produces
such disjoint sets from sets of small measure, this shows that the lower integrals of `‖h n‖ₑ`
over the `n`-th set of any sequence of measurable sets of measure tending to zero tend to zero.
This gives the uniform integrability of weakly convergent sequences in `L¹`, which is the hard
half of the Dunford–Pettis weak compactness criterion.

More generally, a sequence of real or complex integrable functions whose integrals over every
measurable set form Cauchy sequences, as happens for a weakly Cauchy sequence in `L¹`, is
uniformly integrable. If the integrals of `‖h (i n)‖` over sets `s n` of measure tending to zero
stay above `ε`, either infinitely many indices `i n` lie below some bound, contradicting the
uniform integrability of finitely many functions, or the differences `h (i (ψ k)) - h k` along a
suitable subsequence have vanishing integrals over every fixed set but not over the sets
`s (ψ k)`. This is the key step of the weak sequential completeness of `L¹`.

## Main statements

* `MeasureTheory.tendsto_setIntegral_iUnion_ge_of_pairwise_disjoint`: integrals over the tails
  `⋃ m ≥ M, B m` of a pairwise disjoint sequence tend to zero.
* `MeasureTheory.tendsto_setIntegral_of_pairwise_disjoint`: integrals along disjoint sets of a
  sequence whose integrals over each fixed measurable set tend to zero tend to zero.
* `MeasureTheory.tendsto_setIntegral_norm_of_pairwise_disjoint`: the same for the integrals of the
  norm, for real or complex functions.
* `MeasureTheory.tendsto_setLIntegral_enorm_of_tendsto_setIntegral`: the lower integrals of
  `‖h n‖ₑ` over sets of measure tending to zero tend to zero, for real or complex functions.
* `MeasureTheory.unifIntegrable_of_forall_cauchySeq_setIntegral`: a sequence of real or complex
  integrable functions whose integrals over every measurable set are Cauchy is uniformly
  integrable.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §5.2, for the role of these
  statements in the Dunford–Pettis theorem.
-/

public section

open Filter Function Set Topology
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

section Bochner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integrals of an integrable function over the tails `⋃ m ≥ M, B m` of a pairwise
disjoint sequence of measurable sets tend to zero. -/
theorem tendsto_setIntegral_iUnion_ge_of_pairwise_disjoint {g : α → E} (hg : Integrable g μ)
    {B : ℕ → Set α} (hBm : ∀ n, MeasurableSet (B n)) (hB : Pairwise (Disjoint on B)) :
    Tendsto (fun M ↦ ∫ x in ⋃ m ≥ M, B m, g x ∂μ) atTop (𝓝 0) := by
  have hanti : Antitone fun M ↦ ⋃ m ≥ M, B m := fun M M' hMM' x hx ↦ by
    simp only [mem_iUnion] at hx ⊢
    obtain ⟨m, hm, hx⟩ := hx
    exact ⟨m, hMM'.trans hm, hx⟩
  have hinter : ⋂ M, ⋃ m ≥ M, B m = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx ↦ ?_
    simp only [mem_iInter, mem_iUnion, exists_prop] at hx
    obtain ⟨m, -, hxm⟩ := hx 0
    obtain ⟨k, hk, hxk⟩ := hx (m + 1)
    exact disjoint_left.1 (hB (by omega : m ≠ k)) hxm hxk
  have hlim := tendsto_setIntegral_of_antitone (μ := μ) (f := g)
    (fun M ↦ .iUnion fun m ↦ .iUnion fun _ ↦ hBm m) hanti ⟨0, hg.integrableOn⟩
  rwa [hinter, Measure.restrict_empty, integral_zero_measure] at hlim

/-- The step of the gliding hump argument: if the integrals of `h n` over each fixed measurable set
tend to zero and `‖∫ x in B n, h n x ∂μ‖ ≥ ε` for infinitely many `n`, then for any `N` and `K`
there is an `n ≥ K` with a large integral over `B n` and small integrals over all unions of the
first `N` sets. -/
private theorem exists_large_integral_small_unions {h : ℕ → α → E}
    (hlim : ∀ s, MeasurableSet s → Tendsto (fun n ↦ ∫ x in s, h n x ∂μ) atTop (𝓝 0))
    {B : ℕ → Set α} (hBm : ∀ n, MeasurableSet (B n)) {ε : ℝ} (hε : 0 < ε)
    (hfreq : ∃ᶠ n in atTop, ε ≤ ‖∫ x in B n, h n x ∂μ‖) (N K : ℕ) :
    ∃ n, K ≤ n ∧ ε ≤ ‖∫ x in B n, h n x ∂μ‖ ∧
      ∀ F ⊆ Finset.range N, ‖∫ x in ⋃ m ∈ F, B m, h n x ∂μ‖ < ε / 3 := by
  have hev : ∀ᶠ n in atTop, ∀ F ∈ (Finset.range N).powerset,
      ‖∫ x in ⋃ m ∈ F, B m, h n x ∂μ‖ < ε / 3 := by
    rw [eventually_all_finset]
    intro F _
    have hF := (hlim _ (Finset.measurableSet_biUnion F fun m _ ↦ hBm m)).norm
    rw [norm_zero] at hF
    exact hF.eventually (gt_mem_nhds (by positivity))
  obtain ⟨n, hn, hev, hK⟩ := (hfreq.and_eventually (hev.and (eventually_ge_atTop K))).exists
  exact ⟨n, hK, hn, fun F hF ↦ hev F (Finset.mem_powerset.2 hF)⟩

/-- The estimate of the gliding hump argument: if `f` has a large integral over `B (σ k)`, small
integrals over unions of the sets `B m` with `m < N`, and small integral of `‖f‖` over the later
sets, then its integral over `⋃ j, B (σ j)` is not small. -/
private theorem lt_norm_setIntegral_iUnion_comp {f : α → E} (hf : Integrable f μ) {B : ℕ → Set α}
    (hBm : ∀ n, MeasurableSet (B n)) {σ : ℕ → ℕ}
    (hBσ : Pairwise (Disjoint on fun i ↦ B (σ i))) {ε : ℝ} {k N L : ℕ}
    (hhead : ∀ F ⊆ Finset.range N, ‖∫ x in ⋃ m ∈ F, B m, f x ∂μ‖ < ε / 3)
    (hN : ∀ i < k, σ i < N) (hbig : ε ≤ ‖∫ x in B (σ k), f x ∂μ‖)
    (htail : ∫ x in ⋃ m ≥ L, B m, ‖f x‖ ∂μ < ε / 3) (hL : ∀ i, k < i → L ≤ σ i) :
    ε / 3 < ‖∫ x in ⋃ j, B (σ j), f x ∂μ‖ := by
  obtain ⟨hDeq, hd₁, hd₂⟩ := TauCeti.iUnion_eq_union_of_pairwise_disjoint hBσ k
  have hT'm : MeasurableSet (⋃ i, ⋃ (_ : k < i), B (σ i)) :=
    .iUnion fun i ↦ .iUnion fun _ ↦ hBm _
  have hHb : ‖∫ x in ⋃ i ∈ Finset.range k, B (σ i), f x ∂μ‖ < ε / 3 := by
    have hsub : (Finset.range k).image σ ⊆ Finset.range N := fun m hm ↦ by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hm
      exact Finset.mem_range.2 (hN i (Finset.mem_range.1 hi))
    have hhead' := hhead _ hsub
    rwa [Finset.set_biUnion_finset_image] at hhead'
  have hT'b : ‖∫ x in ⋃ i, ⋃ (_ : k < i), B (σ i), f x ∂μ‖ < ε / 3 := by
    have hsub : (⋃ i, ⋃ (_ : k < i), B (σ i)) ⊆ ⋃ m ≥ L, B m := by
      simp only [iUnion_subset_iff]
      intro i hi
      exact subset_iUnion₂_of_subset (σ i) (hL i hi) subset_rfl
    calc ‖∫ x in ⋃ i, ⋃ (_ : k < i), B (σ i), f x ∂μ‖
        ≤ ∫ x in ⋃ i, ⋃ (_ : k < i), B (σ i), ‖f x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in ⋃ m ≥ L, B m, ‖f x‖ ∂μ :=
        setIntegral_mono_set hf.norm.integrableOn (Eventually.of_forall fun _ ↦ norm_nonneg _)
          (Eventually.of_forall hsub)
      _ < ε / 3 := htail
  have hsplit := norm_setIntegral_le_add_of_disjoint hf.integrableOn (hBm (σ k)) hT'm hd₁ hd₂
  rw [← hDeq] at hsplit
  linarith

/-- If the integrals of `h n` over every fixed measurable set tend to zero, then so do the
integrals of `h n` over the `n`-th set of a pairwise disjoint sequence of measurable sets. -/
theorem tendsto_setIntegral_of_pairwise_disjoint {h : ℕ → α → E} (hh : ∀ n, Integrable (h n) μ)
    (hlim : ∀ s, MeasurableSet s → Tendsto (fun n ↦ ∫ x in s, h n x ∂μ) atTop (𝓝 0))
    {B : ℕ → Set α} (hBm : ∀ n, MeasurableSet (B n)) (hB : Pairwise (Disjoint on B)) :
    Tendsto (fun n ↦ ∫ x in B n, h n x ∂μ) atTop (𝓝 0) := by
  by_contra hne
  rw [Metric.tendsto_nhds] at hne
  push Not at hne
  obtain ⟨ε, hε, hfreq⟩ := hne
  simp only [dist_zero_right] at hfreq
  -- Each `‖h n‖` has small integral over a late enough tail `⋃ m ≥ M, B m`.
  have htail (n : ℕ) : ∃ M, ∫ x in ⋃ m ≥ M, B m, ‖h n x‖ ∂μ < ε / 3 :=
    ((tendsto_setIntegral_iUnion_ge_of_pairwise_disjoint (hh n).norm hBm hB).eventually
      (gt_mem_nhds (by positivity))).exists
  choose M hM using htail
  -- The next index: a large integral on its own set, small integrals on unions of earlier sets.
  choose g hg_ge hg_big hg_head using exists_large_integral_small_unions hlim hBm hε hfreq
  let σ : ℕ → ℕ := fun j ↦ Nat.rec (g 0 0) (fun _ k ↦ g (k + 1) (max (k + 1) (M k))) j
  have hσ_succ (j : ℕ) : σ (j + 1) = g (σ j + 1) (max (σ j + 1) (M (σ j))) := rfl
  have hσ : StrictMono σ := strictMono_nat_of_lt_succ fun j ↦ by
    rw [hσ_succ, Nat.lt_iff_add_one_le]
    exact (le_max_left _ _).trans (hg_ge _ _)
  have hσM (j : ℕ) : M (σ j) ≤ σ (j + 1) := by
    rw [hσ_succ]
    exact (le_max_right _ _).trans (hg_ge _ _)
  -- Along the chosen indices, the integrals over `⋃ j, B (σ j)` stay away from zero.
  have hbound (j : ℕ) : ε / 3 < ‖∫ x in ⋃ i, B (σ i), h (σ (j + 1)) x ∂μ‖ := by
    refine lt_norm_setIntegral_iUnion_comp (hh _) hBm (hB.comp_of_injective hσ.injective)
      (k := j + 1) (N := σ j + 1)
      (L := M (σ (j + 1))) ?_ (fun i hi ↦ Nat.lt_succ_of_le (hσ.monotone (by omega))) ?_ (hM _)
      fun i hi ↦ (hσM (j + 1)).trans (hσ.monotone hi)
    · rw [hσ_succ]
      exact hg_head _ _
    · rw [hσ_succ]
      exact hg_big _ _
  -- But the integrals over the fixed set `⋃ j, B (σ j)` tend to zero.
  have hDm : MeasurableSet (⋃ j, B (σ j)) := .iUnion fun j ↦ hBm _
  have hlimD := ((hlim _ hDm).comp (hσ.tendsto_atTop.comp (tendsto_add_atTop_nat 1))).norm
  rw [norm_zero] at hlimD
  obtain ⟨j, hj⟩ := (hlimD.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).exists
  exact (hbound j).not_gt hj

end Bochner

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- If the integrals of the real or complex functions `h n` over every fixed measurable set tend to
zero, then the integrals of `‖h n‖` over the `n`-th set of a pairwise disjoint sequence of
measurable sets tend to zero. -/
theorem tendsto_setIntegral_norm_of_pairwise_disjoint {h : ℕ → α → 𝕜}
    (hh : ∀ n, Integrable (h n) μ)
    (hlim : ∀ s, MeasurableSet s → Tendsto (fun n ↦ ∫ x in s, h n x ∂μ) atTop (𝓝 0))
    {B : ℕ → Set α} (hBm : ∀ n, MeasurableSet (B n)) (hB : Pairwise (Disjoint on B)) :
    Tendsto (fun n ↦ ∫ x in B n, ‖h n x‖ ∂μ) atTop (𝓝 0) := by
  -- Pass to strongly measurable representatives, so that sign conditions define measurable sets.
  set h' : ℕ → α → 𝕜 := fun n ↦ (hh n).aestronglyMeasurable.mk (h n)
  have hae (n : ℕ) : h n =ᵐ[μ] h' n := (hh n).aestronglyMeasurable.ae_eq_mk
  have hh' (n : ℕ) : Integrable (h' n) μ := (hh n).congr (hae n)
  have hm (n : ℕ) : Measurable (h' n) :=
    (hh n).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hset (n : ℕ) (s : Set α) : ∫ x in s, h n x ∂μ = ∫ x in s, h' n x ∂μ :=
    integral_congr_ae (ae_restrict_of_ae (hae n))
  have hset_norm (n : ℕ) (s : Set α) : ∫ x in s, ‖h n x‖ ∂μ = ∫ x in s, ‖h' n x‖ ∂μ :=
    integral_congr_ae (ae_restrict_of_ae ((hae n).mono fun x hx ↦ by simp only [hx]))
  simp only [hset_norm]
  replace hlim (s : Set α) (hs : MeasurableSet s) :
      Tendsto (fun n ↦ ∫ x in s, h' n x ∂μ) atTop (𝓝 0) := by
    simpa only [hset] using hlim s hs
  -- Integrals of `h'` along subsets of the `B n` tend to zero, hence so do their real and
  -- imaginary parts.
  have hsub (S : ℕ → Set α) (hSm : ∀ n, MeasurableSet (S n)) (hSB : ∀ n, S n ⊆ B n) :
      Tendsto (fun n ↦ ∫ x in S n, h' n x ∂μ) atTop (𝓝 0) :=
    tendsto_setIntegral_of_pairwise_disjoint hh' hlim hSm
      (hB.mono fun i j hij ↦ hij.mono (hSB i) (hSB j))
  have hre (S : ℕ → Set α) (hSm : ∀ n, MeasurableSet (S n)) (hSB : ∀ n, S n ⊆ B n) :
      Tendsto (fun n ↦ ∫ x in S n, RCLike.re (h' n x) ∂μ) atTop (𝓝 0) := by
    have hlim' := (RCLike.continuous_re.tendsto 0).comp (hsub S hSm hSB)
    rw [map_zero] at hlim'
    exact hlim'.congr fun n ↦ (integral_re (hh' n).integrableOn).symm
  have him (S : ℕ → Set α) (hSm : ∀ n, MeasurableSet (S n)) (hSB : ∀ n, S n ⊆ B n) :
      Tendsto (fun n ↦ ∫ x in S n, RCLike.im (h' n x) ∂μ) atTop (𝓝 0) := by
    have hlim' := (RCLike.continuous_im.tendsto 0).comp (hsub S hSm hSB)
    rw [map_zero] at hlim'
    exact hlim'.congr fun n ↦ (integral_im (hh' n).integrableOn).symm
  have hPm (n : ℕ) : MeasurableSet {x | 0 ≤ RCLike.re (h' n x)} :=
    measurableSet_le measurable_const (RCLike.continuous_re.measurable.comp (hm n))
  have hQm (n : ℕ) : MeasurableSet {x | 0 ≤ RCLike.im (h' n x)} :=
    measurableSet_le measurable_const (RCLike.continuous_im.measurable.comp (hm n))
  -- Bound the norm by the absolute values of the real and imaginary parts, and split by sign.
  have hle (n : ℕ) : ∫ x in B n, ‖h' n x‖ ∂μ ≤
      (∫ x in B n ∩ {x | 0 ≤ RCLike.re (h' n x)}, RCLike.re (h' n x) ∂μ -
        ∫ x in B n \ {x | 0 ≤ RCLike.re (h' n x)}, RCLike.re (h' n x) ∂μ) +
      (∫ x in B n ∩ {x | 0 ≤ RCLike.im (h' n x)}, RCLike.im (h' n x) ∂μ -
        ∫ x in B n \ {x | 0 ≤ RCLike.im (h' n x)}, RCLike.im (h' n x) ∂μ) := by
    rw [← TauCeti.setIntegral_abs_eq_sub (hh' n).re.integrableOn,
      ← TauCeti.setIntegral_abs_eq_sub (hh' n).im.integrableOn,
      ← integral_add (hh' n).re.abs.integrableOn (hh' n).im.abs.integrableOn]
    exact setIntegral_mono (hh' n).norm.integrableOn
      ((hh' n).re.abs.add (hh' n).im.abs).integrableOn fun x ↦ RCLike.norm_le_abs_re_add_abs_im _
  have hsum := ((hre _ (fun n ↦ (hBm n).inter (hPm n)) fun n ↦ inter_subset_left).sub
      (hre _ (fun n ↦ (hBm n).diff (hPm n)) fun n ↦ sdiff_subset)).add
    ((him _ (fun n ↦ (hBm n).inter (hQm n)) fun n ↦ inter_subset_left).sub
      (him _ (fun n ↦ (hBm n).diff (hQm n)) fun n ↦ sdiff_subset))
  rw [sub_zero, add_zero] at hsum
  exact squeeze_zero (fun n ↦ integral_nonneg fun x ↦ norm_nonneg _) hle hsum

/-- If the integrals of the real or complex functions `h n` over every fixed measurable set tend to
zero, then the lower integrals of `‖h n‖ₑ` over the `n`-th set of any sequence of measurable sets
whose measures tend to zero tend to zero. -/
theorem tendsto_setLIntegral_enorm_of_tendsto_setIntegral {h : ℕ → α → 𝕜}
    (hh : ∀ n, Integrable (h n) μ)
    (hlim : ∀ s, MeasurableSet s → Tendsto (fun n ↦ ∫ x in s, h n x ∂μ) atTop (𝓝 0))
    {s : ℕ → Set α} (hsm : ∀ n, MeasurableSet (s n)) (hs : Tendsto (fun n ↦ μ (s n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫⁻ x in s n, ‖h n x‖ₑ ∂μ) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  by_contra hne
  -- Along a subsequence the integrals stay above `ε`.
  obtain ⟨φ, hφ, hbig⟩ := extraction_of_frequently_atTop (not_eventually.1 hne)
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  -- Shrink the sets to disjoint ones, losing at most `ε / 2` of the integrals.
  obtain ⟨σ, hσ, B, hBm, hB, -, hσB⟩ := exists_strictMono_pairwise_disjoint_lintegral_le
    (f := fun k x ↦ ‖h (φ k) x‖ₑ) (s := fun k ↦ s (φ k)) (fun k ↦ (hh (φ k)).2.ne)
    (fun k ↦ hsm (φ k)) (hs.comp hφ.tendsto_atTop) hε2
  -- Along disjoint sets, the integrals tend to zero by the gliding hump lemma.
  have hzero := TauCeti.MeasureTheory.tendsto_lintegral_enorm_of_tendsto_integral_norm
    (.of_forall fun j ↦ (hh (φ (σ j))).integrableOn)
    (tendsto_setIntegral_norm_of_pairwise_disjoint (fun j ↦ hh (φ (σ j)))
      (fun S hS ↦ (hlim S hS).comp (hφ.comp hσ).tendsto_atTop) hBm hB)
  obtain ⟨j, hj⟩ := (ENNReal.tendsto_nhds_zero.1 hzero (ε / 2) (pos_iff_ne_zero.2 hε2)).exists
  refine hbig (σ j) ((hσB j).trans ?_)
  calc ∫⁻ x in B j, ‖h (φ (σ j)) x‖ₑ ∂μ + ε / 2 ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves ε

/-- A sequence of real or complex integrable functions whose integrals over every measurable set
form Cauchy sequences, for instance a weakly Cauchy sequence in `L¹`, is uniformly integrable. -/
theorem unifIntegrable_of_forall_cauchySeq_setIntegral {h : ℕ → α → 𝕜}
    (hh : ∀ n, Integrable (h n) μ)
    (hcauchy : ∀ s, MeasurableSet s → CauchySeq fun n ↦ ∫ x in s, h n x ∂μ) :
    UnifIntegrable h 1 μ := by
  by_contra hne
  rw [unifIntegrable_iff'] at hne
  push Not at hne
  obtain ⟨ε, hε, hbad⟩ := hne
  choose i s hsm hμs hbig using fun n : ℕ ↦
    hbad (n : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
  have hs : Tendsto (fun n ↦ μ (s n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ENNReal.tendsto_inv_nat_nhds_zero
      (fun _ ↦ zero_le) hμs
  replace hbig (n : ℕ) : ε < ∫⁻ x in s n, ‖h (i n) x‖ₑ ∂μ := by
    rw [← eLpNorm_one_eq_lintegral_eNorm (hh _).aestronglyMeasurable.restrict]
    exact hbig n
  -- The integrals of each fixed `‖h m‖ₑ` over the sets `s n` tend to zero.
  have hfix (m : ℕ) : Tendsto (fun n ↦ ∫⁻ x in s n, ‖h m x‖ₑ ∂μ) atTop (𝓝 0) :=
    tendsto_setLIntegral_zero (hh m).2.ne hs
  by_cases hi : Tendsto i atTop atTop
  · -- Pair `h (i (ψ k))` with an earlier term `h k` whose integral over `s (ψ k)` is small.
    obtain ⟨ψ, hψ, hψs⟩ := extraction_forall_of_eventually fun k ↦
      ENNReal.tendsto_nhds_zero.1 (hfix k) (ε / 2) (ENNReal.half_pos hε.ne')
    set g : ℕ → α → 𝕜 := fun k x ↦ h (i (ψ k)) x - h k x
    have hg (k : ℕ) : Integrable (g k) μ := (hh _).sub (hh _)
    -- The differences have vanishing integrals over every fixed set, since both indices grow.
    have hset (S : Set α) (hS : MeasurableSet S) :
        Tendsto (fun k ↦ ∫ x in S, g k x ∂μ) atTop (𝓝 0) := by
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (hcauchy S hS)
      have hdiff := (hL.comp (hi.comp hψ.tendsto_atTop)).sub hL
      rw [sub_self] at hdiff
      exact hdiff.congr fun k ↦ (integral_sub (hh _).integrableOn (hh _).integrableOn).symm
    have hzero := tendsto_setLIntegral_enorm_of_tendsto_setIntegral hg hset (fun k ↦ hsm (ψ k))
      (hs.comp hψ.tendsto_atTop)
    obtain ⟨k, hk⟩ := (ENNReal.tendsto_nhds_zero.1 hzero (ε / 2) (ENNReal.half_pos hε.ne')).exists
    refine (hbig (ψ k)).not_ge ?_
    calc ∫⁻ x in s (ψ k), ‖h (i (ψ k)) x‖ₑ ∂μ
        ≤ ∫⁻ x in s (ψ k), ‖g k x‖ₑ ∂μ + ∫⁻ x in s (ψ k), ‖h k x‖ₑ ∂μ :=
          TauCeti.MeasureTheory.lintegral_enorm_le_lintegral_enorm_sub_add
            (hh k).aestronglyMeasurable.restrict _
      _ ≤ ε / 2 + ε / 2 := add_le_add hk (hψs k)
      _ = ε := ENNReal.add_halves ε
  · -- Infinitely many of the indices `i n` lie below some `N`, and the finitely many functions
    -- `h m` with `m < N` have small integrals over `s n` for large `n`.
    rw [tendsto_atTop_atTop] at hi
    push Not at hi
    obtain ⟨N, hN⟩ := hi
    obtain ⟨a, ha⟩ := eventually_atTop.1 ((eventually_all_finset (Finset.range N)).2
      fun m _ ↦ ENNReal.tendsto_nhds_zero.1 (hfix m) ε hε)
    obtain ⟨n, hn, hiN⟩ := hN a
    exact (hbig n).not_ge (ha n hn (i n) (Finset.mem_range.2 hiN))

end RCLike

end MeasureTheory
