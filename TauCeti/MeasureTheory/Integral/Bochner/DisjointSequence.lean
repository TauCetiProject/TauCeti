/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.RCLike.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Set

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
such disjoint sets from sets of small measure, these give the uniform integrability of weakly
convergent sequences in `L¹`, which is the hard half of the Dunford–Pettis weak compactness
criterion.

## Main statements

* `MeasureTheory.tendsto_setIntegral_iUnion_ge_of_pairwise_disjoint`: integrals over the tails
  `⋃ m ≥ M, B m` of a pairwise disjoint sequence tend to zero.
* `MeasureTheory.tendsto_setIntegral_of_pairwise_disjoint`: integrals along disjoint sets of a
  sequence whose integrals over each fixed measurable set tend to zero tend to zero.
* `MeasureTheory.tendsto_setIntegral_norm_of_pairwise_disjoint`: the same for the integrals of the
  norm, for real or complex functions.

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
/-- If `H`, `S` and `T` are disjoint, with `S` and `T` measurable, then the integral of `f` over `S`
is bounded by its integrals over `H ∪ (S ∪ T)`, `H` and `T`. -/
theorem norm_setIntegral_le_add_of_disjoint {f : α → E} (hf : Integrable f μ) {H S T : Set α}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hHST : Disjoint H (S ∪ T))
    (hST : Disjoint S T) :
    ‖∫ x in S, f x ∂μ‖ ≤
      ‖∫ x in H ∪ (S ∪ T), f x ∂μ‖ + ‖∫ x in H, f x ∂μ‖ + ‖∫ x in T, f x ∂μ‖ := by
  rw [setIntegral_union hHST (hS.union hT) hf.integrableOn hf.integrableOn,
    setIntegral_union hST hT hf.integrableOn hf.integrableOn]
  set a := ∫ x in H, f x ∂μ
  set b := ∫ x in S, f x ∂μ
  set c := ∫ x in T, f x ∂μ
  calc ‖b‖ = ‖a + (b + c) - a - c‖ := by congr 1; abel
    _ ≤ ‖a + (b + c) - a‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ ‖a + (b + c)‖ + ‖a‖ + ‖c‖ := by gcongr; exact norm_sub_le _ _

/-- For a strictly monotone `σ` and pairwise disjoint sets `B`, the union `⋃ j, B (σ j)` splits
into the earlier sets, the `k`-th set and the later sets, and these three pieces are disjoint. -/
private theorem iUnion_comp_eq_union_of_pairwise_disjoint {B : ℕ → Set α}
    (hB : Pairwise (Disjoint on B)) {σ : ℕ → ℕ} (hσ : StrictMono σ) (k : ℕ) :
    ⋃ j, B (σ j) = (⋃ i ∈ Finset.range k, B (σ i)) ∪ (B (σ k) ∪ ⋃ i, ⋃ (_ : k < i), B (σ i)) ∧
    Disjoint (⋃ i ∈ Finset.range k, B (σ i)) (B (σ k) ∪ ⋃ i, ⋃ (_ : k < i), B (σ i)) ∧
    Disjoint (B (σ k)) (⋃ i, ⋃ (_ : k < i), B (σ i)) := by
  have hdisj (i i' : ℕ) (hii' : i ≠ i') : Disjoint (B (σ i)) (B (σ i')) :=
    hB (hσ.injective.ne hii')
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [mem_union, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨i, hi⟩
      rcases lt_trichotomy i k with hik | rfl | hik
      · exact Or.inl ⟨i, hik, hi⟩
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr ⟨i, hik, hi⟩)
    · rintro (⟨i, -, hi⟩ | hi | ⟨i, -, hi⟩)
      exacts [⟨i, hi⟩, ⟨k, hi⟩, ⟨i, hi⟩]
  · simp only [disjoint_union_right, disjoint_iUnion_left, disjoint_iUnion_right,
      Finset.mem_range]
    exact ⟨fun i hi ↦ hdisj i k hi.ne, fun i hi i' hi' ↦ hdisj i' i (by omega)⟩
  · simp only [disjoint_iUnion_right]
    exact fun i hi ↦ hdisj k i hi.ne

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
    (hBm : ∀ n, MeasurableSet (B n)) (hB : Pairwise (Disjoint on B)) {σ : ℕ → ℕ}
    (hσ : StrictMono σ) {ε : ℝ} {k N L : ℕ}
    (hhead : ∀ F ⊆ Finset.range N, ‖∫ x in ⋃ m ∈ F, B m, f x ∂μ‖ < ε / 3)
    (hN : ∀ i < k, σ i < N) (hbig : ε ≤ ‖∫ x in B (σ k), f x ∂μ‖)
    (htail : ∫ x in ⋃ m ≥ L, B m, ‖f x‖ ∂μ < ε / 3) (hL : ∀ i, k < i → L ≤ σ i) :
    ε / 3 < ‖∫ x in ⋃ j, B (σ j), f x ∂μ‖ := by
  obtain ⟨hDeq, hd₁, hd₂⟩ := iUnion_comp_eq_union_of_pairwise_disjoint hB hσ k
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
  have hsplit := norm_setIntegral_le_add_of_disjoint hf (hBm (σ k)) hT'm hd₁ hd₂
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
    refine lt_norm_setIntegral_iUnion_comp (hh _) hBm hB hσ (k := j + 1) (N := σ j + 1)
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

end RCLike

end MeasureTheory
