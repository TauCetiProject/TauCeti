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
  set T : ℕ → Set α := fun M ↦ ⋃ m ≥ M, B m
  have htail (n : ℕ) : ∃ M, ∫ x in T M, ‖h n x‖ ∂μ < ε / 3 :=
    ((tendsto_setIntegral_iUnion_ge_of_pairwise_disjoint (hh n).norm hBm hB).eventually
      (gt_mem_nhds (by positivity))).exists
  choose M hM using htail
  -- The next index: a large integral on its own set, small integrals on unions of earlier sets.
  have key (N K : ℕ) : ∃ n, K ≤ n ∧ ε ≤ ‖∫ x in B n, h n x ∂μ‖ ∧
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
  choose g hg_ge hg_big hg_head using key
  let σ : ℕ → ℕ := fun j ↦ Nat.rec (g 0 0) (fun _ k ↦ g (k + 1) (max (k + 1) (M k))) j
  have hσ_succ (j : ℕ) : σ (j + 1) = g (σ j + 1) (max (σ j + 1) (M (σ j))) := rfl
  have hσ : StrictMono σ := strictMono_nat_of_lt_succ fun j ↦ by
    rw [hσ_succ, Nat.lt_iff_add_one_le]
    exact (le_max_left _ _).trans (hg_ge _ _)
  have hσM (j : ℕ) : M (σ j) ≤ σ (j + 1) := by
    rw [hσ_succ]
    exact (le_max_right _ _).trans (hg_ge _ _)
  set D := ⋃ j, B (σ j)
  have hDm : MeasurableSet D := .iUnion fun j ↦ hBm _
  -- Along the chosen indices, the integrals over `D` stay away from zero.
  have hbound (j : ℕ) : ε / 3 < ‖∫ x in D, h (σ (j + 1)) x ∂μ‖ := by
    set k := j + 1
    set n := σ k
    set H := ⋃ i ∈ Finset.range k, B (σ i)
    set T' := ⋃ i, ⋃ (_ : k < i), B (σ i)
    have hHm : MeasurableSet H := Finset.measurableSet_biUnion _ fun i _ ↦ hBm _
    have hT'm : MeasurableSet T' := .iUnion fun i ↦ .iUnion fun _ ↦ hBm _
    have hDeq : D = H ∪ (B n ∪ T') := by
      ext x
      simp only [D, H, T', n, mem_union, mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨i, hi⟩
        rcases lt_trichotomy i k with hik | rfl | hik
        · exact Or.inl ⟨i, hik, hi⟩
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inr ⟨i, hik, hi⟩)
      · rintro (⟨i, -, hi⟩ | hi | ⟨i, -, hi⟩)
        exacts [⟨i, hi⟩, ⟨k, hi⟩, ⟨i, hi⟩]
    have hdisj (i i' : ℕ) (hii' : i ≠ i') : Disjoint (B (σ i)) (B (σ i')) :=
      hB (hσ.injective.ne hii')
    have hdisj₁ : Disjoint H (B n ∪ T') := by
      simp only [H, T', disjoint_union_right, disjoint_iUnion_left, disjoint_iUnion_right,
        Finset.mem_range]
      exact ⟨fun i hi ↦ hdisj i k hi.ne, fun i hi i' hi' ↦ hdisj i' i (by omega)⟩
    have hdisj₂ : Disjoint (B n) T' := by
      simp only [T', disjoint_iUnion_right]
      exact fun i hi ↦ hdisj k i hi.ne
    have hsplit : ∫ x in D, h n x ∂μ =
        ∫ x in H, h n x ∂μ + (∫ x in B n, h n x ∂μ + ∫ x in T', h n x ∂μ) := by
      rw [hDeq, setIntegral_union hdisj₁ ((hBm n).union hT'm) (hh n).integrableOn
        (hh n).integrableOn, setIntegral_union hdisj₂ hT'm (hh n).integrableOn (hh n).integrableOn]
    have hHb : ‖∫ x in H, h n x ∂μ‖ < ε / 3 := by
      have hsub : (Finset.range k).image σ ⊆ Finset.range (σ j + 1) := by
        intro m hm
        simp only [Finset.mem_image, Finset.mem_range] at hm ⊢
        obtain ⟨i, hi, rfl⟩ := hm
        exact Nat.lt_succ_of_le (hσ.monotone (by omega))
      have hhead := hg_head _ (max (σ j + 1) (M (σ j))) _ hsub
      rwa [Finset.set_biUnion_finset_image, ← hσ_succ] at hhead
    have hT'b : ‖∫ x in T', h n x ∂μ‖ < ε / 3 := by
      have hsub : T' ⊆ T (M n) := by
        simp only [T', T, iUnion_subset_iff]
        intro i hi
        exact subset_iUnion₂_of_subset (σ i)
          ((hσM k).trans (hσ.monotone (show k + 1 ≤ i by omega))) subset_rfl
      calc ‖∫ x in T', h n x ∂μ‖ ≤ ∫ x in T', ‖h n x‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ x in T (M n), ‖h n x‖ ∂μ :=
          setIntegral_mono_set (hh n).norm.integrableOn
            (Eventually.of_forall fun _ ↦ norm_nonneg _) (Eventually.of_forall hsub)
        _ < ε / 3 := hM n
    have hBb : ε ≤ ‖∫ x in B n, h n x ∂μ‖ := by
      simp only [n, k, hσ_succ]
      exact hg_big _ _
    rw [hsplit]
    set a := ∫ x in H, h n x ∂μ
    set b := ∫ x in B n, h n x ∂μ
    set c := ∫ x in T', h n x ∂μ
    have htri : ‖b‖ ≤ ‖a + (b + c)‖ + ‖a‖ + ‖c‖ :=
      calc ‖b‖ = ‖a + (b + c) - a - c‖ := by congr 1; abel
        _ ≤ ‖a + (b + c) - a‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ ‖a + (b + c)‖ + ‖a‖ + ‖c‖ := by gcongr; exact norm_sub_le _ _
    linarith
  -- But the integrals over the fixed set `D` tend to zero.
  have hlimD := ((hlim D hDm).comp (hσ.tendsto_atTop.comp (tendsto_add_atTop_nat 1))).norm
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
