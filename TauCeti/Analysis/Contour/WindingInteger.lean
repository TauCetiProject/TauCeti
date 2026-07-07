/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Continuous argument lift for a point-avoiding curve

For a continuous curve `γ : ℝ → ℂ` avoiding a point `w`, the function `t ↦ γ t - w` is continuous
and nowhere zero, so it admits a continuous *argument lift* `θ : ℝ → ℝ` with
`γ t - w = ‖γ t - w‖ · exp (i θ t)`. This is the geometric heart of the integer-valuedness of the
generalized winding number: for a closed curve the total argument change `θ 1 - θ 0` is an integer
multiple of `2π`.

The lift is built on a uniform partition `0 = s₀ < ⋯ < s_N = 1` fine enough that each segment
`(γ t - w) / (γ (s j) - w)` lands in a rotated slit plane `ball (1, 1/2) ⊆ slitPlane`, where
`Complex.log` extracts a single-valued argument; the segment contributions telescope to the global
lift. Alongside it we prove the per-segment fundamental theorem of calculus for `1 / (γ - w)`.

## Main results

* `TauCeti.Contour.exists_continuous_arg_lift_with_partition` — a continuous argument lift for a
  curve continuous on `[0, 1]` and avoiding `w`, together with its partition witness.
* `TauCeti.Contour.segment_log_FTC` — on a segment where `γ` avoids `w` and stays in a slit plane,
  `∫ γ' / (γ - w) = log ((γ b - w) / (γ a - w))`.
* `TauCeti.Contour.segRatio` and its evaluation lemmas — the segment-ratio building block used to
  assemble the index integral downstream.

## Provenance

Adapted from `WindingInteger.lean` in the AINTLIB `LeanModularForms` development. Prerequisite for
the integer-valuedness and local constancy of the generalized winding number, hence for the homology
Cauchy theorem (roadmap `homologyCauchyTheorem`) and the generalized residue theorem.
-/

public section

noncomputable section

open Set

namespace TauCeti.Contour


/-! ### Partition lemma -/

/-- For a continuous function `γ : ℝ → ℂ` avoiding `w` on a compact interval, there
exists `δ > 0` such that on any sub-interval of length `< δ`, `γ` varies by less than
half the minimum distance to `w`. This gives a partition where each segment of
`γ - w` lies in a ball avoiding `0`. -/
private theorem exists_uniform_modulus_avoiding {γ : ℝ → ℂ} {w : ℂ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∃ δ' > 0, ∃ ρ > 0, (∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ ‖γ t - w‖) ∧
      ∀ t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → |t - s| < δ' →
        ‖γ t - γ s‖ < ρ / 2 := by
  -- Step 1: get a positive lower bound ρ for ‖γ t - w‖
  have h_image_compact : IsCompact (γ '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hγ
  have h_image_nonempty : (γ '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨γ 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩
  have h_w_not_mem : w ∉ γ '' Icc (0 : ℝ) 1 :=
    fun ⟨t, ht, heq⟩ ↦ h_avoid t ht heq
  have hρ_pos : 0 < Metric.infDist w (γ '' Icc (0 : ℝ) 1) :=
    (h_image_compact.isClosed.notMem_iff_infDist_pos h_image_nonempty).mp h_w_not_mem
  set ρ := Metric.infDist w (γ '' Icc (0 : ℝ) 1)
  have h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ ‖γ t - w‖ := by
    intro t ht
    have h1 : Metric.infDist w (γ '' Icc (0 : ℝ) 1) ≤ dist w (γ t) :=
      Metric.infDist_le_dist_of_mem (mem_image_of_mem γ ht)
    rwa [Complex.dist_eq, norm_sub_rev] at h1
  -- Step 2: by uniform continuity on compact, get δ' for variation < ρ/2
  have h_unif : UniformContinuousOn γ (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hγ
  rw [Metric.uniformContinuousOn_iff] at h_unif
  obtain ⟨δ', hδ'_pos, h_unif⟩ := h_unif (ρ / 2) (by linarith)
  refine ⟨δ', hδ'_pos, ρ, hρ_pos, h_dist_lb, ?_⟩
  intro t s ht hs h_dist
  rw [← Complex.dist_eq]
  exact h_unif t ht s hs (by rwa [Real.dist_eq])

/-! ### Slit-plane containment for small balls -/

/-- The closed ball of radius `1/2` around `1` is contained in `Complex.slitPlane`. -/
private theorem mem_slitPlane_of_ball_one (z : ℂ) (hz : ‖z - 1‖ < 1 / 2) :
    z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h_re : |z.re - 1| < 1 / 2 :=
    (by simpa using Complex.abs_re_le_norm (z - 1) : |z.re - 1| ≤ ‖z - 1‖).trans_lt hz
  rw [abs_sub_lt_iff] at h_re; linarith

/-! ### W-1 helpers (deferred main theorem)

The main `exists_continuous_arg_lift_with_partition` theorem is deferred — it uses
the telescoping-sum approach with `Finset.sum` over `N` partition segments,
each contributing `Im(log(segRatio j t))` where `segRatio j t` lies in
`ball(1, 1/2) ⊆ slitPlane` by W-0 + `mem_slitPlane_of_ball_one`.

Helper definitions and theorems for this construction are below. -/

/-- Helper: clamp `t` to `[s_j, s_{j+1}]`. For partition segment `j`. -/
private def segClamp (s_j s_jp1 t : ℝ) : ℝ := max s_j (min t s_jp1)

@[fun_prop]
private theorem segClamp_continuous (s_j s_jp1 : ℝ) :
    Continuous (segClamp s_j s_jp1) :=
  continuous_const.max (continuous_id.min continuous_const)

private theorem segClamp_mem_Icc (s_j s_jp1 t : ℝ) (h : s_j ≤ s_jp1) :
    segClamp s_j s_jp1 t ∈ Icc s_j s_jp1 := by
  refine ⟨le_max_left _ _, ?_⟩
  unfold segClamp
  rcases le_total t s_jp1 with ht | ht
  · simpa [min_eq_left ht] using max_le h ht
  · rw [min_eq_right ht, max_le_iff]; exact ⟨h, le_rfl⟩

private theorem segClamp_eq_left {s_j s_jp1 t : ℝ} (h : s_j ≤ s_jp1) (ht : t ≤ s_j) :
    segClamp s_j s_jp1 t = s_j := by
  rw [segClamp, min_eq_left (ht.trans h), max_eq_left ht]

private theorem segClamp_eq_self {s_j s_jp1 t : ℝ} (ht_lo : s_j ≤ t) (ht_hi : t ≤ s_jp1) :
    segClamp s_j s_jp1 t = t := by
  rw [segClamp, min_eq_left ht_hi, max_eq_right ht_lo]

private theorem segClamp_eq_right {s_j s_jp1 t : ℝ} (h : s_j ≤ s_jp1) (ht : s_jp1 ≤ t) :
    segClamp s_j s_jp1 t = s_jp1 := by
  rw [segClamp, min_eq_right ht, max_eq_right h]

/-- The **segment ratio** `(γ (segClamp s_j s_jp1 t) - w) / (γ s_j - w)`: on the partition segment
`[s_j, s_{j+1}]` it measures `γ t - w` against its value at the left endpoint `s_j`, held constant
in `t` outside the segment. Summing the `Complex.log`s of these ratios over a partition yields a
continuous argument lift of `t ↦ γ t - w`. -/
noncomputable def segRatio (γ : ℝ → ℂ) (w : ℂ) (s_j s_jp1 t : ℝ) : ℂ :=
  (γ (segClamp s_j s_jp1 t) - w) / (γ s_j - w)

/-- Before its segment (`t ≤ s_j`), the segment ratio equals `1`. -/
theorem segRatio_eq_one_of_le {γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ}
    (h : s_j ≤ s_jp1) (ht : t ≤ s_j) (h_ne : γ s_j - w ≠ 0) :
    segRatio γ w s_j s_jp1 t = 1 := by
  rw [segRatio, segClamp_eq_left h ht, div_self h_ne]

private theorem segRatio_eq_self_div {γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ}
    (ht_lo : s_j ≤ t) (ht_hi : t ≤ s_jp1) :
    segRatio γ w s_j s_jp1 t = (γ t - w) / (γ s_j - w) := by
  rw [segRatio, segClamp_eq_self ht_lo ht_hi]

/-- After its segment (`s_{j+1} ≤ t`), the segment ratio equals the full endpoint ratio
`(γ s_{j+1} - w) / (γ s_j - w)`. -/
theorem segRatio_eq_full {γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ}
    (h : s_j ≤ s_jp1) (ht : s_jp1 ≤ t) :
    segRatio γ w s_j s_jp1 t = (γ s_jp1 - w) / (γ s_j - w) := by
  rw [segRatio, segClamp_eq_right h ht]

/-- For partition with mesh < δ' and segments [s_j, s_{j+1}] of length ≤ mesh,
on the j-th segment, `γ(clamp t) - γ s_j` is small, so `segRatio j t ∈ ball(1, 1/2)`. -/
private theorem segRatio_mem_ball_one
    {γ : ℝ → ℂ} {w : ℂ} {δ' ρ : ℝ} (hρ_pos : 0 < ρ)
    (h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ ‖γ t - w‖)
    (h_unif : ∀ t s : ℝ, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      |t - s| < δ' → ‖γ t - γ s‖ < ρ / 2)
    {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc (0 : ℝ) 1) (hsjp1 : s_jp1 ∈ Icc (0 : ℝ) 1)
    (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 - s_j < δ') (t : ℝ) :
    ‖segRatio γ w s_j s_jp1 t - 1‖ < 1 / 2 := by
  have h_clamp_mem : segClamp s_j s_jp1 t ∈ Icc s_j s_jp1 :=
    segClamp_mem_Icc s_j s_jp1 t h_le
  have h_clamp_in_01 : segClamp s_j s_jp1 t ∈ Icc (0 : ℝ) 1 :=
    ⟨hsj.1.trans h_clamp_mem.1, h_clamp_mem.2.trans hsjp1.2⟩
  have h_dist : |segClamp s_j s_jp1 t - s_j| < δ' := by
    have h_nn : 0 ≤ segClamp s_j s_jp1 t - s_j := by linarith [h_clamp_mem.1]
    rw [abs_of_nonneg h_nn]; linarith [h_clamp_mem.2]
  have h_lb : ρ ≤ ‖γ s_j - w‖ := h_dist_lb _ hsj
  have h_pos : 0 < ‖γ s_j - w‖ := hρ_pos.trans_le h_lb
  have h_ne : γ s_j - w ≠ 0 := norm_pos_iff.mp h_pos
  unfold segRatio
  have h_rewrite : (γ (segClamp s_j s_jp1 t) - w) / (γ s_j - w) - 1 =
      (γ (segClamp s_j s_jp1 t) - γ s_j) / (γ s_j - w) := by
    rw [div_sub_one h_ne, sub_sub_sub_cancel_right]
  rw [h_rewrite, norm_div, div_lt_iff₀ h_pos]
  calc ‖γ (segClamp s_j s_jp1 t) - γ s_j‖
      < ρ / 2 := h_unif _ _ h_clamp_in_01 hsj h_dist
    _ ≤ ‖γ s_j - w‖ / 2 := by linarith
    _ = 1 / 2 * ‖γ s_j - w‖ := by ring

/-- Continuity of `t ↦ segRatio γ w s_j s_jp1 t` on `Icc (0 : ℝ) 1`. -/
private theorem continuousOn_segRatio {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {w : ℂ} {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc (0 : ℝ) 1)
    (hsjp1 : s_jp1 ∈ Icc (0 : ℝ) 1) (h_le : s_j ≤ s_jp1) :
    ContinuousOn (fun t ↦ segRatio γ w s_j s_jp1 t) (Icc (0 : ℝ) 1) := by
  unfold segRatio
  refine ContinuousOn.div_const ?_ _
  refine ContinuousOn.sub ?_ continuousOn_const
  refine hγ.comp (segClamp_continuous s_j s_jp1).continuousOn ?_
  intro t _
  exact ⟨hsj.1.trans (segClamp_mem_Icc s_j s_jp1 t h_le).1,
    (segClamp_mem_Icc s_j s_jp1 t h_le).2.trans hsjp1.2⟩

/-- Combined: for partition with mesh < δ', `segRatio j t ∈ slitPlane`. -/
private theorem segRatio_mem_slitPlane
    {γ : ℝ → ℂ} {w : ℂ} {δ' ρ : ℝ} (hρ_pos : 0 < ρ)
    (h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ ‖γ t - w‖)
    (h_unif : ∀ t s : ℝ, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      |t - s| < δ' → ‖γ t - γ s‖ < ρ / 2)
    {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc (0 : ℝ) 1) (hsjp1 : s_jp1 ∈ Icc (0 : ℝ) 1)
    (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 - s_j < δ') (t : ℝ) :
    segRatio γ w s_j s_jp1 t ∈ Complex.slitPlane :=
  mem_slitPlane_of_ball_one _
    (segRatio_mem_ball_one hρ_pos h_dist_lb h_unif hsj hsjp1 h_le h_mesh t)

/-! ### Telescoping product over a partition -/

/-- Telescoping product in `ℂ` over `Finset.range`. For `a : ℕ → ℂ` nonzero on
indices `0..k`, the product `∏ j ∈ range k, a (j+1)/a j = a k / a 0`. -/
private lemma prod_range_div_complex (a : ℕ → ℂ) (k : ℕ)
    (ha : ∀ j ≤ k, a j ≠ 0) :
    ∏ j ∈ Finset.range k, (a (j + 1) / a j) = a k / a 0 := by
  induction k with
  | zero => simp [div_self (ha 0 le_rfl)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun j hj ↦ ha j (by omega)),
        div_mul_div_comm, mul_comm (a n) (a (n + 1)),
        mul_div_mul_right _ _ (ha n (by omega))]

/-- Telescoping product: for `t ∈ [s_k, s_{k+1}]` along a monotone partition
`s : ℕ → ℝ` of `[0,1]` with `s 0 = 0` and `γ(s_j) ≠ w` for `0 ≤ j ≤ N`, the
product `∏_{j < N} segRatio γ w (s j) (s (j+1)) t` collapses to
`(γ t - w) / (γ 0 - w)`.

This is the key identity making `Im(log)` of each `segRatio` add up to a
continuous argument lift of `t ↦ γ t - w`. -/
private theorem prod_segRatio_telescope
    {γ : ℝ → ℂ} {w : ℂ} {N : ℕ} {s : ℕ → ℝ}
    (hs_zero : s 0 = 0) (hs_mono : Monotone s)
    (h_avoid : ∀ j ≤ N, γ (s j) - w ≠ 0)
    {t : ℝ} {k : ℕ} (hk : k < N) (hk_lo : s k ≤ t) (hk_hi : t ≤ s (k + 1)) :
    ∏ j ∈ Finset.range N, segRatio γ w (s j) (s (j + 1)) t = (γ t - w) / (γ 0 - w) := by
  -- Split range N = range (k+1) ∪ Ico (k+1) N
  rw [Finset.range_eq_Ico, ← Finset.prod_Ico_consecutive _ (Nat.zero_le (k + 1)) hk,
      ← Finset.range_eq_Ico]
  -- Tail Ico (k+1) N: each segRatio = 1
  have h_ico_eq_one : ∀ j ∈ Finset.Ico (k + 1) N,
      segRatio γ w (s j) (s (j + 1)) t = 1 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    refine segRatio_eq_one_of_le (hs_mono (Nat.le_succ _)) ?_ (h_avoid j hj.2.le)
    exact hk_hi.trans (hs_mono hj.1)
  rw [Finset.prod_congr rfl h_ico_eq_one, Finset.prod_const_one, mul_one]
  -- Peel off middle term j = k from range (k+1)
  rw [Finset.prod_range_succ]
  -- Range k: each segRatio = (γ s_{j+1} - w) / (γ s_j - w) (full ratio)
  have h_range_k_eq : ∀ j ∈ Finset.range k,
      segRatio γ w (s j) (s (j + 1)) t = (γ (s (j + 1)) - w) / (γ (s j) - w) := by
    intro j hj
    rw [Finset.mem_range] at hj
    refine segRatio_eq_full (hs_mono (Nat.le_succ _)) ?_
    exact (hs_mono (Nat.succ_le_of_lt hj)).trans hk_lo
  rw [Finset.prod_congr rfl h_range_k_eq]
  -- Middle term: segRatio at index k = (γ t - w) / (γ s_k - w)
  rw [segRatio_eq_self_div hk_lo hk_hi]
  -- Apply telescoping lemma to range k product
  rw [prod_range_div_complex (fun j ↦ γ (s j) - w) k
        (fun j hj ↦ h_avoid j (hj.trans hk.le))]
  -- Use s 0 = 0 and cancel γ s_k - w
  rw [hs_zero, div_mul_div_comm, mul_comm (γ (s k) - w) (γ t - w),
      mul_div_mul_right _ _ (h_avoid k hk.le)]

/-! ### Continuous arg-lift summand (continued) -/

/-- Each summand in the telescoping arg-lift sum is continuous. -/
private theorem continuousOn_im_log_segRatio {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) {w : ℂ} {δ' ρ : ℝ} (hρ_pos : 0 < ρ)
    (h_dist_lb : ∀ t ∈ Icc (0 : ℝ) 1, ρ ≤ ‖γ t - w‖)
    (h_unif : ∀ t s : ℝ, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      |t - s| < δ' → ‖γ t - γ s‖ < ρ / 2)
    {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc (0 : ℝ) 1) (hsjp1 : s_jp1 ∈ Icc (0 : ℝ) 1)
    (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 - s_j < δ') :
    ContinuousOn (fun t ↦ (Complex.log (segRatio γ w s_j s_jp1 t)).im)
      (Icc (0 : ℝ) 1) := by
  refine Complex.continuous_im.comp_continuousOn ?_
  exact (continuousOn_segRatio hγ hsj hsjp1 h_le).clog
    fun t _ ↦ segRatio_mem_slitPlane hρ_pos h_dist_lb h_unif hsj hsjp1 h_le h_mesh t

/-! ### Helper: `exp(I · Im(log z)) = z / ‖z‖` -/

/-- For a nonzero complex number `z`, `exp(I · Im(log z)) = z / ↑‖z‖`. -/
private lemma exp_I_log_im_eq_div_norm {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (Complex.I * ((Complex.log z).im : ℂ)) = z / (‖z‖ : ℂ) := by
  have h_split : Complex.I * ((Complex.log z).im : ℂ) =
      Complex.log z - ((Complex.log z).re : ℂ) := by
    rw [mul_comm, eq_sub_iff_add_eq, add_comm]
    exact Complex.re_add_im (Complex.log z)
  rw [h_split, Complex.exp_sub, Complex.exp_log hz, Complex.log_re,
      ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr hz)]

/-! ### Partition-segment existence -/

/-- For a uniform partition `s_j = j/N` of `[0,1]` with `N > 0`, every `t ∈ [0,1]`
lies in some segment `[s_k, s_{k+1}]` with `k < N`. -/
private lemma partition_segment_exists {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℕ, k < N ∧ (k : ℝ) / N ≤ t ∧ t ≤ ((k + 1 : ℕ) : ℝ) / N := by
  have hN_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h_tN_nn : 0 ≤ t * N := mul_nonneg ht.1 hN_real.le
  rcases lt_or_eq_of_le ht.2 with h_t_lt_1 | h_t_eq_1
  · refine ⟨⌊t * N⌋₊, ?_, ?_, ?_⟩
    · have h_tN_lt : t * N < N := by nlinarith
      exact_mod_cast lt_of_le_of_lt (Nat.floor_le h_tN_nn) h_tN_lt
    · rw [div_le_iff₀ hN_real]
      exact_mod_cast Nat.floor_le h_tN_nn
    · rw [le_div_iff₀ hN_real]
      have h_lt : t * N < ⌊t * N⌋₊ + 1 := Nat.lt_floor_add_one _
      have h_cast : ((⌊t * N⌋₊ + 1 : ℕ) : ℝ) = (⌊t * N⌋₊ : ℝ) + 1 := by
        push_cast; ring
      rw [h_cast]
      linarith
  · refine ⟨N - 1, Nat.sub_lt hN zero_lt_one, ?_, ?_⟩
    · have hNcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub hN, Nat.cast_one]
      rw [hNcast, h_t_eq_1, div_le_one hN_real]
      linarith
    · have h_eq : ((N - 1 + 1 : ℕ) : ℝ) = (N : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hN
      rw [h_eq, div_self hN_real.ne']
      exact ht.2

/-! ### Main theorem: continuous argument lift -/

/-- **Continuous argument lift with an explicit partition.** For `γ` continuous on `[0, 1]` and
avoiding `w`, there is a uniform partition `0 = s 0 < ⋯ < s N = 1` and a continuous real function
`θ t = arg (γ 0 - w) + ∑_{j < N} (log (segRatio γ w (s j) (s (j+1)) t)).im` on `[0, 1]` satisfying
`γ t - w = ‖γ t - w‖ · exp (I · θ t)`. Each node has `γ (s j) ≠ w`, and on each segment `j` the
ratio `(γ t - w) / (γ (s j) - w)` lies in `Complex.slitPlane`. -/
theorem exists_continuous_arg_lift_with_partition
    {γ : ℝ → ℂ} {w : ℂ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∃ (N : ℕ) (s : ℕ → ℝ),
      0 < N ∧ s 0 = 0 ∧ s N = 1 ∧ Monotone s ∧
      (∀ j ≤ N, s j ∈ Icc (0 : ℝ) 1) ∧
      (∀ j ≤ N, γ (s j) - w ≠ 0) ∧
      (∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
        (γ t - w) / (γ (s j) - w) ∈ Complex.slitPlane) ∧
      ContinuousOn
        (fun t ↦ Complex.arg (γ 0 - w) +
          ∑ j ∈ Finset.range N, (Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im)
        (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t - w = (‖γ t - w‖ : ℂ) * Complex.exp (Complex.I *
        ((Complex.arg (γ 0 - w) +
          ∑ j ∈ Finset.range N,
            (Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im : ℝ) : ℂ))) := by
  obtain ⟨δ', hδ'_pos, ρ, hρ_pos, h_dist_lb, h_unif⟩ :=
    exists_uniform_modulus_avoiding hγ h_avoid
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ')
  have hN_pos : 0 < N := by
    exact_mod_cast (div_nonneg zero_le_one hδ'_pos.le).trans_lt hN
  have hN_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
  have hN_mesh : (1 : ℝ) / N < δ' := by
    rw [div_lt_iff₀ hN_real]
    rw [div_lt_iff₀ hδ'_pos] at hN
    linarith
  set s : ℕ → ℝ := fun j ↦ (j : ℝ) / N with hs_def
  have hs_zero : s 0 = 0 := by simp [hs_def]
  have hs_N : s N = 1 := by
    simp only [hs_def]
    exact div_self hN_real.ne'
  have hs_mono : Monotone s := fun a b hab ↦
    div_le_div_of_nonneg_right (by exact_mod_cast hab) hN_real.le
  have hs_in : ∀ j, j ≤ N → s j ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨div_nonneg (by exact_mod_cast Nat.zero_le j) hN_real.le, ?_⟩
    rw [div_le_one hN_real]
    exact_mod_cast hj
  have hs_avoid : ∀ j ≤ N, γ (s j) - w ≠ 0 := fun j hj ↦
    sub_ne_zero.mpr (h_avoid (s j) (hs_in j hj))
  have hs_mesh : ∀ j, s (j + 1) - s j = 1 / N := by
    intro j; simp only [hs_def]; push_cast; ring
  have hs_le : ∀ j, s j ≤ s (j + 1) := fun j ↦ hs_mono (Nat.le_succ _)
  have h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ t - w) / (γ (s j) - w) ∈ Complex.slitPlane := by
    intro j hj t ht
    rw [show (γ t - w) / (γ (s j) - w) = segRatio γ w (s j) (s (j + 1)) t from
      (segRatio_eq_self_div ht.1 ht.2).symm]
    have h_mesh_j : s (j + 1) - s j < δ' := by rw [hs_mesh j]; exact hN_mesh
    exact segRatio_mem_slitPlane hρ_pos h_dist_lb h_unif
      (hs_in j hj.le) (hs_in (j + 1) hj) (hs_le j) h_mesh_j t
  refine ⟨N, s, hN_pos, hs_zero, hs_N, hs_mono, hs_in, hs_avoid, h_slit, ?_, ?_⟩
  -- Continuity of θ
  · refine ContinuousOn.add continuousOn_const ?_
    refine continuousOn_finsetSum _ ?_
    intro j hj
    refine continuousOn_im_log_segRatio hγ hρ_pos h_dist_lb h_unif
      (hs_in j (Finset.mem_range.mp hj).le) (hs_in (j + 1) (Finset.mem_range.mp hj))
      (hs_le j) ?_
    rw [hs_mesh j]; exact hN_mesh
  -- Lift property
  · intro t ht
    have h_avoid_t : γ t - w ≠ 0 := sub_ne_zero.mpr (h_avoid t ht)
    have h_avoid_0 : γ 0 - w ≠ 0 :=
      sub_ne_zero.mpr (h_avoid 0 ⟨le_rfl, zero_le_one⟩)
    obtain ⟨k, hk_lt, hk_lo, hk_hi⟩ := partition_segment_exists hN_pos ht
    have h_telescope := prod_segRatio_telescope hs_zero hs_mono hs_avoid hk_lt hk_lo hk_hi
    have h_ratio_ne : ∀ j ∈ Finset.range N,
        segRatio γ w (s j) (s (j + 1)) t ≠ 0 := fun j hj ↦
      have h_mesh_j : s (j + 1) - s j < δ' := by rw [hs_mesh j]; exact hN_mesh
      Complex.slitPlane_ne_zero
        (segRatio_mem_slitPlane hρ_pos h_dist_lb h_unif
          (hs_in j (Finset.mem_range.mp hj).le)
          (hs_in (j + 1) (Finset.mem_range.mp hj))
          (hs_le j) h_mesh_j t)
    have h_prod_eq : (γ 0 - w) *
        ∏ j ∈ Finset.range N, segRatio γ w (s j) (s (j + 1)) t = γ t - w := by
      rw [h_telescope, mul_div_cancel₀ _ h_avoid_0]
    have h_theta_cast :
        ((Complex.arg (γ 0 - w) +
          ∑ j ∈ Finset.range N,
            (Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im : ℝ) : ℂ) =
        (Complex.arg (γ 0 - w) : ℂ) +
        ∑ j ∈ Finset.range N,
          ((Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im : ℂ) := by
      push_cast
      rfl
    have h_exp_split :
        Complex.exp (Complex.I *
          ((Complex.arg (γ 0 - w) +
            ∑ j ∈ Finset.range N,
              (Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (Complex.arg (γ 0 - w) : ℂ)) *
          ∏ j ∈ Finset.range N,
            Complex.exp (Complex.I *
              ((Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im : ℂ)) := by
      rw [h_theta_cast, mul_add, Complex.exp_add, Finset.mul_sum, Complex.exp_sum]
    have h_arg : Complex.exp (Complex.I * (Complex.arg (γ 0 - w) : ℂ)) =
        (γ 0 - w) / ((‖γ 0 - w‖ : ℝ) : ℂ) := by
      rw [show (Complex.arg (γ 0 - w) : ℂ) = ((Complex.log (γ 0 - w)).im : ℂ) by
            rw [Complex.log_im]]
      exact exp_I_log_im_eq_div_norm h_avoid_0
    have h_z_eq : ∀ j ∈ Finset.range N,
        Complex.exp (Complex.I *
          ((Complex.log (segRatio γ w (s j) (s (j + 1)) t)).im : ℂ)) =
          segRatio γ w (s j) (s (j + 1)) t /
            ((‖segRatio γ w (s j) (s (j + 1)) t‖ : ℝ) : ℂ) :=
      fun j hj ↦ exp_I_log_im_eq_div_norm (h_ratio_ne j hj)
    have h_norm_prod_real : (‖γ 0 - w‖ : ℝ) *
        (∏ j ∈ Finset.range N, ‖segRatio γ w (s j) (s (j + 1)) t‖) = ‖γ t - w‖ := by
      rw [← Complex.norm_prod, ← norm_mul, h_prod_eq]
    have h_norm_t_ne : ((‖γ t - w‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h_avoid_t)
    rw [h_exp_split, h_arg, Finset.prod_congr rfl h_z_eq, Finset.prod_div_distrib,
        div_mul_div_comm, ← Complex.ofReal_prod, ← Complex.ofReal_mul,
        h_norm_prod_real, h_prod_eq, mul_div_cancel₀ _ h_norm_t_ne]

/-! ### Per-segment FTC for `1 / (γ - w)` -/

/-- **Per-segment fundamental theorem of calculus for `1 / (γ - w)`.** If `γ` is continuous on
`[a, b]`, differentiable off a countable set, avoids `w`, and the ratio `(γ t - w) / (γ a - w)`
stays in `Complex.slitPlane` throughout, then
`∫ t in a..b, γ' t / (γ t - w) = log ((γ b - w) / (γ a - w))`. -/
theorem segment_log_FTC
    {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} (hab : a ≤ b) {P : Set ℝ} (hP_count : P.Countable)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ P, HasDerivAt γ (deriv γ t) t)
    (h_a_ne : γ a - w ≠ 0)
    (h_slit : ∀ t ∈ Icc a b, (γ t - w) / (γ a - w) ∈ Complex.slitPlane)
    (h_int : IntervalIntegrable
      (fun t ↦ deriv γ t / (γ t - w)) MeasureTheory.volume a b) :
    ∫ t in a..b, deriv γ t / (γ t - w) = Complex.log ((γ b - w) / (γ a - w)) := by
  set F : ℝ → ℂ := fun t ↦ Complex.log ((γ t - w) / (γ a - w))
  have hF_cont : ContinuousOn F (Icc a b) :=
    ContinuousOn.clog ((hγ_cont.sub continuousOn_const).div_const _) h_slit
  have hF_deriv : ∀ t ∈ Ioo a b \ P,
      HasDerivAt F (deriv γ t / (γ t - w)) t := by
    intro t ht
    have ht_Icc : t ∈ Icc a b := Ioo_subset_Icc_self ht.1
    have h_inner : HasDerivAt (fun t ↦ (γ t - w) / (γ a - w))
        (deriv γ t / (γ a - w)) t :=
      ((hγ_diff t ht).sub_const w).div_const _
    have h_slit_t : (γ t - w) / (γ a - w) ∈ Complex.slitPlane := h_slit t ht_Icc
    have h_log := h_inner.clog_real h_slit_t
    have h_t_minus_ne : γ t - w ≠ 0 :=
      fun h ↦ Complex.slitPlane_ne_zero h_slit_t (by rw [h, zero_div])
    convert h_log using 1
    field_simp
  have h_FTC := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le _ _ hab hP_count
    hF_cont hF_deriv h_int
  rw [h_FTC]
  change Complex.log ((γ b - w) / (γ a - w)) - Complex.log ((γ a - w) / (γ a - w)) =
       Complex.log ((γ b - w) / (γ a - w))
  rw [div_self h_a_ne, Complex.log_one, sub_zero]

end TauCeti.Contour

end

