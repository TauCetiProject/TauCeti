/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Scaling
import TauCeti.Analysis.Calculus.IteratedFDeriv.Cutoff
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Normed.Module.Ball

/-!
# Cutting off a Schwartz function

Let `χ : E → ℝ` be a smooth compactly supported function that equals `1` near the origin. For a
Schwartz function `f`, the truncations `x ↦ χ (R⁻¹ • x) • f x` are smooth and compactly supported,
and they converge to `f` in the Schwartz topology as `R → ∞`. Mathlib's
`SchwartzMap.dense_hasCompactSupport` gives the resulting density of compactly supported
functions in `𝓢(E, F)` when `E` is finite-dimensional.

This is how a statement proved for smooth compactly supported test functions is passed to Schwartz
test functions: any quantity controlled by finitely many Schwartz seminorms (for instance a
weighted sup norm of the Fourier transform) is approximated by its values on the truncations.

The estimate is explicit. If `h` is smooth with bounded derivatives and vanishes on the ball of
radius `ρ`, then every Schwartz seminorm of `h • f` is `O(ρ⁻¹)`: expand the derivatives of `h • f`
by the Leibniz rule; they vanish where `‖x‖ < ρ`, and where `‖x‖ ≥ ρ` trading one power of `‖x‖`
against `ρ⁻¹` bounds each term by a `(k + 1, ·)` seminorm of `f` divided by `ρ`. Suppose `χ = 1` on
the ball of radius `r` and `R ≥ 1`. The difference `f - χ (R⁻¹ • ·) • f` is
`(1 - χ (R⁻¹ • ·)) • f`, where `1 - χ (R⁻¹ • ·)` vanishes on the ball of radius `r R` and its
derivatives are bounded independently of `R`, so its `(k, n)` seminorm is `O(R⁻¹)`.

## Main results

* `SchwartzMap.seminorm_le_of_eq_smul_of_eq_zero`: the bound `seminorm k j (h • f) ≤ K / ρ` for a
  smooth `h` with bounded derivatives vanishing on the ball of radius `ρ`.
* `SchwartzMap.seminorm_sub_smulLeftCLM_comp_inv_smul_le`: the explicit bound
  `seminorm k n (f - χ (R⁻¹ • ·) • f) ≤ K / (r R)` for `R ≥ 1`.
* `SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop`: the truncations converge to `f` in
  `𝓢(E, F)`.
* `SchwartzMap.hasCompactSupport_smulLeftCLM_comp_inv_smul`: the truncations are compactly
  supported.
* `SchwartzMap.tendsto_seminorm_smulLeftCLM_comp_smul_sub_of_iteratedFDeriv_eq_zero`: if the
  derivatives of `f` of order at most `N` vanish at `x`, the seminorms of order at most `N` of the
  products `φ (t • (· - x)) • f` with shrinking cutoffs tend to zero as `t → ∞`.
* `SchwartzMap.tendsto_smulLeftCLM_contDiffBump`: the truncations `φ (R⁻¹ ·) • f` by a
  `ContDiffBump` converge to `f` as `R → ∞`, for complex-valued multipliers.
* `ContDiffBump.lowPassSchwartz`: the low-pass symbol `φ (R⁻¹ ·)` of a `ContDiffBump`, as a
  complex Schwartz function, and `ContDiffBump.mul_lowPassSchwartz_of_support_subset`: it fixes
  every symbol supported in the closed ball of radius `R φ.rIn`.
* `ContDiffBump.fourierInv_lowPassSchwartz_apply`: its kernel is the `L¹`-normalised dilate
  `R^n 𝓕⁻ φ (R ·)` of the kernel at scale `1`.
* Mathlib's `SchwartzMap.dense_hasCompactSupport`: compactly supported functions are dense in
  `𝓢(E, F)` for finite-dimensional `E`.
* `IsCompact.exists_schwartzMap_cutoff`: a compact subset `K` of an open set `U` has a compactly
  supported Schwartz cutoff `χ : 𝓢(E, ℂ)` with support in `U` and equal to `1` near `K`.
* `SchwartzMap.hasSum_smulLeftCLM_latticeBump_sub`: the partition of unity `∑ⱼ χ(· - j) = 1` by the
  integer translates of `TauCeti.latticeBump n` cuts a Schwartz function on `ℝⁿ` into pieces whose
  series converges to it in `𝓢(ℝⁿ, F)`. The partial sums are `f` times `∑_{j ∈ s} χ(· - j)`, which
  equals `1` on a large ball and has derivatives bounded independently of `s`, so the same
  estimate as for the truncations applies.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Section 7.1.
-/

public section

open Filter Metric Set
open scoped ContDiff Topology SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace SchwartzMap

variable {χ : E → ℝ}

/-- The truncation `χ (R⁻¹ • ·) • f` of a Schwartz function by a cutoff of temperate growth,
evaluated pointwise. -/
@[simp]
theorem smulLeftCLM_comp_inv_smul_apply (hχ : χ.HasTemperateGrowth) (R : ℝ) (f : 𝓢(E, F))
    (x : E) : smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f x = χ (R⁻¹ • x) • f x :=
  smulLeftCLM_apply_apply (hχ.comp (R⁻¹ • ContinuousLinearMap.id ℝ E).hasTemperateGrowth) f x

/-- A truncation of a Schwartz function by a compactly supported cutoff is compactly supported. -/
theorem hasCompactSupport_smulLeftCLM_comp_inv_smul
    (hsupp : HasCompactSupport χ) {R : ℝ} (hR : R ≠ 0) (f : 𝓢(E, F)) :
    HasCompactSupport (smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) :=
  (hsupp.comp_smul (inv_ne_zero hR)).isCompact.of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_smulLeftCLM_subset _ f).trans Set.inter_subset_right)

/-- Multiplying a Schwartz function by the shifted and dilated cutoff `φ (t • (· - x))`, for a
smooth compactly supported `φ` and `t ≠ 0`, is pointwise multiplication. -/
theorem smulLeftCLM_comp_smul_sub_apply {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) {t : ℝ} (ht : t ≠ 0) (x : E) (f : 𝓢(E, F)) :
    smulLeftCLM F (fun y ↦ φ (t • (y - x))) f = fun y ↦ φ (t • (y - x)) • f y :=
  smulLeftCLM_apply ((hφc.comp_homeomorph
    ((Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero t ht))).hasTemperateGrowth
    (hφ.comp ((contDiff_const_smul t).comp (contDiff_id.sub contDiff_const)))) f

/-- Where `‖x‖ ≥ ρ > 0`, one power of `‖x‖` can be traded for `ρ⁻¹` against the next seminorm. -/
private lemma pow_mul_norm_iteratedFDeriv_le_div (f : 𝓢(E, F)) (k j : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {x : E} (hx : ρ ≤ ‖x‖) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ ≤ SchwartzMap.seminorm ℝ (k + 1) j f / ρ := by
  rw [le_div_iff₀ hρ]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ * ρ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ j f x‖ := by ring
    _ ≤ SchwartzMap.seminorm ℝ (k + 1) j f := le_seminorm ℝ (k + 1) j f x

/-- A Schwartz function times a smooth function `h` with bounded derivatives that vanishes on the
ball of radius `ρ` about the origin has Schwartz seminorms of size `O(ρ⁻¹)`. -/
theorem seminorm_le_of_eq_smul_of_eq_zero {h : E → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : ℕ → ℝ} (hB : ∀ i y, ‖iteratedFDeriv ℝ i h y‖ ≤ B i) {ρ : ℝ} (hρ : 0 < ρ)
    (h0 : ∀ y, ‖y‖ < ρ → h y = 0) {f g : 𝓢(E, F)} (hg : ∀ y, g y = h y • f y)
    (k j : ℕ) :
    SchwartzMap.seminorm ℝ k j g ≤ (∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * B i * SchwartzMap.seminorm ℝ (k + 1) (j - i) f) / ρ := by
  have hB0 : ∀ i, 0 ≤ B i := fun i ↦ (norm_nonneg _).trans (hB i 0)
  have hK : 0 ≤ ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * B i * SchwartzMap.seminorm ℝ (k + 1) (j - i) f :=
    Finset.sum_nonneg fun i _ ↦ by have := hB0 i; positivity
  refine seminorm_le_bound ℝ k j g (div_nonneg hK hρ.le) fun y ↦ ?_
  have hg' : ⇑g = fun y ↦ h y • f y := funext hg
  rw [hg']
  rcases lt_or_ge ‖y‖ ρ with hy | hy
  · -- Near `y` the product vanishes.
    have hzero : (fun y ↦ h y • f y) =ᶠ[𝓝 y] 0 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)] with y' hy'
      simp [h0 y' (mem_ball_zero_iff.1 hy')]
    rw [(hzero.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply, norm_zero,
      mul_zero]
    exact div_nonneg hK hρ.le
  · refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hh (f.smooth ⊤) y
      (by exact_mod_cast le_top)) (by positivity)).trans ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    calc ‖y‖ ^ k * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i h y‖ *
          ‖iteratedFDeriv ℝ (j - i) f y‖)
        = (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i h y‖ *
            (‖y‖ ^ k * ‖iteratedFDeriv ℝ (j - i) f y‖) := by ring
      _ ≤ (j.choose i : ℝ) * B i * (SchwartzMap.seminorm ℝ (k + 1) (j - i) f / ρ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hB i y) (Nat.cast_nonneg _))
            (pow_mul_norm_iteratedFDeriv_le_div f k (j - i) hρ hy) (by positivity)
            (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
      _ = _ := by ring

/-- For `R ≥ 1`, the derivatives of `1 - χ (R⁻¹ • ·)` are bounded by `1 + B i` when those of `χ`
are bounded by `B i`. -/
private lemma norm_iteratedFDeriv_one_sub_comp_inv_smul_le {B : ℕ → ℝ}
    (hB : ∀ i x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B i) {R : ℝ} (hR : 1 ≤ R) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y ↦ 1 - χ (R⁻¹ • y)) x‖ ≤ 1 + B i := by
  have hB0 : 0 ≤ B i := (norm_nonneg _).trans (hB i 0)
  rcases eq_or_ne i 0 with rfl | hi
  · rw [norm_iteratedFDeriv_zero]
    refine (norm_sub_le _ _).trans ?_
    have := hB 0 (R⁻¹ • x)
    rw [norm_iteratedFDeriv_zero] at this
    simpa using this
  · have heq : (fun y ↦ 1 - χ (R⁻¹ • y)) = -(fun y ↦ χ (R⁻¹ • y) - 1) := by
      funext y
      exact (neg_sub _ _).symm
    rw [heq, iteratedFDeriv_neg_apply (𝕜 := ℝ), norm_neg]
    refine (TauCeti.norm_iteratedFDeriv_comp_inv_smul_sub_const_le hi (hB i) hR 1 x).trans ?_
    exact (div_le_self hB0 hR).trans (le_add_of_nonneg_left zero_le_one)

/-- **The truncation estimate.** Let `χ` be smooth with `‖D^i χ‖ ≤ B i` for every `i`, and equal
to `1` on the ball of radius `r > 0`. For `R ≥ 1` the `(k, n)` seminorm of `f - χ (R⁻¹ • ·) • f`
is at most `K / (r R)`, where `K` depends on `χ`, `f`, `k` and `n` but not on `R`. -/
theorem seminorm_sub_smulLeftCLM_comp_inv_smul_le (hχ : ContDiff ℝ ∞ χ)
    {B : ℕ → ℝ} (hB : ∀ i x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B i)
    {r : ℝ} (hr : 0 < r) (hχ1 : ∀ y, ‖y‖ < r → χ y = 1) (f : 𝓢(E, F)) (k n : ℕ) {R : ℝ}
    (hR : 1 ≤ R) :
    SchwartzMap.seminorm ℝ k n (f - smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
        SchwartzMap.seminorm ℝ (k + 1) (n - i) f) / (r * R) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hχt : χ.HasTemperateGrowth := ⟨hχ, fun i ↦ ⟨0, B i, fun x ↦ by simpa using hB i x⟩⟩
  refine seminorm_le_of_eq_smul_of_eq_zero (h := fun y ↦ 1 - χ (R⁻¹ • y))
    (contDiff_const.sub (hχ.comp (contDiff_const_smul _)))
    (norm_iteratedFDeriv_one_sub_comp_inv_smul_le hB hR) (mul_pos hr hR0) (fun y hy ↦ ?_)
    (fun y ↦ ?_) k n
  · -- Near the origin the truncation agrees with `f`.
    have hy' : ‖R⁻¹ • y‖ < r := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hR0.le, inv_mul_lt_iff₀ hR0]
      linarith
    simp [hχ1 _ hy']
  · simp [smulLeftCLM_comp_inv_smul_apply hχt R f y, sub_smul]

/-- **Truncations converge in the Schwartz topology.** If `χ` is smooth with every derivative
bounded (for instance, if `χ` is compactly supported) and equal to `1` near the origin, then
`χ (R⁻¹ • ·) • f → f` in `𝓢(E, F)` as `R → ∞`. -/
theorem tendsto_smulLeftCLM_comp_inv_smul_atTop (hχ : ContDiff ℝ ∞ χ)
    (hbdd : ∀ i, ∃ B, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B) (hχ1 : χ =ᶠ[𝓝 0] 1) (f : 𝓢(E, F)) :
    Tendsto (fun R : ℝ ↦ smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) atTop (𝓝 f) := by
  choose B hB using hbdd
  obtain ⟨r, hr, hχr⟩ := Metric.eventually_nhds_iff.1 hχ1
  have hχ1' : ∀ y, ‖y‖ < r → χ y = 1 := fun y hy ↦ hχr (by rwa [dist_zero_right])
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  set K := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
    SchwartzMap.seminorm ℝ (k + 1) (n - i) f
  filter_upwards [eventually_ge_atTop 1, eventually_gt_atTop (K / (r * ε))] with R hR hKR
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  rw [schwartzSeminormFamily_apply, ← map_neg_eq_map, neg_sub]
  refine (seminorm_sub_smulLeftCLM_comp_inv_smul_le hχ hB hr hχ1' f k n hR).trans_lt ?_
  rw [div_lt_iff₀ (mul_pos hr hR0)]
  rw [div_lt_iff₀ (mul_pos hr hε)] at hKR
  linarith [mul_comm R (r * ε), mul_left_comm ε r R]

section ShrinkingCutoff

variable [FiniteDimensional ℝ E]

/-- **Shrinking cutoffs at a flat point.** If the derivatives of `f` of order at most `N` vanish
at `x`, the Schwartz seminorms of order `n ≤ N` of the products of `f` with the shrinking cutoffs
`φ (t • (· - x))` tend to zero as `t → ∞`: by `TauCeti.exists_norm_iteratedFDeriv_smul_le_mul`
their derivatives of order at most `N` are `O(t⁻¹)`, and they are supported in
`closedBall x t⁻¹`. -/
theorem tendsto_seminorm_smulLeftCLM_comp_smul_sub_of_iteratedFDeriv_eq_zero {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφs : tsupport φ ⊆ closedBall 0 1) (f : 𝓢(E, F)) {x : E} {N : ℕ}
    (hf : ∀ i ≤ N, iteratedFDeriv ℝ i f x = 0) (k : ℕ) {n : ℕ} (hn : n ≤ N) :
    Tendsto (fun t : ℝ ↦ (smulLeftCLM F (fun y ↦ φ (t • (y - x))) f).seminorm ℝ k n)
      atTop (𝓝 0) := by
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport φ) hφs
  obtain ⟨C, hC⟩ := TauCeti.exists_norm_iteratedFDeriv_smul_le_mul (r := N)
    (hφ.of_le (mod_cast le_top)) hφs (f.smooth _) hf
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 1 one_pos le_rfl 0 (Nat.zero_le _) x)
  refine squeeze_zero' (g := fun t : ℝ ↦ (‖x‖ + 1) ^ k * C * t⁻¹)
    (.of_forall fun _ ↦ apply_nonneg _ _) ?_
    (by simpa using tendsto_inv_atTop_zero.const_mul ((‖x‖ + 1) ^ k * C))
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := one_pos.trans_le ht
  have ht1 : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  refine seminorm_le_bound ℝ k n _ (by positivity) fun y ↦ ?_
  have hy := hC t⁻¹ (inv_pos.2 ht0) ht1 n hn y
  have hsupp := TauCeti.tsupport_comp_inv_smul_sub_subset_closedBall hφs (inv_pos.2 ht0) x
  simp only [inv_inv] at hy hsupp
  rw [smulLeftCLM_comp_smul_sub_apply hφ hφc ht0.ne']
  by_cases hyx : y ∈ closedBall x t⁻¹
  · have hy1 : ‖y‖ ≤ ‖x‖ + 1 := by
      calc ‖y‖ = ‖x + (y - x)‖ := by simp
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by gcongr; exact (mem_closedBall_iff_norm.1 hyx).trans ht1
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ φ (t • (y - x)) • f y) y‖
        ≤ (‖x‖ + 1) ^ k * (C * t⁻¹) := by gcongr
      _ = (‖x‖ + 1) ^ k * C * t⁻¹ := by ring
  · -- Away from `closedBall x t⁻¹` the product vanishes near `y`.
    have hy0 : y ∉ tsupport fun y ↦ φ (t • (y - x)) • f y :=
      fun h ↦ hyx (hsupp (tsupport_smul_subset_left _ _ h))
    rw [Function.notMem_support.mp fun h ↦ hy0 (support_iteratedFDeriv_subset n h), norm_zero,
      mul_zero]
    positivity

end ShrinkingCutoff

section Truncation

variable [FiniteDimensional ℝ E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The low-pass truncations `φ (R⁻¹ ·) • f` of a Schwartz function by a `ContDiffBump`, for
complex-valued multipliers, converge to `f` in the Schwartz topology along any family of scales
`R → ∞`. -/
theorem tendsto_smulLeftCLM_contDiffBump {α : Type*} {l : Filter α} {R : α → ℝ}
    (hR : Tendsto R l atTop) (φ : ContDiffBump (0 : E)) (f : 𝓢(E, G)) :
    Tendsto (fun a ↦ smulLeftCLM G (fun ξ ↦ (φ ((R a)⁻¹ • ξ) : ℂ)) f) l (𝓝 f) := by
  have hφ : (⇑φ).HasTemperateGrowth := φ.hasCompactSupport.hasTemperateGrowth φ.contDiff
  have h := (tendsto_smulLeftCLM_comp_smul φ.contDiff φ.hasCompactSupport φ.eventuallyEq_one
    f).comp (tendsto_inv_atTop_zero.comp hR)
  refine h.congr fun a ↦ ?_
  have hc : (fun ξ ↦ φ ((R a)⁻¹ • ξ)).HasTemperateGrowth := by fun_prop
  rw [Function.comp_apply, Function.comp_apply, ← smulLeftCLM_ofReal ℂ hc,
    RCLike.ofReal_eq_complex_ofReal]

end Truncation

section Lattice

open TauCeti

variable {n : ℕ}

/-- **The lattice partition of unity converges in Schwartz space:** for every Schwartz function
`f`, the series `∑ⱼ χ(· - j) f` converges to `f` in `𝓢(ℝⁿ, F)`, where `χ = latticeBump n`. -/
theorem hasSum_smulLeftCLM_latticeBump_sub (f : 𝓢(EuclideanSpace ℝ (Fin n), F)) :
    HasSum (fun j : Fin n → ℤ ↦
      SchwartzMap.smulLeftCLM F (fun y ↦ latticeBump n (y - latticePoint j)) f) f := by
  set S := 8 ^ n * ∑' d : Fin n → ℤ, latticeWeight d
  choose B hB using fun i : ℕ ↦ exists_norm_iteratedFDeriv_latticeBump_le (n := n) i
  have hB0 : ∀ i, 0 ≤ B i := fun i ↦ (norm_nonneg _).trans (hB i 0)
  have hS0 : 0 ≤ S := by
    have : 0 ≤ ∑' d : Fin n → ℤ, latticeWeight d := tsum_nonneg fun d ↦ latticeWeight_nonneg d
    positivity
  rw [HasSum, (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin n)) F).tendsto_nhds]
  rintro ⟨k, j⟩ ε hε
  set K := ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * (B i * (1 + (n : ℝ)) ^ n * S + 1) * SchwartzMap.seminorm ℝ (k + 1) (j - i) f
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ ↦ by have := hB0 i; positivity
  set R := √n + K / ε + 1
  have hRn : 0 < R - √n := by have := div_nonneg hK hε.le; simp only [R]; linarith
  filter_upwards [Filter.eventually_ge_atTop (finite_setOf_norm_latticePoint_le R).toFinset]
    with s hs
  rw [schwartzSeminormFamily_apply]
  -- The partial sum is `f` times `∑_{j ∈ s} χ(· - j) - 1`, which vanishes on `‖y‖ < R - √n`.
  refine (seminorm_le_of_eq_smul_of_eq_zero
    (h := fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j) - 1)
    ((ContDiff.sum fun j _ ↦ contDiff_latticeBump_sub j).sub contDiff_const)
    (B := fun i ↦ B i * (1 + (n : ℝ)) ^ n * S + 1) (fun i y ↦ ?_) hRn (fun y hy ↦ ?_)
    (f := f) (fun y ↦ ?_) k j).trans_lt ?_
  · exact norm_iteratedFDeriv_sum_latticeBump_sub_sub_one_le (hB i) s y
  · simp [sum_latticeBump_sub_eq_one (fun j hj ↦ hs ((Set.Finite.mem_toFinset _).2 hj.le))
      (by linarith : ‖y‖ + √n < R)]
  · simp [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_latticeBump_sub _),
      Finset.sum_smul, sub_smul]
  · rw [div_lt_iff₀ hRn]
    calc K = K / ε * ε := by field_simp
      _ < (R - √n) * ε := by gcongr; simp only [R]; linarith
      _ = ε * (R - √n) := mul_comm _ _

end Lattice

end SchwartzMap

namespace ContDiffBump

variable [FiniteDimensional ℝ E] (φ : ContDiffBump (0 : E))

/-- The **low-pass symbol** `φ (R⁻¹ ·)` at a scale `R ≠ 0`, as a complex Schwartz function: it is
smooth and supported in the closed ball of radius `|R| φ.rOut`. -/
noncomputable def lowPassSchwartz {R : ℝ} (hR : R ≠ 0) : 𝓢(E, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun ξ ↦ (φ (R⁻¹ • ξ) : ℂ))
    ((φ.hasCompactSupport.comp_smul (inv_ne_zero hR)).comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp (contDiff_const_smul _)))

/-- The values of the low-pass Schwartz symbol `φ (R⁻¹ ·)`. -/
@[simp]
theorem lowPassSchwartz_apply {R : ℝ} (hR : R ≠ 0) (ξ : E) :
    φ.lowPassSchwartz hR ξ = (φ (R⁻¹ • ξ) : ℂ) :=
  (rfl)

/-- The low-pass Schwartz symbol `φ (R⁻¹ ·)`, as a function. -/
theorem coe_lowPassSchwartz {R : ℝ} (hR : R ≠ 0) :
    ⇑(φ.lowPassSchwartz hR) = fun ξ ↦ (φ (R⁻¹ • ξ) : ℂ) :=
  (rfl)

/-- The low-pass Schwartz symbol at scale `R` is the dilation of the one at scale `1`. -/
theorem coe_lowPassSchwartz_eq_comp {R : ℝ} (hR : R ≠ 0) :
    ⇑(φ.lowPassSchwartz hR) = fun ξ ↦ φ.lowPassSchwartz one_ne_zero (R⁻¹ • ξ) := by
  ext ξ
  simp

/-- **The low-pass symbol fixes low-frequency symbols.** Multiplication by `φ (R⁻¹ ·)`, `R > 0`,
fixes every function supported in the closed ball of radius `R φ.rIn`, where `φ (R⁻¹ ·) = 1`. -/
theorem mul_lowPassSchwartz_of_support_subset {R : ℝ} (hR : 0 < R) {g : E → ℂ}
    (hg : Function.support g ⊆ closedBall 0 (R * φ.rIn)) :
    g * ⇑(φ.lowPassSchwartz hR.ne') = g := by
  ext ξ
  by_cases hξ : g ξ = 0
  · simp [hξ]
  rw [Pi.mul_apply, lowPassSchwartz_apply, φ.one_of_mem_closedBall, Complex.ofReal_one, mul_one]
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hR.le, inv_mul_le_iff₀ hR]
  exact mem_closedBall_zero_iff.1 (hg hξ)

open FourierTransform in
/-- The kernel `𝓕⁻ (φ (R⁻¹ ·))` of the low-pass symbol at a scale `R > 0` is the
`L¹`-normalised dilate `R^n 𝓕⁻ φ (R ·)` of the kernel at scale `1`, where `n` is the dimension. -/
theorem fourierInv_lowPassSchwartz_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (φ : ContDiffBump (0 : E)) {R : ℝ} (hR : 0 < R) (y : E) :
    𝓕⁻ (⇑(φ.lowPassSchwartz hR.ne')) y =
      (R ^ Module.finrank ℝ E) • 𝓕⁻ (⇑(φ.lowPassSchwartz one_ne_zero)) (R • y) := by
  rw [coe_lowPassSchwartz_eq_comp, TauCeti.fourierInv_comp_smul, inv_inv, inv_pow, abs_inv,
    inv_inv, abs_of_pos (by positivity)]

end ContDiffBump

/-- A compact subset `K` of an open set `U` of a finite-dimensional space has a compactly supported
Schwartz cutoff, with topological support in `U` and equal to `1` on a neighbourhood of `K`. -/
theorem IsCompact.exists_schwartzMap_cutoff [FiniteDimensional ℝ E] {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : 𝓢(E, ℂ), HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∀ᶠ x in 𝓝ˢ K, χ x = 1 := by
  obtain ⟨ψ, hψ, -, hψ1, hψc, hψU⟩ := hK.exists_contDiff_cutoff hU hKU
  have hc : HasCompactSupport fun x ↦ (ψ x : ℂ) := hψc.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ ∞ fun x ↦ (ψ x : ℂ) := Complex.ofRealCLM.contDiff.comp hψ
  have hχ : ⇑(hc.toSchwartzMap hd) = fun x ↦ (ψ x : ℂ) := funext (hc.toSchwartzMap_toFun hd)
  refine ⟨hc.toSchwartzMap hd, by rwa [hχ], ?_, ?_⟩
  · rw [hχ]
    exact (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψU
  filter_upwards [subset_interior_iff_mem_nhdsSet.1 hψ1] with x hx
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
  rw [hχ]
  simp [hx]
