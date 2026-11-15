/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Scaling

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

The estimate is explicit. Suppose `χ = 1` on the ball of radius `r` and `R ≥ 1`. The difference
`f - χ (R⁻¹ • ·) • f` is `(1 - χ (R⁻¹ • ·)) • f`, which vanishes on the ball of radius `r R`.
Expand its `n`-th derivative by the Leibniz rule. The term in which no derivative falls on the
cutoff is supported where `‖x‖ ≥ r R`, so trading one power of `‖x‖` against `(r R)⁻¹` bounds it by
the `(k + 1, n)` seminorm of `f` divided by `r R`. Every other term carries a derivative of
`χ (R⁻¹ • ·)` of order `i ≥ 1`, which is `R⁻ⁱ` times a derivative of `χ` and hence `O(R⁻¹)`.
Altogether the `(k, n)` seminorm of the difference is `O(R⁻¹)`.

## Main results

* `SchwartzMap.seminorm_sub_smulLeftCLM_comp_inv_smul_le`: the explicit bound
  `seminorm k n (f - χ (R⁻¹ • ·) • f) ≤ K / R` for `R ≥ 1`.
* `SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop`: the truncations converge to `f` in
  `𝓢(E, F)`.
* `SchwartzMap.hasCompactSupport_smulLeftCLM_comp_inv_smul`: the truncations are compactly
  supported.
* `SchwartzMap.tendsto_smulLeftCLM_contDiffBump_two_pow`: the dyadic truncations
  `φ (2^{-N} ·) • f` by a `ContDiffBump` converge to `f`, for complex-valued multipliers.
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

/-- Where `‖x‖ ≥ ρ > 0`, one power of `‖x‖` can be traded for `ρ⁻¹` against the next seminorm. -/
private lemma pow_mul_norm_iteratedFDeriv_le_div (f : 𝓢(E, F)) (k j : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {x : E} (hx : ρ ≤ ‖x‖) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ ≤ SchwartzMap.seminorm ℝ (k + 1) j f / ρ := by
  rw [le_div_iff₀ hρ]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ * ρ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ j f x‖ := by ring
    _ ≤ SchwartzMap.seminorm ℝ (k + 1) j f := le_seminorm ℝ (k + 1) j f x

/-- One Leibniz term of `D^n ((1 - χ (R⁻¹ • ·)) • f)` at a point with `‖x‖ ≥ r R` is `O(R⁻¹)`:
if no derivative falls on the cutoff, the factor `‖x‖ ^ k` is traded for `(r R)⁻¹`, and otherwise
the derivative of the cutoff contributes the factor `R⁻¹`. -/
private lemma norm_iteratedFDeriv_one_sub_mul_le {B : ℕ → ℝ}
    (hB : ∀ i x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B i) {r : ℝ} (hr : 0 < r) (f : 𝓢(E, F))
    (k n i : ℕ) {R : ℝ} (hR : 1 ≤ R) {x : E} (hx : r * R ≤ ‖x‖) :
    ‖iteratedFDeriv ℝ i (fun y ↦ 1 - χ (R⁻¹ • y)) x‖ *
        (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) ≤
      (1 + B i) * (SchwartzMap.seminorm ℝ k (n - i) f +
        SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) / R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hB0 : ∀ i, 0 ≤ B i := fun i ↦ (norm_nonneg _).trans (hB i 0)
  have hrR : 0 < r * R := mul_pos hr hR0
  rcases eq_or_ne i 0 with rfl | hi
  · -- No derivative falls on the cutoff: use `‖x‖ ≥ r R`.
    have hh0 : ‖iteratedFDeriv ℝ 0 (fun y ↦ 1 - χ (R⁻¹ • y)) x‖ ≤ 1 + B 0 := by
      rw [norm_iteratedFDeriv_zero]
      refine (norm_sub_le _ _).trans ?_
      have := hB 0 (R⁻¹ • x)
      rw [norm_iteratedFDeriv_zero] at this
      simpa using this
    have hf0 := pow_mul_norm_iteratedFDeriv_le_div f k (n - 0) hrR hx
    have hS : 0 ≤ SchwartzMap.seminorm ℝ k (n - 0) f := apply_nonneg _ _
    calc _ ≤ (1 + B 0) * (SchwartzMap.seminorm ℝ (k + 1) (n - 0) f / (r * R)) :=
          mul_le_mul hh0 hf0 (by positivity) (by linarith [hB0 0])
      _ = (1 + B 0) * (SchwartzMap.seminorm ℝ (k + 1) (n - 0) f / r) / R := by
          field_simp
      _ ≤ _ := by
          gcongr
          · linarith [hB0 0]
          · exact le_add_of_nonneg_left hS
  · -- A derivative falls on the cutoff: it contributes a factor `R⁻¹`.
    have hhi : ‖iteratedFDeriv ℝ i (fun y ↦ 1 - χ (R⁻¹ • y)) x‖ ≤ B i / R := by
      have heq : (fun y ↦ 1 - χ (R⁻¹ • y)) = -(fun y ↦ χ (R⁻¹ • y) - 1) := by
        funext y
        exact (neg_sub _ _).symm
      rw [heq, iteratedFDeriv_neg_apply (𝕜 := ℝ), norm_neg]
      exact TauCeti.norm_iteratedFDeriv_comp_inv_smul_sub_const_le hi (hB i) hR 1 x
    have hfi : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤
        SchwartzMap.seminorm ℝ k (n - i) f := le_seminorm ℝ k (n - i) f x
    have hS : 0 ≤ SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r :=
      div_nonneg (apply_nonneg _ _) hr.le
    calc _ ≤ B i / R * SchwartzMap.seminorm ℝ k (n - i) f :=
          mul_le_mul hhi hfi (by positivity) (by have := hB0 i; positivity)
      _ ≤ (1 + B i) / R * (SchwartzMap.seminorm ℝ k (n - i) f +
            SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) := by
          gcongr
          · exact div_nonneg (by linarith [hB0 i]) hR0.le
          · linarith
          · exact le_add_of_nonneg_right hS
      _ = _ := by ring

/-- **The truncation estimate.** Let `χ` be smooth with `‖D^i χ‖ ≤ B i` for every `i`, and equal
to `1` on the ball of radius `r > 0`. For `R ≥ 1` the `(k, n)` seminorm of `f - χ (R⁻¹ • ·) • f`
is at most `K / R`, where `K` depends on `χ`, `f`, `k` and `n` but not on `R`. -/
theorem seminorm_sub_smulLeftCLM_comp_inv_smul_le (hχ : ContDiff ℝ ∞ χ)
    {B : ℕ → ℝ} (hB : ∀ i x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B i)
    {r : ℝ} (hr : 0 < r) (hχ1 : ∀ y, ‖y‖ < r → χ y = 1) (f : 𝓢(E, F)) (k n : ℕ) {R : ℝ}
    (hR : 1 ≤ R) :
    SchwartzMap.seminorm ℝ k n (f - smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
        (SchwartzMap.seminorm ℝ k (n - i) f + SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r)) /
        R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hB0 : ∀ i, 0 ≤ B i := fun i ↦ (norm_nonneg _).trans (hB i 0)
  set h : E → ℝ := fun y ↦ 1 - χ (R⁻¹ • y) with hh
  have hhsmooth : ContDiff ℝ ∞ h := contDiff_const.sub (hχ.comp (contDiff_const_smul _))
  have hcoe : ⇑(f - smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) = fun x ↦ h x • f x := by
    ext x
    have hχt : χ.HasTemperateGrowth := ⟨hχ, fun i ↦ ⟨0, B i, fun x ↦ by simpa using hB i x⟩⟩
    simp only [sub_apply, smulLeftCLM_comp_inv_smul_apply hχt R f x, hh, sub_smul, one_smul]
  have hK : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
      (SchwartzMap.seminorm ℝ k (n - i) f + SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (by linarith [hB0 i])) (add_nonneg (apply_nonneg _ _) (div_nonneg (apply_nonneg _ _) hr.le))
  refine seminorm_le_bound ℝ k n _ (div_nonneg hK hR0.le) fun x ↦ ?_
  rw [hcoe]
  rcases lt_or_ge ‖x‖ (r * R) with hx | hx
  · -- Near the origin the truncation agrees with `f`, so the difference is locally zero.
    have hzero : (fun y ↦ h y • f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
      rw [mem_ball_zero_iff] at hy
      have hy' : ‖R⁻¹ • y‖ < r := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hR0.le, inv_mul_lt_iff₀ hR0]
        linarith
      simp [hh, hχ1 _ hy']
    rw [(hzero.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply,
      norm_zero, mul_zero]
    exact div_nonneg hK hR0.le
  · -- Away from the origin, expand by the Leibniz rule and bound each term by `O(R⁻¹)`.
    refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hhsmooth (f.smooth ⊤) x
      (mod_cast le_top)) (by positivity)).trans ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i h x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        = (n.choose i : ℝ) *
            (‖iteratedFDeriv ℝ i h x‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖)) := by ring
      _ ≤ (n.choose i : ℝ) * ((1 + B i) * (SchwartzMap.seminorm ℝ k (n - i) f +
            SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r) / R) :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_one_sub_mul_le hB hr f k n i hR hx)
            (Nat.cast_nonneg _)
      _ = _ := by ring

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
    (SchwartzMap.seminorm ℝ k (n - i) f + SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r)
  filter_upwards [eventually_ge_atTop 1, eventually_gt_atTop (K / ε)] with R hR hKR
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  rw [schwartzSeminormFamily_apply, ← map_neg_eq_map, neg_sub]
  refine (seminorm_sub_smulLeftCLM_comp_inv_smul_le hχ hB hr hχ1' f k n hR).trans_lt ?_
  rw [div_lt_iff₀ hR0]
  rwa [div_lt_iff₀ hε, mul_comm] at hKR

section Truncation

variable [FiniteDimensional ℝ E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The low-pass truncations `φ (2^{-N} ·) • f` of a Schwartz function converge to `f` in the
Schwartz topology. -/
theorem tendsto_smulLeftCLM_contDiffBump_two_pow (φ : ContDiffBump (0 : E)) (f : 𝓢(E, G)) :
    Tendsto (fun N : ℕ ↦ smulLeftCLM G (fun ξ ↦ (φ (((2 : ℝ) ^ N)⁻¹ • ξ) : ℂ)) f) atTop
      (𝓝 f) := by
  have hφ : (⇑φ).HasTemperateGrowth := φ.hasCompactSupport.hasTemperateGrowth φ.contDiff
  have h := (tendsto_smulLeftCLM_comp_smul φ.contDiff φ.hasCompactSupport φ.eventuallyEq_one
    f).comp (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))))
  refine h.congr fun N ↦ ?_
  have hc : (fun ξ ↦ φ (((2 : ℝ) ^ N)⁻¹ • ξ)).HasTemperateGrowth := by fun_prop
  rw [Function.comp_apply, Function.comp_apply, ← smulLeftCLM_ofReal ℂ hc,
    RCLike.ofReal_eq_complex_ofReal]

end Truncation

section Lattice

open TauCeti

/-- A Schwartz function times a smooth function `h` with bounded derivatives that vanishes on the
ball of radius `ρ` about the origin has Schwartz seminorms of size `O(ρ⁻¹)`. -/
private theorem seminorm_le_of_eq_smul_of_eq_zero {h : E → ℝ} (hh : ContDiff ℝ ∞ h)
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
    have hf : ‖y‖ ^ k * ‖iteratedFDeriv ℝ (j - i) f y‖ ≤
        SchwartzMap.seminorm ℝ (k + 1) (j - i) f / ρ := by
      rw [le_div_iff₀ hρ]
      calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ (j - i) f y‖ * ρ ≤
            ‖y‖ ^ k * ‖iteratedFDeriv ℝ (j - i) f y‖ * ‖y‖ :=
            mul_le_mul_of_nonneg_left hy (by positivity)
        _ = ‖y‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (j - i) f y‖ := by ring
        _ ≤ _ := SchwartzMap.le_seminorm ℝ (k + 1) (j - i) f y
    calc ‖y‖ ^ k * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i h y‖ *
          ‖iteratedFDeriv ℝ (j - i) f y‖)
        = (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i h y‖ *
            (‖y‖ ^ k * ‖iteratedFDeriv ℝ (j - i) f y‖) := by ring
      _ ≤ (j.choose i : ℝ) * B i * (SchwartzMap.seminorm ℝ (k + 1) (j - i) f / ρ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hB i y) (Nat.cast_nonneg _)) hf (by positivity)
            (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
      _ = _ := by ring


variable {n : ℕ}

/-- The partial sums of the lattice partition of unity, minus `1`, have derivatives bounded
independently of the finite set of lattice points. -/
private theorem norm_iteratedFDeriv_sum_latticeBump_sub_sub_one_le {k : ℕ} {B : ℝ}
    (hB : ∀ y, ‖iteratedFDeriv ℝ k (latticeBump n) y‖ ≤ B) (s : Finset (Fin n → ℤ))
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ k (fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j) - 1) y‖ ≤
      B * (1 + (n : ℝ)) ^ n * (8 ^ n * ∑' d : Fin n → ℤ, latticeWeight d) + 1 := by
  have hs : ContDiff ℝ k fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j) :=
    ContDiff.sum fun j _ ↦ contDiff_latticeBump.comp (contDiff_id.sub contDiff_const)
  have e : (fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j) - 1) =
      (fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j)) - fun _ ↦ (1 : ℝ) := rfl
  rw [e, iteratedFDeriv_sub_apply hs.contDiffAt contDiff_const.contDiffAt]
  refine (norm_sub_le _ _).trans (add_le_add
    (norm_iteratedFDeriv_sum_latticeBump_sub_le hB s y) ?_)
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [iteratedFDeriv_const_of_ne hk]

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
  have hsmooth (j : Fin n → ℤ) : ContDiff ℝ ∞ fun y ↦ latticeBump n (y - latticePoint j) :=
    contDiff_latticeBump.comp (contDiff_id.sub contDiff_const)
  have htg (j : Fin n → ℤ) : (fun y ↦ latticeBump n (y - latticePoint j)).HasTemperateGrowth :=
    (hasCompactSupport_latticeBump.comp_homeomorph
      (Homeomorph.subRight (latticePoint j))).hasTemperateGrowth (hsmooth j)
  rw [HasSum, (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin n)) F).tendsto_nhds]
  rintro ⟨k, j⟩ ε hε
  set K := ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * (B i * (1 + (n : ℝ)) ^ n * S + 1) * SchwartzMap.seminorm ℝ (k + 1) (j - i) f
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ ↦ by have := hB0 i; positivity
  set R := √n + K / ε + 1
  have hRn : 0 < R - √n := by have := div_nonneg hK hε.le; simp only [R]; linarith
  filter_upwards [Filter.eventually_ge_atTop (finite_setOf_norm_latticePoint_lt R).toFinset]
    with s hs
  rw [schwartzSeminormFamily_apply]
  -- The partial sum is `f` times `∑_{j ∈ s} χ(· - j) - 1`, which vanishes on `‖y‖ < R - √n`.
  refine (seminorm_le_of_eq_smul_of_eq_zero
    (h := fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j) - 1)
    ((ContDiff.sum fun j _ ↦ hsmooth j).sub contDiff_const)
    (B := fun i ↦ B i * (1 + (n : ℝ)) ^ n * S + 1) (fun i y ↦ ?_) hRn (fun y hy ↦ ?_)
    (f := f) (fun y ↦ ?_) k j).trans_lt ?_
  · exact norm_iteratedFDeriv_sum_latticeBump_sub_sub_one_le (hB i) s y
  · simp [sum_latticeBump_sub_eq_one (fun j hj ↦ hs ((Set.Finite.mem_toFinset _).2 hj))
      (by linarith : ‖y‖ + √n < R)]
  · simp [SchwartzMap.smulLeftCLM_apply_apply (htg _), Finset.sum_smul, sub_smul]
  · rw [div_lt_iff₀ hRn]
    calc K = K / ε * ε := by field_simp
      _ < (R - √n) * ε := by gcongr; simp only [R]; linarith
      _ = ε * (R - √n) := mul_comm _ _

end Lattice

end SchwartzMap

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
