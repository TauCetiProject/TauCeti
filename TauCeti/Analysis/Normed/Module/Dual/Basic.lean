/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Algebra.InfiniteSum.Module
import TauCeti.Analysis.Normed.Operator.Prod

/-!
# Real parts of continuous linear functionals

For a continuous linear functional `f` on a seminormed space over `RCLike` scalars and a radius
`0 ≤ r`, the upper bounds of `re ∘ f` on `closedBall x r` are exactly the reals that are at least
`re (f x) + r * ‖f‖`. Hahn–Banach separation arguments use this to turn a separating real-part
bound on a ball into a bound on the norm of the separating functional. Similarly, for `0 ≤ r`
the real part of `f` exceeds `r * ‖x‖` at some point `x` if and only if `r < ‖f‖`. Applying
`re_apply_add_mul_norm_le_iff` on unit balls of two factors gives the `ℓ¹` norm identity
`‖Ψ ∘ inl‖ + ‖Ψ ∘ inr‖ = ‖Ψ‖` on `ℓ^∞` products `E × F`.

Rotating a vector by a unit scalar turns `f x` into the nonnegative real `‖f x‖`. So a
functional attains its norm on the closed unit ball exactly when its real part takes the value
`‖f‖` there, and exactly when its real part has a maximum there. Real parts of functionals also
commute with real-weighted series of a bounded family.

For `0 < c`, the scaled Fenchel–Young inequality `2 re (f x) ≤ ‖f‖ ^ 2 / c + c ‖x‖ ^ 2` bounds the
real part of `f` at every point, and it determines the dual norm: `‖f‖ ^ 2 / c` is the supremum of
`2 re (f x) - c ‖x‖ ^ 2` over all `x`.

## Main results

* `StrongDual.re_apply_add_mul_norm_le_iff`: for `0 ≤ r`, the real part of a functional is at
  most `u` on `closedBall x r` if and only if its value at the centre plus the radius times its
  norm is at most `u`.
* `StrongDual.exists_mul_norm_lt_re_apply_iff`: for `0 ≤ r`, the real part of `f` exceeds
  `r * ‖x‖` at some point `x` if and only if `r < ‖f‖`.
* `StrongDual.norm_comp_inl_add_norm_comp_inr`: on `E × F` over `RCLike` scalars, the operator
  norm of `Ψ` equals the sum of the norms of its restrictions `Ψ.comp (.inl 𝕜 E F)` and
  `Ψ.comp (.inr 𝕜 E F)`.
* `StrongDual.exists_norm_le_one_re_apply_eq_norm_iff`,
  `StrongDual.exists_isMaxOn_re_apply_closedBall_iff`: a functional attains its norm on the
  closed unit ball exactly when its real part takes the value `‖f‖`, or has a maximum, there.
* `StrongDual.hasSum_mul_re_apply`: the real part of a functional applied to a real-weighted
  series of a bounded family.
* `StrongDual.two_mul_re_apply_le`: the scaled Fenchel–Young inequality.
* `StrongDual.sq_norm_div_le_of_forall`: an upper bound on `2 re (f x) - c ‖x‖ ^ 2` for all `x`
  bounds `‖f‖ ^ 2 / c`.
-/

public section

open Metric RCLike

variable {𝕜 E F : Type*}

namespace StrongDual

variable [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The real part of a continuous linear functional `f` is at most `u` on the closed ball of
radius `r ≥ 0` about `x` if and only if `re (f x) + r * ‖f‖ ≤ u`. Thus `re (f x) + r * ‖f‖` is
the least upper bound of `re ∘ f` on that ball. -/
theorem re_apply_add_mul_norm_le_iff {f : StrongDual 𝕜 E} {x : E} {r u : ℝ} (hr : 0 ≤ r) :
    re (f x) + r * ‖f‖ ≤ u ↔ ∀ y ∈ closedBall x r, re (f y) ≤ u := by
  refine ⟨fun hu y hy ↦ ?_, fun h ↦ ?_⟩
  · -- `re (f (y - x)) ≤ ‖f‖ * ‖y - x‖ ≤ ‖f‖ * r`, and `f y = f x + f (y - x)`.
    have hyx : re (f (y - x)) ≤ ‖f‖ * r :=
      (re_le_norm _).trans <| (f.le_opNorm _).trans <|
        mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.1 hy) (norm_nonneg f)
    rw [map_sub, map_sub] at hyx
    linarith
  have hx : re (f x) ≤ u := h x (mem_closedBall_self hr)
  rcases hr.eq_or_lt with rfl | hr
  · simpa using hx
  suffices ‖f‖ ≤ (u - re (f x)) / r by
    rw [le_div_iff₀ hr] at this
    linarith
  refine f.opNorm_le_bound' (div_nonneg (sub_nonneg.2 hx) hr.le) fun z hz ↦ ?_
  have hz : 0 < ‖z‖ := (norm_nonneg z).lt_of_ne' hz
  -- Rotate `z` so that `f` takes a nonnegative real value on it, and rescale it to norm `r`.
  obtain ⟨a, ha, hfz⟩ := exists_norm_eq_mul_self (f z)
  have hy := h (x + ((r / ‖z‖ : ℝ) : 𝕜) • a • z) <| by
    simp [dist_eq_norm, norm_smul, ha, abs_of_pos hr, hz.ne']
  simp only [map_add, map_smul, smul_eq_mul, ← hfz, ← ofReal_mul, ofReal_re] at hy
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  field_simp at hy
  nlinarith

/-- For `0 ≤ r`, the real part of `f` exceeds `r * ‖x‖` at some point `x` if and only if
`r < ‖f‖`. -/
theorem exists_mul_norm_lt_re_apply_iff (f : StrongDual 𝕜 E) {r : ℝ} (hr₀ : 0 ≤ r) :
    (∃ x, r * ‖x‖ < re (f x)) ↔ r < ‖f‖ := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun hr ↦ ?_⟩
  · -- `r * ‖x‖ < re (f x) ≤ ‖f‖ * ‖x‖`.
    exact lt_of_mul_lt_mul_right (hx.trans_le ((re_le_norm _).trans (f.le_opNorm x)))
      (norm_nonneg x)
  obtain ⟨x, hx⟩ := f.exists_mul_lt_of_lt_opNorm hr₀ hr
  -- Rotate `x` so that `f` takes the nonnegative real value `‖f x‖` on it.
  obtain ⟨a, ha, hax⟩ := exists_norm_eq_mul_self (f x)
  refine ⟨a • x, ?_⟩
  rw [map_smul, smul_eq_mul, ← hax, ofReal_re, norm_smul, ha, one_mul]
  exact hx

/-- On an `ℓ^∞`-normed product `E × F` over `RCLike` scalars, the operator norm of `Ψ` equals the
sum of the norms of its restrictions to the two factors. -/
theorem norm_comp_inl_add_norm_comp_inr [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (Ψ : StrongDual 𝕜 (E × F)) :
    ‖Ψ.comp (ContinuousLinearMap.inl 𝕜 E F)‖ + ‖Ψ.comp (ContinuousLinearMap.inr 𝕜 E F)‖ = ‖Ψ‖ := by
  set f₀ := Ψ.comp (.inl 𝕜 E F); set f₁ := Ψ.comp (.inr 𝕜 E F)
  refine le_antisymm ?_
    ((congrArg norm Ψ.coprod_comp_inl_inr.symm).trans_le (f₀.opNorm_coprod_le f₁))
  have hball {y₀ : E} (hy₀ : y₀ ∈ closedBall 0 1) {y₁ : F} (hy₁ : y₁ ∈ closedBall 0 1) :
      re (f₀ y₀) + re (f₁ y₁) ≤ ‖Ψ‖ := by
    have hnorm : ‖(y₀, y₁)‖ ≤ 1 := by
      simp [Prod.norm_def, mem_closedBall_zero_iff.1 hy₀, mem_closedBall_zero_iff.1 hy₁]
    rw [← map_add, Ψ.comp_inl_add_comp_inr (y₀, y₁)]
    exact (re_le_norm _).trans <|
      (Ψ.le_opNorm _).trans <| mul_le_of_le_one_right (norm_nonneg Ψ) hnorm
  have h₁ : ∀ y₁ ∈ closedBall (0 : F) 1, re (f₁ y₁) ≤ ‖Ψ‖ - ‖f₀‖ := fun y₁ hy₁ ↦ by
    have h0 := (re_apply_add_mul_norm_le_iff (f := f₀) (x := 0) (u := ‖Ψ‖ - re (f₁ y₁))
      zero_le_one).2 fun y₀ hy₀ ↦ by linarith [hball hy₀ hy₁]
    rw [map_zero, map_zero, zero_add, one_mul] at h0; linarith
  have h0 := (re_apply_add_mul_norm_le_iff (f := f₁) (x := 0) zero_le_one).2 h₁
  rw [map_zero, map_zero, zero_add, one_mul] at h0; linarith

/-- A rotation `y` of `x`, of the same norm, on which `f` takes the nonnegative real value
`‖f x‖`. -/
theorem exists_norm_eq_apply_eq_norm_apply (f : StrongDual 𝕜 E) (x : E) :
    ∃ y : E, ‖y‖ = ‖x‖ ∧ f y = ‖f x‖ := by
  obtain ⟨a, ha, hax⟩ := exists_norm_eq_mul_self (f x)
  exact ⟨a • x, by rw [norm_smul, ha, one_mul], by rw [map_smul, smul_eq_mul, hax]⟩

/-- A functional attains its norm on the closed unit ball exactly when its real part takes the
value `‖f‖` there. -/
theorem exists_norm_le_one_re_apply_eq_norm_iff {f : StrongDual 𝕜 E} :
    (∃ x : E, ‖x‖ ≤ 1 ∧ re (f x) = ‖f‖) ↔ ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ := by
  refine ⟨fun ⟨x, hx, h⟩ ↦ ⟨x, hx, (f.unit_le_opNorm x hx).antisymm
    (h.symm.trans_le (re_le_norm _))⟩, fun ⟨x, hx, h⟩ ↦ ?_⟩
  obtain ⟨y, hy, hfy⟩ := f.exists_norm_eq_apply_eq_norm_apply x
  exact ⟨y, hy ▸ hx, by rw [hfy, ofReal_re, h]⟩

/-- A functional attains its norm on the closed unit ball exactly when its real part has a maximum
there. -/
theorem exists_isMaxOn_re_apply_closedBall_iff {f : StrongDual 𝕜 E} :
    (∃ x ∈ closedBall (0 : E) 1, IsMaxOn (fun y ↦ re (f y)) (closedBall 0 1) x) ↔
      ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ := by
  rw [← exists_norm_le_one_re_apply_eq_norm_iff]
  refine ⟨fun ⟨x, hx, hmax⟩ ↦ ⟨x, mem_closedBall_zero_iff.1 hx, ?_⟩, fun ⟨x, hx, h⟩ ↦
    ⟨x, mem_closedBall_zero_iff.2 hx, isMaxOn_iff.2 fun y hy ↦ h ▸ (re_le_norm _).trans
      (f.unit_le_opNorm y (mem_closedBall_zero_iff.1 hy))⟩⟩
  -- `re (f x)` bounds `re ∘ f` on the closed unit ball, so it is at least `‖f‖`.
  refine ((re_le_norm _).trans (f.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx))).antisymm ?_
  simpa using (re_apply_add_mul_norm_le_iff (f := f) (x := 0) zero_le_one).2
    fun y hy ↦ isMaxOn_iff.1 hmax y hy

/-- The real part of a functional `L` commutes with a real-weighted series `∑' i, w i • h i` of a
bounded family `h`. -/
theorem hasSum_mul_re_apply {ι : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] (L : StrongDual 𝕜 F) {w : ι → ℝ} (hw : Summable w) {h : ι → F} {C : ℝ}
    (hC : ∀ i, ‖h i‖ ≤ C) :
    HasSum (fun i ↦ w i * re (L (h i))) (re (L (∑' i, (w i : 𝕜) • h i))) := by
  have hs : Summable fun i ↦ (w i : 𝕜) • h i :=
    Summable.of_norm_bounded (hw.abs.mul_right C) fun i ↦ by
      rw [norm_smul, norm_ofReal]
      exact mul_le_mul_of_nonneg_left (hC i) (abs_nonneg _)
  simpa only [map_smul, smul_eq_mul, reCLM_apply, re_ofReal_mul] using
    reCLM.hasSum (L.hasSum hs.hasSum)

/-- The scaled Fenchel–Young inequality `2 re (f x) ≤ ‖f‖ ^ 2 / c + c ‖x‖ ^ 2` for `0 < c`. -/
theorem two_mul_re_apply_le (f : StrongDual 𝕜 E) (x : E) {c : ℝ} (hc : 0 < c) :
    2 * re (f x) ≤ ‖f‖ ^ 2 / c + c * ‖x‖ ^ 2 := by
  have h₁ : re (f x) ≤ ‖f‖ * ‖x‖ := (re_le_norm _).trans (f.le_opNorm x)
  have h₂ := two_mul_le_add_mul_sq (a := ‖x‖) (b := ‖f‖) hc
  rw [div_eq_inv_mul]
  linarith

/-- The scaled Fenchel–Young inequality determines the dual norm: if
`2 re (f x) - c ‖x‖ ^ 2 ≤ B` for every `x`, then `‖f‖ ^ 2 / c ≤ B`. -/
theorem sq_norm_div_le_of_forall {f : StrongDual 𝕜 E} {c B : ℝ} (hc : 0 < c)
    (h : ∀ x, 2 * re (f x) - c * ‖x‖ ^ 2 ≤ B) : ‖f‖ ^ 2 / c ≤ B := by
  have hB : 0 ≤ B := by simpa using h 0
  by_contra! hlt
  -- Otherwise `r = √(c B) < ‖f‖`, and a vector on which `re f` exceeds `r ‖x‖`, suitably
  -- rescaled, violates the bound.
  have hf : 0 < ‖f‖ := (norm_nonneg f).lt_of_ne fun h₀ ↦ by
    rw [← h₀] at hlt
    simp at hlt
    linarith
  have hr : √(c * B) < ‖f‖ := by
    rw [Real.sqrt_lt' hf]
    rwa [lt_div_iff₀ hc, mul_comm] at hlt
  obtain ⟨x, hx⟩ := (f.exists_mul_norm_lt_re_apply_iff (Real.sqrt_nonneg _)).2 hr
  have hfx : 0 < re (f x) := lt_of_le_of_lt (by positivity) hx
  have hx₀ : 0 < ‖x‖ := (norm_nonneg x).lt_of_ne fun h₀ ↦ by
    have := (re_le_norm (f x)).trans (f.le_opNorm x)
    rw [← h₀, mul_zero] at this
    linarith
  have hcx : 0 < c * ‖x‖ ^ 2 := mul_pos hc (pow_pos hx₀ 2)
  set s : ℝ := re (f x) / (c * ‖x‖ ^ 2)
  have hs := h ((s : 𝕜) • x)
  rw [map_smul, smul_eq_mul, re_ofReal_mul, norm_smul, norm_ofReal,
    abs_of_pos (div_pos hfx hcx)] at hs
  have e : 2 * (s * re (f x)) - c * (s * ‖x‖) ^ 2 = re (f x) ^ 2 / (c * ‖x‖ ^ 2) := by
    have := hx₀.ne'
    simp only [s]
    field_simp
    ring
  rw [e, div_le_iff₀ hcx] at hs
  have h₁ : (√(c * B) * ‖x‖) ^ 2 < re (f x) ^ 2 := pow_lt_pow_left₀ hx (by positivity) two_ne_zero
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h₁
  nlinarith

end StrongDual
