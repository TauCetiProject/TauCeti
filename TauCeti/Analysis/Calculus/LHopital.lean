/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.MeanValue

/-!
# L'Hôpital's rule for little-o at `+∞`

Mathlib's L'Hôpital rules (`HasDerivAt.lhopital_zero_atTop` and its variants) treat limits of
quotients of real functions in the form `0/0`. This file proves the comparison form of the rule
for `∞/∞` at `+∞`, with a numerator in any real normed space: if `g → +∞` with `g' ≥ 0`
eventually, and `f' = o(g')`, then `f = o(g)` (`TauCeti.isLittleO_atTop_of_hasDerivAt`).

It is used to compare a function with an explicit primitive of a dominant integrand, as in the
asymptotics of `∫ˣ e^{2ξ} ξ' (1 + o(1))`, where only the derivatives are known in closed form.
The proof is the mean value inequality with variable bound
(`image_norm_le_of_norm_deriv_right_le_deriv_boundary'`) on `[x₀, x]`.
-/

public section

open Set Filter Asymptotics
open scoped Topology

namespace TauCeti

/-- **L'Hôpital's rule for little-o at `+∞`.** Let `f` take values in a real normed space and let
`g` be real, with derivatives `f'` and `g'` eventually. If `g → +∞`, `g' ≥ 0` eventually and
`f' = o(g')`, then `f = o(g)`. -/
theorem isLittleO_atTop_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {g g' : ℝ → ℝ} (hf : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in atTop, HasDerivAt g (g' x) x) (hg₀ : ∀ᶠ x in atTop, 0 ≤ g' x)
    (hgt : Tendsto g atTop atTop) (hfg : f' =o[atTop] g') : f =o[atTop] g := by
  refine IsLittleO.of_bound fun c hc ↦ ?_
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 <|
    (hf.and hg).and (hg₀.and (hfg.bound (half_pos hc)))
  -- the mean value inequality on `[x₀, x]`: `‖f x - f x₀‖ ≤ c / 2 (g x - g x₀)`
  have hmv (x : ℝ) (hx : x₀ ≤ x) : ‖f x - f x₀‖ ≤ c / 2 * (g x - g x₀) := by
    have hd (y : ℝ) (hy : y ∈ Icc x₀ x) := hx₀ y hy.1
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := fun y ↦ f y - f x₀)
      (f' := f') (B := fun y ↦ c / 2 * (g y - g x₀)) (B' := fun y ↦ c / 2 * g' y)
      (fun y hy ↦ ((hd y hy).1.1.continuousAt.sub continuousAt_const).continuousWithinAt)
      (fun y hy ↦ ((hd y (Ico_subset_Icc_self hy)).1.1.sub_const (f x₀)).hasDerivWithinAt)
      (by simp) (fun y hy ↦ (((hd y hy).1.2.continuousAt.sub
        continuousAt_const).const_mul _).continuousWithinAt)
      (fun y hy ↦ (((hd y (Ico_subset_Icc_self hy)).1.2.sub_const (g x₀)).const_mul
        (c / 2)).hasDerivWithinAt) (fun y hy ↦ ?_) ⟨hx, le_rfl⟩
    obtain ⟨h0, h⟩ := (hd y (Ico_subset_Icc_self hy)).2
    rwa [Real.norm_of_nonneg h0] at h
  filter_upwards [eventually_ge_atTop x₀,
    hgt.eventually_ge_atTop (2 / c * ‖f x₀‖ + |g x₀|), hgt.eventually_ge_atTop 0] with x hx hgx hg0
  rw [Real.norm_of_nonneg hg0]
  have h1 := norm_sub_norm_le (f x) (f x₀)
  have h2 := hmv x hx
  have h3 := neg_le_abs (g x₀)
  have h4 : c / 2 * (2 / c * ‖f x₀‖ + |g x₀|) ≤ c / 2 * g x :=
    mul_le_mul_of_nonneg_left hgx (by positivity)
  have h5 : c / 2 * (2 / c * ‖f x₀‖) = ‖f x₀‖ := by field_simp
  nlinarith [h1, h2, h3, h4, h5, abs_nonneg (g x₀)]

end TauCeti
