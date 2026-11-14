/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Second derivatives and Taylor remainders along a line

Mathlib's `DifferentiableAt.deriv_comp_add_smul` computes the derivative of the restriction
`s ↦ f (x + s • y)` of a function to a line. This file records the second derivative: it is the
diagonal entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` of the Hessian. It also bounds the
integral remainder in Mathlib's `map_add_eq_sum_add_integral_iteratedFDeriv`, Taylor's theorem
along a segment for a function on a normed space.

## Main results

* `DifferentiableAt.hasDerivAt_deriv_comp_add_smul`: if `f` is differentiable near `x + t • y`
  and `fderiv 𝕜 f` is differentiable at `x + t • y`, then the derivative of
  `s ↦ f (x + s • y)` has derivative `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` at `t`.
* `ContDiffAt.deriv_deriv_comp_add_smul`: the second derivative of `s ↦ f (x + s • y)` at `t` is
  `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y`, for `f` of class `C²` at `x + t • y`.
* `TauCeti.norm_sub_sum_iteratedFDeriv_le`: Taylor's theorem with a bound on the remainder for a
  function on a normed space, along a segment, from a bound on the next Fréchet derivative.
* `TauCeti.norm_sub_sum_iteratedFDeriv_le_one_add_norm_sq_rpow`: the Taylor remainder of a
  function whose next derivative has polynomial growth, `C' ⟨ξ⟩ ^ t ⟨v⟩ ^ (|t| + N + 1)`.
-/

public section

open Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {x y : E} {t : 𝕜}

/-- If `f` is differentiable near `x + t • y` and `fderiv 𝕜 f` is differentiable at
`x + t • y`, then the derivative of the restriction `s ↦ f (x + s • y)` of `f` to a line has
derivative the diagonal Hessian entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y` at `t`. -/
theorem DifferentiableAt.hasDerivAt_deriv_comp_add_smul
    (hf' : DifferentiableAt 𝕜 (fderiv 𝕜 f) (x + t • y))
    (hf : ∀ᶠ z in 𝓝 (x + t • y), DifferentiableAt 𝕜 f z) :
    HasDerivAt (deriv fun s : 𝕜 => f (x + s • y)) (fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y) t := by
  have hline : HasDerivAt (fun s : 𝕜 => x + s • y) y t := by
    simpa using ((hasDerivAt_id t).smul_const y).const_add x
  have hev : (fun s => fderiv 𝕜 f (x + s • y) y) =ᶠ[𝓝 t] deriv fun s : 𝕜 => f (x + s • y) := by
    filter_upwards [hline.continuousAt.tendsto.eventually hf] with s hs
    exact hs.deriv_comp_add_smul.symm
  simpa using ((hf'.hasFDerivAt.comp_hasDerivAt t hline).clm_apply
    (hasDerivAt_const t y)).congr_of_eventuallyEq hev.symm

/-- The second derivative of the restriction `s ↦ f (x + s • y)` of a `C²` function to a line is
the diagonal Hessian entry `fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y`. -/
theorem ContDiffAt.deriv_deriv_comp_add_smul (hf : ContDiffAt 𝕜 2 f (x + t • y)) :
    deriv (deriv fun s : 𝕜 => f (x + s • y)) t = fderiv 𝕜 (fderiv 𝕜 f) (x + t • y) y y :=
  ((hf.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasDerivAt_deriv_comp_add_smul
    (hf.eventually (by simp) |>.mono fun _ hz => hz.differentiableAt two_ne_zero) |>.deriv

open Set
open scoped Nat

namespace TauCeti

/-! ### Taylor's theorem along a segment -/

section Segment

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [CompleteSpace G]

/-- **Taylor's theorem along a segment**, with a bound on the remainder. If `h` is `C^{N+1}` at
every point of the segment from `ξ` to `ξ + v` and its `(N + 1)`-st derivative is bounded by `B`
there, then `h (ξ + v)` differs
from the Taylor polynomial `∑_{k ≤ N} D^k h(ξ) (v, …, v) / k!` by at most
`B ‖v‖ ^ (N + 1) / N!`. This bounds the integral remainder of Mathlib's
`map_add_eq_sum_add_integral_iteratedFDeriv`. -/
theorem norm_sub_sum_iteratedFDeriv_le {h : E → G} {N : ℕ} (ξ v : E)
    (hh : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (N + 1) h (ξ + s • v)) {B : ℝ}
    (hB : ∀ s ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (N + 1) h (ξ + s • v)‖ ≤ B) :
    ‖h (ξ + v) - ∑ k ∈ Finset.range (N + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k h ξ (fun _ ↦ v)‖ ≤
      B * ‖v‖ ^ (N + 1) / N ! := by
  rw [map_add_eq_sum_add_integral_iteratedFDeriv hh, add_sub_cancel_left,
    norm_smul, norm_inv, RCLike.norm_natCast, inv_mul_eq_div]
  gcongr
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_).trans_eq
    (by rw [sub_zero, abs_one, mul_one])
  rw [uIoc_of_le zero_le_one] at ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
  rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht'.2])]
  refine (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (by linarith [ht'.2])
    (by linarith [ht'.1]))).trans ?_
  refine ((iteratedFDeriv ℝ (N + 1) h (ξ + t • v)).le_opNorm _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact hB t ht'

/-- **Taylor's theorem with a weighted remainder.** If the `(N + 1)`-st derivative of `h` grows
like `‖D^{N+1} h ζ‖ ≤ C ⟨ζ⟩ ^ t`, then by Peetre's inequality `h (ξ + v)` differs from its Taylor
polynomial of order `N` at `ξ` by at most `C 2 ^ (|t| / 2) / N! ⟨ξ⟩ ^ t ⟨v⟩ ^ (|t| + N + 1)`, where
`⟨x⟩ ^ s = (1 + ‖x‖ ^ 2) ^ (s / 2)`. -/
theorem norm_sub_sum_iteratedFDeriv_le_one_add_norm_sq_rpow {h : E → G} {N : ℕ}
    (hh : ContDiff ℝ (N + 1) h) {C t : ℝ}
    (hN : ∀ ζ, ‖iteratedFDeriv ℝ (N + 1) h ζ‖ ≤ C * (1 + ‖ζ‖ ^ 2) ^ (t / 2)) (ξ v : E) :
    ‖h (ξ + v) - ∑ k ∈ Finset.range (N + 1), (k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k h ξ (fun _ ↦ v)‖ ≤
      C * 2 ^ (|t| / 2) / N ! * (1 + ‖ξ‖ ^ 2) ^ (t / 2) *
        (1 + ‖v‖ ^ 2) ^ ((|t| + (N + 1)) / 2) := by
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hN 0)
    exact nonneg_of_mul_nonneg_left this (by positivity)
  set w := 1 + ‖v‖ ^ 2
  -- Peetre's inequality bounds the `(N + 1)`-st derivative along the segment.
  have hB : ∀ s ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (N + 1) h (ξ + s • v)‖ ≤
      C * (2 ^ (|t| / 2) * w ^ (|t| / 2) * (1 + ‖ξ‖ ^ 2) ^ (t / 2)) := fun s hs ↦ by
    refine (hN _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    refine (one_add_norm_sq_rpow_le_mul_sub t (ξ + s • v) ξ).trans ?_
    gcongr
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1]
    have : s * ‖v‖ ≤ ‖v‖ := mul_le_of_le_one_left (norm_nonneg _) hs.2
    have : 0 ≤ s * ‖v‖ := mul_nonneg hs.1 (norm_nonneg _)
    simp only [w]
    nlinarith
  refine (norm_sub_sum_iteratedFDeriv_le ξ v (fun _ _ ↦ hh.contDiffAt) hB).trans (le_of_le_of_eq
    (b := C * (2 ^ (|t| / 2) * w ^ (|t| / 2) * (1 + ‖ξ‖ ^ 2) ^ (t / 2)) *
      w ^ (((N + 1 : ℕ) : ℝ) / 2) / N !) ?_ ?_)
  · gcongr
    exact norm_pow_le_one_add_norm_sq_rpow _ _
  · have hw : w ^ (|t| / 2) * w ^ (((N + 1 : ℕ) : ℝ) / 2) = w ^ ((|t| + (N + 1)) / 2) := by
      rw [← Real.rpow_add (by positivity)]
      push_cast
      ring_nf
    rw [← hw]
    field_simp

end Segment

end TauCeti
