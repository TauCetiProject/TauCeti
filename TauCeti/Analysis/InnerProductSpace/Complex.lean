/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Real and complex inner product compatibility and real-span isotropy

Let `E` be a seminormed group carrying both a complex inner product and a real inner product for the
same norm. Because both inner products satisfy the norm-square identity on `(E, +, ‖·‖)`,
polarization forces `⟪x, y⟫_ℝ = Re ⟪x, y⟫_ℂ` (`TauCeti.real_inner_eq_re_inner_complex`) without any
separate compatibility hypothesis. This applies simultaneously to `InnerProductSpace.complexToReal`
and to spaces such as `EuclideanSpace ℂ ι` whose coordinatewise real inner product is only
propositionally equal to `Re ⟪·, ·⟫_ℂ`.

On any complex inner product space, Hermitian symmetry gives `Im ⟪x, x⟫_ℂ = 0`, so pairwise
vanishing of `Im ⟪·, ·⟫_ℂ` on a generating set `s` extends by `ℝ`-bilinearity to all pairs in
`Submodule.span ℝ s` (`Set.Pairwise.im_inner_eq_zero_of_mem_span`). Geometrically, this expresses
isotropy of the real span for the alternating form `Im ⟪·, ·⟫_ℂ` (the standard Kähler/symplectic
form when `E` is normed), which becomes the Lagrangian condition when the real span has half the
ambient real dimension.

## Main results

* `TauCeti.real_inner_eq_re_inner_complex`: `⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re` whenever both inner products
  share the same seminormed group structure.
* `Set.Pairwise.im_inner_eq_zero_of_mem_span`: if `Im ⟪x, y⟫_ℂ` vanishes for distinct elements of
  `s`, then `Im ⟪x, y⟫_ℂ = 0` for all `x, y ∈ Submodule.span ℝ s`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

/-- On any seminormed space carrying both a complex and a real inner product for the same norm, the
real inner product equals the real part of the complex inner product. -/
theorem real_inner_eq_re_inner_complex {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] [InnerProductSpace ℝ E] (x y : E) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  have h := norm_add_sq (𝕜 := ℂ) x y
  rw [RCLike.re_to_complex] at h
  linarith [norm_add_sq_real x y]

end TauCeti

namespace Set.Pairwise

/-- If `Im ⟪x, y⟫_ℂ = 0` for distinct elements of `s`, then `Im ⟪x, y⟫_ℂ = 0` for all
`x, y ∈ Submodule.span ℝ s`: the real span of `s` is isotropic for `Im ⟪·, ·⟫_ℂ`. -/
theorem im_inner_eq_zero_of_mem_span {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Set E} (hs : s.Pairwise fun x y ↦ (⟪x, y⟫_ℂ).im = 0)
    {x y : E} (hx : x ∈ Submodule.span ℝ s) (hy : y ∈ Submodule.span ℝ s) :
    (⟪x, y⟫_ℂ).im = 0 := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
    induction hy using Submodule.span_induction with
    | mem v hv =>
      rcases eq_or_ne u v with rfl | huv
      · exact inner_self_im (𝕜 := ℂ) u
      · exact hs hu hv huv
    | zero => simp
    | add y₁ y₂ _ _ hy₁ hy₂ => rw [inner_add_right, Complex.add_im, hy₁, hy₂, add_zero]
    | smul r y _ hy =>
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_right]
      simp [hy]
  | zero => simp
  | add x₁ x₂ _ _ hx₁ hx₂ => rw [inner_add_left, Complex.add_im, hx₁, hx₂, add_zero]
  | smul r x _ hx =>
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left]
    simp [hx]

end Set.Pairwise
