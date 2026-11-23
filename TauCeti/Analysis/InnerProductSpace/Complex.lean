/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Real and complex inner product compatibility and real-span isotropy

Let `E` be a seminormed group carrying both an `RCLike` inner product over `𝕜` (in particular `ℂ`)
and a real inner product for the same norm. Because both inner products satisfy the norm-square
identity on `(E, +, ‖·‖)`, polarization forces `⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_𝕜`
(`TauCeti.inner_real_eq_re_inner`) without any separate compatibility hypothesis. This applies
simultaneously to `InnerProductSpace.rclikeToReal` (and `InnerProductSpace.complexToReal`) and to
spaces such as `EuclideanSpace ℂ ι` whose coordinatewise real inner product is only propositionally
equal to `Re ⟪·, ·⟫_ℂ`. In particular, on any such space scalar multiplication by `ζ : 𝕜` scales
the real inner product by `‖ζ‖ ^ 2` (`TauCeti.real_inner_smul_smul`).

On any complex inner product space, Hermitian symmetry gives `Im ⟪x, x⟫_ℂ = 0`, so pairwise
vanishing of `Im ⟪·, ·⟫_ℂ` on a generating set `s` extends by `ℝ`-bilinearity to all pairs in
`Submodule.span ℝ s` (`Set.Pairwise.im_inner_eq_zero_of_mem_span`). Geometrically, this expresses
isotropy of the real span for the alternating form `Im ⟪·, ·⟫_ℂ` (the standard Kähler/symplectic
form when `E` is normed), which becomes the Lagrangian condition when the real span has half the
ambient real dimension.

## Main results

* `TauCeti.inner_real_eq_re_inner`: `⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_𝕜` whenever a `𝕜`-inner product
  (for `[RCLike 𝕜]`) and a real inner product share the same seminormed group structure.
* `TauCeti.real_inner_smul_smul`: `⟪ζ • x, ζ • y⟫_ℝ = ‖ζ‖ ^ 2 * ⟪x, y⟫_ℝ` for `ζ : 𝕜` on such a
  space.
* `Set.Pairwise.im_inner_eq_zero_of_mem_span`: if `Im ⟪x, y⟫_ℂ` vanishes for distinct elements of
  `s`, then `Im ⟪x, y⟫_ℂ = 0` for all `x, y ∈ Submodule.span ℝ s`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

/-- On any seminormed space carrying both a `𝕜`-inner product (for an `RCLike` field `𝕜`) and a
real inner product for the same norm, the real inner product equals the real part of the
`𝕜`-inner product. -/
theorem inner_real_eq_re_inner (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ E] (x y : E) :
    ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_𝕜 := by
  linarith [norm_add_sq (𝕜 := 𝕜) x y, norm_add_sq_real x y]

/-- On any seminormed space carrying both a `𝕜`-inner product (for an `RCLike` field `𝕜`) and a
real inner product for the same norm, scalar multiplication by `ζ : 𝕜` scales the real inner
product by `‖ζ‖ ^ 2`. -/
theorem real_inner_smul_smul {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ E] (ζ : 𝕜) (x y : E) :
    ⟪ζ • x, ζ • y⟫_ℝ = ‖ζ‖ ^ 2 * ⟪x, y⟫_ℝ := by
  rw [inner_real_eq_re_inner 𝕜, inner_real_eq_re_inner 𝕜, inner_smul_left, inner_smul_right,
    ← mul_assoc, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]

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
