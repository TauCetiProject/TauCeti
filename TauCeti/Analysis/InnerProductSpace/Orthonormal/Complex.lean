/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Real and complex orthonormality on Hermitian inner product spaces

Let `E` be a seminormed group carrying both a complex inner product and a real inner product for the
same norm. Because both inner products satisfy the norm-square identity on `(E, +, ‖·‖)`,
polarization forces `⟪x, y⟫_ℝ = Re ⟪x, y⟫_ℂ` (`TauCeti.real_inner_eq_re_inner`) without any
separate compatibility hypothesis. This applies simultaneously to `InnerProductSpace.complexToReal`
and to spaces such as `EuclideanSpace ℂ ι` whose coordinatewise real inner product is only
propositionally equal to `Re ⟪·, ·⟫_ℂ`.

Unit length is therefore the same over `ℝ` and over `ℂ`, while `⟪x, y⟫_ℂ = 0` splits into
`⟪x, y⟫_ℝ = 0` and `Im ⟪x, y⟫_ℂ = 0`. Every `ℂ`-orthonormal family is `ℝ`-orthonormal
(`Orthonormal.real`), and an `ℝ`-orthonormal family `v` is `ℂ`-orthonormal (unitary) if and only if
the imaginary parts of its complex inner products vanish (`Orthonormal.complex_iff`). Since
`Im ⟪x, x⟫_ℂ = 0` holds unconditionally by Hermitian symmetry, the imaginary condition may be
written either pairwise for `i ≠ j` or for all `i, j`
(`Orthonormal.complex_iff_forall_im_inner_eq_zero`), and pairwise vanishing on any generating set
`s` extends by `ℝ`-bilinearity to all pairs in `Submodule.span ℝ s`
(`Set.Pairwise.im_inner_eq_zero_of_mem_span`). Geometrically, this expresses isotropy of the real
span for the symplectic form `Im ⟪·, ·⟫_ℂ`, which becomes the Lagrangian condition when the real
span has half the ambient real dimension.

## Main results

* `TauCeti.real_inner_eq_re_inner`: `⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re` whenever both inner products share
  the same seminormed group structure.
* `Set.Pairwise.im_inner_eq_zero_of_mem_span`: if `Im ⟪x, y⟫_ℂ` vanishes for distinct elements of
  `s`, then `Im ⟪x, y⟫_ℂ = 0` for all `x, y ∈ Submodule.span ℝ s`.
* `Orthonormal.real`: every `ℂ`-orthonormal family is `ℝ`-orthonormal.
* `Orthonormal.complex_iff`, `Orthonormal.complex_iff_forall_im_inner_eq_zero`: an `ℝ`-orthonormal
  family is `ℂ`-orthonormal if and only if `Im ⟪v i, v j⟫_ℂ = 0` (pairwise for `i ≠ j`, or for all
  `i, j`).
-/

public section

open scoped InnerProductSpace

namespace TauCeti

/-- On any seminormed space carrying both a complex and a real inner product for the same norm, the
real inner product equals the real part of the complex inner product by polarization. -/
theorem real_inner_eq_re_inner {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] (x y : E) : ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  have h := norm_add_sq (𝕜 := ℂ) x y
  rw [RCLike.re_to_complex] at h
  linarith [norm_add_sq_real x y]

end TauCeti

namespace Set.Pairwise

/-- If the imaginary part of a complex inner product vanishes on distinct elements of `s`, then by
Hermitian symmetry (`Im ⟪u, u⟫_ℂ = 0`) and `ℝ`-bilinearity it vanishes on all pairs in the real
span of `s`: the real span of `s` is isotropic for `Im ⟪·, ·⟫_ℂ`. -/
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

namespace Orthonormal

variable {E ι : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]

/-- Every `ℂ`-orthonormal family is `ℝ`-orthonormal. -/
theorem real {v : ι → E} (hv : Orthonormal ℂ v) : Orthonormal ℝ v :=
  ⟨hv.1, fun {_ _} hij ↦ by
    dsimp only
    rw [TauCeti.real_inner_eq_re_inner, hv.2 hij, Complex.zero_re]⟩

/-- An `ℝ`-orthonormal family is `ℂ`-orthonormal if and only if the off-diagonal imaginary parts
`Im ⟪v i, v j⟫_ℂ` vanish. -/
theorem complex_iff {v : ι → E} (hv : Orthonormal ℝ v) :
    Orthonormal ℂ v ↔ Pairwise fun i j ↦ (⟪v i, v j⟫_ℂ).im = 0 := by
  refine ⟨fun hc _ _ hij ↦ by dsimp only; rw [hc.2 hij, Complex.zero_im],
    fun him ↦ ⟨hv.1, fun {_ _} hij ↦ ?_⟩⟩
  dsimp only
  apply Complex.ext
  · rw [← TauCeti.real_inner_eq_re_inner, hv.2 hij, Complex.zero_re]
  · rw [him hij, Complex.zero_im]

/-- An `ℝ`-orthonormal family is `ℂ`-orthonormal if and only if `Im ⟪v i, v j⟫_ℂ = 0` for all
`i, j`, including `i = j`. -/
theorem complex_iff_forall_im_inner_eq_zero {v : ι → E} (hv : Orthonormal ℝ v) :
    Orthonormal ℂ v ↔ ∀ i j, (⟪v i, v j⟫_ℂ).im = 0 := by
  rw [hv.complex_iff]
  refine ⟨fun hp i j ↦ ?_, fun hall _ _ _ ↦ hall _ _⟩
  by_cases hij : i = j
  · subst hij; exact inner_self_im (𝕜 := ℂ) (v i)
  · exact hp hij

end Orthonormal
