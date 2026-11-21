/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import TauCeti.LinearAlgebra.Complex.Orientation
import TauCeti.Analysis.InnerProductSpace.Complex

/-!
# Real and complex orthonormality on Hermitian inner product spaces

Let `E` be a seminormed group carrying both an `RCLike` inner product over `𝕜` (in particular `ℂ`)
and a real inner product for the same norm. Because `⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_𝕜`
(`TauCeti.inner_real_eq_re_inner`), unit length is the same over `ℝ` and over `𝕜`, while over `ℂ`
orthogonality `⟪x, y⟫_ℂ = 0` splits into `⟪x, y⟫_ℝ = 0` and `Im ⟪x, y⟫_ℂ = 0`.

Consequently, every `𝕜`-orthonormal family is `ℝ`-orthonormal (`Orthonormal.real`), and an
`ℝ`-orthonormal family `v` is `ℂ`-orthonormal (unitary) if and only if the imaginary parts of its
complex inner products vanish (`Orthonormal.complex_iff`). Since `Im ⟪x, x⟫_ℂ = 0` holds
unconditionally by Hermitian symmetry, the imaginary condition may be written either pairwise for
`i ≠ j` or for all `i, j` (`Orthonormal.complex_iff_forall_im_inner_eq_zero`). For any
complex-orthonormal family `u`, its underlying real family `(u₀, i • u₀, …)`
(`TauCeti.complexToRealFamily u`) is real-orthonormal (`TauCeti.orthonormal_complexToRealFamily`).

## Main results

* `Orthonormal.real`: every `𝕜`-orthonormal family (for `[RCLike 𝕜]`) is `ℝ`-orthonormal.
* `Orthonormal.complex_iff`, `Orthonormal.complex_iff_forall_im_inner_eq_zero`: an `ℝ`-orthonormal
  family is `ℂ`-orthonormal if and only if `Im ⟪v i, v j⟫_ℂ = 0` (pairwise for `i ≠ j`, or for all
  `i, j`).
* `TauCeti.orthonormal_complexToRealFamily`: the underlying real family `(u₀, i • u₀, …)` of a
  complex-orthonormal family is real-orthonormal for any compatible real inner product.
-/

public section

open scoped InnerProductSpace

namespace Orthonormal

/-- Every `𝕜`-orthonormal family (over an `RCLike` field `𝕜`, in particular `ℂ`) is
`ℝ`-orthonormal for any real inner product sharing the same norm. -/
theorem real {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [InnerProductSpace ℝ E] {v : ι → E} (hv : Orthonormal 𝕜 v) : Orthonormal ℝ v :=
  ⟨hv.1, fun {_ _} hij ↦ by
    dsimp only
    rw [TauCeti.inner_real_eq_re_inner 𝕜, hv.2 hij, map_zero]⟩

section Complex

variable {E ι : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]

/-- An `ℝ`-orthonormal family is `ℂ`-orthonormal if and only if the off-diagonal imaginary parts
`Im ⟪v i, v j⟫_ℂ` vanish. -/
theorem complex_iff {v : ι → E} (hv : Orthonormal ℝ v) :
    Orthonormal ℂ v ↔ Pairwise fun i j ↦ (⟪v i, v j⟫_ℂ).im = 0 := by
  refine ⟨fun hc _ _ hij ↦ by dsimp only; rw [hc.2 hij, Complex.zero_im],
    fun him ↦ ⟨hv.1, fun {_ _} hij ↦ ?_⟩⟩
  dsimp only
  apply Complex.ext
  · rw [← RCLike.re_to_complex, ← TauCeti.inner_real_eq_re_inner ℂ, hv.2 hij, Complex.zero_re]
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

end Complex

end Orthonormal

namespace TauCeti

open scoped RealInnerProductSpace

/-- The underlying real family `(u₀, i • u₀, …)` of a complex-orthonormal family is
real-orthonormal for any compatible real inner product. -/
theorem orthonormal_complexToRealFamily {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] [InnerProductSpace ℂ E] {r : ℕ} {u : Fin r → E}
    (hu : Orthonormal ℂ u) : Orthonormal ℝ (complexToRealFamily u) := by
  rw [orthonormal_iff_ite]
  intro i j
  obtain ⟨⟨a, p⟩, rfl⟩ := (complexRealIndexEquiv r).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (complexRealIndexEquiv r).surjective j
  simp only [complexToRealFamily_complexRealIndexEquiv, TauCeti.inner_real_eq_re_inner ℂ,
    inner_smul_left, inner_smul_right, (complexRealIndexEquiv r).injective.eq_iff, Prod.mk.injEq]
  rcases eq_or_ne a b with rfl | hab
  · fin_cases p <;> fin_cases q <;> simp [hu.1 a]
  · simp [hab, hu.2 hab]

end TauCeti
