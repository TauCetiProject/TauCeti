/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
import TauCeti.Analysis.InnerProductSpace.Complex

/-!
# Real and complex orthonormality on Hermitian inner product spaces

Let `E` be a seminormed group carrying both a complex inner product and a real inner product for the
same norm. Because `⟪x, y⟫_ℝ = Re ⟪x, y⟫_ℂ` (`TauCeti.real_inner_eq_re_inner_complex`), unit length
is the same over `ℝ` and over `ℂ`, while `⟪x, y⟫_ℂ = 0` splits into `⟪x, y⟫_ℝ = 0` and
`Im ⟪x, y⟫_ℂ = 0`.

Consequently, every `ℂ`-orthonormal family is `ℝ`-orthonormal (`Orthonormal.real`), and an
`ℝ`-orthonormal family `v` is `ℂ`-orthonormal (unitary) if and only if the imaginary parts of its
complex inner products vanish (`Orthonormal.complex_iff`). Since `Im ⟪x, x⟫_ℂ = 0` holds
unconditionally by Hermitian symmetry, the imaginary condition may be written either pairwise for
`i ≠ j` or for all `i, j` (`Orthonormal.complex_iff_forall_im_inner_eq_zero`).

## Main results

* `Orthonormal.real`: every `ℂ`-orthonormal family is `ℝ`-orthonormal.
* `Orthonormal.complex_iff`, `Orthonormal.complex_iff_forall_im_inner_eq_zero`: an `ℝ`-orthonormal
  family is `ℂ`-orthonormal if and only if `Im ⟪v i, v j⟫_ℂ = 0` (pairwise for `i ≠ j`, or for all
  `i, j`).
-/

public section

open scoped InnerProductSpace

namespace Orthonormal

variable {E ι : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]

/-- Every `ℂ`-orthonormal family is `ℝ`-orthonormal. -/
theorem real {v : ι → E} (hv : Orthonormal ℂ v) : Orthonormal ℝ v :=
  ⟨hv.1, fun {_ _} hij ↦ by
    dsimp only
    rw [TauCeti.real_inner_eq_re_inner_complex, hv.2 hij, Complex.zero_re]⟩

/-- An `ℝ`-orthonormal family is `ℂ`-orthonormal if and only if the off-diagonal imaginary parts
`Im ⟪v i, v j⟫_ℂ` vanish. -/
theorem complex_iff {v : ι → E} (hv : Orthonormal ℝ v) :
    Orthonormal ℂ v ↔ Pairwise fun i j ↦ (⟪v i, v j⟫_ℂ).im = 0 := by
  refine ⟨fun hc _ _ hij ↦ by dsimp only; rw [hc.2 hij, Complex.zero_im],
    fun him ↦ ⟨hv.1, fun {_ _} hij ↦ ?_⟩⟩
  dsimp only
  apply Complex.ext
  · rw [← TauCeti.real_inner_eq_re_inner_complex, hv.2 hij, Complex.zero_re]
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
