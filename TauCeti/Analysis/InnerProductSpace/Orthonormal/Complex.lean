/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Real and complex orthonormality on Hermitian inner product spaces

Let `E` be a normed group carrying both a complex inner product and a compatible real inner product
satisfying `⟪x, y⟫_ℝ = Re ⟪x, y⟫_ℂ`. Both `InnerProductSpace.complexToReal` and the coordinatewise
real inner product on `EuclideanSpace ℂ ι` satisfy this compatibility
(`EuclideanSpace.real_inner_eq_re_inner`), though they are only propositionally equal on
`EuclideanSpace ℂ ι`. Stating the general lemmas under an explicit compatibility hypothesis avoids
typeclass diamonds while applying directly to both.

Because the norm comes from the underlying `NormedAddCommGroup`, unit length is the same over `ℝ`
and over `ℂ`, while `⟪x, y⟫_ℂ = 0` splits into `⟪x, y⟫_ℝ = 0` and `Im ⟪x, y⟫_ℂ = 0`. A family `v` is
therefore `ℂ`-orthonormal (unitary) if and only if it is `ℝ`-orthonormal and the imaginary parts of
its complex inner products vanish. Since `Im ⟪v i, v i⟫_ℂ = 0` holds unconditionally by Hermitian
symmetry, the imaginary condition may be written either pairwise for `i ≠ j` or for all `i, j`; the
second form is the Lagrangian condition for the symplectic form `-Im ⟪·, ·⟫_ℂ`.

## Main results

* `EuclideanSpace.real_inner_eq_re_inner`: on `EuclideanSpace ℂ ι`, `⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re`.
* `Orthonormal.real_of_real_inner_eq_re`, `Orthonormal.real`: every `ℂ`-orthonormal family is
  `ℝ`-orthonormal.
* `Orthonormal.complex_iff_of_real_inner_eq_re`,
  `Orthonormal.complex_iff_forall_im_eq_zero_of_real_inner_eq_re`,
  `Orthonormal.complex_iff`, `Orthonormal.complex_iff_forall_im_eq_zero`: an `ℝ`-orthonormal family
  is `ℂ`-orthonormal if and only if `Im ⟪v i, v j⟫_ℂ = 0` (for `i ≠ j`, or for all `i, j`).
* `TauCeti.orthonormal_complex_iff_of_real_inner_eq_re`,
  `TauCeti.orthonormal_complex_iff_forall_im_eq_zero_of_real_inner_eq_re`,
  `TauCeti.orthonormal_complex_euclideanSpace_iff`,
  `TauCeti.orthonormal_complex_euclideanSpace_iff_forall_im_eq_zero`: the combined equivalences
  `Orthonormal ℂ v ↔ Orthonormal ℝ v ∧ …`.
-/

public section

open scoped InnerProductSpace

namespace EuclideanSpace

/-- On `EuclideanSpace ℂ ι`, the coordinatewise real inner product equals the real part of the
complex inner product. -/
theorem real_inner_eq_re_inner {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp [PiLp.inner_apply, Complex.re_sum]

end EuclideanSpace

namespace Orthonormal

section General

variable {E n : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]

/-- Every `ℂ`-orthonormal family is `ℝ`-orthonormal whenever `⟪x, y⟫_ℝ = Re ⟪x, y⟫_ℂ`. -/
theorem real_of_real_inner_eq_re {v : n → E} (hv : Orthonormal ℂ v)
    (hre : ∀ x y : E, ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re) : Orthonormal ℝ v :=
  ⟨hv.1, fun {_ _} hij ↦ by dsimp only; rw [hre, hv.2 hij, Complex.zero_re]⟩

/-- An `ℝ`-orthonormal family is `ℂ`-orthonormal if and only if the off-diagonal imaginary parts
`Im ⟪v i, v j⟫_ℂ` vanish. -/
theorem complex_iff_of_real_inner_eq_re {v : n → E} (hv : Orthonormal ℝ v)
    (hre : ∀ x y : E, ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re) :
    Orthonormal ℂ v ↔ Pairwise fun i j ↦ (⟪v i, v j⟫_ℂ).im = 0 := by
  refine ⟨fun hc _ _ hij ↦ by dsimp only; rw [hc.2 hij, Complex.zero_im],
    fun him ↦ ⟨hv.1, fun {_ _} hij ↦ ?_⟩⟩
  dsimp only
  apply Complex.ext
  · rw [← hre, hv.2 hij, Complex.zero_re]
  · rw [him hij, Complex.zero_im]

/-- An `ℝ`-orthonormal family is `ℂ`-orthonormal if and only if `Im ⟪v i, v j⟫_ℂ = 0` for all
`i, j`, including `i = j`. -/
theorem complex_iff_forall_im_eq_zero_of_real_inner_eq_re {v : n → E} (hv : Orthonormal ℝ v)
    (hre : ∀ x y : E, ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re) :
    Orthonormal ℂ v ↔ ∀ i j, (⟪v i, v j⟫_ℂ).im = 0 := by
  rw [hv.complex_iff_of_real_inner_eq_re hre]
  refine ⟨fun hp i j ↦ ?_, fun hall _ _ _ ↦ hall _ _⟩
  by_cases hij : i = j
  · subst hij; exact inner_self_im (𝕜 := ℂ) (v i)
  · exact hp hij

end General

section EuclideanSpace

variable {ι n : Type*} [Fintype ι]

/-- Every `ℂ`-orthonormal family in `EuclideanSpace ℂ ι` is `ℝ`-orthonormal. -/
theorem real {v : n → EuclideanSpace ℂ ι} (hv : Orthonormal ℂ v) : Orthonormal ℝ v :=
  hv.real_of_real_inner_eq_re EuclideanSpace.real_inner_eq_re_inner

/-- An `ℝ`-orthonormal family in `EuclideanSpace ℂ ι` is `ℂ`-orthonormal if and only if the
off-diagonal imaginary parts `Im ⟪v i, v j⟫_ℂ` vanish. -/
theorem complex_iff {v : n → EuclideanSpace ℂ ι} (hv : Orthonormal ℝ v) :
    Orthonormal ℂ v ↔ Pairwise fun i j ↦ (⟪v i, v j⟫_ℂ).im = 0 :=
  hv.complex_iff_of_real_inner_eq_re EuclideanSpace.real_inner_eq_re_inner

/-- An `ℝ`-orthonormal family in `EuclideanSpace ℂ ι` is `ℂ`-orthonormal if and only if
`Im ⟪v i, v j⟫_ℂ = 0` for all `i, j`. -/
theorem complex_iff_forall_im_eq_zero {v : n → EuclideanSpace ℂ ι} (hv : Orthonormal ℝ v) :
    Orthonormal ℂ v ↔ ∀ i j, (⟪v i, v j⟫_ℂ).im = 0 :=
  hv.complex_iff_forall_im_eq_zero_of_real_inner_eq_re EuclideanSpace.real_inner_eq_re_inner

end EuclideanSpace

end Orthonormal

namespace TauCeti

section General

variable {E n : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]

/-- A family is `ℂ`-orthonormal if and only if it is `ℝ`-orthonormal and has pairwise vanishing
imaginary inner products. -/
theorem orthonormal_complex_iff_of_real_inner_eq_re (hre : ∀ x y : E, ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re)
    (v : n → E) :
    Orthonormal ℂ v ↔ Orthonormal ℝ v ∧ Pairwise fun i j ↦ (⟪v i, v j⟫_ℂ).im = 0 :=
  ⟨fun hc ↦ ⟨hc.real_of_real_inner_eq_re hre,
    (hc.real_of_real_inner_eq_re hre |>.complex_iff_of_real_inner_eq_re hre).mp hc⟩,
    fun ⟨hr, him⟩ ↦ (hr.complex_iff_of_real_inner_eq_re hre).mpr him⟩

/-- A family is `ℂ`-orthonormal if and only if it is `ℝ`-orthonormal and `Im ⟪v i, v j⟫_ℂ = 0` for
all `i, j`. -/
theorem orthonormal_complex_iff_forall_im_eq_zero_of_real_inner_eq_re
    (hre : ∀ x y : E, ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re) (v : n → E) :
    Orthonormal ℂ v ↔ Orthonormal ℝ v ∧ ∀ i j, (⟪v i, v j⟫_ℂ).im = 0 :=
  ⟨fun hc ↦ ⟨hc.real_of_real_inner_eq_re hre,
    ((hc.real_of_real_inner_eq_re hre).complex_iff_forall_im_eq_zero_of_real_inner_eq_re hre).mp
      hc⟩,
    fun ⟨hr, him⟩ ↦ (hr.complex_iff_forall_im_eq_zero_of_real_inner_eq_re hre).mpr him⟩

end General

section EuclideanSpace

variable {ι n : Type*} [Fintype ι]

/-- A family in `EuclideanSpace ℂ ι` is `ℂ`-orthonormal if and only if it is `ℝ`-orthonormal and has
pairwise vanishing imaginary inner products. -/
theorem orthonormal_complex_euclideanSpace_iff (v : n → EuclideanSpace ℂ ι) :
    Orthonormal ℂ v ↔ Orthonormal ℝ v ∧ Pairwise fun i j ↦ (⟪v i, v j⟫_ℂ).im = 0 :=
  orthonormal_complex_iff_of_real_inner_eq_re EuclideanSpace.real_inner_eq_re_inner v

/-- A family in `EuclideanSpace ℂ ι` is `ℂ`-orthonormal if and only if it is `ℝ`-orthonormal and
`Im ⟪v i, v j⟫_ℂ = 0` for all `i, j`. -/
theorem orthonormal_complex_euclideanSpace_iff_forall_im_eq_zero (v : n → EuclideanSpace ℂ ι) :
    Orthonormal ℂ v ↔ Orthonormal ℝ v ∧ ∀ i j, (⟪v i, v j⟫_ℂ).im = 0 :=
  orthonormal_complex_iff_forall_im_eq_zero_of_real_inner_eq_re
    EuclideanSpace.real_inner_eq_re_inner v

end EuclideanSpace

end TauCeti
