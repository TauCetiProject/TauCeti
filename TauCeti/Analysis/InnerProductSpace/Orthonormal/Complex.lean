/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
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
`i ≠ j` or for all `i, j` (`Orthonormal.complex_iff_forall_im_inner_eq_zero`).

Over `ℂ`, a complex orthonormal family `v` moreover gives the real orthonormal family
`(v i, I • v i)` (`Orthonormal.complexToReal`), indexed by `ι × Fin 2` as the real basis
`Module.Basis.complexToReal` underlying a complex basis. For a complex orthonormal basis `b` this is
the real orthonormal basis `b.complexToReal`, whose underlying basis is `b.toBasis.complexToReal`
(`OrthonormalBasis.toBasis_complexToReal`).

## Main definitions

* `OrthonormalBasis.complexToReal`: the real orthonormal basis `(b i, I • b i)` underlying a complex
  orthonormal basis `b`.

## Main results

* `Orthonormal.real`: every `𝕜`-orthonormal family (for `[RCLike 𝕜]`) is `ℝ`-orthonormal.
* `Orthonormal.complex_iff`, `Orthonormal.complex_iff_forall_im_inner_eq_zero`: an `ℝ`-orthonormal
  family is `ℂ`-orthonormal if and only if `Im ⟪v i, v j⟫_ℂ = 0` (pairwise for `i ≠ j`, or for all
  `i, j`).
* `Orthonormal.complexToReal`: the family `(v i, I • v i)` of a complex orthonormal family `v` is
  real orthonormal.
* `OrthonormalBasis.complexToReal_apply`, `OrthonormalBasis.complexToReal_repr_apply`: the vectors
  and coordinates of `b.complexToReal`.
-/

public section

open Module
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

section ComplexToReal

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]

/-- The family `(v i, I • v i)`, indexed by `ι × Fin 2` as in `Module.Basis.complexToReal`, of a
complex orthonormal family `v` is orthonormal for any real inner product with the same norm. -/
theorem Orthonormal.complexToReal {v : ι → E} (hv : Orthonormal ℂ v) :
    Orthonormal ℝ fun p : ι × Fin 2 ↦ Complex.basisOneI p.2 • v p.1 := by
  classical
  rw [orthonormal_iff_ite] at hv ⊢
  rintro ⟨i, k⟩ ⟨j, l⟩
  rw [TauCeti.inner_real_eq_re_inner ℂ]
  fin_cases k <;> fin_cases l <;>
    simp [inner_smul_left, inner_smul_right, hv, apply_ite]

namespace OrthonormalBasis

variable [Fintype ι] [IsScalarTower ℝ ℂ E]

/-- The real orthonormal basis underlying a complex orthonormal basis `b`: its vectors are `b i` at
index `(i, 0)` and `I • b i` at index `(i, 1)`. -/
noncomputable def complexToReal (b : OrthonormalBasis ι ℂ E) : OrthonormalBasis (ι × Fin 2) ℝ E :=
  b.toBasis.complexToReal.toOrthonormalBasis <| by
    convert b.orthonormal.complexToReal using 1
    funext ⟨i, k⟩
    simp

/-- The basis underlying `b.complexToReal` is the real basis `b.toBasis.complexToReal`. -/
@[simp]
theorem toBasis_complexToReal (b : OrthonormalBasis ι ℂ E) :
    b.complexToReal.toBasis = b.toBasis.complexToReal :=
  Basis.toBasis_toOrthonormalBasis _ _

/-- The vectors of `b.complexToReal` are `Complex.basisOneI k • b i`, that is, `b i` and
`I • b i`. -/
@[simp]
theorem complexToReal_apply (b : OrthonormalBasis ι ℂ E) (i : ι) (k : Fin 2) :
    b.complexToReal (i, k) = Complex.basisOneI k • b i := by
  rw [← OrthonormalBasis.coe_toBasis, toBasis_complexToReal, Basis.complexToReal_apply,
    OrthonormalBasis.coe_toBasis]

/-- The real coordinates of a vector in `b.complexToReal` are the real and imaginary parts of its
complex coordinates in `b`. -/
@[simp]
theorem complexToReal_repr_apply (b : OrthonormalBasis ι ℂ E) (x : E) (i : ι) (k : Fin 2) :
    b.complexToReal.repr x (i, k) = Complex.basisOneI.repr (b.repr x i) k := by
  rw [← OrthonormalBasis.coe_toBasis_repr_apply, toBasis_complexToReal,
    Basis.complexToReal_repr_apply, OrthonormalBasis.coe_toBasis_repr_apply]

end OrthonormalBasis

end ComplexToReal
