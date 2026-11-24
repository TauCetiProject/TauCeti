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
# The real orthonormal basis underlying a complex orthonormal basis

Let `E` be a complex inner product space which also carries a real inner product for the same
norm, such as `Re ⟪·, ·⟫_ℂ` (`InnerProductSpace.complexToReal`). A complex orthonormal family `v`
gives the real orthonormal family `(v i, I • v i)` (`Orthonormal.complexToReal`), indexed by
`ι × Fin 2` as the real basis `Module.Basis.complexToReal` underlying a complex basis. For a complex
orthonormal basis `b` this is the real orthonormal basis `b.complexToReal`, whose underlying basis
is `b.toBasis.complexToReal` (`OrthonormalBasis.toBasis_complexToReal`).

## Main definitions

* `OrthonormalBasis.complexToReal`: the real orthonormal basis `(b i, I • b i)` underlying a complex
  orthonormal basis `b`.

## Main results

* `Orthonormal.complexToReal`: the family `(v i, I • v i)` of a complex orthonormal family `v` is
  real orthonormal.
* `OrthonormalBasis.complexToReal_apply`, `OrthonormalBasis.complexToReal_repr_apply`: the vectors
  and coordinates of `b.complexToReal`.
-/

public section

open Module
open scoped InnerProductSpace

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
