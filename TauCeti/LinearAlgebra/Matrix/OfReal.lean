/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.DetDescent

/-!
# Real matrices as complex matrices

A real matrix `N` is viewed as a complex matrix through the entrywise coercion
`N.map ((↑) : ℝ → ℂ)`. This file records that a real orthogonal matrix is unitary and a real
symmetric matrix Hermitian as a complex matrix, and how the real Gram matrix `Re (Mᴴ M)` of the
columns of a complex matrix `M` behaves: it transforms by congruence under a real change of basis,
and it is positive definite when `Mᴴ M` is, in particular when `M` has independent columns.

## Main results

* `Matrix.map_ofReal_mem_unitaryGroup`: an orthogonal real matrix is unitary.
* `Matrix.IsHermitian.map_ofReal`: a real symmetric matrix is Hermitian.
* `Matrix.IsHermitian.eq_map_ofReal_map_re_of_transpose_eq`: a Hermitian complex matrix equal to
  its transpose is real.
* `Matrix.map_re_conjTranspose_mul_self_mul_map_ofReal`: the real Gram matrix of `M N` for a real
  matrix `N` is `Nᵀ Re (Mᴴ M) N`.
* `Matrix.conjTranspose_mul_self_map_ofReal_add_I_smul`: the Gram matrix of `P + i Q` for real
  matrices `P` and `Q` has real part `Pᵀ P + Qᵀ Q` and imaginary part `Pᵀ Q - Qᵀ P`.
* `Matrix.PosDef.map_re`: the real part of a positive definite complex matrix is positive
  definite.
* `Matrix.PosDef.map_re_conjTranspose_mul_self`: the real Gram matrix of a complex matrix with
  independent columns is positive definite.
-/

public section

open scoped ComplexOrder

namespace Matrix

variable {l m n : Type*}

/-- An orthogonal real matrix is unitary as a complex matrix. -/
theorem map_ofReal_mem_unitaryGroup [Fintype n] [DecidableEq n] {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) : O.map ((↑) : ℝ → ℂ) ∈ unitaryGroup n ℂ := by
  rw [mem_orthogonalGroup_iff'] at hO
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose,
    ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial]
  exact (map_mul Complex.ofRealHom.mapMatrix _ _).symm.trans ((congrArg _ hO).trans (map_one _))

/-- A real symmetric matrix is Hermitian as a complex matrix. -/
theorem IsHermitian.map_ofReal {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (A.map ((↑) : ℝ → ℂ)).IsHermitian :=
  hA.map _ fun _ ↦ by simp

/-- A Hermitian complex matrix that is equal to its transpose is real. -/
theorem IsHermitian.eq_map_ofReal_map_re_of_transpose_eq {q : Matrix n n ℂ} (hq : q.IsHermitian)
    (hT : qᵀ = q) : q = (q.map Complex.re).map ((↑) : ℝ → ℂ) := by
  ext i j
  have h : star (q i j) = q i j := by
    rw [← conjTranspose_apply, hq.eq, ← transpose_apply q i j, hT]
  simp only [map_apply]
  exact (Complex.conj_eq_iff_re.1 h).symm

/-- The real Gram matrix `Re ((M N)ᴴ (M N))` of the columns of `M N`, for a real matrix `N`, is
`Nᵀ Re (Mᴴ M) N`. -/
theorem map_re_conjTranspose_mul_self_mul_map_ofReal [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (N : Matrix n l ℝ) :
    ((M * N.map ((↑) : ℝ → ℂ))ᴴ * (M * N.map ((↑) : ℝ → ℂ))).map Complex.re =
      Nᵀ * (Mᴴ * M).map Complex.re * N := by
  rw [conjTranspose_mul, ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ]
  exact ((map_algebraMap_mul Complex.reLm Nᵀ _).trans
    (congrArg (Nᵀ * ·) (map_mul_algebraMap Complex.reLm N (Mᴴ * M)))).trans
      (Matrix.mul_assoc _ _ _).symm

/-- The Gram matrix of the complex matrix `P + i Q`, for real matrices `P` and `Q`, has real part
`Pᵀ P + Qᵀ Q` and imaginary part `Pᵀ Q - Qᵀ P`. -/
theorem conjTranspose_mul_self_map_ofReal_add_I_smul [Fintype m] (P Q : Matrix m n ℝ) :
    (P.map ((↑) : ℝ → ℂ) + Complex.I • Q.map ((↑) : ℝ → ℂ))ᴴ *
        (P.map ((↑) : ℝ → ℂ) + Complex.I • Q.map ((↑) : ℝ → ℂ)) =
      (Pᵀ * P + Qᵀ * Q).map ((↑) : ℝ → ℂ) +
        Complex.I • (Pᵀ * Q - Qᵀ * P).map ((↑) : ℝ → ℂ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.conjTranspose_apply, Matrix.sub_apply, smul_eq_mul, Matrix.transpose_apply]
  apply Complex.ext
  · simp [Complex.mul_re, Finset.sum_add_distrib, Complex.re_sum]
  · simp [Complex.mul_im, Finset.sum_add_distrib, Complex.im_sum]
    ring_nf

/-- The real part of a positive definite complex matrix is positive definite. -/
theorem PosDef.map_re [Finite n] {K : Matrix n n ℂ} (hK : K.PosDef) :
    (K.map Complex.re).PosDef := by
  have := Fintype.ofFinite n
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · ext i j
    have := congrFun (congrFun hK.1 i) j
    simp only [conjTranspose_apply, RCLike.star_def] at this
    simp only [conjTranspose_apply, map_apply, star_trivial, ← this, Complex.conj_re]
  · set xc : n → ℂ := fun i ↦ (x i : ℂ)
    have hxc : xc ≠ 0 := fun h ↦ hx (funext fun i ↦ by simpa [xc] using congrFun h i)
    have hre : (star xc ⬝ᵥ (K *ᵥ xc)).re = star x ⬝ᵥ (K.map Complex.re *ᵥ x) := by
      simp [xc, dotProduct, mulVec, Complex.re_sum, Finset.mul_sum]
    rw [← hre]
    exact (Complex.pos_iff.1 (hK.dotProduct_mulVec_pos hxc)).1

/-- The real Gram matrix `Re (Mᴴ M)` of a complex matrix `M` with linearly independent columns is
positive definite. -/
theorem PosDef.map_re_conjTranspose_mul_self [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (hM : Function.Injective M.mulVec) : ((Mᴴ * M).map Complex.re).PosDef :=
  (PosDef.conjTranspose_mul_self M hM).map_re

end Matrix
