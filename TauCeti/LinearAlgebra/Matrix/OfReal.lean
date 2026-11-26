/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.DetDescent
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse

/-!
# Real matrices as complex matrices

A real matrix `N` is viewed as a complex matrix through the entrywise coercion
`N.map ((↑) : ℝ → ℂ)`. This file records that a real orthogonal matrix is unitary, a real
symmetric matrix Hermitian and a real positive definite matrix positive definite as a complex
matrix, that the determinant does not change, how a real rotation pair `(e₁, e₂)` satisfies the
eigenspace identity `(A.map (↑)) *ᵥ (e₁ + I • e₂) = exp (α I) • (e₁ + I • e₂)` (giving an
`exp (α I)`-eigenvector whenever `(e₁, e₂) ≠ 0`), and how the real Gram matrix `Re (Mᴴ M)` of the
columns of a complex matrix `M` behaves: it transforms by congruence under a real change of basis,
and it is positive definite when `Mᴴ M` is, in particular when `M` has independent columns. The
imaginary part `Im (Mᴴ M)`, the matrix of the symplectic form `Im ⟪·, ·⟫` on the columns,
transforms by the same congruence. For a symmetric complex matrix `Ω`, the imaginary part is
`Im Ω = (Ω - Ωᴴ) / 2i`.

## Main results

* `Matrix.map_ofReal_mul_transpose_map_ofReal_eq_one`: an orthogonal real matrix `O` satisfies
  `O Oᵀ = 1` as a complex matrix.
* `Matrix.map_ofReal_mem_unitaryGroup`: an orthogonal real matrix is unitary.
* `Matrix.IsHermitian.map_ofReal`: a real symmetric matrix is Hermitian.
* `Matrix.map_ofReal_mulVec`: multiplying `A.map (↑)` by a coerced real vector gives the coerced
  product `(A *ᵥ u)`.
* `Matrix.map_intCast_complex_eq_map_ofReal` and `Matrix.map_intCast_mulVec_ofReal`: casting an
  integer matrix to `ℂ` factors through `ℝ`, and its action on a coerced real vector agrees with
  the real action.
* `Matrix.map_ofReal_mulVec_of_rotation`: for a real rotation pair `(e₁, e₂)`,
  `(A.map (↑)) *ᵥ (e₁ + I • e₂) = exp (α I) • (e₁ + I • e₂)` (an `exp (α I)`-eigenvector when
  `(e₁, e₂) ≠ 0`).
* `Matrix.map_im_map_ofReal_of_transpose_eq`: for a symmetric complex matrix `Ω`, the complex
  matrix of `Im Ω` is `(Ω - Ωᴴ) / 2i`.
* `Matrix.map_ofReal_mul`, `Matrix.map_ofReal_one`, `Matrix.trace_map_ofReal`: the entrywise
  coercion is multiplicative, preserves the identity and commutes with the trace.
* `Matrix.isUnit_map_ofReal_iff`: a real matrix is invertible exactly when it is invertible as a
  complex matrix.
* `Matrix.det_map_ofReal`: the determinant of a real matrix is unchanged as a complex matrix.
* `Matrix.map_re_conjTranspose_mul_self_mul_map_ofReal`: the real Gram matrix of `M N` for a real
  matrix `N` is `Nᵀ Re (Mᴴ M) N`.
* `Matrix.map_im_conjTranspose_mul_self_mul_map_ofReal`: likewise, the imaginary part of the Gram
  matrix of `M N` is `Nᵀ Im (Mᴴ M) N`.
* `Matrix.PosDef.map_re`: the real part of a positive definite complex matrix is positive
  definite.
* `Matrix.PosDef.map_ofReal`: a real positive definite matrix is positive definite as a complex
  matrix.
* `Matrix.PosDef.map_re_conjTranspose_mul_self`: the real Gram matrix of a complex matrix with
  independent columns is positive definite.
-/

public section

open scoped ComplexOrder

namespace Matrix

variable {l m n : Type*}

/-- The complex image `O` of an orthogonal real matrix `O` satisfies `O Oᵀ = 1`. -/
theorem map_ofReal_mul_transpose_map_ofReal_eq_one [Fintype n] [DecidableEq n] {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) : O.map ((↑) : ℝ → ℂ) * (O.map ((↑) : ℝ → ℂ))ᵀ = 1 := by
  rw [← transpose_map]
  -- `N.map (↑)` is `Complex.ofRealHom.mapMatrix N`, which is multiplicative.
  exact (map_mul Complex.ofRealHom.mapMatrix _ _).symm.trans
    ((congrArg _ ((mem_orthogonalGroup_iff _ _).1 hO)).trans (map_one _))

/-- An orthogonal real matrix is unitary as a complex matrix. -/
theorem map_ofReal_mem_unitaryGroup [Fintype n] [DecidableEq n] {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) : O.map ((↑) : ℝ → ℂ) ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose,
    ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial, transpose_map]
  exact map_ofReal_mul_transpose_map_ofReal_eq_one hO

/-- A real symmetric matrix is Hermitian as a complex matrix. -/
theorem IsHermitian.map_ofReal {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (A.map ((↑) : ℝ → ℂ)).IsHermitian :=
  hA.map _ fun _ ↦ by simp

/-- Multiplying the complex image `A.map (↑)` of a real matrix `A` by a real vector coerced
entrywise to `ℂ` yields the entrywise coercion of `A *ᵥ u`. -/
theorem map_ofReal_mulVec [Fintype n] (A : Matrix m n ℝ) (u : n → ℝ) :
    (A.map ((↑) : ℝ → ℂ)) *ᵥ (fun i ↦ (u i : ℂ)) = fun i ↦ ((A *ᵥ u) i : ℂ) := funext fun i ↦ by
  simpa [funext Complex.ofRealHom_eq_coe, Function.comp_def] using
    (Complex.ofRealHom.map_mulVec A u i).symm

/-- Casting an integer matrix to `ℂ` agrees with casting to `ℝ` and then coercing entrywise to
`ℂ`. -/
theorem map_intCast_complex_eq_map_ofReal (G : Matrix m n ℤ) :
    G.map (Int.castRingHom ℂ) = (G.map (Int.castRingHom ℝ)).map ((↑) : ℝ → ℂ) := by
  ext; simp

/-- Multiplying the complex image `G.map (Int.castRingHom ℂ)` of an integer matrix `G` by a real
vector coerced entrywise to `ℂ` yields the entrywise coercion of
`(G.map (Int.castRingHom ℝ)) *ᵥ u`. -/
theorem map_intCast_mulVec_ofReal [Fintype n] (G : Matrix m n ℤ) (u : n → ℝ) :
    (G.map (Int.castRingHom ℂ)) *ᵥ (fun i ↦ (u i : ℂ)) =
      fun i ↦ (((G.map (Int.castRingHom ℝ)) *ᵥ u) i : ℂ) := by
  rw [map_intCast_complex_eq_map_ofReal, Matrix.map_ofReal_mulVec]

/-- If a real matrix `A` rotates `(e₁, e₂)` by `-α` (`A *ᵥ e₁ = cos α • e₁ - sin α • e₂` and
`A *ᵥ e₂ = sin α • e₁ + cos α • e₂`), then `e₁ + I • e₂` satisfies the eigenspace identity
`(A.map (↑)) *ᵥ (e₁ + I • e₂) = exp (α I) • (e₁ + I • e₂)` (and is an `exp (α I)`-eigenvector
when `(e₁, e₂) ≠ 0`). -/
theorem map_ofReal_mulVec_of_rotation [Fintype n] {A : Matrix n n ℝ} {e₁ e₂ : n → ℝ} {α : ℝ}
    (he₁ : A *ᵥ e₁ = Real.cos α • e₁ - Real.sin α • e₂)
    (he₂ : A *ᵥ e₂ = Real.sin α • e₁ + Real.cos α • e₂) :
    (A.map ((↑) : ℝ → ℂ)) *ᵥ (fun i ↦ (e₁ i : ℂ) + Complex.I * (e₂ i : ℂ)) =
      Complex.exp ((α : ℂ) * Complex.I) • (fun i ↦ (e₁ i : ℂ) + Complex.I * (e₂ i : ℂ)) := by
  rw [show (fun i ↦ (e₁ i : ℂ) + Complex.I * (e₂ i : ℂ)) =
      (fun i ↦ (e₁ i : ℂ)) + Complex.I • (fun i ↦ (e₂ i : ℂ)) from
      funext fun _ ↦ by simp [smul_eq_mul],
    mulVec_add, mulVec_smul, map_ofReal_mulVec, map_ofReal_mulVec, he₁, he₂, Complex.exp_mul_I]
  ext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_mul, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  linear_combination -↑(Real.sin α) * (e₂ i : ℂ) * Complex.I_sq

/-- For a symmetric complex matrix `Ω`, the complex matrix of `Im Ω` is `(Ω - Ωᴴ) / 2i`. -/
theorem map_im_map_ofReal_of_transpose_eq {Ω : Matrix n n ℂ} (h : Ωᵀ = Ω) :
    (Ω.map Complex.im).map ((↑) : ℝ → ℂ) = (2 * Complex.I)⁻¹ • (Ω - Ωᴴ) := by
  ext i j
  have hij : Ω j i = Ω i j := by simpa using congrFun (congrFun h i) j
  simp [hij, Complex.ext_iff, Complex.sub_conj]

/-- The entrywise coercion of real matrices to complex matrices is multiplicative. -/
@[simp]
theorem map_ofReal_mul [Fintype m] (X : Matrix l m ℝ) (Y : Matrix m n ℝ) :
    (X * Y).map ((↑) : ℝ → ℂ) = X.map (↑) * Y.map (↑) :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- The entrywise coercion of the real identity matrix is the complex identity matrix. -/
theorem map_ofReal_one [DecidableEq n] : (1 : Matrix n n ℝ).map ((↑) : ℝ → ℂ) = 1 :=
  Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

/-- The trace of a real matrix, viewed as a complex matrix, is the coercion of its trace. -/
@[simp]
theorem trace_map_ofReal [Fintype n] (X : Matrix n n ℝ) :
    trace (X.map ((↑) : ℝ → ℂ)) = ((trace X : ℝ) : ℂ) :=
  (AddMonoidHom.map_trace Complex.ofRealHom X).symm

/-- A real square matrix is invertible exactly when it is invertible as a complex matrix: the
case `ℝ → ℂ` of `Matrix.isUnit_map_iff`. -/
@[simp]
theorem isUnit_map_ofReal_iff [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} :
    IsUnit (M.map ((↑) : ℝ → ℂ)) ↔ IsUnit M :=
  isUnit_map_iff Complex.ofRealHom M

/-- The determinant of the complex image of a real matrix is the image of its determinant. -/
@[simp]
theorem det_map_ofReal [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    (M.map ((↑) : ℝ → ℂ)).det = M.det :=
  (Complex.ofRealHom.map_det M).symm

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

/-- The imaginary part `Im ((M N)ᴴ (M N))` of the Gram matrix of the columns of `M N`, for a real
matrix `N`, is `Nᵀ Im (Mᴴ M) N`. -/
theorem map_im_conjTranspose_mul_self_mul_map_ofReal [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (N : Matrix n l ℝ) :
    ((M * N.map ((↑) : ℝ → ℂ))ᴴ * (M * N.map ((↑) : ℝ → ℂ))).map Complex.im =
      Nᵀ * (Mᴴ * M).map Complex.im * N := by
  rw [conjTranspose_mul, ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ]
  exact ((map_algebraMap_mul Complex.imLm Nᵀ _).trans
    (congrArg (Nᵀ * ·) (map_mul_algebraMap Complex.imLm N (Mᴴ * M)))).trans
      (Matrix.mul_assoc _ _ _).symm

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

/-- A real positive definite matrix is positive definite as a complex matrix: for `x = a + i b`,
`x* Y x = aᵀ Y a + bᵀ Y b`. -/
theorem PosDef.map_ofReal [Finite n] {Y : Matrix n n ℝ} (hY : Y.PosDef) :
    (Y.map ((↑) : ℝ → ℂ)).PosDef := by
  classical
  have := Fintype.ofFinite n
  refine PosDef.of_dotProduct_mulVec_pos hY.isHermitian.map_ofReal fun x hx ↦ ?_
  set a : n → ℝ := fun i ↦ (x i).re
  set b : n → ℝ := fun i ↦ (x i).im
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra! h
    exact hx (funext fun i ↦ Complex.ext (by simpa [a] using congrFun h.1 i)
      (by simpa [b] using congrFun h.2 i))
  have hsymm : ∀ i j, Y i j = Y j i := fun i j ↦ by
    simpa using congrFun (congrFun hY.isHermitian.eq j) i
  -- the cross terms cancel by symmetry of `Y`
  have hcross : ∑ i, ∑ j, (a i * Y i j * b j - b i * Y i j * a j) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [sub_eq_zero, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      rw [hsymm i j]; ring
  have key : star x ⬝ᵥ (Y.map ((↑) : ℝ → ℂ) *ᵥ x) =
      ((a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, map_apply, Complex.re_sum,
        Complex.ofReal_re, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      simp [a, b, Complex.mul_re, Complex.mul_im]
    · have : (star x ⬝ᵥ (Y.map ((↑) : ℝ → ℂ) *ᵥ x)).im =
          ∑ i, ∑ j, (a i * Y i j * b j - b i * Y i j * a j) := by
        simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, map_apply, Complex.im_sum]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [RCLike.star_def, Complex.mul_im, Complex.mul_re, Complex.conj_re,
          Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, a, b]
        ring
      rw [this, hcross, Complex.ofReal_im]
  rw [key, Complex.zero_lt_real]
  rcases hab with ha | hb
  · exact add_pos_of_pos_of_nonneg (by simpa using hY.dotProduct_mulVec_pos ha)
      (by simpa using hY.posSemidef.dotProduct_mulVec_nonneg b)
  · exact add_pos_of_nonneg_of_pos (by simpa using hY.posSemidef.dotProduct_mulVec_nonneg a)
      (by simpa using hY.dotProduct_mulVec_pos hb)

/-- The real Gram matrix `Re (Mᴴ M)` of a complex matrix `M` with linearly independent columns is
positive definite. -/
theorem PosDef.map_re_conjTranspose_mul_self [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (hM : Function.Injective M.mulVec) : ((Mᴴ * M).map Complex.re).PosDef :=
  (PosDef.conjTranspose_mul_self M hM).map_re

end Matrix
