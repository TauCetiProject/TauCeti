/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Real Euclidean coordinates of complex Euclidean space

`TauCeti.complexEuclideanRealLinearIsometryEquiv` identifies complex Euclidean space, regarded
as a real inner product space, with real Euclidean space of twice the dimension. Each real part
is immediately followed by its imaginary part, including in dimension zero.

The construction uses Mathlib's `Pi.orthonormalBasis` and `Complex.orthonormalBasisOneI`
together with the norm-preserving reindexing `LinearIsometryEquiv.piLpCongrLeft`. The resulting
isometry can transport real manifold models without changing their chart carriers.
-/

public section

namespace TauCeti

/-- The standard real coordinates of complex Euclidean space, preserving the Euclidean norm.
Each real part is immediately followed by the corresponding imaginary part. -/
noncomputable def complexEuclideanRealLinearIsometryEquiv (n : ℕ) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  (Pi.orthonormalBasis (fun _ : Fin n ↦ Complex.orthonormalBasisOneI)).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      ((Equiv.sigmaEquivProd (Fin n) (Fin 2)).trans
        (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))))

/-- The coordinate at index `k` is the real or imaginary part selected by its remainder modulo
`2`, of the complex coordinate selected by its quotient by `2`. -/
@[simp↓]
theorem complexEuclideanRealLinearIsometryEquiv_apply {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (k : Fin (2 * n)) :
    complexEuclideanRealLinearIsometryEquiv n v k =
      ![(v (Fin.cast (Nat.mul_comm 2 n) k).divNat).re,
        (v (Fin.cast (Nat.mul_comm 2 n) k).divNat).im]
        (Fin.cast (Nat.mul_comm 2 n) k).modNat := by
  simp only [complexEuclideanRealLinearIsometryEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    Equiv.symm_trans_apply, finCongr_symm_apply, finProdFinEquiv_symm_apply,
    Equiv.sigmaEquivProd_symm_apply]
  simpa only [WithLp.toLp_ofLp, Complex.orthonormalBasisOneI_repr_apply] using
    (Pi.orthonormalBasis_repr (fun _ : Fin n ↦ Complex.orthonormalBasisOneI) v.ofLp
      ⟨(Fin.cast (Nat.mul_comm 2 n) k).divNat, (Fin.cast (Nat.mul_comm 2 n) k).modNat⟩)

/-- The coordinates are read through the real basis `(1, I)` of `ℂ`. -/
theorem complexEuclideanRealLinearIsometryEquiv_apply_finProdFinEquiv {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (a : Fin 2) (j : Fin n) :
    complexEuclideanRealLinearIsometryEquiv n v
        (Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (j, a))) =
      Complex.basisOneI.repr (v j) a := by
  let e := (Equiv.sigmaEquivProd (Fin n) (Fin 2)).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2)))
  have h : e.symm (Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (j, a))) = ⟨j, a⟩ :=
    e.symm_apply_apply ⟨j, a⟩
  simp only [complexEuclideanRealLinearIsometryEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
  rw [h]
  simpa only [WithLp.toLp_ofLp, Complex.orthonormalBasisOneI_repr_apply,
    Complex.coe_basisOneI_repr] using
    (Pi.orthonormalBasis_repr (fun _ : Fin n ↦ Complex.orthonormalBasisOneI) v.ofLp ⟨j, a⟩)

/-- The even coordinates are the real parts. -/
theorem complexEuclideanRealLinearIsometryEquiv_apply_re {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    complexEuclideanRealLinearIsometryEquiv n v
        (Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (j, 0))) = (v j).re := by
  rw [complexEuclideanRealLinearIsometryEquiv_apply_finProdFinEquiv]
  simp

/-- The odd coordinates are the imaginary parts. -/
theorem complexEuclideanRealLinearIsometryEquiv_apply_im {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    complexEuclideanRealLinearIsometryEquiv n v
        (Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (j, 1))) = (v j).im := by
  rw [complexEuclideanRealLinearIsometryEquiv_apply_finProdFinEquiv]
  simp

/-- The inverse reconstructs each complex coordinate from its real and imaginary parts. -/
@[simp↓]
theorem complexEuclideanRealLinearIsometryEquiv_symm_apply {n : ℕ}
    (v : EuclideanSpace ℝ (Fin (2 * n))) (j : Fin n) :
    (complexEuclideanRealLinearIsometryEquiv n).symm v j =
      (v (Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (j, 0))) : ℂ) +
        v (Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (j, 1))) * Complex.I := by
  apply Complex.ext
  · have h := congrArg (fun w ↦ w (Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (j, 0))))
      ((complexEuclideanRealLinearIsometryEquiv n).apply_symm_apply v)
    rw [complexEuclideanRealLinearIsometryEquiv_apply_re] at h
    simpa using h
  · have h := congrArg (fun w ↦ w (Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (j, 1))))
      ((complexEuclideanRealLinearIsometryEquiv n).apply_symm_apply v)
    rw [complexEuclideanRealLinearIsometryEquiv_apply_im] at h
    simpa using h

end TauCeti
