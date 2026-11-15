/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.Complex.Orientation

/-!
# Real Euclidean coordinates of complex Euclidean space

`TauCeti.complexEuclideanRealLinearIsometryEquiv` identifies complex Euclidean space, regarded
as a real inner product space, with real Euclidean space of twice the dimension. Each real part
is immediately followed by its imaginary part, including in dimension zero.

The construction uses Mathlib's `Pi.orthonormalBasis` and `Complex.orthonormalBasisOneI`
together with the norm-preserving reindexing `LinearIsometryEquiv.piLpCongrLeft`. Because this
basis ordering agrees with `Module.Basis.complexToReal` reindexed by
`TauCeti.complexRealIndexEquiv`, the coordinate equivalence carries the canonical real orientation
`TauCeti.complexOrientation` of `EuclideanSpace ℂ (Fin n)` to the standard orientation of
`EuclideanSpace ℝ (Fin (2 * n))`
(`TauCeti.map_complexEuclideanRealLinearIsometryEquiv_complexOrientation`). The resulting isometry
can transport real manifold models and orientations without changing their chart carriers.
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

/-- Under `complexEuclideanRealLinearIsometryEquiv n`, the real basis `(e₀, I • e₀, e₁, I • e₁, …)`
underlying the standard complex basis of `EuclideanSpace ℂ (Fin n)` maps to the standard real basis
of `EuclideanSpace ℝ (Fin (2 * n))`. -/
theorem basis_map_complexEuclideanRealLinearIsometryEquiv (n : ℕ) :
    (((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.complexToReal).reindex
      (complexRealIndexEquiv n)).map (complexEuclideanRealLinearIsometryEquiv n).toLinearEquiv =
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis := by
  refine Module.Basis.eq_of_apply_eq fun k ↦ ?_
  obtain ⟨⟨j, a⟩, rfl⟩ := (complexRealIndexEquiv n).surjective k
  ext m
  obtain ⟨⟨j', a'⟩, rfl⟩ := (complexRealIndexEquiv n).surjective m
  simp only [Module.Basis.map_apply, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, Module.Basis.complexToReal_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.single,
    PiLp.single_apply, (complexRealIndexEquiv n).injective.eq_iff, Prod.mk.injEq]
  -- `complexRealIndexEquiv` is abstract across module boundaries, whereas
  -- `complexEuclideanRealLinearIsometryEquiv_apply_finProdFinEquiv` uses the explicit
  -- `Fin.cast`/`finProdFinEquiv` index; compare underlying `ℕ` values to bridge the two.
  have hidx : complexRealIndexEquiv n (j', a') =
      Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (j', a')) :=
    Fin.ext (by simp [Nat.add_comm])
  rw [hidx, complexEuclideanRealLinearIsometryEquiv_apply_finProdFinEquiv]
  by_cases hj : j' = j
  · subst hj
    fin_cases a <;> fin_cases a' <;> simp
  · simp [hj]

/-- `complexEuclideanRealLinearIsometryEquiv n` carries the canonical real orientation of
`EuclideanSpace ℂ (Fin n)` to the standard orientation of `EuclideanSpace ℝ (Fin (2 * n))`, up to
the index cast from `finrank ℂ (EuclideanSpace ℂ (Fin n)) = n`. -/
@[simp]
theorem map_complexEuclideanRealLinearIsometryEquiv_complexOrientation (n : ℕ) :
    Orientation.map _ (complexEuclideanRealLinearIsometryEquiv n).toLinearEquiv
        (complexOrientation (EuclideanSpace ℂ (Fin n))) =
      Orientation.reindex ℝ _ (finCongr (by rw [finrank_euclideanSpace_fin]))
        (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.orientation := by
  set b : Module.Basis (Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin n)))) ℂ
      (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.reindex (finCongr finrank_euclideanSpace_fin.symm)
  rw [b.complexOrientation_eq, ← Module.Basis.orientation_reindex, ← Module.Basis.orientation_map,
    ← Module.Basis.orientation_reindex, ← basis_map_complexEuclideanRealLinearIsometryEquiv n]
  congr 1
  refine Module.Basis.eq_of_apply_eq fun k ↦ ?_
  obtain ⟨⟨j, a⟩, rfl⟩ :=
    ((complexRealIndexEquiv n).trans (finCongr (by rw [finrank_euclideanSpace_fin]))).surjective k
  simp [b]

/-- After reindexing the canonical real orientation of `EuclideanSpace ℂ (Fin n)` to `Fin (2 * n)`,
`complexEuclideanRealLinearIsometryEquiv n` maps it directly to the standard orientation of
`EuclideanSpace ℝ (Fin (2 * n))`. -/
theorem map_complexEuclideanRealLinearIsometryEquiv_reindex_complexOrientation (n : ℕ) :
    Orientation.map _ (complexEuclideanRealLinearIsometryEquiv n).toLinearEquiv
        (Orientation.reindex ℝ _ (finCongr (by rw [finrank_euclideanSpace_fin]))
          (complexOrientation (EuclideanSpace ℂ (Fin n)))) =
      (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis.orientation := by
  rw [Orientation.map_reindex, map_complexEuclideanRealLinearIsometryEquiv_complexOrientation]
  exact (Orientation.reindex ℝ _
    (finCongr (by rw [finrank_euclideanSpace_fin]))).symm_apply_apply _

end TauCeti
