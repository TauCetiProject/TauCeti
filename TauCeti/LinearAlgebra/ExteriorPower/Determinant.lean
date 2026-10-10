/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Determinants of exterior-square actions in rank four

An endomorphism of a free module of rank four acts on its exterior square with determinant
the cube of its original determinant. This holds over every commutative ring: the wedge
pairing gives the squared identity over the universal polynomial ring, evaluation at the
identity fixes the sign, and specialization gives the result over arbitrary rings.
-/

public section

open Module

namespace Module.Basis

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [LinearOrder I] [Fintype I]

/-- The matrix of an exterior-power map consists of the corresponding minors. -/
theorem toMatrix_exteriorPower_map (b : Basis I R M) (n : ℕ) (f : M →ₗ[R] M)
    (s t : Set.powersetCard I n) :
    LinearMap.toMatrix (b.exteriorPower n) (b.exteriorPower n) (exteriorPower.map n f) s t =
      (Matrix.of fun i j : Fin n ↦
        LinearMap.toMatrix b b f (Set.powersetCard.ofFinEmbEquiv.symm s j)
          (Set.powersetCard.ofFinEmbEquiv.symm t i)).det := by
  simp [LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti,
    Basis.coord_apply]

end Module.Basis

namespace RingHom

variable {R S I : Type*} [CommRing R] [CommRing S] [LinearOrder I] [Fintype I]

/-- Exterior-power matrices commute with a change of coefficient ring. -/
theorem map_toMatrix_exteriorPower (φ : R →+* S) (n : ℕ) (A : Matrix I I R) :
    φ.mapMatrix (LinearMap.toMatrix ((Pi.basisFun R I).exteriorPower n)
      ((Pi.basisFun R I).exteriorPower n) (exteriorPower.map n A.toLin')) =
    LinearMap.toMatrix ((Pi.basisFun S I).exteriorPower n)
      ((Pi.basisFun S I).exteriorPower n) (exteriorPower.map n (φ.mapMatrix A).toLin') := by
  classical
  ext s t
  rw [RingHom.mapMatrix_apply, Matrix.map_apply,
    Module.Basis.toMatrix_exteriorPower_map, Module.Basis.toMatrix_exteriorPower_map]
  simp only [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rw [RingHom.map_det]
  rfl

end RingHom

namespace Matrix

variable {R : Type*} [CommRing R]

private theorem det_exteriorPower_two_sq [IsDomain R] (A : Matrix (Fin 4) (Fin 4) R) :
    LinearMap.det (exteriorPower.map 2 A.toLin') ^ 2 = A.det ^ 6 := by
  classical
  -- The wedge pairing scales by `det A`; its Gram determinant gives the squared identity.
  let b := Pi.basisFun R (Fin 4)
  let vol := ((LinearEquiv.ofEq
    (⋀[R]^(Module.finrank R (Fin 4 → R)) (Fin 4 → R))
    (⋀[R]^4 (Fin 4 → R)) (by simp)).trans b.exteriorPowerTopEquiv)
  let B : LinearMap.BilinForm R (⋀[R]^2 (Fin 4 → R)) :=
    exteriorPower.wedgePairing vol (show 2 + 2 = Module.finrank R (Fin 4 → R) by simp)
  have hB : B.IsPerfPair := by dsimp [B]; infer_instance
  have hpair : B = (exteriorPower.wedge R (Fin 4 → R) 2 2).compr₂
      b.exteriorPowerTopEquiv := by
    -- Remove the degree transports in the perfect wedge pairing.
    have htransport (n : ℕ) (hn : Module.finrank R (Fin 4 → R) = n)
        (hd : 2 + 2 = n) (v : (⋀[R]^n (Fin 4 → R)) ≃ₗ[R] R) :
        exteriorPower.wedgePairing
          ((LinearEquiv.ofEq _ _ (congrArg (fun d ↦ ⋀[R]^d (Fin 4 → R)) hn)).trans v)
          (hd.trans hn.symm) = (exteriorPower.wedge R (Fin 4 → R) 2 2).compr₂ (hd ▸ v) := by
      subst n
      rfl
    exact htransport 4 (by simp) rfl b.exteriorPowerTopEquiv
  have hcomp : B.comp (exteriorPower.map 2 A.toLin') (exteriorPower.map 2 A.toLin') =
      A.det • B := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro u
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.BilinForm.comp_apply,
      exteriorPower.map_apply_ιMulti, hpair, LinearMap.smul_apply, LinearMap.compr₂_apply]
    have hw (u v : Fin 2 → (Fin 4 → R)) :
        exteriorPower.wedge R (Fin 4 → R) 2 2 (exteriorPower.ιMulti R 2 u)
          (exteriorPower.ιMulti R 2 v) = exteriorPower.ιMulti R 4 (Fin.append u v) := by
      apply Subtype.ext
      simp only [SetLike.coe_gMul, exteriorPower.wedge, DirectSum.gMulLHom_apply_apply,
        exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]
    rw [hw, hw]
    simp only [smul_eq_mul]
    have happ : Fin.append (A.toLin' ∘ u) (A.toLin' ∘ v) = A.toLin' ∘ Fin.append u v := by
      funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;>
        simp only [Fin.append_left, Fin.append_right, Function.comp_apply]
    -- Expose the linear equivalence behind the volume map's linear-map coercion.
    change b.exteriorPowerTopEquiv (exteriorPower.ιMulti R 4
      (Fin.append (A.toLin' ∘ u) (A.toLin' ∘ v))) =
        A.det * b.exteriorPowerTopEquiv (exteriorPower.ιMulti R 4 (Fin.append u v))
    rw [happ, Basis.exteriorPowerTopEquiv_apply_ιMulti,
      Basis.exteriorPowerTopEquiv_apply_ιMulti, Basis.det_comp, LinearMap.det_toLin']
  let e := b.exteriorPower 2
  have hG : (LinearMap.BilinForm.toMatrix e B).det ≠ 0 :=
    (LinearMap.separatingLeft_iff_det_ne_zero e).mp hB.separatingLeft
  have h := congrArg (fun C ↦ (LinearMap.BilinForm.toMatrix e C).det) hcomp
  rw [LinearMap.BilinForm.toMatrix_comp e e B, map_smul, Matrix.det_smul,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at h
  have hcard : Fintype.card (Set.powersetCard (Fin 4) 2) = 6 := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card]
    norm_num [Nat.card_eq_fintype_card]
    decide
  rw [hcard] at h
  apply mul_right_cancel₀ hG
  linear_combination h

end Matrix

namespace Module.Basis

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An endomorphism of a free module with a four-element basis acts on its exterior square
with determinant the cube of its original determinant, over any commutative ring. -/
theorem det_exteriorPower_two (b₀ : Basis (Fin 4) R M) (f : M →ₗ[R] M) :
    LinearMap.det (exteriorPower.map 2 f) = LinearMap.det f ^ 3 := by
  classical
  let A := LinearMap.toMatrix b₀ b₀ f
  let P := MvPolynomial (Fin 4 × Fin 4) ℤ
  let U : Matrix (Fin 4) (Fin 4) P := fun i j ↦ MvPolynomial.X (i, j)
  let b := (Pi.basisFun P (Fin 4)).exteriorPower 2
  let C := LinearMap.toMatrix b b (exteriorPower.map 2 U.toLin')
  have hs : C.det = U.det ^ 3 ∨ C.det = -(U.det ^ 3) := by
    apply eq_or_eq_neg_of_sq_eq_sq
    rw [LinearMap.det_toMatrix, ← pow_mul]
    exact Matrix.det_exteriorPower_two_sq U
  have hpos : C.det = U.det ^ 3 := by
    rcases hs with h | h
    · exact h
    · let ε : P →+* ℤ := MvPolynomial.eval₂Hom (RingHom.id ℤ)
        (fun ij ↦ (1 : Matrix (Fin 4) (Fin 4) ℤ) ij.1 ij.2)
      have hU : ε.mapMatrix U = 1 := by
        ext i j
        rw [RingHom.mapMatrix_apply, Matrix.map_apply]
        exact MvPolynomial.eval₂Hom_X' _ _ (i, j)
      have hC : ε.mapMatrix C = 1 := by
        rw [RingHom.map_toMatrix_exteriorPower, hU]
        simp only [Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]
      have he := congrArg ε h
      rw [map_neg, map_pow, RingHom.map_det, RingHom.map_det, hC, hU] at he
      norm_num at he
  let ε : P →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ij ↦ A ij.1 ij.2)
  have hU : ε.mapMatrix U = A := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact MvPolynomial.eval₂Hom_X' _ _ (i, j)
  have h := congrArg ε hpos
  rw [map_pow, RingHom.map_det, RingHom.map_det,
    RingHom.map_toMatrix_exteriorPower, hU] at h
  have hmatrix : LinearMap.toMatrix ((Pi.basisFun R (Fin 4)).exteriorPower 2)
      ((Pi.basisFun R (Fin 4)).exteriorPower 2) (exteriorPower.map 2 A.toLin') =
      LinearMap.toMatrix (b₀.exteriorPower 2) (b₀.exteriorPower 2) (exteriorPower.map 2 f) := by
    ext s t
    simp only [Basis.toMatrix_exteriorPower_map, LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    rfl
  rw [hmatrix] at h
  simpa only [A, LinearMap.det_toMatrix] using h

end Module.Basis
