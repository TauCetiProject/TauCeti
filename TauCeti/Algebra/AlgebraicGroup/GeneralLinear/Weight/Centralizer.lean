/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic
import TauCeti.LinearAlgebra.Matrix.MonoidAlgebra

/-!
# Schematic centralizers of weight tori

The schematic centralizer of a diagonal torus representation consists exactly of matrices
whose entries between distinct weights vanish. Repeated weights give full matrix blocks;
when the weights are distinct, the centralizer consists of diagonal matrices. These results
hold over every commutative base ring and every value algebra: comparison with the universal
torus point, not merely rational points, separates weights even over finite fields.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* The universal-point coefficient argument is adapted from
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Centralizer`.
-/

public section

open TensorProduct WithConv

namespace TauCeti.GeneralLinear

universe u v w

variable {R : Type u} [CommRing R] {X : Type v} [CommGroup X] {n : ℕ}

/-- The schematic centralizer of a diagonal representation preserves its character blocks over
every value algebra. The character group need not be free, and characters may repeat. -/
theorem _root_.BialgHom.centralizerHopfIdeal_le_ker_iff_apply_eq_zero_of_coordinates
    (π : coordinateHopfAlgebra R n →ₐc[R] MonoidAlgebra R X)
    (e : Fin n → X)
    (hπ : ∀ i j, π (coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      if i = j then MonoidAlgebra.single (e i) 1 else 0)
    {A : Type w} [CommRing A] [Algebra R A]
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (BialgHom.centralizerHopfIdeal π).toIdeal ≤
        RingHom.ker g.ofConv ↔
      ∀ i j, e i ≠ e j → (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) i j = 0 := by
  classical
  let B := A ⊗[R] MonoidAlgebra R X
  let u : WithConv (MonoidAlgebra R X →ₐ[R] B) := toConv Algebra.TensorProduct.includeRight
  let φ : A →ₐ[R] B := Algebra.TensorProduct.includeLeft
  -- The universal torus point records the characters as monomials on its diagonal.
  have hD : (pointsMulEquiv n (BialgHom.mapDomain π u) : Matrix (Fin n) (Fin n) B) =
      Matrix.diagonal fun a ↦ (1 : A) ⊗ₜ[R] MonoidAlgebra.single (e a) (1 : R) := by
    ext a b
    rw [pointsMulEquiv_apply, pointToGeneralLinear_apply, BialgHom.mapDomain_apply,
      ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom,
      hπ, Matrix.diagonal_apply]
    split_ifs
    · exact Algebra.TensorProduct.includeRight_apply _
    · simp
  have hM (i j : Fin n) :
      (pointsMulEquiv n (AlgHom.mapValue φ g) : Matrix (Fin n) (Fin n) B) i j =
        (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) i j ⊗ₜ[R]
          (1 : MonoidAlgebra R X) := by
    rw [pointsMulEquiv_mapValue]
    simp only [Matrix.GeneralLinearGroup.map_apply, AlgHom.coe_toRingHom]
    exact Algebra.TensorProduct.includeLeft_apply _
  rw [BialgHom.centralizerHopfIdeal_le_ker_iff_commute_of_injective _ g
    (AlgHom.id R B) Function.injective_id, AlgHom.id_comp, AlgHom.id_comp]
  constructor
  · intro hcomm i j hij
    have hm := congrArg (fun h ↦
      (pointsMulEquiv n h : Matrix (Fin n) (Fin n) B)) hcomm.eq
    simp only [map_mul, Units.val_mul] at hm
    have hmap : (pointsMulEquiv n (AlgHom.mapValue φ g) : Matrix (Fin n) (Fin n) B) =
        (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A).map φ := by
      ext a b
      exact hM a b
    rw [hD, hmap] at hm
    -- Coefficients of distinct character monomials force the off-diagonal entry to vanish.
    exact Matrix.apply_eq_zero_of_commute_diagonal_monomial _ e hm hij.symm
  · intro hg
    -- A character-block matrix commutes with the universal diagonal torus point.
    apply (pointsMulEquiv n).injective
    apply Units.ext
    simp only [map_mul, Units.val_mul]
    rw [hD]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hM]
    by_cases hij : e i = e j
    · rw [hij, mul_comm]
    · rw [hg i j hij, zero_tmul, zero_mul, mul_zero]

/-- A diagonal representation with distinct characters has exactly the diagonal matrices as
its schematic centralizer, over every value algebra. The displayed coordinate equations specify
its diagonal representation without requiring the character group to be free. -/
theorem _root_.BialgHom.centralizerHopfIdeal_le_ker_iff_isDiag_of_coordinates
    (π : coordinateHopfAlgebra R n →ₐc[R] MonoidAlgebra R X)
    (e : Fin n → X) (he : Function.Injective e)
    (hπ : ∀ i j, π (coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      if i = j then MonoidAlgebra.single (e i) 1 else 0)
    {A : Type w} [CommRing A] [Algebra R A]
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (BialgHom.centralizerHopfIdeal π).toIdeal ≤
        RingHom.ker g.ofConv ↔
      (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A).IsDiag := by
  rw [BialgHom.centralizerHopfIdeal_le_ker_iff_apply_eq_zero_of_coordinates π e hπ]
  exact ⟨fun h i j hij ↦ h i j (he.ne hij),
    fun h i j hij ↦ h (ne_of_apply_ne e hij)⟩

/-- The schematic centralizer of any weight torus consists of matrices preserving the weight
blocks, over arbitrary value algebras. There is no restriction on weight multiplicities. -/
theorem centralizerHopfIdeal_weightTorus_le_ker_iff_apply_eq_zero
    {σ : Type v} [Finite σ] (wt : Fin n → σ → ℤ)
    {A : Type w} [CommRing A] [Algebra R A]
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (BialgHom.centralizerHopfIdeal (weightTorusCoordinateBialgHom (S := R) wt)).toIdeal ≤
        RingHom.ker g.ofConv ↔
      ∀ i j, wt i ≠ wt j → (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) i j = 0 := by
  classical
  rw [BialgHom.centralizerHopfIdeal_le_ker_iff_apply_eq_zero_of_coordinates
    (weightTorusCoordinateBialgHom (S := R) wt)
    (fun i ↦ .ofAdd (Finsupp.equivFunOnFinite.symm (wt i)))
    (weightTorusCoordinateBialgHom_X wt)]
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]

/-- The schematic centralizer of a weight torus with distinct weights consists of diagonal
matrices, over arbitrary value algebras, without infinitude, reducedness or field assumptions. -/
theorem centralizerHopfIdeal_weightTorus_le_ker_iff_isDiag
    {σ : Type v} [Finite σ] (wt : Fin n → σ → ℤ) (hwt : Function.Injective wt)
    {A : Type w} [CommRing A] [Algebra R A]
    (g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (BialgHom.centralizerHopfIdeal (weightTorusCoordinateBialgHom (S := R) wt)).toIdeal ≤
        RingHom.ker g.ofConv ↔
      (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A).IsDiag := by
  classical
  exact BialgHom.centralizerHopfIdeal_le_ker_iff_isDiag_of_coordinates
    (weightTorusCoordinateBialgHom (S := R) wt)
    (fun i ↦ .ofAdd (Finsupp.equivFunOnFinite.symm (wt i)))
    (Multiplicative.ofAdd.injective.comp (Finsupp.equivFunOnFinite.symm.injective.comp hwt))
    (weightTorusCoordinateBialgHom_X wt) g

end TauCeti.GeneralLinear
