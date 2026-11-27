/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Alternating
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Matrix.StdBasis
import TauCeti.Data.Matrix.Basis

/-!
# Lie homomorphisms from matrix-unit families

The matrix-unit commutator relations are exactly the relations needed to extend a family of
operators linearly to a Lie homomorphism out of the general linear Lie algebra. They are
preserved under a change of basis and, more generally, under restriction to a split summand.
This allows the quantum-minor identities to be used on the operators for an adapted subspace.

The change-of-basis formula is the matrix-unit part of `Formalism.FourierDecayAlt.Q.Econj`
in L. Alpöge's formalization of the Riemann hypothesis for Dirichlet L-functions.
-/

public section

attribute [local instance 100] LieRing.ofAssociativeRing

open Finset

namespace Matrix.HasMatrixUnitLieRelations

variable {ι K A : Type*} [Fintype ι] [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A]
  {E : Matrix ι ι A}

-- The linear extension of a family along the matrix-unit basis takes its prescribed values.
private theorem constr_single (E : Matrix ι ι A) (i j : ι) :
    (stdBasis K ι ι).constr K (fun i ↦ E i.1 i.2) (single i j 1) = E i j := by
  rw [← stdBasis_eq_single]
  exact (stdBasis K ι ι).constr_basis K (fun i ↦ E i.1 i.2) (i, j)

/-- Extend a family satisfying the matrix-unit relations to the general linear Lie algebra. -/
noncomputable def toLieHom (hE : E.HasMatrixUnitLieRelations) : Matrix ι ι K →ₗ⁅K⁆ A where
  __ := (stdBasis K ι ι).constr K fun i ↦ E i.1 i.2
  map_lie' {x y} := by
    let b := stdBasis K ι ι
    let f := b.constr K fun i ↦ E i.1 i.2
    let bracket₁ := (LieAlgebra.ad K (Matrix ι ι K)).toLinearMap
    let bracket₂ := (LieAlgebra.ad K A).toLinearMap
    have h : bracket₁.compr₂ f = bracket₂.compl₁₂ f f := by
      apply LinearMap.ext_basis b b
      rintro ⟨i, j⟩ ⟨k, l⟩
      simp only [bracket₁, bracket₂, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
        LieHom.coe_toLinearMap, LieAlgebra.ad_apply, b, stdBasis_eq_single, Ring.lie_def,
        single_mul_single_eq_ite, mul_one, map_sub, apply_ite, map_zero, f, constr_single]
      by_cases hli : l = i <;>
        simpa only [hli, ite_true, ite_false] using
          ((hasMatrixUnitLieRelations_iff E).mp hE i j k l).symm
    exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

-- The underlying linear map of the extension is the linear extension along the matrix-unit
-- basis. This is the one place where the definition of `toLieHom` is unfolded.
private theorem toLieHom_toLinearMap (hE : E.HasMatrixUnitLieRelations) :
    (hE.toLieHom (K := K) : Matrix ι ι K →ₗ[K] A) = (stdBasis K ι ι).constr K fun i ↦ E i.1 i.2 :=
  rfl

/-- The extension sends each matrix unit to its prescribed value. -/
@[simp] theorem toLieHom_single (hE : E.HasMatrixUnitLieRelations) (i j : ι) :
    hE.toLieHom (K := K) (single i j 1) = E i j := by
  rw [← LieHom.coe_toLinearMap, toLieHom_toLinearMap, constr_single]

/-- The extension is the linear combination of the family with the input matrix's entries. -/
theorem toLieHom_apply (hE : E.HasMatrixUnitLieRelations) (X : Matrix ι ι K) :
    hE.toLieHom X = ∑ i, ∑ j, X i j • E i j := by
  simpa only [LieHom.coe_toLinearMap, toLieHom_single] using
    hE.toLieHom.toLinearMap.apply_eq_sum_sum_smul_single X

/-- A Lie homomorphism with the prescribed values on matrix units is the extension. -/
theorem toLieHom_eq (hE : E.HasMatrixUnitLieRelations) (f : Matrix ι ι K →ₗ⁅K⁆ A)
    (hf : ∀ i j, f (single i j 1) = E i j) : hE.toLieHom = f := by
  ext X
  rw [toLieHom_apply, ← LieHom.coe_toLinearMap f, f.toLinearMap.apply_eq_sum_sum_smul_single]
  simp only [LieHom.coe_toLinearMap, hf]

/-- The family whose `(i, j)` entry is `hE.toLieHom (P * single i j 1 * Q)`, that is
`∑ c, ∑ d, (P c i * Q j d) • E c d`, again satisfies the matrix-unit relations when `Q * P = 1`.
Rectangular `P` and `Q` give the relations on a split summand. -/
theorem change_of_basis (hE : E.HasMatrixUnitLieRelations) {κ : Type*} [DecidableEq κ]
    (P : Matrix ι κ K) (Q : Matrix κ ι K) (hQP : Q * P = 1) :
    (of fun i j : κ ↦ ∑ c, ∑ d, (P c i * Q j d) • E c d).HasMatrixUnitLieRelations := by
  let f := hE.toLieHom (K := K)
  let S : Matrix κ κ (Matrix ι ι K) := of fun i j ↦ vecMulVec (P.col i) (Q.row j)
  have hmul (i j k l : κ) : S i j * S k l = if j = k then S i l else 0 := by
    have hdot : Q.row j ⬝ᵥ P.col k = if j = k then 1 else 0 := by
      have hentry := congrArg (fun M : Matrix κ κ K ↦ M j k) hQP
      simpa only [Matrix.mul_apply, Matrix.one_apply, dotProduct, row_apply, col_apply] using hentry
    simp only [S, of_apply, vecMulVec_mul_vecMulVec, hdot]
    split <;> simp
  convert (HasMatrixUnitLieRelations.of_mul_eq_ite hmul).map_of_commutator f
    (fun x y ↦ by simpa only [Ring.lie_def] using f.map_lie x y) using 1
  ext i j
  simp only [of_apply, map_apply, f, toLieHom_apply, S, vecMulVec_apply, col_apply, row_apply]

end Matrix.HasMatrixUnitLieRelations
