/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExchangeRelations
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The determinant-matrix action on period polynomials

For even `w`, the right substitution action of a determinant-`n` matrix on homogeneous binary
forms of degree `w` depends only on its class modulo sign. Extending this action linearly gives
an action of the matrix module used in the level-one trace formula. Popa and Zagier's exchange
relations ensure that this action maps each of `ker (1 + S)` and `ker (1 + U + U²)`, with `U = T S`,
into the other, and hence preserves their intersection, the period-polynomial space.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1.
-/

public section

open MonoidAlgebra MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups RightActions

namespace TauCeti.TraceFormulaMatrixModule

variable {R : Type*} [CommRing R] {n : ℤ} {w : ℕ}

/-- Substitution by a projective determinant-`n` matrix on binary forms of even degree. -/
noncomputable def binaryFormAction (hw : Even w) (x : TraceFormulaMatrixModule n) :
    Module.End R (homogeneousSubmodule (Fin 2) R w) :=
  Quotient.lift (fun A : TraceFormulaMatrix n ↦ binaryFormRep R w (op A.1))
    (fun A B h ↦ by
      rcases h with h | h
      · subst B; rfl
      · rw [h, TraceFormulaMatrix.val_neg, binaryFormRep_op_neg_of_even hw]) x

/-- On a representative, the projective action is the usual binary-form substitution. -/
@[simp]
theorem binaryFormAction_mk (hw : Even w) (A : TraceFormulaMatrix n) :
    binaryFormAction (R := R) hw (TraceFormulaMatrixModule.mk A) =
      binaryFormRep R w (op A.1) := by
  rw [binaryFormAction, TraceFormulaMatrixModule.lift_mk]

/-- Linear extension of the determinant-matrix substitution to the free matrix module. -/
noncomputable def periodAction (hw : Even w) :
    R[TraceFormulaMatrixModule n] →ₗ[R]
      Module.End R (homogeneousSubmodule (Fin 2) R w) :=
  (Finsupp.lsum R fun x ↦ (LinearMap.id : R →ₗ[R] R).smulRight (binaryFormAction (R := R) hw x)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- A basis element acts by its coefficient times the matrix substitution. -/
@[simp]
theorem periodAction_single (hw : Even w) (x : TraceFormulaMatrixModule n) (c : R) :
    periodAction (R := R) hw (single x c) = c • binaryFormAction (R := R) hw x := by
  simp [periodAction]

/-- Left multiplication of a determinant matrix precomposes its substitution action. -/
@[simp]
theorem binaryFormAction_smul (hw : Even w) (g : SL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    binaryFormAction (R := R) hw (g • x) =
      binaryFormAction (R := R) hw x *
        binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
  induction x using TraceFormulaMatrixModule.induction with
  | h A =>
    rw [TraceFormulaMatrixModule.smul_mk, binaryFormAction_mk, binaryFormAction_mk]
    apply LinearMap.ext
    intro P
    simpa only [FixedDetMatrices.smul_coe, Module.End.mul_apply] using
      binaryFormRep_op_mul_apply (g : Matrix (Fin 2) (Fin 2) ℤ) A.1 P

/-- Right multiplication of a determinant matrix postcomposes its substitution action. -/
@[simp]
theorem binaryFormAction_op_smul (hw : Even w) (g : SL(2, ℤ))
    (x : TraceFormulaMatrixModule n) :
    binaryFormAction (R := R) hw (op (g : PSL(2, ℤ)) • x) =
      binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ)) *
        binaryFormAction (R := R) hw x := by
  induction x using TraceFormulaMatrixModule.induction with
  | h A =>
    rw [TraceFormulaMatrixModule.op_smul_mk, binaryFormAction_mk, binaryFormAction_mk]
    apply LinearMap.ext
    intro P
    simpa only [val_traceFormulaMatrixRight, inv_inv, Module.End.mul_apply] using
      binaryFormRep_op_mul_apply A.1 (g : Matrix (Fin 2) (Fin 2) ℤ) P

/-- The free matrix action turns left multiplication in the matrix module into
precomposition of substitutions. -/
@[simp]
theorem periodAction_ofMulAction (hw : Even w) (g : SL(2, ℤ))
    (ξ : R[TraceFormulaMatrixModule n]) :
    periodAction (R := R) hw
        (Representation.ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) g ξ) =
      periodAction (R := R) hw ξ *
        binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ)) := by
  have h : (periodAction (R := R) hw).comp
      (Representation.ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) g) =
      (LinearMap.mulRight R (binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ)))).comp
        (periodAction (R := R) hw) := by
    apply MonoidAlgebra.lhom_ext'
    intro x
    ext c P
    simp [binaryFormAction_smul]
  exact congrArg (fun f : R[TraceFormulaMatrixModule n] →ₗ[R] _ ↦ f ξ) h

/-- The free matrix action turns right multiplication in the matrix module into
postcomposition of substitutions. -/
@[simp]
theorem periodAction_ofMulAction_op (hw : Even w) (g : SL(2, ℤ))
    (ξ : R[TraceFormulaMatrixModule n]) :
    periodAction (R := R) hw
        (Representation.ofMulAction R PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n)
          (op (g : PSL(2, ℤ))) ξ) =
      binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ)) *
        periodAction (R := R) hw ξ := by
  have h : (periodAction (R := R) hw).comp
      (Representation.ofMulAction R PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n)
        (op (g : PSL(2, ℤ)))) =
      (LinearMap.mulLeft R (binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ)))).comp
        (periodAction (R := R) hw) := by
    apply MonoidAlgebra.lhom_ext'
    intro x
    ext c P
    simp [binaryFormAction_op_smul]
  exact congrArg (fun f : R[TraceFormulaMatrixModule n] →ₗ[R] _ ↦ f ξ) h

private theorem periodAction_left_one_add (hw : Even w) (g : SL(2, ℤ))
    (ξ : R[TraceFormulaMatrixModule n])
    (P : homogeneousSubmodule (Fin 2) R w) :
    periodAction (R := R) hw
        ((1 + Representation.ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) g) ξ) P =
      periodAction (R := R) hw ξ
        (P + binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ)) P) := by
  simp [periodAction_ofMulAction, map_add]

private theorem periodAction_right_one_add (hw : Even w) (g : SL(2, ℤ))
    (ξ : R[TraceFormulaMatrixModule n])
    (P : homogeneousSubmodule (Fin 2) R w) :
    periodAction (R := R) hw
        ((1 + Representation.ofMulAction R PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n)
          (op (g : PSL(2, ℤ)))) ξ) P =
      periodAction (R := R) hw ξ P +
        binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ))
          (periodAction (R := R) hw ξ P) := by
  simp [periodAction_ofMulAction_op]

private theorem periodAction_left_one_add_add_sq (hw : Even w) (g : SL(2, ℤ))
    (ξ : R[TraceFormulaMatrixModule n])
    (P : homogeneousSubmodule (Fin 2) R w) :
    periodAction (R := R) hw
        (((1 + Representation.ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) g +
          Representation.ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) g ^ 2) :
          Module.End R R[TraceFormulaMatrixModule n]) ξ) P =
      periodAction (R := R) hw ξ
        (P + binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ)) P +
          binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ))
            (binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ)) P)) := by
  simp [periodAction_ofMulAction, pow_two, map_add]

private theorem periodAction_right_one_add_add_sq (hw : Even w) (g : SL(2, ℤ))
    (ξ : R[TraceFormulaMatrixModule n])
    (P : homogeneousSubmodule (Fin 2) R w) :
    periodAction (R := R) hw
        (((1 + Representation.ofMulAction R PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n)
            (op (g : PSL(2, ℤ))) +
          Representation.ofMulAction R PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n)
            (op (g : PSL(2, ℤ))) ^ 2) :
          Module.End R R[TraceFormulaMatrixModule n]) ξ) P =
      periodAction (R := R) hw ξ P +
        binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ))
          (periodAction (R := R) hw ξ P) +
        binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ))
          (binaryFormRep R w (op (g : Matrix (Fin 2) (Fin 2) ℤ))
            (periodAction (R := R) hw ξ P)) := by
  simp [periodAction_ofMulAction_op, pow_two, map_add]

/-- **The first exchange map.** By the exchange relation `ξ (1 + S) ∈ (1 + U + U²) ℛₙ`, the action
of `ξ` maps `ker (1 + U + U²)` into `ker (1 + S)`, where `U = T S`. -/
theorem ExchangeRelations.periodAction_mem_ker_one_add_S (hw : Even w)
    {ξ : R[TraceFormulaMatrixModule n]} (hξ : ExchangeRelations R n ξ)
    {P : homogeneousSubmodule (Fin 2) R w}
    (hP : P ∈ LinearMap.ker
      (1 + binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
        binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2)) :
    periodAction (R := R) hw ξ P ∈
      LinearMap.ker (1 + binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ))) := by
  have hU : P + binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P +
      binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
        (binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P) = 0 := by
    simpa [pow_two] using hP
  obtain ⟨η, hη⟩ := hξ.one_add_S
  have h := congrArg (fun ζ : R[TraceFormulaMatrixModule n] ↦ periodAction (R := R) hw ζ P) hη
  rw [periodAction_left_one_add_add_sq hw (T * S) η P, hU, map_zero,
    periodAction_right_one_add hw S ξ P] at h
  simpa using h.symm

/-- **The second exchange map.** By the exchange relation `ξ (1 + U + U²) ∈ (1 + S) ℛₙ`, the action
of `ξ` maps `ker (1 + S)` into `ker (1 + U + U²)`, where `U = T S`. -/
theorem ExchangeRelations.periodAction_mem_ker_one_add_U_add_U_sq (hw : Even w)
    {ξ : R[TraceFormulaMatrixModule n]} (hξ : ExchangeRelations R n ξ)
    {P : homogeneousSubmodule (Fin 2) R w}
    (hP : P ∈ LinearMap.ker (1 + binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ)))) :
    periodAction (R := R) hw ξ P ∈ LinearMap.ker
      (1 + binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
        binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2) := by
  have hS : P + binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ)) P = 0 := by simpa using hP
  obtain ⟨θ, hθ⟩ := hξ.one_add_U_add_U_sq
  have h := congrArg (fun ζ : R[TraceFormulaMatrixModule n] ↦ periodAction (R := R) hw ζ P) hθ
  -- The exchange relation multiplies the images of `T` and `S` in `PSL(2, ℤ)`, while
  -- `periodAction_right_one_add_add_sq` takes the image of a single matrix `U = T S` of
  -- `SL(2, ℤ)`; the projection `SL(2, ℤ) → PSL(2, ℤ)` is multiplicative.
  have hU : ((T * S : SL(2, ℤ)) : PSL(2, ℤ)) = (T : PSL(2, ℤ)) * S := QuotientGroup.mk_mul _ _ _
  rw [← hU] at h
  rw [periodAction_left_one_add hw S θ P, hS, map_zero,
    periodAction_right_one_add_add_sq hw (T * S) ξ P] at h
  simpa [pow_two] using h.symm

/-- Popa and Zagier's exchange relations make the determinant-matrix action preserve the
period-polynomial space. -/
theorem ExchangeRelations.periodAction_mem_periodPolynomials (hw : Even w)
    {ξ : R[TraceFormulaMatrixModule n]} (hξ : ExchangeRelations R n ξ)
    {P : homogeneousSubmodule (Fin 2) R w} (hP : P ∈ periodPolynomials R w) :
    periodAction (R := R) hw ξ P ∈ periodPolynomials R w := by
  rw [periodPolynomials_def, Submodule.mem_inf] at hP ⊢
  exact ⟨hξ.periodAction_mem_ker_one_add_S hw hP.2,
    hξ.periodAction_mem_ker_one_add_U_add_U_sq hw hP.1⟩

/-- The action of an element satisfying the exchange relations on period polynomials. -/
noncomputable def ExchangeRelations.periodActionRestrict (hw : Even w)
    {ξ : R[TraceFormulaMatrixModule n]} (hξ : ExchangeRelations R n ξ) :
    Module.End R (periodPolynomials R w) :=
  (periodAction (R := R) hw ξ).restrict fun _ hP ↦
    hξ.periodAction_mem_periodPolynomials hw hP

/-- The restricted action agrees with the action on homogeneous forms. -/
@[simp]
theorem ExchangeRelations.coe_periodActionRestrict_apply (hw : Even w)
    {ξ : R[TraceFormulaMatrixModule n]} (hξ : ExchangeRelations R n ξ)
    (P : periodPolynomials R w) :
    ((hξ.periodActionRestrict hw P : periodPolynomials R w) :
        homogeneousSubmodule (Fin 2) R w) = periodAction (R := R) hw ξ P :=
  LinearMap.coe_restrict_apply _ _

end TauCeti.TraceFormulaMatrixModule
