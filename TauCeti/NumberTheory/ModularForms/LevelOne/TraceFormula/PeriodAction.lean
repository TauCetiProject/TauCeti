/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExchangeRelations
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The determinant-matrix action on period polynomials

For even `w`, the right substitution action of a determinant-`n` matrix on homogeneous binary
forms of degree `w` depends only on its class modulo sign. Extending this action linearly gives
an action of the matrix module used in the level-one trace formula. Popa and Zagier's exchange
relations ensure that this action maps each of `ker (1 + S)` and `ker (1 + U + U²)`, with `U = T S`,
into the other, and hence preserves their intersection, the period-polynomial space.

Evaluating Popa and Zagier's period relation (A) on the monomial `Y^w` — which is fixed by `T` and
sent to `Y^w - X^w = -(X^w - Y^w)` by `1 - S` — also shows that every solution `ξ` of
`PeriodRelation R n ξ` (`n ≥ 1`) scales the Eisenstein period polynomial `X^w - Y^w` by
`σ_{w+1}(n)` (`PeriodRelation.periodAction_eisensteinPeriodPolynomial`).

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §§1–2.
-/

public section

open MonoidAlgebra MulOpposite MvPolynomial ModularGroup
open scoped ArithmeticFunction.sigma MatrixGroups RightActions

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
  linearLift (fun A ↦ binaryFormRep R w (op A.1)) fun A ↦ by
    rw [TraceFormulaMatrix.val_neg, binaryFormRep_op_neg_of_even hw]

/-- A basis element acts by its coefficient times the matrix substitution. -/
@[simp]
theorem periodAction_single (hw : Even w) (x : TraceFormulaMatrixModule n) (c : R) :
    periodAction (R := R) hw (single x c) = c • binaryFormAction (R := R) hw x := by
  induction x using TraceFormulaMatrixModule.induction with
  | h A => rw [periodAction, linearLift_single, binaryFormAction_mk]

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
    simpa only [FixedDetMatrices.smul_coe, mul_apply_eq_comp] using
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
    simpa only [val_traceFormulaMatrixRight, inv_inv, mul_apply_eq_comp] using
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

/-! ### Action of the period relation on the Eisenstein period polynomial -/

/-- `T = (1 1; 0 1)` fixes the monomial `Y^w`. -/
private theorem binaryFormRep_T_X_one_pow :
    binaryFormRep R w (op (T : Matrix (Fin 2) (Fin 2) ℤ)) ⟨X 1 ^ w, isHomogeneous_X_pow 1 w⟩ =
      ⟨X 1 ^ w, isHomogeneous_X_pow 1 w⟩ := by
  simpa [coe_T] using binaryFormRep_upperTriangular_X_one_pow (R := R) (w := w)
    (M := (T : Matrix (Fin 2) (Fin 2) ℤ)) (by simp [coe_T])

/-- `Y^w - Y^w ∣ S = Y^w - X^w = -eisensteinPeriodPolynomial R w`. -/
private theorem sub_binaryFormRep_S_X_one_pow :
    (⟨X 1 ^ w, isHomogeneous_X_pow 1 w⟩ : homogeneousSubmodule (Fin 2) R w) -
      binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ))
        ⟨X 1 ^ w, isHomogeneous_X_pow 1 w⟩ =
      -eisensteinPeriodPolynomial R w := by
  apply Subtype.ext
  rw [Submodule.coe_sub, Submodule.coe_neg, coe_binaryFormRep_apply,
    coe_eisensteinPeriodPolynomial]
  simp [Fin.sum_univ_two, coe_S]

/-- The upper-triangular sum `Tₙ^∞` (`n ≥ 1`) scales `Y^w` by `σ_{w+1}(n)`: for each positive
divisor `d ∣ n` there are `d` upper-triangular representatives `(n/d, b; 0, d)` with `0 ≤ b < d`,
each scaling `Y^w` by `d^w`. -/
theorem periodAction_upperTriangularSum_X_one_pow (hw : Even w) (n : ℕ) [NeZero n] :
    periodAction (R := R) hw (upperTriangularSum R n) ⟨X 1 ^ w, isHomogeneous_X_pow 1 w⟩ =
      (σ (w + 1) n : R) • ⟨X 1 ^ w, isHomogeneous_X_pow 1 w⟩ := by
  have hn : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hsign : (n : ℤ).sign = 1 := Int.sign_eq_one_of_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero n))
  rw [upperTriangularSum_eq_sum_reps, map_sum, LinearMap.sum_apply]
  have hterm (A : FixedDetMatrices.reps (n : ℤ)) :
      periodAction (R := R) hw (single (mk A.1) 1) ⟨X 1 ^ w, isHomogeneous_X_pow 1 w⟩ =
        (A.1.1 1 1 : R) ^ w • ⟨X 1 ^ w, isHomogeneous_X_pow 1 w⟩ := by
    rw [periodAction_single, one_smul, binaryFormAction_mk,
      binaryFormRep_upperTriangular_X_one_pow A.2.1]
  simp_rw [hterm, ← Finset.sum_smul]
  congr 1
  refine (Fintype.sum_equiv (FixedDetMatrices.repsEquiv hn).symm
    (fun x ↦ (((FixedDetMatrices.repsEquiv hn).symm x).1.1 1 1 : R) ^ w)
    (fun A ↦ (A.1.1 1 1 : R) ^ w) fun _ ↦ rfl).symm.trans ?_
  have hval (x : (p : ↥(n : ℤ).natAbs.divisorsAntidiagonal) × Fin p.1.2) :
      (((FixedDetMatrices.repsEquiv hn).symm x).1.1 1 1 : R) ^ w = ((x.1.1.2 : ℤ) : R) ^ w := by
    have hmatrix : ((FixedDetMatrices.repsEquiv hn).symm x).1.1 =
        !![(x.1.1.1 : ℤ), (x.2 : ℕ); 0, (n : ℤ).sign * x.1.1.2] :=
      FixedDetMatrices.coe_repsEquiv_symm_apply hn x
    rw [hmatrix, hsign]
    simp
  simp_rw [hval]
  rw [Fintype.sum_sigma]
  have hinner (p : ↥(n : ℤ).natAbs.divisorsAntidiagonal) :
      ∑ _ : Fin p.1.2, ((p.1.2 : ℤ) : R) ^ w = ((p.1.2 ^ (w + 1) : ℕ) : R) := by
    rw [Finset.sum_const, Finset.card_fin, Int.cast_natCast, nsmul_eq_mul, Nat.cast_pow,
      pow_succ']
  simp_rw [hinner]
  rw [Finset.sum_coe_sort (n : ℤ).natAbs.divisorsAntidiagonal
      fun p ↦ ((p.2 ^ (w + 1) : ℕ) : R),
    Int.natAbs_natCast,
    Nat.sum_divisorsAntidiagonal' fun _ d ↦ ((d ^ (w + 1) : ℕ) : R),
    ArithmeticFunction.sigma_apply, Nat.cast_sum]

end TauCeti.TraceFormulaMatrixModule
