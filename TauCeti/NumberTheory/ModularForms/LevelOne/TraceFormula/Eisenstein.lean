/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.HeckeSymbol
public import TauCeti.NumberTheory.ModularForms.ModularSymbols.Boundary

/-!
# The Hecke eigenvalue of the Eisenstein period polynomial

Let `w` be even and `n ≠ 0`. Every solution `ξ` of Popa–Zagier's period relation (A) in
`ℛₙ = R[ℳₙ]` acts on the Eisenstein period polynomial `X^w - Y^w` by the scalar `σ_{w+1}(|n|)`:

`(X^w - Y^w) ∣ ξ = σ_{w+1}(|n|) (X^w - Y^w)`

(`TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_eisensteinPeriodPolynomial`). For
`n > 0` and positive even `w`, this is the eigenvalue of the Hecke operator `Tₙ` on the Eisenstein
series `E_{w+2}`, whose extended even period polynomial is a multiple of `X^w - Y^w`: the
solutions of (A) act on period polynomials as `Tₙ` on the Eisenstein part, as they do on the
period polynomials of cusp forms
(`TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_periodPolynomial`). This is the
Eisenstein contribution `σ_{k-1}(n)` to the trace of `Tₙ` on the period-polynomial space, in
weight `k = w + 2 ≥ 4`. At `w = 0` the polynomial `X^0 - Y^0` is zero and `E₂` is not a level-one
modular form, so the identity holds trivially and has no such interpretation.

The proof is algebraic. The binary form attached to the functional `P ↦ P(1, 0) - P(0, 1)` is
`Y^w - X^w`, and this functional is the evaluation of the modular symbols `{∞, 0} ⊗ P` at the
cusps (`TauCeti.ModularSymbols.boundaryEval`). By Popa–Zagier's Proposition 2 on modular symbols
(`TauCeti.TraceFormulaMatrixModule.PeriodRelation.symbolAction_eq`), the action of `ξ` on it is
the evaluation of `∑ {a∞, a0} ⊗ (P ∣ adj a)` at the cusps, the sum over the upper-triangular
representatives `a = (a b; 0 d)` of `Γ \ ℳₙ`. The values at `a∞ = ∞` are
`P(adj a (1, 0)) = P(d, 0) = dʷ P(1, 0)`, and there are `|d|` representatives for each factor
pair `(a, d)`, so they sum to `σ_{w+1}(|n|) P(1, 0)`
(`TauCeti.TraceFormulaMatrixModule.boundaryEval_comp_upperTriangularSymbol`). The values at
`a0 = (aS)∞` are the values at `∞` along the representatives `aS`. The functional
`M ↦ (P ∣ adj M)(v_{M∞})` is invariant under left multiplication by `SL(2, ℤ)`, and `Tₙ^∞ S` is the
formal sum of another set of representatives of `Γ \ ℳₙ`, so these sum to
`σ_{w+1}(|n|) (P ∣ S)(1, 0) = σ_{w+1}(|n|) P(0, 1)`. No count of the cusps `b/d` is needed.

## Main results

* `TauCeti.binaryFormDual_evalCusp_infty_sub_evalCusp_zero`: the binary
  form attached to `P ↦ P(1, 0) - P(0, 1)` is `-(X^w - Y^w)`, for even `w`.
* `TauCeti.TraceFormulaMatrixModule.boundaryEval_comp_upperTriangularSymbol`: the evaluation at
  the cusps of `∑ {a∞, a0} ⊗ (P ∣ adj a)` is `σ_{w+1}(|n|) (P(1, 0) - P(0, 1))`.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_eisensteinPeriodPolynomial`: every
  solution of the period relation acts on `X^w - Y^w` by `σ_{w+1}(|n|)`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §§1–2.
* W. Kohnen and D. Zagier, *Modular forms with rational periods*, in *Modular Forms*
  (R. A. Rankin, ed.), Ellis Horwood, 1984, 197–249, §1.
-/

public section

open MonoidAlgebra MulOpposite MvPolynomial ModularGroup OnePoint Representation
open TauCeti.ModularSymbols
open FixedDetMatrices (toGL toGL_smul)
open Matrix.SpecialLinearGroup (mapGL)
open scoped MatrixGroups RightActions

namespace TauCeti

variable {R : Type*} [CommRing R] {n : ℤ} {w : ℕ}

/-! ### The binary form of the evaluation at `∞` and `0` -/

/-- The value at `∞` of the monomial `Xⁱ Yʷ⁻ⁱ` is `1` for `i = w` and `0` otherwise. -/
private theorem evalCusp_infty_binaryFormMonomialBasis (i : Fin (w + 1)) :
    evalCusp R w ∞ (binaryFormMonomialBasis R w i) = if i = Fin.last w then 1 else 0 := by
  have hi : (i : ℕ) ≤ w := Nat.lt_succ_iff.mp i.2
  rw [evalCusp_infty, coe_binaryFormMonomialBasis]
  simp only [eval_mul, eval_pow, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow,
    one_mul, zero_pow_eq, Nat.sub_eq_zero_iff_le, hi.ge_iff_eq',
    Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | omega

/-- The value at `0` of the monomial `Xⁱ Yʷ⁻ⁱ` is `1` for `i = 0` and `0` otherwise. -/
private theorem evalCusp_zero_binaryFormMonomialBasis (i : Fin (w + 1)) :
    evalCusp R w (0 : ℚ) (binaryFormMonomialBasis R w i) = if i = 0 then 1 else 0 := by
  rw [evalCusp_coe, coe_binaryFormMonomialBasis]
  simp only [Rat.num_zero, Rat.den_zero, Int.cast_zero, Nat.cast_one, eval_mul, eval_pow, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one, zero_pow_eq, Fin.ext_iff,
    Fin.val_zero]

/-- **The Eisenstein polynomial is the binary form of the evaluation at `∞` and `0`.** For even
`w`, the binary form attached to `P ↦ P(1, 0) - P(0, 1)` is `Y^w - X^w`. -/
theorem binaryFormDual_evalCusp_infty_sub_evalCusp_zero (hw : Even w) :
    binaryFormDual R w (evalCusp R w ∞ - evalCusp R w (0 : ℚ)) =
      -eisensteinPeriodPolynomial R w := by
  have hlast : ∀ j : Fin (w + 1), Fin.rev j = Fin.last w ↔ j = 0 := fun j ↦ by
    rw [← Fin.rev_zero, Fin.rev_inj]
  have hzero : ∀ j : Fin (w + 1), Fin.rev j = 0 ↔ j = Fin.last w := fun j ↦ by
    rw [← Fin.rev_last, Fin.rev_inj]
  rw [binaryFormDual_apply]
  simp only [LinearMap.sub_apply, evalCusp_infty_binaryFormMonomialBasis,
    evalCusp_zero_binaryFormMonomialBasis, hlast, hzero, mul_sub, mul_ite, mul_one, mul_zero]
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, sub_smul, ite_smul, zero_smul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp [hw.neg_one_pow]

namespace TraceFormulaMatrixModule

/-! ### The values at the cusps `a∞` -/

/-- The functional `P ↦ (P ∣ adj M)(v_{M∞})` attached to a determinant-`n` matrix `M`. -/
private noncomputable def infinityEval (hn : n ≠ 0) (A : TraceFormulaMatrix n) :
    homogeneousSubmodule (Fin 2) R w →ₗ[R] R :=
  evalCusp R w (toGL hn A • ∞) ∘ₗ binaryFormAdjugateRep R w A.1

private theorem infinityEval_neg (hn : n ≠ 0) (hw : Even w) (A : TraceFormulaMatrix n) :
    infinityEval (R := R) (w := w) hn (-A) = infinityEval hn A := by
  rw [infinityEval, infinityEval, toGL_neg_smul, TraceFormulaMatrix.val_neg,
    binaryFormAdjugateRep_neg_of_even hw]

/-- The functional `infinityEval` is invariant under left multiplication by `SL(2, ℤ)`. -/
private theorem infinityEval_smul (hn : n ≠ 0) (hw : Even w) (g : SL(2, ℤ))
    (A : TraceFormulaMatrix n) :
    infinityEval (R := R) (w := w) hn (g • A) = infinityEval hn A := by
  ext P
  simp only [infinityEval, LinearMap.comp_apply, toGL_smul, mul_smul, FixedDetMatrices.smul_coe,
    map_mul, mul_apply_eq_comp, binaryFormAdjugateRep_coe, evalCusp_mapGL_smul hw]

/-- On an upper-triangular representative `(a b; 0 d)`, `infinityEval` is `P ↦ dʷ P(1, 0)`. -/
private theorem infinityEval_of_mem_reps (hn : n ≠ 0) (A : TraceFormulaMatrix n)
    (hA : A ∈ FixedDetMatrices.reps n) :
    infinityEval (R := R) (w := w) hn A = ((A.1 1 1 : ℤ) : R) ^ w • evalCusp R w ∞ := by
  ext P
  have hc : A.1 1 0 = 0 := hA.1
  have hinf : toGL hn A • (∞ : OnePoint ℚ) = ∞ :=
    smul_infty_eq_self_iff.2 (by simp [FixedDetMatrices.coe_toGL, hc])
  -- `adj A (1, 0) = (d, 0) = d • (1, 0)`
  have hv : Matrix.mulVec ((Matrix.adjugate A.1).map (Int.cast : ℤ → R)) ![1, 0] =
      ((A.1 1 1 : ℤ) : R) • ![1, 0] := by
    ext i
    fin_cases i <;> simp [Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, hc]
  simp only [infinityEval, LinearMap.comp_apply, hinf, evalCusp_infty, binaryFormAdjugateRep_apply,
    coe_binaryFormRep_apply, eval_linearSubst, hv, ((mem_homogeneousSubmodule _ _).1 P.2).eval_smul,
    LinearMap.smul_apply]

/-- The linear extension of `infinityEval` to `R[ℳₙ]`. -/
private noncomputable def infinityEvalAction (hn : n ≠ 0) (hw : Even w) :
    R[TraceFormulaMatrixModule n] →ₗ[R] homogeneousSubmodule (Fin 2) R w →ₗ[R] R :=
  linearLift (infinityEval hn) (infinityEval_neg hn hw)

private theorem infinityEvalAction_ofMulAction (hn : n ≠ 0) (hw : Even w) (g : SL(2, ℤ))
    (ξ : R[TraceFormulaMatrixModule n]) :
    infinityEvalAction (w := w) hn hw (ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) g ξ) =
      infinityEvalAction hn hw ξ := by
  induction ξ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add ξ η hξ hη => simp only [map_add, hξ, hη]
  | single x c =>
    induction x using TraceFormulaMatrixModule.induction with | h A => ?_
    rw [ofMulAction_single, smul_mk, infinityEvalAction, linearLift_single, linearLift_single,
      infinityEval_smul hn hw]

/-- `infinityEvalAction` kills the coinvariant kernel of the left action of `SL(2, ℤ)`. -/
private theorem infinityEvalAction_eq_zero_of_mem (hn : n ≠ 0) (hw : Even w)
    {ζ : R[TraceFormulaMatrixModule n]}
    (hζ : ζ ∈ Coinvariants.ker (ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n))) :
    infinityEvalAction (w := w) hn hw ζ = 0 := by
  rw [← Coinvariants.lift_mk _ (infinityEvalAction hn hw)
    (fun g ↦ LinearMap.ext (infinityEvalAction_ofMulAction hn hw g)) ζ,
    (Coinvariants.mk_eq_zero _).2 hζ, map_zero]

/-- `infinityEvalAction` sends `Tₙ^∞` to `σ_{w+1}(|n|)` times the value at `∞`. -/
private theorem infinityEvalAction_upperTriangularSum (hn : n ≠ 0) (hw : Even w) :
    infinityEvalAction (w := w) hn hw (upperTriangularSum R n) =
      (ArithmeticFunction.sigma (w + 1) n.natAbs : R) • evalCusp R w ∞ := by
  rw [upperTriangularSum_eq_sum_reps, map_sum, ← FixedDetMatrices.sum_reps_pow hn hw,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [infinityEvalAction, linearLift_single, one_smul, infinityEval_of_mem_reps hn A.1 A.2]

/-! ### The values at the cusps `a0` -/

/-- The value of `P ∣ adj M` at `M0` is the value of `(P ∣ S) ∣ adj (MS)` at `(MS)∞`. -/
private theorem evalCusp_toGL_smul_zero (hn : n ≠ 0) (A : TraceFormulaMatrix n) :
    evalCusp R w (toGL hn A • ((0 : ℚ) : OnePoint ℚ)) ∘ₗ binaryFormAdjugateRep R w A.1 =
      infinityEval hn (traceFormulaMatrixRight S⁻¹ A) ∘ₗ
        binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ)) := by
  ext P
  simp only [infinityEval, LinearMap.comp_apply, toGL_traceFormulaMatrixRight, inv_inv, mul_smul,
    mapGL_S_smul_infty, val_traceFormulaMatrixRight, map_mul, mul_apply_eq_comp,
    binaryFormAdjugateRep_coe, binaryFormSLRep_binaryFormRep]

/-- The values at the cusps `a0` sum to `σ_{w+1}(|n|)` times the value at `0`. -/
private theorem sum_reps_evalCusp_toGL_smul_zero (hn : n ≠ 0) (hw : Even w) :
    ∑ A : FixedDetMatrices.reps n,
        evalCusp R w (toGL hn A.1 • ((0 : ℚ) : OnePoint ℚ)) ∘ₗ binaryFormAdjugateRep R w A.1.1 =
      (ArithmeticFunction.sigma (w + 1) n.natAbs : R) • evalCusp R w (0 : ℚ) := by
  -- the left side is `infinityEvalAction` of `Tₙ^∞ S`, which has the coinvariant class of `Tₙ^∞`
  have hS : infinityEvalAction (w := w) hn hw
      (ofMulAction R PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n) (op (S : PSL(2, ℤ)))
        (upperTriangularSum R n)) = infinityEvalAction hn hw (upperTriangularSum R n) := by
    have h := infinityEvalAction_eq_zero_of_mem (w := w) hn hw
      (one_sub_ofMulAction_op_upperTriangularSum_mem (k := R) (n := n) (S : PSL(2, ℤ)))
    rw [LinearMap.sub_apply, one_apply_eq_self, map_sub, sub_eq_zero] at h
    exact h.symm
  have hsum : infinityEvalAction (w := w) hn hw
      (ofMulAction R PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n) (op (S : PSL(2, ℤ)))
        (upperTriangularSum R n)) =
      ∑ A : FixedDetMatrices.reps n, infinityEval hn (traceFormulaMatrixRight S⁻¹ A.1) := by
    rw [upperTriangularSum_eq_sum_reps, map_sum, map_sum]
    refine Finset.sum_congr rfl fun A _ ↦ ?_
    rw [ofMulAction_single, op_smul_mk, infinityEvalAction, linearLift_single, one_smul]
  -- `(P ∣ S)(1, 0) = P(0, 1)`
  have hval : evalCusp R w ∞ ∘ₗ binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ)) =
      evalCusp R w (0 : ℚ) := by
    ext P
    have hv : Matrix.mulVec ((S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R)) ![1, 0] =
        ![(((0 : ℚ).num : ℤ) : R), (((0 : ℚ).den : ℕ) : R)] := by
      ext i
      fin_cases i <;> simp [coe_S, Matrix.mulVec, dotProduct]
    rw [LinearMap.comp_apply, evalCusp_infty, coe_binaryFormRep_apply, eval_linearSubst, hv,
      evalCusp_coe]
  simp_rw [evalCusp_toGL_smul_zero hn]
  rw [← hval, ← LinearMap.smul_comp, ← infinityEvalAction_upperTriangularSum hn hw, ← hS, hsum]
  ext P
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]

/-! ### The Hecke eigenvalue -/

/-- **The evaluation at the cusps of the Hecke sum over `ℳₙ^∞`.** For `n ≠ 0` and even `w`, the
evaluation at the cusps of `∑ {∞, b/d} ⊗ (P ∣ adj (a b; 0 d))`, the sum over the upper-triangular
representatives of `Γ \ ℳₙ`, is `σ_{w+1}(|n|) (P(1, 0) - P(0, 1))`. -/
theorem boundaryEval_comp_upperTriangularSymbol (hn : n ≠ 0) (hw : Even w) :
    boundaryEval ⊤ hw ∘ₗ upperTriangularSymbol R n w =
      (ArithmeticFunction.sigma (w + 1) n.natAbs : R) •
        (evalCusp R w ∞ - evalCusp R w (0 : ℚ)) := by
  have hinf := infinityEvalAction_upperTriangularSum (R := R) (w := w) hn hw
  rw [upperTriangularSum_eq_sum_reps, map_sum] at hinf
  simp only [infinityEvalAction, linearLift_single, one_smul] at hinf
  rw [smul_sub, ← hinf, ← sum_reps_evalCusp_toGL_smul_zero hn hw, ← Finset.sum_sub_distrib,
    upperTriangularSymbol_eq_sum_toGL_smul hn]
  ext P
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    boundaryEval_symbol, LinearMap.sub_apply, infinityEval]

/-- **The Hecke eigenvalue of the Eisenstein period polynomial.** For `n ≠ 0` and even `w`, every
solution `ξ` of Popa–Zagier's period relation (A) acts on the Eisenstein polynomial `X^w - Y^w`
by `σ_{w+1}(|n|)`: `(X^w - Y^w) ∣ ξ = σ_{w+1}(|n|) (X^w - Y^w)`. -/
theorem PeriodRelation.periodAction_eisensteinPeriodPolynomial (hn : n ≠ 0) (hw : Even w)
    {ξ : R[TraceFormulaMatrixModule n]} (h : PeriodRelation R n ξ) :
    periodAction hw ξ (eisensteinPeriodPolynomial R w) =
      (ArithmeticFunction.sigma (w + 1) n.natAbs : R) • eisensteinPeriodPolynomial R w := by
  have key := h.periodAction_binaryFormDual hn hw (boundaryEval ⊤ hw)
  rw [boundaryEval_comp_symbol, boundaryEval_comp_upperTriangularSymbol hn hw, _root_.map_smul,
    binaryFormDual_evalCusp_infty_sub_evalCusp_zero hw, map_neg, smul_neg] at key
  exact neg_injective key

end TraceFormulaMatrixModule

end TauCeti
