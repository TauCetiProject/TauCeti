/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PeriodAction
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PeriodRelation
public import TauCeti.NumberTheory.ModularForms.LevelOne.Hecke
public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.CuspForm

/-!
# Solutions of the period relation act as Hecke operators

Let `ℳₙ` be the projective determinant-`n` matrix module and `ℛₙ = R[ℳₙ]`. An element
`ξ = ∑ c_M M` of `ℛₙ` sends a binary form `P` of even degree `w` to the level-one modular symbol

`∑ c_M {∞, 0} ⊗ (P ∣ adj M) ∈ 𝕄_w(SL(2, ℤ); R)`

(`TauCeti.TraceFormulaMatrixModule.symbolAction`), where `P ∣ adj M` is the adjugate
substitution. Through the duality `TauCeti.binaryFormDual` between binary forms and functionals
on them, this is the transpose of the substitution action
`TauCeti.TraceFormulaMatrixModule.periodAction` of `ξ` on period polynomials
(`TauCeti.TraceFormulaMatrixModule.periodAction_binaryFormDual`).

Popa and Zagier's Proposition 2 says that every solution `ξ` of the period relation (A)
`(1 - S)·ξ - Tₙ^∞·(1 - S) ∈ (1 - T)·ℛₙ` acts on period polynomials as the classical Hecke
operator `Tₙ`.
On modular symbols this is the identity

`∑ c_M {∞, 0} ⊗ (P ∣ adj M) = ∑_{(a b; 0 d) ∈ ℳₙ^∞} {∞, b/d} ⊗ (P ∣ adj (a b; 0 d))`

(`TauCeti.TraceFormulaMatrixModule.PeriodRelation.symbolAction_eq`). Its right-hand side
`TauCeti.TraceFormulaMatrixModule.upperTriangularSymbol` is `∑ {a∞, a0} ⊗ (P ∣ adj a)`, the sum
of the translates of `{∞, 0} ⊗ P` by the upper-triangular representatives `a = (a b; 0 d)` of
`Γ \ ℳₙ`; for `n > 0` these are the matrices with `ad = n`, `a > 0` and `0 ≤ b < d`. For `n > 0`
this is the classical Hecke operator `Tₙ` applied to `{∞, 0} ⊗ P`, which runs over all
determinant-`n` double cosets `Γ diag(a, d) Γ` with `a ∣ d`. Identifying it with the sum of the
double-coset operators `TauCeti.ModularSymbols.heckeSymbol` over these cosets is not proved here;
for non-squarefree `n` this sum has more terms than the single double coset `Γ diag(1, n) Γ` of
`TauCeti.ModularSymbols.heckeTSymbol`.

The proof applies to the relation (A) the linear map `M ↦ {∞, M0} ⊗ (P ∣ adj M)`. Left
multiplication by `g ∈ SL(2, ℤ)` replaces its value by `{g⁻¹∞, M0} ⊗ (P ∣ adj M)`. For `g = T`
nothing changes, so the map kills `(1 - T)·ℛₙ`; for `g = S` the value drops by
`{∞, 0} ⊗ (P ∣ adj M)`, so the map sends `(1 - S)·ξ` to the action of `ξ`. It sends `Tₙ^∞` to
the right-hand side above and kills `Tₙ^∞·S`, since `(a S)0 = a∞ = ∞` for upper-triangular `a`.

The period map of a level-one cusp form `f` is a functional on `𝕄_w(SL(2, ℤ); ℂ)`, and the binary
form attached to its restriction to the symbols `{∞, 0} ⊗ P` is the period polynomial `r_f`. So
`TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_binaryFormDual` expresses the
action of `ξ` on `r_f` through the periods of `f` on the symbols `∑ {a∞, a0} ⊗ (P ∣ adj a)`.
The substitution `z ↦ a z` turns these into the periods of the slashes `f ∣[k] a` on `{∞, 0}`,
whose sum is the classical Hecke transform `Tₙ f = TauCeti.heckeTCuspLevelOne k n f`.
Hence `r_f ∣ ξ = r_{Tₙ f}` for every `n ≥ 1`
(`TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_periodPolynomial`).

## Main definitions

* `TauCeti.TraceFormulaMatrixModule.symbolAction hw`: the action
  `ξ ↦ (P ↦ ∑ c_M {∞, 0} ⊗ (P ∣ adj M))` of `ℛₙ` on level-one modular symbols.
* `TauCeti.TraceFormulaMatrixModule.upperTriangularSymbol R n w`: the map
  `P ↦ ∑_{(a b; 0 d) ∈ ℳₙ^∞} {∞, b/d} ⊗ (P ∣ adj (a b; 0 d))`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.upperTriangularSymbol_eq_sum_toGL_smul`: for `n ≠ 0`,
  `upperTriangularSymbol` is `P ↦ ∑ {a∞, a0} ⊗ (P ∣ adj a)`.
* `TauCeti.TraceFormulaMatrixModule.periodAction_binaryFormDual`: the substitution action of
  `ξ` on the binary form attached to `φ ∘ {∞, 0}` is the binary form attached to
  `φ ∘ symbolAction ξ`.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.symbolAction_eq`: for `n ≠ 0`, a solution of
  the period relation (A) acts on `{∞, 0}` as `upperTriangularSymbol`, the sum over `ℳₙ^∞`.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_binaryFormDual`: the same
  statement for the action on binary forms attached to functionals on modular symbols, such as
  period polynomials.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_periodPolynomial`: for `n ≥ 1`,
  a solution `ξ` of the period relation (A) acts on period polynomials of level-one cusp forms as
  the Hecke operator `Tₙ`: `r_f ∣ ξ = r_{Tₙ f}`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §2, Proposition 2.
* Y. J. Choie and D. Zagier, *Rational period functions for PSL(2, ℤ)*,
  Contemp. Math. **143** (1993), 89–108.
-/

public section

open Matrix MonoidAlgebra MulOpposite MvPolynomial ModularGroup OnePoint Representation
open TauCeti.ModularSymbols
open FixedDetMatrices (toGL toGL_smul)
open Matrix.SpecialLinearGroup (mapGL)
open scoped MatrixGroups ModularForm RightActions

namespace TauCeti.TraceFormulaMatrixModule

variable {R : Type*} [CommRing R] {n : ℤ} {w : ℕ}

/-! ### The action of `ℛₙ` on the Manin symbol `{∞, 0}` -/

/-- **The action of `ℛₙ` on the Manin symbol `{∞, 0}`.** An element `ξ = ∑ c_M M` of
`R[ℳₙ]` sends a binary form `P` of even degree `w` to `∑ c_M {∞, 0} ⊗ (P ∣ adj M)` in the
level-one modular symbols. Under the duality between binary forms and functionals it is the
transpose of the substitution action `TauCeti.TraceFormulaMatrixModule.periodAction`
(`TauCeti.TraceFormulaMatrixModule.periodAction_binaryFormDual`). -/
noncomputable def symbolAction (hw : Even w) :
    R[TraceFormulaMatrixModule n] →ₗ[R]
      homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R ⊤ w :=
  linearLift (fun A ↦ symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ) ∘ₗ binaryFormAdjugateRep R w A.1)
    fun A ↦ by rw [TraceFormulaMatrix.val_neg, binaryFormAdjugateRep_neg_of_even hw]

/-- A basis element `c • [M]` acts by `P ↦ c • {∞, 0} ⊗ (P ∣ adj M)`. -/
@[simp]
theorem symbolAction_single (hw : Even w) (A : TraceFormulaMatrix n) (c : R) :
    symbolAction hw (single (mk A) c) =
      c • (symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ) ∘ₗ binaryFormAdjugateRep R w A.1) := by
  rw [symbolAction, linearLift_single]

/-- **The action on modular symbols is the transpose of the action on binary forms.** For a
functional `φ` on the level-one modular symbols, the substitution action of `ξ` on the binary
form attached to `P ↦ φ ({∞, 0} ⊗ P)` is the binary form attached to `φ ∘ symbolAction ξ`. For
`φ` the period map of a cusp form `f`, the former binary form is the period polynomial `r_f`. -/
theorem periodAction_binaryFormDual (hw : Even w) (ξ : R[TraceFormulaMatrixModule n])
    (φ : ModularSymbols R ⊤ w →ₗ[R] R) :
    periodAction hw ξ (binaryFormDual R w (φ ∘ₗ symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ))) =
      binaryFormDual R w (φ ∘ₗ symbolAction hw ξ) := by
  induction ξ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add ξ η hξ hη => simp only [map_add, LinearMap.add_apply, hξ, hη, LinearMap.comp_add]
  | single x c =>
    induction x using TraceFormulaMatrixModule.induction with | h A => ?_
    rw [periodAction_single, symbolAction_single, binaryFormAction_mk, LinearMap.smul_apply,
      binaryFormRep_binaryFormDual, LinearMap.comp_smul, _root_.map_smul, LinearMap.comp_assoc]

/-! ### The sum over the upper-triangular representatives -/

variable (R n w) in
/-- **The sum over the upper-triangular representatives** of `Γ \ ℳₙ`: the map sending a binary
form `P` to `∑ {∞, b/d} ⊗ (P ∣ adj (a b; 0 d))`, the sum over `FixedDetMatrices.reps n`. Each
summand is the translate `{a∞, a0} ⊗ (P ∣ adj a)` of `{∞, 0} ⊗ P` by `a = (a b; 0 d)`. For `n > 0`
this is the classical Hecke operator `Tₙ`, over all determinant-`n` double cosets, applied to
`{∞, 0} ⊗ P`; its identification with `TauCeti.ModularSymbols.heckeSymbol` is not proved here. -/
noncomputable def upperTriangularSymbol :
    homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R ⊤ w :=
  ∑ A : FixedDetMatrices.reps n,
    symbol ⊤ ∞ (((A.1.1 0 1 : ℚ) / A.1.1 1 1 : ℚ) : OnePoint ℚ) ∘ₗ binaryFormAdjugateRep R w A.1.1

/-- The value of `upperTriangularSymbol R n w` at `P` is
`∑ {∞, b/d} ⊗ (P ∣ adj (a b; 0 d))`. -/
theorem upperTriangularSymbol_apply (P : homogeneousSubmodule (Fin 2) R w) :
    upperTriangularSymbol R n w P =
      ∑ A : FixedDetMatrices.reps n,
        symbol ⊤ ∞ (((A.1.1 0 1 : ℚ) / A.1.1 1 1 : ℚ) : OnePoint ℚ)
          (binaryFormAdjugateRep R w A.1.1 P) := by
  simp [upperTriangularSymbol]

/-! ### The auxiliary map `M ↦ {∞, M0} ⊗ (P ∣ adj M)` -/

/-- The image of the cusp `0` under a determinant-`n` matrix `(a b; c d)` is `b / d`, or `∞`
when `d = 0`. -/
private theorem toGL_smul_zero (hn : n ≠ 0) (A : TraceFormulaMatrix n) :
    toGL hn A • ((0 : ℚ) : OnePoint ℚ) =
      if A.1 1 1 = 0 then ∞ else (((A.1 0 1 : ℚ) / A.1 1 1 : ℚ) : OnePoint ℚ) := by
  rw [OnePoint.smul_some_eq_ite]
  simp

/-- **The sum over `ℳₙ^∞` as a sum of translates.** For `n ≠ 0`, `upperTriangularSymbol R n w`
sends `P` to `∑ {a∞, a0} ⊗ (P ∣ adj a)`, the sum over the upper-triangular representatives `a`
of `Γ \ ℳₙ` acting on the cusps through `FixedDetMatrices.toGL`. -/
theorem upperTriangularSymbol_eq_sum_toGL_smul (hn : n ≠ 0) :
    upperTriangularSymbol R n w = ∑ A : FixedDetMatrices.reps n,
      symbol ⊤ (toGL hn A.1 • ∞) (toGL hn A.1 • ((0 : ℚ) : OnePoint ℚ)) ∘ₗ
        binaryFormAdjugateRep R w A.1.1 := by
  rw [upperTriangularSymbol]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  -- `|b| < |d|` forces `d ≠ 0`, and `c = 0` means that `a` fixes `∞`
  have hd : A.1.1 1 1 ≠ 0 := abs_pos.mp ((abs_nonneg _).trans_lt A.2.2.2.2)
  rw [toGL_smul_zero, OnePoint.smul_infty_eq_self_iff.2 (by simp [A.2.1])]
  simp only [hd, ↓reduceIte]

/-- The symbol `{∞, M0} ⊗ (P ∣ adj M)` of a representative `M`, as a linear map in `P`. -/
private noncomputable def cuspSymbol (hn : n ≠ 0) (A : TraceFormulaMatrix n) :
    homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R ⊤ w :=
  symbol ⊤ ∞ (toGL hn A • ((0 : ℚ) : OnePoint ℚ)) ∘ₗ binaryFormAdjugateRep R w A.1

/-- The symbol `{∞, M0} ⊗ (P ∣ adj M)` depends only on the class of `M` modulo sign. -/
private theorem cuspSymbol_neg (hn : n ≠ 0) (hw : Even w) (A : TraceFormulaMatrix n) :
    cuspSymbol (R := R) (w := w) hn (-A) = cuspSymbol hn A := by
  rw [cuspSymbol, cuspSymbol, TraceFormulaMatrix.val_neg, binaryFormAdjugateRep_neg_of_even hw,
    toGL_smul_zero, toGL_smul_zero]
  simp [neg_div_neg_eq]

/-- **Left multiplication changes the symbol by a symbol from `g⁻¹∞` to `∞`**:
`{∞, gM0} ⊗ (P ∣ adj (gM)) = {g⁻¹∞, M0} ⊗ (P ∣ adj M)`. -/
private theorem cuspSymbol_smul (hn : n ≠ 0) (g : SL(2, ℤ)) (A : TraceFormulaMatrix n) :
    cuspSymbol (R := R) (w := w) hn (g • A) =
      symbol ⊤ (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹ • ∞) (toGL hn A • ((0 : ℚ) : OnePoint ℚ)) ∘ₗ
        binaryFormAdjugateRep R w A.1 := by
  have hinf : (∞ : OnePoint ℚ) =
      Matrix.SpecialLinearGroup.mapGL ℚ g • Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹ • ∞ := by
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  ext P
  rw [cuspSymbol, LinearMap.comp_apply, LinearMap.comp_apply, toGL_smul, mul_smul,
    FixedDetMatrices.smul_coe, map_mul, Module.End.mul_apply, binaryFormAdjugateRep_coe]
  nth_rw 1 [hinf]
  rw [symbol_mapGL_smul ⊤ (Subgroup.mem_top g), binaryFormRep_binaryFormSLRep]

/-- The linear extension of `M ↦ {∞, M0} ⊗ (P ∣ adj M)` to `R[ℳₙ]`. -/
private noncomputable def cuspSymbolAction (hn : n ≠ 0) (hw : Even w) :
    R[TraceFormulaMatrixModule n] →ₗ[R]
      homogeneousSubmodule (Fin 2) R w →ₗ[R] ModularSymbols R ⊤ w :=
  linearLift (cuspSymbol hn) (cuspSymbol_neg hn hw)

private theorem cuspSymbolAction_single (hn : n ≠ 0) (hw : Even w) (A : TraceFormulaMatrix n)
    (c : R) : cuspSymbolAction hn hw (single (mk A) c) = c • cuspSymbol (w := w) hn A :=
  linearLift_single _ _ A c

/-- The auxiliary map kills `(1 - T)·ℛₙ`: left multiplication by `T` does not change it. -/
private theorem cuspSymbolAction_ofMulAction_T (hn : n ≠ 0) (hw : Even w)
    (ζ : R[TraceFormulaMatrixModule n]) :
    cuspSymbolAction hn hw (ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) T ζ) =
      cuspSymbolAction (w := w) hn hw ζ := by
  induction ζ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add ξ η hξ hη => simp only [map_add, hξ, hη]
  | single x c =>
    induction x using TraceFormulaMatrixModule.induction with | h A => ?_
    rw [ofMulAction_single, smul_mk, cuspSymbolAction_single, cuspSymbolAction_single,
      cuspSymbol_smul, map_inv, inv_smul_eq_iff.2 mapGL_T_smul_infty.symm, cuspSymbol]

/-- The auxiliary map sends `(1 - S)·ξ` to the action of `ξ` on `{∞, 0}`. -/
private theorem cuspSymbolAction_sub_ofMulAction_S (hn : n ≠ 0) (hw : Even w)
    (ξ : R[TraceFormulaMatrixModule n]) :
    cuspSymbolAction hn hw ξ -
        cuspSymbolAction hn hw (ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) S ξ) =
      symbolAction (R := R) (w := w) hw ξ := by
  induction ξ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add ξ η hξ hη => rw [map_add, map_add, map_add, map_add, ← hξ, ← hη]; abel
  | single x c =>
    induction x using TraceFormulaMatrixModule.induction with | h A => ?_
    rw [ofMulAction_single, smul_mk, cuspSymbolAction_single, cuspSymbolAction_single,
      cuspSymbol_smul, map_inv, inv_smul_eq_iff.2 mapGL_S_smul_zero.symm, symbolAction_single,
      cuspSymbol, ← smul_sub, ← LinearMap.sub_comp,
      ← symbol_add_symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ), add_sub_cancel_right]

/-- The auxiliary map sends `Tₙ^∞` to `upperTriangularSymbol`, the sum over `ℳₙ^∞`. -/
private theorem cuspSymbolAction_upperTriangularSum (hn : n ≠ 0) (hw : Even w) :
    cuspSymbolAction hn hw (upperTriangularSum R n) = upperTriangularSymbol R n w := by
  rw [upperTriangularSum_eq_sum_reps, map_sum, upperTriangularSymbol]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  -- `|b| < |d|` forces `d ≠ 0`
  have hd : A.1.1 1 1 ≠ 0 := abs_pos.mp ((abs_nonneg _).trans_lt A.2.2.2.2)
  rw [cuspSymbolAction_single, one_smul, cuspSymbol, toGL_smul_zero]
  simp only [hd, ↓reduceIte]

/-- The auxiliary map kills `Tₙ^∞·S`: for `a ∈ ℳₙ^∞` upper-triangular, `(a S)0 = a∞ = ∞`. -/
private theorem cuspSymbolAction_ofMulAction_op_S_upperTriangularSum (hn : n ≠ 0)
    (hw : Even w) :
    cuspSymbolAction (w := w) hn hw
        (ofMulAction R PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n) (op (S : PSL(2, ℤ)))
          (upperTriangularSum R n)) = 0 := by
  rw [upperTriangularSum_eq_sum_reps, map_sum, map_sum]
  refine Finset.sum_eq_zero fun A _ ↦ ?_
  -- the lower-right entry of `a S` is minus the lower-left entry of `a`, which vanishes
  have hd : (traceFormulaMatrixRight S⁻¹ A.1).1 1 1 = 0 := by
    simp [A.2.1, coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ofMulAction_single, op_smul_mk, cuspSymbolAction_single, one_smul, cuspSymbol,
    toGL_smul_zero]
  simp only [hd, ↓reduceIte, symbol_self, LinearMap.zero_comp]

/-! ### Popa–Zagier's Proposition 2 on modular symbols -/

/-- **Popa–Zagier, Proposition 2, on modular symbols.** For `n ≠ 0`, every solution
`ξ = ∑ c_M M` of the period relation (A) satisfies

`∑ c_M {∞, 0} ⊗ (P ∣ adj M) = ∑_{(a b; 0 d)} {∞, b/d} ⊗ (P ∣ adj (a b; 0 d))`,

the sum `upperTriangularSymbol R n w` on the right running over the upper-triangular
representatives `FixedDetMatrices.reps n` of `Γ \ ℳₙ`, on which `(a b; 0 d)` sends `∞` to `∞` and
`0` to `b/d`. -/
theorem PeriodRelation.symbolAction_eq (hn : n ≠ 0) (hw : Even w)
    {ξ : R[TraceFormulaMatrixModule n]} (h : PeriodRelation R n ξ) :
    symbolAction hw ξ = upperTriangularSymbol R n w := by
  obtain ⟨ζ, hζ⟩ := periodRelation_iff.1 h
  have hΞ := congrArg (cuspSymbolAction (w := w) hn hw) hζ
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub,
    cuspSymbolAction_ofMulAction_T, sub_self,
    cuspSymbolAction_ofMulAction_op_S_upperTriangularSum, sub_zero] at hΞ
  rw [← cuspSymbolAction_sub_ofMulAction_S hn hw, ← cuspSymbolAction_upperTriangularSum hn hw,
    ← sub_eq_zero, ← hΞ]

/-- **Popa–Zagier, Proposition 2.** Let `n ≠ 0`, let `ξ` be a solution of the period relation
(A), and let `φ` be a functional on the level-one modular symbols. The substitution action of `ξ`
on the binary form attached to `P ↦ φ ({∞, 0} ⊗ P)` is the binary form attached to
`φ ∘ upperTriangularSymbol R n w`, that is, to `P ↦ φ (∑ {∞, b/d} ⊗ (P ∣ adj (a b; 0 d)))`, the
sum over the upper-triangular representatives `(a b; 0 d)` of `Γ \ ℳₙ`. For `φ` the period map of
a level-one cusp form `f`, the former binary form is the period polynomial `r_f`. -/
theorem PeriodRelation.periodAction_binaryFormDual (hn : n ≠ 0) (hw : Even w)
    {ξ : R[TraceFormulaMatrixModule n]} (h : PeriodRelation R n ξ)
    (φ : ModularSymbols R ⊤ w →ₗ[R] R) :
    periodAction hw ξ (binaryFormDual R w (φ ∘ₗ symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ))) =
      binaryFormDual R w (φ ∘ₗ upperTriangularSymbol R n w) := by
  rw [TraceFormulaMatrixModule.periodAction_binaryFormDual, h.symbolAction_eq hn hw]

/-! ### Popa–Zagier's Proposition 2 on period polynomials of cusp forms -/

/-- **The periods of `Tₙ f` on `{∞, 0}`.** For a level-one cusp form `f` of weight `w + 2`, the
period of `Tₙ f` on `{∞, 0} ⊗ P` is the period of `f` on `∑ {a∞, a0} ⊗ (P ∣ adj a)`, the sum over
the upper-triangular representatives `a` of `Γ \ ℳₙ`: the substitution `z ↦ a z` in each summand
of `∫₀^{i∞} (Tₙ f)(z) P(z, 1) dz`. Here `F` and `G` are `f` and `Tₙ f` viewed as cusp forms for
the image of `⊤ : Subgroup SL(2, ℤ)`, the group of the period map. -/
private theorem periodMap_symbol_heckeTCuspLevelOne {k : ℤ} (hk : k = w + 2) (n : ℕ) [NeZero n]
    (f : CuspForm 𝒮ℒ k) {F G : CuspForm ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) k}
    (hF : ⇑F = ⇑f) (hG : ⇑G = ⇑(heckeTCuspLevelOne k n f))
    (P : homogeneousSubmodule (Fin 2) ℂ w) :
    periodMap ℂ ⊤ hk G (symbol ⊤ ∞ ((0 : ℚ) : OnePoint ℚ) P) =
      periodMap ℂ ⊤ hk F (upperTriangularSymbol ℂ n w P) := by
  have hn : ((n : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.2 (NeZero.ne n)
  have hpos (A : FixedDetMatrices.reps (n : ℤ)) :
      0 < ((toGL hn A.1 : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [FixedDetMatrices.det_toGL]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hA (A : FixedDetMatrices.reps (n : ℤ)) := FixedDetMatrices.coe_toGL hn A.1
  -- the period of `Tₙ f` is the sum of the periods of the slashes `f ∣[k] a` along `{∞, 0}`; the
  -- summands are integrable there, being periods of `f` along the geodesics moved by `a`
  have hsum := cuspIntegral_sum (g := 1) Finset.univ (one_pos.trans_eq Matrix.det_one.symm)
    (F := fun A : FixedDetMatrices.reps (n : ℤ) ↦ periodIntegrand (⇑f ∣[k] toGL hn A.1) P)
    fun A _ ↦ by
      rw [SlashAction.slash_one, ← periodIntegrand_adjugate_slash hk f P (hA A) (hpos A)]
      exact integrableOn_resToImagAxis_periodIntegrand_slash f hk _ (hpos A)
  simp only [one_smul] at hsum
  rw [periodMap_symbol, hG, coe_heckeTCuspLevelOne, heckeSlashLevelOne_def,
    periodIntegrand_sum_left, hsum, upperTriangularSymbol_eq_sum_toGL_smul hn,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  -- each summand is the substitution `z ↦ a z`
  rw [LinearMap.comp_apply, periodMap_symbol, hF, binaryFormAdjugateRep_apply,
    cuspIntegral_periodIntegrand_slash hk f P (hA A) (hpos A)]

/-- **Popa–Zagier, Proposition 2, on period polynomials.** Let `n ≥ 1` and let `ξ` be a solution
of the period relation (A). For every level-one cusp form `f` of weight `w + 2`, the action of `ξ`
on the period polynomial of `f` is the period polynomial of the Hecke transform:

`r_f ∣ ξ = r_{Tₙ f}`,

with `Tₙ = TauCeti.heckeTCuspLevelOne (w + 2) n` the classical Hecke operator, the sum
over all of `SL(2, ℤ) \ ℳₙ`. -/
theorem PeriodRelation.periodAction_periodPolynomial {k : ℤ} (hk : k = w + 2) (hw : Even w)
    (n : ℕ) [NeZero n] {ξ : ℂ[TraceFormulaMatrixModule n]} (h : PeriodRelation ℂ n ξ)
    (f : CuspForm 𝒮ℒ k) :
    periodAction hw ξ (periodPolynomial hk f : homogeneousSubmodule (Fin 2) ℂ w) =
      periodPolynomial hk (heckeTCuspLevelOne k n f) := by
  have hΓ : (⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ) = 𝒮ℒ := (MonoidHom.range_eq_map _).symm
  rw [coe_periodPolynomial_eq_binaryFormDual hk f (F := CuspForm.mcast rfl f hΓ) (rfl),
    coe_periodPolynomial_eq_binaryFormDual hk _
      (F := CuspForm.mcast rfl (heckeTCuspLevelOne k n f) hΓ) (rfl),
    h.periodAction_binaryFormDual (Int.natCast_ne_zero.2 (NeZero.ne n)) hw]
  congr 1
  exact LinearMap.ext fun P ↦
    (periodMap_symbol_heckeTCuspLevelOne hk n f (rfl) (rfl) P).symm

end TauCeti.TraceFormulaMatrixModule
