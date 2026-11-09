/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.HeckeSymbol

/-!
# The parity symmetry of the period relation and Hecke equivariance of `r_f^±`

Let `ε = !![-1, 0; 0, 1]`. Conjugation `A ↦ ε A ε` sends a determinant-`n` matrix `(a b; c d)` to
`(a -b; -c d)`, again of determinant `n`, and descends to an involution of the projective matrix
module `ℳₙ`. It normalizes the data of Popa and Zagier's period relation

`(A)  (1 - S)·ξ - Tₙ^∞·(1 - S) ∈ (1 - T)·ℛₙ`:

`ε S ε = -S` acts on `ℳₙ` as `S`, on the left and on the right; `ε T ε = T⁻¹`, so the ideal
`(1 - T)·ℛₙ` is preserved; and each upper-triangular representative `(a b; 0 d)` of `Γ \ ℳₙ` goes
to `(a -b; 0 d)`, which lies in the `⟨T⟩`-orbit of another representative, so the conjugate of
`Tₙ^∞` has the same `⟨T⟩`-orbit sums as `Tₙ^∞`. Hence the conjugate of a solution of (A) is again
a solution.

The conjugate of `ξ` acts on binary forms by `P ↦ ((P ∣ ε) ∣ ξ) ∣ ε`. Every solution of (A) acts
on the period polynomials of level-one cusp forms as the Hecke operator `Tₙ` (Popa–Zagier,
Proposition 2). Applying this to `ξ` and to its conjugate shows that the action of `ξ` commutes
with the parity involution `P(X, Y) ↦ P(-X, Y)` on period polynomials of cusp forms:
`(r_f ∣ ε) ∣ ξ = r_{Tₙ f} ∣ ε`. Consequently the even and odd period polynomials are
Hecke-equivariant, `r_f^± ∣ ξ = r_{Tₙ f}^±`: the maps `f ↦ r_f^±` from `S_k(SL(2, ℤ))` to `W_w^±`
intertwine `Tₙ` with the action of any solution of (A), such as Popa and Zagier's explicit
element.

## Main definitions

* `TauCeti.TraceFormulaMatrix.parityConj`: the conjugate `ε A ε` of a determinant-`n` matrix.
* `TauCeti.TraceFormulaMatrixModule.parityConj`: the induced involution of `ℳₙ`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.mapDomainLinearMap_parityConj_upperTriangularSum_sub_mem`:
  the conjugate of `Tₙ^∞` is congruent to `Tₙ^∞` modulo `(1 - T)·ℛₙ`.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.mapDomainLinearMap_parityConj`: the conjugate
  of a solution of the period relation (A) is a solution.
* `TauCeti.TraceFormulaMatrixModule.periodAction_mapDomainLinearMap_parityConj`: the conjugate
  of `ξ` acts on binary forms by `P ↦ ((P ∣ ε) ∣ ξ) ∣ ε`.
* `TraceFormulaMatrixModule.PeriodRelation.periodAction_binaryFormRep_parity_periodPolynomial`:
  `(r_f ∣ ε) ∣ ξ = r_{Tₙ f} ∣ ε` for every solution `ξ` of (A).
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_evenPeriodPolynomial` and
  `TauCeti.TraceFormulaMatrixModule.PeriodRelation.periodAction_oddPeriodPolynomial`:
  `r_f^± ∣ ξ = r_{Tₙ f}^±`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §§1–2. The period relation (A)
  is stated in §1 and Proposition 2 is in §2.
-/

public section

open Matrix MonoidAlgebra MulOpposite MvPolynomial Representation ModularGroup
open scoped MatrixGroups RightActions

namespace TauCeti

variable {n : ℤ}

/-- The conjugate `ε A ε` of a determinant-`n` matrix `A = (a b; c d)` by the parity matrix
`ε = !![-1, 0; 0, 1]`: the matrix `(a -b; -c d)`, again of determinant `n`. -/
def TraceFormulaMatrix.parityConj (A : TraceFormulaMatrix n) : TraceFormulaMatrix n :=
  ⟨!![-1, 0; 0, 1] * A.1 * !![-1, 0; 0, 1], by rw [det_mul, det_mul, A.2, det_fin_two_of]; ring⟩

/-- The underlying matrix of `TraceFormulaMatrix.parityConj A` is `ε A ε`. -/
@[simp]
theorem TraceFormulaMatrix.val_parityConj (A : TraceFormulaMatrix n) :
    (TraceFormulaMatrix.parityConj A).1 = !![-1, 0; 0, 1] * A.1 * !![-1, 0; 0, 1] := (rfl)

/-- Conjugation by the parity matrix commutes with negation. -/
@[simp]
theorem TraceFormulaMatrix.parityConj_neg (A : TraceFormulaMatrix n) :
    TraceFormulaMatrix.parityConj (-A) = -TraceFormulaMatrix.parityConj A :=
  FixedDetMatrices.ext' _ _ <| by
    simp only [val_parityConj, val_neg, Matrix.mul_neg, Matrix.neg_mul]

namespace TraceFormulaMatrixModule

/-- The involution of the projective matrix module `ℳₙ` induced by conjugation `A ↦ ε A ε` by the
parity matrix `ε = !![-1, 0; 0, 1]`. -/
def parityConj (x : TraceFormulaMatrixModule n) : TraceFormulaMatrixModule n :=
  Quotient.lift (fun A ↦ mk (TraceFormulaMatrix.parityConj A)) (fun A B h ↦ by
    rcases h with rfl | rfl
    · rfl
    · rw [TraceFormulaMatrix.parityConj_neg, mk_neg]) x

/-- On a representative, the involution of `ℳₙ` is conjugation by the parity matrix. -/
@[simp]
theorem parityConj_mk (A : TraceFormulaMatrix n) :
    parityConj (mk A) = mk (TraceFormulaMatrix.parityConj A) := by
  rw [parityConj, lift_mk]

/-- Conjugation by the parity matrix is an involution of `ℳₙ`. -/
@[simp]
theorem parityConj_parityConj (x : TraceFormulaMatrixModule n) : parityConj (parityConj x) = x := by
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  rw [parityConj_mk, parityConj_mk]
  congr 1
  refine FixedDetMatrices.ext' _ _ ?_
  simp only [TraceFormulaMatrix.val_parityConj, Matrix.mul_assoc, parity_mul_parity,
    Matrix.mul_one]
  rw [← Matrix.mul_assoc, parity_mul_parity, Matrix.one_mul]

/-- Conjugation by the parity matrix is an involution of `ℳₙ`. -/
theorem parityConj_involutive : Function.Involutive (parityConj (n := n)) :=
  parityConj_parityConj

/-- `ε S ε = -S`, so conjugation by the parity matrix commutes with left multiplication by `S`. -/
@[simp]
theorem parityConj_S_smul (x : TraceFormulaMatrixModule n) :
    parityConj (S • x) = S • parityConj x := by
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  rw [smul_mk, parityConj_mk, parityConj_mk, smul_mk, mk_eq_iff]
  refine Or.inr <| FixedDetMatrices.ext' _ _ ?_
  simp only [TraceFormulaMatrix.val_parityConj, TraceFormulaMatrix.val_neg,
    FixedDetMatrices.smul_coe, ← Matrix.mul_assoc, parity_mul_S, Matrix.neg_mul]

/-- `ε T^m ε = T^(-m)`, so conjugation by the parity matrix turns left multiplication by `T ^ m`
into left multiplication by `T ^ (-m)`. -/
@[simp]
theorem parityConj_T_zpow_smul (m : ℤ) (x : TraceFormulaMatrixModule n) :
    parityConj (T ^ m • x) = T ^ (-m) • parityConj x := by
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  rw [smul_mk, parityConj_mk, parityConj_mk, smul_mk]
  congr 1
  refine FixedDetMatrices.ext' _ _ ?_
  simp only [TraceFormulaMatrix.val_parityConj, FixedDetMatrices.smul_coe, ← Matrix.mul_assoc,
    parity_mul_T_zpow]

/-- `ε T ε = T⁻¹`, so conjugation by the parity matrix turns left multiplication by `T` into left
multiplication by `T⁻¹`. -/
@[simp]
theorem parityConj_T_smul (x : TraceFormulaMatrixModule n) :
    parityConj (T • x) = T⁻¹ • parityConj x := by
  simpa using parityConj_T_zpow_smul 1 x

/-- `ε S ε = -S`, so conjugation by the parity matrix commutes with right multiplication by `S`. -/
@[simp]
theorem parityConj_op_S_smul (x : TraceFormulaMatrixModule n) :
    parityConj (x <• (S : PSL(2, ℤ))) = parityConj x <• (S : PSL(2, ℤ)) := by
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  rw [op_smul_mk, parityConj_mk, parityConj_mk, op_smul_mk, mk_eq_iff]
  refine Or.inr <| FixedDetMatrices.ext' _ _ ?_
  -- `ε A S ε = -(ε A ε S)`, by `S ε = -(ε S)`
  have hSε : (S : Matrix (Fin 2) (Fin 2) ℤ) * !![-1, 0; 0, 1] =
      -(!![-1, 0; 0, 1] * (S : Matrix (Fin 2) (Fin 2) ℤ)) := by
    rw [parity_mul_S, neg_neg]
  simp only [TraceFormulaMatrix.val_parityConj, TraceFormulaMatrix.val_neg,
    val_traceFormulaMatrixRight, inv_inv, Matrix.mul_assoc, hSε, Matrix.mul_neg]

/-! ### The conjugate of `Tₙ^∞` -/

/-- Conjugation by the parity matrix sends an element of `ℳₙ^∞` to the `⟨T⟩`-orbit of an element
of `ℳₙ^∞`: it keeps matrices upper-triangular. -/
private theorem exists_T_zpow_smul_parityConj_mem_upperTriangularReps
    {x : TraceFormulaMatrixModule n} (hx : x ∈ upperTriangularReps n) :
    ∃ m : ℤ, T ^ m • parityConj x ∈ upperTriangularReps n := by
  obtain ⟨A, hA, rfl⟩ := mem_upperTriangularReps.1 hx
  rw [parityConj_mk]
  exact exists_T_zpow_smul_mk_mem_upperTriangularReps (by rintro rfl; simp at hA)
    (by simp only [TraceFormulaMatrix.val_parityConj, Matrix.mul_apply, Fin.sum_univ_two]
        simp [hA.1])

variable {R : Type*} [CommRing R]

/-- **The conjugate of `Tₙ^∞` by the parity matrix is `Tₙ^∞` modulo `(1 - T)·ℛₙ`.** Conjugation
sends the representative `(a b; 0 d)` of `ℳₙ^∞` to `(a -b; 0 d)`, which lies in the `⟨T⟩`-orbit of
the representative `(a b'; 0 d)` with `b' ≡ -b mod d`. -/
theorem mapDomainLinearMap_parityConj_upperTriangularSum_sub_mem :
    mapDomainLinearMap R R parityConj (upperTriangularSum R n) - upperTriangularSum R n ∈
      LinearMap.range (1 - ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) T) := by
  rw [mem_range_one_sub_T_iff, map_sub, sub_eq_zero]
  choose! m hm using fun x (hx : x ∈ upperTriangularReps n) ↦
    exists_T_zpow_smul_parityConj_mem_upperTriangularReps hx
  -- `φ x = T ^ (m x) • ε x ε` is an involution of `ℳₙ^∞`, since `ℳₙ^∞` meets each `SL(2, ℤ)`-orbit
  -- at most once
  let φ (x : TraceFormulaMatrixModule n) := T ^ m x • parityConj x
  have inv (x) (hx : x ∈ upperTriangularReps n) : φ (φ x) = x := by
    have h := hm _ (hm x hx)
    simp only [φ, parityConj_T_zpow_smul, parityConj_parityConj, smul_smul] at h ⊢
    exact smul_eq_self_of_mem_upperTriangularReps hx h
  simp only [upperTriangularSum_def, map_sum, mapDomainLinearMap_single]
  refine Finset.sum_nbij' φ φ (by simpa using hm) (by simpa using hm) (by simpa using inv)
    (by simpa using inv) fun x _ ↦ ?_
  -- `ε x ε` and `φ x` lie in the same `⟨T⟩`-orbit
  congr 1
  exact Quotient.sound ⟨⟨T ^ (-m x), Subgroup.zpow_mem_zpowers T _⟩, by
    simp [φ, Subgroup.smul_def, smul_smul]⟩

/-- Pushing forward along the parity involution intertwines left multiplication by `g` and `g'`
on `R[ℳₙ]` when the involution intertwines them on `ℳₙ`. -/
private theorem mapDomainLinearMap_parityConj_comp_ofMulAction {G : Type*} [Monoid G]
    [MulAction G (TraceFormulaMatrixModule n)] {g g' : G}
    (h : ∀ x : TraceFormulaMatrixModule n, parityConj (g • x) = g' • parityConj x) :
    mapDomainLinearMap R R parityConj ∘ₗ ofMulAction R G (TraceFormulaMatrixModule n) g =
      ofMulAction R G (TraceFormulaMatrixModule n) g' ∘ₗ mapDomainLinearMap R R parityConj := by
  ext x : 2
  simp [h]

/-- Pushing forward along the parity involution preserves `(1 - T)·ℛₙ`: it sends `(1 - T)·ζ` to
`(1 - T⁻¹)·ζ' = (1 - T)·(-T⁻¹·ζ')`. -/
private theorem mapDomainLinearMap_parityConj_mem_range {y : R[TraceFormulaMatrixModule n]}
    (hy : y ∈ LinearMap.range (1 - ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) T)) :
    mapDomainLinearMap R R parityConj y ∈
      LinearMap.range (1 - ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) T) := by
  obtain ⟨z, rfl⟩ := hy
  have hT := LinearMap.congr_fun (mapDomainLinearMap_parityConj_comp_ofMulAction (R := R)
    (n := n) parityConj_T_smul) z
  have hTT : ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) T
      (ofMulAction R SL(2, ℤ) _ T⁻¹ (mapDomainLinearMap R R parityConj z)) =
        mapDomainLinearMap R R parityConj z := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hT
  refine ⟨-ofMulAction R SL(2, ℤ) _ T⁻¹ (mapDomainLinearMap R R parityConj z), ?_⟩
  simp only [LinearMap.sub_apply, one_apply_eq_self, map_sub, map_neg, hT, hTT]
  abel

/-- Right multiplication preserves `(1 - T)·ℛₙ`, since it commutes with left multiplication. -/
private theorem ofMulAction_op_mem_range (g : PSL(2, ℤ)) {y : R[TraceFormulaMatrixModule n]}
    (hy : y ∈ LinearMap.range (1 - ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) T)) :
    ofMulAction R PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n) (op g) y ∈
      LinearMap.range (1 - ofMulAction R SL(2, ℤ) (TraceFormulaMatrixModule n) T) := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨_, LinearMap.congr_fun ((Commute.one_left _).sub_left
    (commute_ofMulAction (k := R) (X := TraceFormulaMatrixModule n) T (op g))).eq z⟩

/-- **The parity conjugate of a solution of the period relation is a solution.** If `ξ` satisfies
Popa–Zagier's period relation (A), then so does its image under conjugation `M ↦ ε M ε` by
`ε = !![-1, 0; 0, 1]`. -/
theorem PeriodRelation.mapDomainLinearMap_parityConj {ξ : R[TraceFormulaMatrixModule n]}
    (h : PeriodRelation R n ξ) : PeriodRelation R n (mapDomainLinearMap R R parityConj ξ) := by
  have hS := LinearMap.congr_fun (mapDomainLinearMap_parityConj_comp_ofMulAction (R := R)
    (n := n) parityConj_S_smul)
  have hS' := LinearMap.congr_fun (mapDomainLinearMap_parityConj_comp_ofMulAction (R := R)
    (n := n) parityConj_op_S_smul)
  simp only [LinearMap.comp_apply] at hS hS'
  have hU := mapDomainLinearMap_parityConj_upperTriangularSum_sub_mem (R := R) (n := n)
  -- the conjugate of (A) for `ξ`, corrected by `(ι Tₙ^∞ - Tₙ^∞)·(1 - S) ∈ (1 - T)·ℛₙ`
  have key := add_mem (mapDomainLinearMap_parityConj_mem_range (periodRelation_iff.1 h))
    (_root_.sub_mem hU (ofMulAction_op_mem_range (S : PSL(2, ℤ)) hU))
  rw [periodRelation_iff]
  convert key using 1
  simp only [LinearMap.sub_apply, one_apply_eq_self, map_sub, hS, hS']
  abel

/-! ### The action on binary forms -/

variable {w : ℕ}

/-- **The parity conjugate acts by conjugating with the parity involution.** The image of `ξ`
under `M ↦ ε M ε` acts on binary forms of even degree by `P ↦ ((P ∣ ε) ∣ ξ) ∣ ε`. -/
theorem periodAction_mapDomainLinearMap_parityConj (hw : Even w)
    (ξ : R[TraceFormulaMatrixModule n]) :
    periodAction hw (mapDomainLinearMap R R parityConj ξ) =
      binaryFormRep R w (op !![-1, 0; 0, 1]) * periodAction hw ξ *
        binaryFormRep R w (op !![-1, 0; 0, 1]) := by
  induction ξ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add ξ η hξ hη => rw [map_add, map_add, hξ, hη, map_add, mul_add, add_mul]
  | single x c =>
    induction x using TraceFormulaMatrixModule.induction with | h A => ?_
    ext P : 1
    rw [mapDomainLinearMap_single, periodAction_single, periodAction_single, parityConj_mk,
      binaryFormAction_mk, binaryFormAction_mk, TraceFormulaMatrix.val_parityConj]
    simp only [LinearMap.smul_apply, mul_apply_eq_comp, binaryFormRep_op_mul_apply,
      _root_.map_smul]

/-! ### Hecke equivariance of the even and odd period polynomials -/

/-- **The Hecke action commutes with the parity involution on period polynomials.** Let `n ≥ 1`
and let `ξ` be a solution of the period relation (A). For every level-one cusp form `f` of weight
`w + 2`, `(r_f ∣ ε) ∣ ξ = r_{Tₙ f} ∣ ε`, where `ε = !![-1, 0; 0, 1]` acts by
`P(X, Y) ↦ P(-X, Y)` and `Tₙ = TauCeti.heckeTCuspLevelOne (w + 2) n`. -/
theorem PeriodRelation.periodAction_binaryFormRep_parity_periodPolynomial {k : ℤ}
    (hk : k = w + 2) (hw : Even w) (n : ℕ) [NeZero n] {ξ : ℂ[TraceFormulaMatrixModule n]}
    (h : PeriodRelation ℂ n ξ) (f : CuspForm 𝒮ℒ k) :
    periodAction hw ξ (binaryFormRep ℂ w (op !![-1, 0; 0, 1]) (periodPolynomial hk f)) =
      binaryFormRep ℂ w (op !![-1, 0; 0, 1]) (periodPolynomial hk (heckeTCuspLevelOne k n f)) := by
  have h' := h.mapDomainLinearMap_parityConj.periodAction_periodPolynomial hk hw n f
  rw [periodAction_mapDomainLinearMap_parityConj, mul_apply_eq_comp,
    mul_apply_eq_comp] at h'
  rw [← h', binaryFormRep_parity_involutive]

/-- **Hecke equivariance of the even period polynomial.** Let `n ≥ 1` and let `ξ` be a solution of
the period relation (A). For every level-one cusp form `f` of weight `w + 2`,
`r_f^+ ∣ ξ = r_{Tₙ f}^+`, with `Tₙ = TauCeti.heckeTCuspLevelOne (w + 2) n`. -/
theorem PeriodRelation.periodAction_evenPeriodPolynomial {k : ℤ} (hk : k = w + 2) (hw : Even w)
    (n : ℕ) [NeZero n] {ξ : ℂ[TraceFormulaMatrixModule n]} (h : PeriodRelation ℂ n ξ)
    (f : CuspForm 𝒮ℒ k) :
    periodAction hw ξ (evenPeriodPolynomial hk f : homogeneousSubmodule (Fin 2) ℂ w) =
      evenPeriodPolynomial hk (heckeTCuspLevelOne k n f) := by
  rw [coe_evenPeriodPolynomial, coe_evenPeriodPolynomial, map_smul, map_add,
    h.periodAction_periodPolynomial hk hw n f,
    h.periodAction_binaryFormRep_parity_periodPolynomial hk hw n f]

/-- **Hecke equivariance of the odd period polynomial.** Let `n ≥ 1` and let `ξ` be a solution of
the period relation (A). For every level-one cusp form `f` of weight `w + 2`,
`r_f^- ∣ ξ = r_{Tₙ f}^-`, with `Tₙ = TauCeti.heckeTCuspLevelOne (w + 2) n`. -/
theorem PeriodRelation.periodAction_oddPeriodPolynomial {k : ℤ} (hk : k = w + 2) (hw : Even w)
    (n : ℕ) [NeZero n] {ξ : ℂ[TraceFormulaMatrixModule n]} (h : PeriodRelation ℂ n ξ)
    (f : CuspForm 𝒮ℒ k) :
    periodAction hw ξ (oddPeriodPolynomial hk f : homogeneousSubmodule (Fin 2) ℂ w) =
      oddPeriodPolynomial hk (heckeTCuspLevelOne k n f) := by
  rw [coe_oddPeriodPolynomial, coe_oddPeriodPolynomial, map_smul, map_sub,
    h.periodAction_periodPolynomial hk hw n f,
    h.periodAction_binaryFormRep_parity_periodPolynomial hk hw n f]

end TraceFormulaMatrixModule

end TauCeti
