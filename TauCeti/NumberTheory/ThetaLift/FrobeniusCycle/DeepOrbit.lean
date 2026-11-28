/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Basic
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# Generic unipotent orbit of the shallow coordinate space

Treat the shallow variables of a Frobenius cycle as indeterminates and set the deep
variables to zero. The upper block unipotents carry this tuple to points with fixed shallow
coordinates and deep coordinates that are linear forms in the shallow variables. In
characteristic `p` the points are indexed by rectangular matrices over the residue field;
they are distinct, as one even letter recovers the entire matrix. The resulting count is
used when comparing the vanishing order at this orbit with weighted polynomial degree.

The orbit is the one used in `New.FrobeniusCycle.exists_le_weight_of_mem_deepForms` in
`grh/src/New/UpperBound/ElementaryDivisors/Depth.lean` of lsernau/grh-lean (commit `72fead1`).
-/

public section

open IsLocalRing Matrix MvPolynomial

namespace TauCeti.FrobeniusCycle

variable {W K : Type*} [CommRing W] [IsLocalRing W] [CommRing K] {N : ℕ}
    (T : FrobeniusCycle W K N)

/-- In characteristic `p`, a letter map factors through the residue field. -/
def residueLetterMap (hp : (T.p : K) = 0) (s : ZMod N) : ResidueField W →+* K :=
  Ideal.Quotient.lift _ (T.ι s) fun _ hy ↦ by
    simpa [hp] using T.dvd_ι_of_mem_maximalIdeal hy s

/-- On a representative, the residue letter map agrees with the original letter map. -/
@[simp] theorem residueLetterMap_residue (hp : (T.p : K) = 0) (s : ZMod N) (a : W) :
    T.residueLetterMap hp s (residue W a) = T.ι s a := (rfl)

/-- The consecutive residue letter maps differ by the `P`-th power. -/
theorem residueLetterMap_add_one (hp : (T.p : K) = 0) (s : ZMod N) (a : ResidueField W) :
    T.residueLetterMap hp (s + 1) a = T.residueLetterMap hp s a ^ T.P := by
  obtain ⟨y, rfl⟩ := residue_surjective a
  simpa [hp, T.P_def, sub_eq_zero] using T.dvd_ι_add_one_sub_pow s y

variable {k r : ℕ}

/-- The deep coordinates of the image of the generic shallow tuple under the unipotent with
upper-right block `A`. An even letter pairs a column of `A` with its shallow variables; an odd
letter pairs the negative of a row of `A` with its shallow variables. -/
noncomputable def deepUnipotentPoint (hp : (T.p : K) = 0)
    (A : Matrix {i : Fin k // (i : ℕ) < r} {j : Fin k // r ≤ (j : ℕ)} (ResidueField W))
    (x : {x : Fin k × ZMod N // T.IsDeep r x}) :
    MvPolynomial {x : Fin k × ZMod N // ¬ T.IsDeep r x} K :=
  if hs : T.isEven x.val.2 = true then
    ∑ i : {i : Fin k // (i : ℕ) < r},
      C (T.residueLetterMap hp x.val.2 (A i ⟨x.val.1, by
        simpa [hs] using x.property⟩)) * X ⟨(i.val, x.val.2), by simp [hs, i.property.not_ge]⟩
  else
    ∑ j : {j : Fin k // r ≤ (j : ℕ)},
      C (-T.residueLetterMap hp x.val.2 (A ⟨x.val.1, by
        simpa [hs] using x.property⟩ j)) * X ⟨(j.val, x.val.2), by simp [hs, j.property.not_gt]⟩

/-- The even-letter coordinate is the linear form from the corresponding column. -/
theorem deepUnipotentPoint_even (hp : (T.p : K) = 0)
    (A : Matrix {i : Fin k // (i : ℕ) < r} {j : Fin k // r ≤ (j : ℕ)} (ResidueField W))
    {s : ZMod N} (hs : T.isEven s = true) (j : {j : Fin k // r ≤ (j : ℕ)}) :
    T.deepUnipotentPoint hp A ⟨(j.val, s), by simp [hs, j.property]⟩ =
      ∑ i : {i : Fin k // (i : ℕ) < r}, C (T.residueLetterMap hp s (A i j)) *
        X ⟨(i.val, s), by simp [hs, i.property.not_ge]⟩ := by
  simp [deepUnipotentPoint, hs]

/-- The odd-letter coordinate is the linear form from the negative of the corresponding row. -/
theorem deepUnipotentPoint_odd (hp : (T.p : K) = 0)
    (A : Matrix {i : Fin k // (i : ℕ) < r} {j : Fin k // r ≤ (j : ℕ)} (ResidueField W))
    {s : ZMod N} (hs : T.isEven s = false) (i : {i : Fin k // (i : ℕ) < r}) :
    T.deepUnipotentPoint hp A ⟨(i.val, s), by simp [hs, i.property]⟩ =
      ∑ j : {j : Fin k // r ≤ (j : ℕ)}, C (-T.residueLetterMap hp s (A i j)) *
        X ⟨(j.val, s), by simp [hs, j.property.not_gt]⟩ := by
  simp [deepUnipotentPoint, hs]

/-- The coefficients at any even letter determine the entire unipotent block. -/
theorem deepUnipotentPoint_injective [Nontrivial K] (hp : (T.p : K) = 0) :
    Function.Injective (T.deepUnipotentPoint (k := k) (r := r) hp) := by
  classical
  have ⟨s, hs⟩ : ∃ s : ZMod N, T.isEven s = true := by
    cases h : T.isEven 0
    · exact ⟨0 + 1, (T.isEven_add_one 0).trans (by simp [h])⟩
    · exact ⟨0, h⟩
  intro A B h
  ext i j
  apply (T.residueLetterMap hp s).injective
  have hcoord := congrFun h ⟨(j.val, s), by simp [hs, j.property]⟩
  rw [T.deepUnipotentPoint_even hp A hs j, T.deepUnipotentPoint_even hp B hs j] at hcoord
  let u : {x : Fin k × ZMod N // ¬ T.IsDeep r x} :=
    ⟨(i.val, s), by simp [hs, i.property.not_ge]⟩
  have hiff (a : {i : Fin k // (i : ℕ) < r}) :
      (⟨(a.val, s), by simp [hs, a.property.not_ge]⟩ : {x // ¬ T.IsDeep r x}) = u ↔ a = i := by
    simp only [u, Prod.mk.injEq, and_true, Subtype.ext_iff]
  have heval := congrArg (eval fun v ↦ if v = u then (1 : K) else 0) hcoord
  simp only [map_sum, map_mul, eval_C, eval_X, hiff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at heval
  exact heval

/-- The orbit has one point per residue-field matrix; for a split at `r ≤ k` this gives
`q^(r*(k-r))` distinct points over the shallow indeterminates. -/
theorem natCard_range_deepUnipotentPoint [Nontrivial K] (hp : (T.p : K) = 0) :
    Nat.card (Set.range (T.deepUnipotentPoint (k := k) (r := r) hp)) = T.q ^ (r * (k - r)) := by
  rw [Nat.card_range_of_injective (T.deepUnipotentPoint_injective hp)]
  -- `Matrix` is represented by its curried entry function.
  rw [Nat.card_congr Matrix.of.symm, Nat.card_fun, Nat.card_fun,
    T.card_residueField_eq_q, ← pow_mul]
  have hright : Fintype.card {i : Fin k // r ≤ (i : ℕ)} = k - r := by
    by_cases hr : r ≤ k
    · have hc := Fintype.card_congr (Equiv.sumCompl fun i : Fin k ↦ (i : ℕ) < r)
      rw [Fintype.card_sum, Fintype.card_fin_lt_of_le hr, Fintype.card_fin] at hc
      rw [Fintype.card_congr (Equiv.subtypeEquivRight fun i : Fin k ↦ not_lt.symm)]
      omega
    · let : IsEmpty {i : Fin k // r ≤ (i : ℕ)} := ⟨fun i ↦ hr (i.property.trans i.val.isLt.le)⟩
      simp [Nat.sub_eq_zero_of_le (le_of_not_ge hr)]
  rw [Nat.card_eq_fintype_card, hright]
  by_cases hr : r ≤ k
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin_lt_of_le hr, mul_comm]
  · simp [Nat.sub_eq_zero_of_le (le_of_not_ge hr)]

/-- Every point is realized by an upper block unipotent over `W`. The displayed sum
is the image of the variable `(c,s)` under the twisted substitution, evaluated at the
shallow indeterminates and with all deep variables set to zero. -/
private theorem exists_letterMatrix_deepUnipotentPoint (hp : (T.p : K) = 0)
    (A : Matrix {i : Fin k // (i : ℕ) < r} {j : Fin k // r ≤ (j : ℕ)} (ResidueField W)) :
    ∃ g : GL (Fin k) W, ∀ (c : Fin k) (s : ZMod N),
      (∑ b : Fin k, T.letterMatrix s g b c •
        (if h : T.IsDeep r (b, s) then 0 else
          (X ⟨(b, s), h⟩ : MvPolynomial {x // ¬ T.IsDeep r x} K))) =
        if h : T.IsDeep r (c, s) then T.deepUnipotentPoint hp A ⟨(c, s), h⟩ else X ⟨(c, s), h⟩ := by
  classical
  let e : ({i : Fin k // (i : ℕ) < r} ⊕ {j : Fin k // r ≤ (j : ℕ)}) ≃ Fin k :=
    (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun _ ↦ not_lt.symm)).trans
      (Equiv.sumCompl fun i : Fin k ↦ (i : ℕ) < r)
  choose B hB using fun i j ↦ residue_surjective (A i j)
  let g := e.reindexGL W (upperBlockGL (Matrix.of B))
  refine ⟨g, fun c s ↦ ?_⟩
  obtain ⟨c, rfl⟩ := e.surjective c
  rw [← Fintype.sum_equiv e (fun b ↦ T.letterMatrix s g (e b) (e c) •
    (if h : T.IsDeep r (e b, s) then 0 else X ⟨(e b, s), h⟩)) _ (fun _ ↦ rfl),
    Fintype.sum_sum_type]
  have hl (b : {i : Fin k // (i : ℕ) < r}) : (b.val : ℕ) < r := b.property
  have hr (b : {j : Fin k // r ≤ (j : ℕ)}) : ¬ (b.val : ℕ) < r := b.property.not_gt
  cases hpar : T.isEven s
  · rw [T.letterMatrix_of_not_isEven hpar, ← map_inv, upperBlockGL_inv, Equiv.coe_reindexGL,
      coe_upperBlockGL]
    simp only [Matrix.map_apply, transpose_apply, submatrix_apply, Equiv.symm_apply_apply]
    cases c with
    | inl c =>
        simp [e, hpar, hl, hr, deepUnipotentPoint_odd, ← hB, smul_eq_C_mul]
    | inr c =>
        simp [e, hpar, hr, Matrix.one_apply]
  · rw [T.letterMatrix_of_isEven hpar, Equiv.coe_reindexGL, coe_upperBlockGL]
    simp only [Matrix.map_apply, submatrix_apply, Equiv.symm_apply_apply]
    cases c with
    | inl c =>
        simp [e, hpar, not_le.mpr (hl _), Matrix.one_apply]
    | inr c =>
        simp [e, hpar, not_le.mpr (hl _), not_lt.mp (hr _), deepUnipotentPoint_even,
          ← hB, smul_eq_C_mul]

/-- Evaluation at an orbit point, with the shallow coordinates left generic, is evaluation
on the shallow coordinate space after a twisted linear substitution. In particular, a
polynomial whose translates vanish on that space vanishes at every orbit point. -/
theorem exists_aeval_eq_aeval_deepUnipotentPoint (hp : (T.p : K) = 0)
    (A : Matrix {i : Fin k // (i : ℕ) < r} {j : Fin k // r ≤ (j : ℕ)} (ResidueField W)) :
    haveI := T.neZero
    ∃ g : GL (Fin k) W,
      (aeval (fun x : Fin k × ZMod N ↦ if h : T.IsDeep r x then 0 else
        (X ⟨x, h⟩ : MvPolynomial {x // ¬ T.IsDeep r x} K))).comp
        (polynomialAction (blockDiagonal fun s ↦ T.letterMatrix s g)) =
      aeval (fun x : Fin k × ZMod N ↦ if h : T.IsDeep r x then T.deepUnipotentPoint hp A ⟨x, h⟩
        else X ⟨x, h⟩) := by
  classical
  let := T.neZero
  obtain ⟨g, hg⟩ := T.exists_letterMatrix_deepUnipotentPoint hp A
  refine ⟨g, MvPolynomial.algHom_ext fun ⟨c, s⟩ ↦ ?_⟩
  simp only [AlgHom.comp_apply, polynomialAction_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    aeval_X, Fintype.sum_prod_type, blockDiagonal_apply, apply_ite C, map_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simpa only [smul_eq_C_mul] using hg c s

end TauCeti.FrobeniusCycle
