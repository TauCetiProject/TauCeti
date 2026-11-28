/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Basic
public import TauCeti.LinearAlgebra.Matrix.MvPolynomial.Degrees
public import Mathlib.Data.Matrix.Block

/-!
# Degrees in the generic Frobenius substitution

Each letter acts on the variables for that letter by rows of an ordered product of factors.
A deep row uses one extra factor, and at an odd letter the cofactor matrix replaces the
product. With generic Frobenius factors the substitution matrix entries on monomials are
polynomials in the generic matrix parameters. Their total-degree bound in particular controls
how many powers of the variables of any single copy can occur.

The substitution and degree estimate correspond to `New.FrobeniusCycle.substitutionOperator`
and `New.FrobeniusCycle.degree_le_of_coeff_substitutionOperator` in
`grh/src/New/UpperBound/ElementaryDivisors/FrobeniusFactors.lean` of
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public noncomputable section

open Matrix MvPolynomial

namespace TauCeti.FrobeniusCycle

variable {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R] {N k : ℕ}
    (T : FrobeniusCycle W R N)

/-- The generic factor at `(s,d)` is the entrywise `P^d`-th power of the generic matrix in copy
`s - d`. -/
def genericFrobFactor (s : ZMod N) (d : ℕ) :
    Matrix (Fin k) (Fin k) (MvPolynomial (ZMod N × Fin k × Fin k) R) :=
  Matrix.of fun i j ↦ X (s - d, i, j) ^ (T.P ^ d)

/-- The entries of a generic Frobenius factor. -/
@[simp]
theorem genericFrobFactor_apply (s : ZMod N) (d : ℕ) (i j : Fin k) :
    T.genericFrobFactor s d i j = (X (s - d, i, j) : MvPolynomial _ R) ^ (T.P ^ d) :=
  (rfl)

/-- In row `i` at letter `s`, take row `i` of `F_(s,m-1) ⋯ F_(s,0)` for an even letter and
of its transposed adjugate for an odd letter. Here `m = ℓ+1` for a deep row and `m = ℓ`
otherwise. -/
def substitutionLetterMatrix {S : Type*} [CommRing S] (r ℓ : ℕ)
    (F : ZMod N → ℕ → Matrix (Fin k) (Fin k) S) (s : ZMod N) :
    Matrix (Fin k) (Fin k) S :=
  Matrix.of fun i j ↦
    let m := if T.IsDeep r (i, s) then ℓ + 1 else ℓ
    let A := ((List.range m).reverse.map (F s)).prod
    if T.isEven s then A i j else A.adjugate j i

/-- The row formula for the substitution matrix at a letter. -/
theorem substitutionLetterMatrix_apply {S : Type*} [CommRing S] (r ℓ : ℕ)
    (F : ZMod N → ℕ → Matrix (Fin k) (Fin k) S) (s : ZMod N) (i j : Fin k) :
    T.substitutionLetterMatrix r ℓ F s i j =
      let m := if T.IsDeep r (i, s) then ℓ + 1 else ℓ
      let A := ((List.range m).reverse.map (F s)).prod
      if T.isEven s then A i j else A.adjugate j i :=
  (rfl)

/-- Entry `(β,γ)` is the coefficient of `X^γ` in the image of `X^β` under the block diagonal
linear substitution of the letter variables. Restricting both indices to exponents of degree `n`
in each letter reads the product of the letterwise symmetric powers, with input in the row index. -/
def substitutionOperator {S : Type*} [CommRing S] (r ℓ : ℕ)
    (F : ZMod N → ℕ → Matrix (Fin k) (Fin k) S) :
    Matrix (Fin k × ZMod N →₀ ℕ) (Fin k × ZMod N →₀ ℕ) S :=
  letI := T.neZero
  Matrix.of fun β γ ↦
    (linearSubst (blockDiagonal (T.substitutionLetterMatrix r ℓ F)) (monomial β 1)).coeff γ

/-- The monomial coefficient formula for an entry of the substitution operator. -/
@[simp]
theorem substitutionOperator_apply {S : Type*} [CommRing S] [NeZero N] (r ℓ : ℕ)
    (F : ZMod N → ℕ → Matrix (Fin k) (Fin k) S) (β γ : Fin k × ZMod N →₀ ℕ) :
    T.substitutionOperator r ℓ F β γ =
      (linearSubst (blockDiagonal (T.substitutionLetterMatrix r ℓ F)) (monomial β 1)).coeff γ :=
  (rfl)

/-- A generic Frobenius factor has degree at most `P^d` in its matrix parameters. -/
theorem totalDegree_genericFrobFactor_apply_le (s : ZMod N) (d : ℕ) (i j : Fin k) :
    (T.genericFrobFactor s d i j).totalDegree ≤ T.P ^ d := by
  rw [genericFrobFactor_apply]
  exact (totalDegree_pow _ _).trans
    (mul_le_of_le_one_right (Nat.zero_le _) (TauCeti.totalDegree_X_le (R := R) (s - d, i, j)))

/-- The row length and the cofactor operation give a uniform degree bound at every letter,
including the rows that use the extra factor. -/
theorem totalDegree_substitutionLetterMatrix_apply_le {σ S : Type*} [CommRing S] (r ℓ : ℕ)
    {F : ZMod N → ℕ → Matrix (Fin k) (Fin k) (MvPolynomial σ S)} {D : ℕ}
    (hF : ∀ s d, d ≤ ℓ → ∀ a b, (F s d a b).totalDegree ≤ D)
    (s : ZMod N) (i j : Fin k) :
    (T.substitutionLetterMatrix r ℓ F s i j).totalDegree ≤ k * ((ℓ + 1) * D) := by
  rw [substitutionLetterMatrix_apply]
  let m := if T.IsDeep r (i, s) then ℓ + 1 else ℓ
  let l := (List.range m).reverse
  have hm : m ≤ ℓ + 1 := by dsimp [m]; split <;> omega
  have hA (a b : Fin k) : ((l.map (F s)).prod a b).totalDegree ≤ (ℓ + 1) * D := by
    refine (Matrix.totalDegree_list_prod_apply_le (d := fun _ ↦ D) l (fun d hd ↦ ?_) a b).trans ?_
    · have hdm := List.mem_range.mp (List.mem_reverse.mp hd)
      exact hF s d (by omega)
    · simpa [l] using Nat.mul_le_mul_right D hm
  dsimp only
  split
  · exact (hA i j).trans (Nat.le_mul_of_pos_left _ (by have := i.isLt; omega))
  · simpa only [Fintype.card_fin] using Matrix.totalDegree_adjugate_apply_le hA j i

/-- An entry with input degree at most `n` in each letter has parameter degree at most
`N * n * k * (ℓ+1) * D` if each factor used has entries of degree at most `D`. -/
theorem totalDegree_substitutionOperator_apply_le {σ S : Type*} [CommRing S] (r ℓ : ℕ)
    {F : ZMod N → ℕ → Matrix (Fin k) (Fin k) (MvPolynomial σ S)} {D : ℕ}
    (hF : ∀ s d, d ≤ ℓ → ∀ a b, (F s d a b).totalDegree ≤ D)
    {β : Fin k × ZMod N →₀ ℕ} (γ : Fin k × ZMod N →₀ ℕ) {n : ℕ}
    (hβ : ∀ s, ∑ i : Fin k, β (i, s) ≤ n) :
    (T.substitutionOperator r ℓ F β γ).totalDegree ≤ N * n * k * (ℓ + 1) * D := by
  let := T.neZero
  have hA : ∀ x y, (blockDiagonal (T.substitutionLetterMatrix r ℓ F) x y).totalDegree ≤
      k * ((ℓ + 1) * D) := by
    rintro ⟨i, s⟩ ⟨j, t⟩
    by_cases h : s = t
    · subst t
      rw [blockDiagonal_apply_eq]
      exact T.totalDegree_substitutionLetterMatrix_apply_le r ℓ hF s i j
    · rw [blockDiagonal_apply_ne _ _ _ h, totalDegree_zero]
      exact Nat.zero_le _
  rw [substitutionOperator_apply]
  have h := totalDegree_coeff_linearSubst_monomial_le (d := fun _ ↦ k * ((ℓ + 1) * D)) hA β γ
  refine h.trans ?_
  rw [← Finset.sum_mul, Fintype.sum_prod_type_right]
  calc
    _ ≤ (∑ _s : ZMod N, n) * (k * ((ℓ + 1) * D)) :=
      Nat.mul_le_mul_right _ (Finset.sum_le_sum fun s _ ↦ hβ s)
    _ = _ := by simp [ZMod.card, mul_assoc]

/-- A monomial occurring in an entry for the generic factors has degree in each copy at most
`N * n * k * (ℓ+1) * P^ℓ`. -/
theorem degree_le_of_coeff_substitutionOperator (r ℓ : ℕ)
    {β : Fin k × ZMod N →₀ ℕ} (γ : Fin k × ZMod N →₀ ℕ) {n : ℕ}
    (hβ : ∀ s, ∑ i : Fin k, β (i, s) ≤ n) {ν : (ZMod N × Fin k × Fin k) →₀ ℕ}
    (hν : (T.substitutionOperator r ℓ T.genericFrobFactor β γ).coeff ν ≠ 0) (s : ZMod N) :
    ∑ ij : Fin k × Fin k, ν (s, ij) ≤ N * n * k * (ℓ + 1) * T.P ^ ℓ := by
  have hP : 1 ≤ T.P := by have := T.five_le_P; omega
  have hF (t : ZMod N) (d : ℕ) (hd : d ≤ ℓ) (a b : Fin k) :
      (T.genericFrobFactor t d a b).totalDegree ≤ T.P ^ ℓ :=
    (T.totalDegree_genericFrobFactor_apply_le t d a b).trans (pow_le_pow_right₀ hP hd)
  refine le_trans ?_ ((le_totalDegree (mem_support_iff.mpr hν)).trans
    (T.totalDegree_substitutionOperator_apply_le r ℓ hF γ hβ))
  let := T.neZero
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    _ ≤ ∑ t : ZMod N, ∑ ij : Fin k × Fin k, ν (t, ij) :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ s)
    _ = _ := (Fintype.sum_prod_type _).symm

end TauCeti.FrobeniusCycle
