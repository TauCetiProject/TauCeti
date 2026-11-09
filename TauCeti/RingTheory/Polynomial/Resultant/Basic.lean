/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.Algebra.Polynomial.Degree.Operations

/-!
# Resultant lemmas

Mathlib evaluates the resultant against the linear polynomial `X - C x` on either side
(`Polynomial.resultant_X_sub_C_left`, `Polynomial.resultant_X_sub_C_right`). This file records the
companion for the *reversed* polynomial `C x - X`, which is the shape that arises as `x - θ` in
`AdjoinRoot f`: the answer is `f.eval x`, with **no sign**.

The file also normalizes bounded resultants with a monic left argument. This makes the resultant
independent of the chosen valid right degree bound, as needed when comparing resultant-based
discriminant formulas that use different bounds.

That absence is the point. `C x - X` is `C (-1) * (X - C x)`, which contributes `(-1) ^ m`, and
`resultant_X_sub_C_right` contributes another `(-1) ^ m`, so the two cancel.

The resultant with `1 - t X` at a degree bound `n` for `f` is the value at `t` of the reversal
`reflect n f`, and the multiplicativity `Res(f₁ * f₂, g) = Res(f₁, g) * Res(f₂, g)` holds for
arbitrary valid degree bounds, the bounds adding. These are the identities behind Coleman's
spectral transform, whose rank is a specified degree bound rather than an actual degree.
Reversing both arguments at their degree bounds changes the resultant only by the sign
`(-1) ^ (m * n)`, with no degree hypothesis: the reversals permute the rows of the Sylvester
matrix and the columns within each of its two blocks.

Resultants taken at the actual degrees commute with any coefficient map preserving both
degrees, the form of base change used when comparing a resultant with its specializations.
Finally, the entries of the Sylvester matrix are written out explicitly, column by column, for
expanding its determinant term by term.

Since a resultant with a monic left argument is a unit exactly when the two polynomials are
coprime, coprimality can be read off a unit resultant: against `X - C a` this is a unit value at
`a`, and modulo an ideal in the Jacobson radical it lifts from the reductions.

## Main results

* `Polynomial.sylvester_apply_of_lt`, `Polynomial.sylvester_apply_of_le`: the entries of the
  Sylvester matrix in its first `n` and its last `m` columns.
* `Polynomial.resultant_C_sub_X_right`
* `Polynomial.resultant_one_sub_C_mul_X_right`: `Res_(n,1)(f, 1 - t X) = (reflect n f)(t)`.
* `Polynomial.resultant_mul_left_of_natDegree_le`: multiplicativity in the left argument at
  arbitrary degree bounds.
* `Polynomial.resultant_prod_left_of_monic`: multiplicativity in a finite product of monic left
  arguments, at the actual degrees.
* `Polynomial.resultant_reflect`: reversing both arguments at their degree bounds multiplies the
  resultant by `(-1) ^ (m * n)`.
* `Polynomial.resultant_map_of_natDegree_eq`: resultants at the actual degrees commute with a
  coefficient map that preserves both degrees.
* `Polynomial.Monic.resultant_of_le`: for a monic left argument, the resultant is independent of
  the valid degree bound supplied for the right argument.
* `Polynomial.isCoprime_X_sub_C_of_isUnit_eval`: `X - C a` is coprime to any polynomial whose value
  at `a` is a unit.
* `Polynomial.isCoprime_of_isCoprime_map`: a monic polynomial and any polynomial whose reductions
  modulo an ideal in the Jacobson radical are coprime are themselves coprime.

## Provenance

`Polynomial.resultant_C_sub_X_right` is adapted from Michael Stoll's `EllipticCurves`
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/Mathlib/Basic.lean` line 615, where
it is a Mathlib-bound prerequisite of the explicit `2`-descent.
-/

public section

namespace Polynomial

section Sylvester

variable {S : Type*} [Semiring S]

/-- An entry of the Sylvester matrix in one of the first `n` columns, which carry the
coefficients of the second polynomial. -/
theorem sylvester_apply_of_lt (f g : S[X]) {n m : ℕ} (i x : Fin (n + m))
    (hx : (x : ℕ) < n) :
    sylvester f g n m i x =
      if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ x + m then g.coeff (i - x) else 0 := by
  obtain ⟨x, rfl⟩ : ∃ y : Fin n, Fin.castAdd m y = x := ⟨⟨x, hx⟩, rfl⟩
  simp [sylvester]

/-- An entry of the Sylvester matrix in one of the last `m` columns, which carry the
coefficients of the first polynomial. -/
theorem sylvester_apply_of_le (f g : S[X]) {n m : ℕ} (i x : Fin (n + m))
    (hx : n ≤ (x : ℕ)) :
    sylvester f g n m i x =
      if (x : ℕ) ≤ i + n ∧ (i : ℕ) ≤ x then f.coeff (i + n - x) else 0 := by
  obtain ⟨x, rfl⟩ : ∃ y : Fin m, Fin.natAdd n y = x :=
    ⟨⟨x - n, by omega⟩, Fin.ext (by simp; omega)⟩
  simp only [sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc, Fin.val_natAdd]
  congr 1
  · exact propext (by omega)
  · congr 1; omega

/-- The permutation of `Fin (m + n)` reversing each of the blocks `Fin m` and `Fin n`. -/
private def blockRevPerm (m n : ℕ) : Equiv.Perm (Fin (m + n)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr Fin.revPerm Fin.revPerm).trans finSumFinEquiv)

/-- Reversing both polynomials at their degree bounds reverses the rows of the Sylvester matrix
and the columns within each of its two blocks. -/
private theorem sylvester_reflect (f g : S[X]) (m n : ℕ) :
    sylvester (f.reflect m) (g.reflect n) m n =
      (sylvester f g m n).submatrix Fin.revPerm (blockRevPerm m n) := by
  ext i j
  have hi := i.isLt
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, blockRevPerm, Matrix.submatrix_apply, Matrix.of_apply,
      Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, Fin.addCases_left, Fin.revPerm_apply, Set.mem_Icc, Fin.val_rev,
      coeff_reflect]
    have hj := j.isLt
    by_cases h : (j : ℕ) ≤ i ∧ (i : ℕ) ≤ j + n
    · rw [ite_eq_left h, ite_eq_left (by omega), revAt_le (by omega)]
      congr 1
      omega
    · rw [ite_eq_right h, ite_eq_right (by omega)]
  | right j =>
    simp only [sylvester, blockRevPerm, Matrix.submatrix_apply, Matrix.of_apply,
      Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
      finSumFinEquiv_apply_right, Fin.addCases_right, Fin.revPerm_apply, Set.mem_Icc,
      Fin.val_rev, coeff_reflect]
    have hj := j.isLt
    by_cases h : (j : ℕ) ≤ i ∧ (i : ℕ) ≤ j + m
    · rw [ite_eq_left h, ite_eq_left (by omega), revAt_le (by omega)]
      congr 1
      omega
    · rw [ite_eq_right h, ite_eq_right (by omega)]

end Sylvester

variable {R : Type*} [CommRing R]

/-- The resultant of `f` with the reversed linear polynomial `C x - X` is `f.eval x`. Note the
absence of a sign: `C x - X` is `-(X - C x)`, and the two signs cancel. -/
@[simp]
theorem resultant_C_sub_X_right (f : R[X]) (x : R) (m : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  -- `C x - X` is `X - C x` scaled by the constant `-1`
  have hneg : C x - X = C (-1 : R) * (X - C x) := by simp
  rw [hneg, resultant_C_mul_right, resultant_X_sub_C_right f m x hm, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- `Res(f₁ * f₂, g) = Res(f₁, g) * Res(f₂, g)` for arbitrary valid degree bounds: the bound for
the product is the sum of the bounds for the factors. -/
theorem resultant_mul_left_of_natDegree_le {f₁ f₂ g : R[X]} {m₁ m₂ n : ℕ}
    (hf₁ : f₁.natDegree ≤ m₁) (hf₂ : f₂.natDegree ≤ m₂) (hg : g.natDegree ≤ n) :
    (f₁ * f₂).resultant g (m₁ + m₂) n = f₁.resultant g m₁ n * f₂.resultant g m₂ n := by
  obtain ⟨k₁, rfl⟩ := Nat.exists_eq_add_of_le hf₁
  obtain ⟨k₂, rfl⟩ := Nat.exists_eq_add_of_le hf₂
  rw [Nat.add_add_add_comm, resultant_add_left_deg _ _ _ _ _ natDegree_mul_le,
    resultant_mul_left _ _ _ _ hg, resultant_add_left_deg _ _ _ _ _ le_rfl,
    resultant_add_left_deg _ _ _ _ _ le_rfl]
  ring

/-- `Res(∏ fᵢ, g) = ∏ Res(fᵢ, g)` for a finite product of monic polynomials, the resultants being
taken at the actual degrees. -/
theorem resultant_prod_left_of_monic {ι : Type*} (s : Finset ι) {f : ι → R[X]}
    (hf : ∀ i ∈ s, (f i).Monic) (g : R[X]) :
    (∏ i ∈ s, f i).resultant g = ∏ i ∈ s, (f i).resultant g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.forall_mem_insert] at hf
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ← ih hf.2,
      hf.1.natDegree_mul (monic_prod_of_monic _ _ hf.2), resultant_mul_left _ _ _ _ le_rfl]

/-- The resultant of `f` with the linear polynomial `1 - t X`, at the degree bound `n` for `f`, is
the value at `t` of the reversal of `f` in degree `n`. When `f = ∏ (X - αᵢ)` has degree `n`, both
sides are `∏ (1 - αᵢ t)`. -/
theorem resultant_one_sub_C_mul_X_right (f : R[X]) (t : R) {n : ℕ} (hf : f.natDegree ≤ n) :
    f.resultant (1 - C t * X) n 1 = (f.reflect n).eval t := by
  set ℓ : R[X] := 1 - C t * X
  have hℓ : ℓ.natDegree ≤ 1 := natDegree_one_sub_C_mul_X_le t
  -- the value of the reversal, as a sum over the coefficients of `f`
  set c : R := ∑ j ∈ Finset.range (n + 1), f.coeff j * t ^ (n - j)
  have hc : (f.reflect n).eval t = c := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_reflect_le.trans (max_le le_rfl hf))),
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.succ_sub_one, coeff_reflect, revAt_le (Nat.sub_le n j), Nat.sub_sub_self hj]
  rw [hc]
  obtain _ | n := n
  · rw [resultant_zero_left_deg]
    simp [c]
  -- modulo `ℓ`, `X ^ j` is congruent to `t ^ (n - j) * X ^ n`, through a polynomial of degree `< n`
  set p : R[X] := -∑ j ∈ Finset.range (n + 2), ∑ i ∈ Finset.range (n + 1 - j),
    C (f.coeff j * t ^ i) * X ^ (j + i)
  have hp : p.natDegree + 1 ≤ n + 1 := by
    refine Nat.succ_le_succ ((natDegree_neg _).le.trans (natDegree_sum_le_of_forall_le _ _
      fun j _ ↦ natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_))
    exact (natDegree_C_mul_X_pow_le _ _).trans (by simp at hi; lia)
  have hfp : f + ℓ * p = C c * X ^ (n + 1) := by
    have hgeom (j : ℕ) : ℓ * ∑ i ∈ Finset.range (n + 1 - j), C (f.coeff j * t ^ i) * X ^ (j + i)
        = C (f.coeff j) * X ^ j - C (f.coeff j) * X ^ j * (C t * X) ^ (n + 1 - j) := by
      rw [← mul_one_sub, ← mul_neg_geom_sum]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [ℓ, C_mul, C_pow]
      ring
    rw [as_sum_range_C_mul_X_pow' f (n := n + 2) (by lia), mul_neg, Finset.mul_sum,
      Finset.sum_congr rfl fun j _ ↦ hgeom j, Finset.sum_sub_distrib, neg_sub, add_sub_cancel]
    simp only [c, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← pow_mul_pow_sub X hj, C_mul, C_pow]
    ring
  rw [← resultant_add_mul_left f ℓ p (n + 1) 1 hp hℓ, hfp, resultant_C_mul_left,
    resultant_X_pow_left _ _ _ hℓ]
  simp [ℓ]

/-- Resultants at the actual degrees commute with a coefficient map that preserves both degrees,
for instance an injective one or one that does not kill the leading coefficients
(`Polynomial.natDegree_map_of_leadingCoeff_ne_zero`). Without this hypothesis the original
degrees must be kept as explicit bounds, as in `Polynomial.resultant_map_map`. -/
theorem resultant_map_of_natDegree_eq {S : Type*} [CommRing S] (φ : R →+* S) {f g : R[X]}
    (hf : (f.map φ).natDegree = f.natDegree) (hg : (g.map φ).natDegree = g.natDegree) :
    (f.map φ).resultant (g.map φ) = φ (f.resultant g) := by
  rw [hf, hg, resultant_map_map]

/-- The resultant of the reversals is the resultant up to the sign of the permutation of the
Sylvester matrix that the reversals induce. -/
private theorem resultant_reflect_eq_sign_mul (f g : R[X]) (m n : ℕ) :
    resultant (f.reflect m) (g.reflect n) m n =
      ((Equiv.Perm.sign (blockRevPerm m n) * Equiv.Perm.sign (Fin.revPerm (n := m + n)) : ℤˣ) :
        R) * resultant f g m n := by
  have h := Matrix.det_permute' (blockRevPerm m n) ((sylvester f g m n).submatrix Fin.revPerm id)
  rw [Matrix.submatrix_submatrix, Matrix.det_permute] at h
  rw [resultant, sylvester_reflect, resultant, Units.val_mul, Int.cast_mul, mul_assoc]
  exact h

/-- **Resultant of reversals.** Reversing both arguments of a resultant at their degree bounds
multiplies it by `(-1) ^ (m * n)`. No degree hypothesis is needed: only the coefficients in
degrees at most the bounds enter the Sylvester matrix, and the reversals permute its rows and
columns. For instance `Res(1 - a X, 1 - b X) = b - a = -Res(X - a, X - b)` at the bounds
`m = n = 1`. -/
theorem resultant_reflect (f g : R[X]) (m n : ℕ) :
    resultant (f.reflect m) (g.reflect n) m n = (-1) ^ (m * n) * resultant f g m n := by
  -- the sign does not depend on the polynomials; `f = X ^ m` and `g = 1` over `ℤ` compute it
  have hsign : ((Equiv.Perm.sign (blockRevPerm m n) *
      Equiv.Perm.sign (Fin.revPerm (n := m + n)) : ℤˣ) : ℤ) = (-1) ^ (m * n) := by
    have h := resultant_reflect_eq_sign_mul (X ^ m : ℤ[X]) 1 m n
    rw [reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero, ← C_1, reflect_C,
      resultant_C_left, resultant_C_right] at h
    simpa using h.symm
  rw [resultant_reflect_eq_sign_mul, hsign, Int.cast_pow, Int.cast_neg, Int.cast_one]

end Polynomial

namespace TauCeti

open Polynomial

variable {R : Type*} [CommRing R]

/-- For monic `f`, `f.resultant g` does not depend on which valid upper bound is supplied for the
degree of `g`. -/
theorem _root_.Polynomial.Monic.resultant_of_le {f g : R[X]} (hf : f.Monic) {n : ℕ}
    (hn : g.natDegree ≤ n) : f.resultant g f.natDegree n = f.resultant g := by
  have hn' : n = g.natDegree + (n - g.natDegree) :=
    (Nat.add_sub_cancel' hn).symm
  conv_lhs => rw [hn']
  rw [Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, Polynomial.coeff_natDegree,
    hf.leadingCoeff, one_pow, one_mul]

end TauCeti

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- `X - C a` is coprime to every polynomial whose value at `a` is a unit, over any commutative
ring: the resultant of the two is that value. -/
theorem isCoprime_X_sub_C_of_isUnit_eval {p : R[X]} {a : R} (h : IsUnit (p.eval a)) :
    IsCoprime (X - C a) p := by
  cases subsingleton_or_nontrivial R with
  | inl _ => rw [Subsingleton.elim (X - C a) 1]; exact isCoprime_one_left
  | inr _ =>
    rwa [← isUnit_resultant_iff_isCoprime (monic_X_sub_C a), natDegree_X_sub_C,
      resultant_X_sub_C_left (hg := le_rfl)]

/-- **Coprimality lifts along the Jacobson radical.** If `g` is monic and the reductions of `g`
and `h` modulo an ideal `I` in the Jacobson radical are coprime, then `g` and `h` are coprime. -/
theorem isCoprime_of_isCoprime_map {I : Ideal R} (hI : I ≤ Ring.jacobson R) {g h : R[X]}
    (hg : g.Monic) (hgh : IsCoprime (g.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I))) :
    IsCoprime g h := by
  have : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson hI
  rw [← isUnit_resultant_iff_isCoprime hg]
  refine IsUnit.of_map (Ideal.Quotient.mk I) _ ?_
  cases subsingleton_or_nontrivial (R ⧸ I) with
  | inl _ => exact isUnit_of_subsingleton _
  | inr _ =>
    rwa [← isUnit_resultant_iff_isCoprime (hg.map _),
      ← (hg.map _).resultant_of_le (natDegree_map_le (f := Ideal.Quotient.mk I) (p := h)),
      hg.natDegree_map, resultant_map_map] at hgh

end Polynomial
