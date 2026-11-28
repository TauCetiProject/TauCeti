/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import TauCeti.Algebra.Polynomial.Degree.Operations
import TauCeti.Algebra.Polynomial.RingDivision

/-!
# Resultant lemmas

Mathlib evaluates the resultant against the linear polynomial `X - C x` on either side
(`Polynomial.resultant_X_sub_C_left`, `Polynomial.resultant_X_sub_C_right`). This file records the
companion for the *reversed* polynomial `C x - X`, which is the shape that arises as `x - θ` in
`AdjoinRoot f`: the answer is `f.eval x`, with **no sign**.

The file also normalizes bounded resultants with a monic left argument. This makes the resultant
independent of the chosen valid right degree bound, as needed when comparing resultant-based
discriminant formulas that use different bounds, and makes `f.resultant` multiplicative in its
right argument with no leading-coefficient assumption on the right factors. Over an integrally
closed domain, vanishing of `f.resultant g` for a monic irreducible `f` is equivalent to `f ∣ g`.

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
coprime, coprimality can be read off a unit resultant; in particular, coprimality with a monic
polynomial lifts from the reductions modulo an ideal in the Jacobson radical.

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
* `Polynomial.Monic.resultant_of_le`, `Polynomial.Monic.resultant_mul_right`,
  `Polynomial.Monic.resultant_prod_right`: for a monic left argument, the resultant is independent
  of the valid degree bound supplied for the right argument, and hence multiplicative in the right
  argument.
* `Polynomial.Monic.resultant_eq_zero_iff_dvd`: over an integrally closed domain, for a monic
  irreducible `f`, `f.resultant g = 0` iff `f ∣ g`.
* `Polynomial.resultant_sub_mem_of_map_eq`: polynomials congruent modulo an ideal have congruent
  resultants.
* `Polynomial.Monic.resultant_ne_zero_of_not_dvd`: over an integrally closed domain, a monic
  irreducible polynomial has nonzero resultant against every polynomial it does not divide.
* `Polynomial.resultant_congr_of_coeff_eq`: the resultant at degree bounds `m` and `n` only sees
  the coefficients of index at most `m` and `n`.
* `Polynomial.resultant_C_mul_X_add_C_C_mul_X_add_C`: `Res_{1,1}(a X + b, c X + e) = a e - b c`.
* `Polynomial.exists_mul_add_mul_eq_C_resultant_mul`: for `f`, `g` of degrees at most `m`, `n` and
  any `P` of degree less than `m + n` there are `p`, `q` of degrees less than `n`, `m` with
  `f p + g q = Res_{m,n}(f, g) P`.
* `Polynomial.isCoprime_of_isCoprime_map`: a monic polynomial and any polynomial whose reductions
  modulo an ideal in the Jacobson radical are coprime are themselves coprime.
* `Polynomial.IsDistinguishedAt.isUnit_resultant_of_isUnit_coeff_zero`: a polynomial distinguished
  at an ideal contained in the Jacobson radical has unit resultant with every polynomial whose
  constant coefficient is a unit.

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
  nontriviality R
  refine resultant_prod_left s f g _ ?_ le_rfl
  rw [Finset.prod_congr rfl fun i hi ↦ (hf i hi).leadingCoeff, Finset.prod_const_one]
  exact one_ne_zero

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

/-- For monic `f`, `Res(f, g₁ * g₂) = Res(f, g₁) * Res(f, g₂)` at the actual degrees, with no
hypothesis on the leading coefficients of `g₁` and `g₂`. -/
protected theorem Monic.resultant_mul_right {f g₁ g₂ : R[X]} (hf : f.Monic) :
    f.resultant (g₁ * g₂) = f.resultant g₁ * f.resultant g₂ := by
  rw [← hf.resultant_of_le natDegree_mul_le, Polynomial.resultant_mul_right _ _ _ _ le_rfl]

/-- For monic `f`, `Res(f, ∏ gᵢ) = ∏ Res(f, gᵢ)` at the actual degrees, with no hypothesis on the
leading coefficients of the factors `gᵢ`. -/
protected theorem Monic.resultant_prod_right {ι : Type*} (s : Finset ι) {f : R[X]} (hf : f.Monic)
    (g : ι → R[X]) :
    f.resultant (∏ i ∈ s, g i) = ∏ i ∈ s, f.resultant (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, hf.resultant_mul_right, ih]

/-- Over an integrally closed domain, the resultant of a monic irreducible polynomial `f` with `g`
vanishes if and only if `f` divides `g`. -/
protected theorem Monic.resultant_eq_zero_iff_dvd [IsDomain R] [IsIntegrallyClosed R] {f g : R[X]}
    (hf : f.Monic) (hirr : Irreducible f) : f.resultant g = 0 ↔ f ∣ g := by
  let φ := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hirr' : Irreducible (f.map φ) := hf.irreducible_iff_irreducible_map_fraction_map.mp hirr
  rw [← map_eq_zero_iff φ hφ,
    ← resultant_map_of_natDegree_eq φ (natDegree_map_eq_of_injective hφ f)
      (natDegree_map_eq_of_injective hφ g),
    resultant_eq_zero_iff, and_iff_right (Or.inl (hf.map φ).ne_zero),
    ← hirr'.dvd_iff_not_isCoprime, map_dvd_map φ hφ hf]

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

/-- A polynomial distinguished at an ideal `I` contained in the Jacobson radical has unit resultant
with every polynomial whose constant coefficient is a unit: modulo `I` the distinguished polynomial
reduces to `X ^ d`, which is coprime to any polynomial with unit constant term. -/
theorem IsDistinguishedAt.isUnit_resultant_of_isUnit_coeff_zero {I : Ideal R} {P Q : R[X]}
    (hP : P.IsDistinguishedAt I) (hI : I ≤ Ring.jacobson R) (hQ : IsUnit (Q.coeff 0)) :
    IsUnit (P.resultant Q) := by
  nontriviality R
  rw [isUnit_resultant_iff_isCoprime hP.monic]
  refine isCoprime_of_isCoprime_map hI hP.monic ?_
  rw [hP.map_eq_X_pow]
  have heval : IsUnit ((Q.map (Ideal.Quotient.mk I)).eval 0) := by
    rw [← coeff_zero_eq_eval_zero, coeff_map]
    exact hQ.map _
  simpa using ((isCoprime_X_sub_C_iff_isUnit_eval _ (a := 0)).mpr heval).pow_left

/-- The resultant with degree bounds `m` and `n` only involves the coefficients of index at most
`m` of the first polynomial and at most `n` of the second. -/
theorem resultant_congr_of_coeff_eq {f f' g g' : R[X]} {m n : ℕ}
    (hf : ∀ i ≤ m, f.coeff i = f'.coeff i) (hg : ∀ i ≤ n, g.coeff i = g'.coeff i) :
    resultant f g m n = resultant f' g' m n := by
  rw [resultant, resultant]
  congr 1
  ext i j
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs with h
    · exact hg _ (by simp only [Set.mem_Icc] at h; omega)
    · rfl
  | right j =>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs with h
    · exact hf _ (by simp only [Set.mem_Icc] at h; omega)
    · rfl

/-- **Resultants of congruent polynomials are congruent.** If `f ≡ f'` and `g ≡ g'` modulo an
ideal `I`, then the resultants at the same degree bounds are congruent modulo `I`. -/
theorem resultant_sub_mem_of_map_eq {I : Ideal R} {f f' g g' : R[X]}
    (hf : f.map (Ideal.Quotient.mk I) = f'.map (Ideal.Quotient.mk I))
    (hg : g.map (Ideal.Quotient.mk I) = g'.map (Ideal.Quotient.mk I)) (m n : ℕ) :
    f.resultant g m n - f'.resultant g' m n ∈ I := by
  rw [← Ideal.Quotient.eq, ← resultant_map_map, ← resultant_map_map, hf, hg]

/-- **A monic irreducible non-divisor has nonzero resultant.** Over an integrally closed domain,
if a monic irreducible `g` does not divide `f`, then `Res(f, g) ≠ 0`: by Gauss's lemma `g` stays
irreducible over the fraction field, where it is therefore coprime to `f`. -/
theorem Monic.resultant_ne_zero_of_not_dvd [IsDomain R] [IsIntegrallyClosed R] {f g : R[X]}
    (hg : g.Monic) (hirr : Irreducible g) (hdvd : ¬g ∣ f) : f.resultant g ≠ 0 := by
  rw [resultant_comm, mul_ne_zero_iff]
  exact ⟨pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero),
    (hg.resultant_eq_zero_iff_dvd hirr).not.mpr hdvd⟩

/-- The resultant of two linear polynomials is the determinant of their coefficient matrix:
`Res_{1,1}(a X + b, c X + e) = a e - b c`. -/
@[simp]
theorem resultant_C_mul_X_add_C_C_mul_X_add_C (a b c e : R) :
    (C a * X + C b).resultant (C c * X + C e) 1 1 = a * e - b * c := by
  -- The Sylvester matrix has the coefficients of `c X + e` in its first column and those of
  -- `a X + b` in its second.
  have h : sylvester (C a * X + C b) (C c * X + C e) 1 1 = !![e, b; c, a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sylvester, Fin.addCases]
  rw [resultant, h, Matrix.det_fin_two_of, mul_comm e a]

/-- **Bézout identity for the resultant with an arbitrary right-hand side.** For `f` and `g` of
degrees at most `m` and `n` and any `P` of degree less than `m + n`, there are `p` and `q` of
degrees less than `n` and `m` with `f p + g q = Res_{m,n}(f, g) P`. Mathlib's
`Polynomial.exists_mul_add_mul_eq_C_resultant` is the case `P = 1`; the proof is the same, applying
the adjugate `Polynomial.adjSylvester` of the Sylvester map to `P` instead of to `1`. -/
theorem exists_mul_add_mul_eq_C_resultant_mul {f g : R[X]} {m n : ℕ} (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) {P : R[X]} (hP : P.degree < ↑(m + n)) :
    ∃ p q : R[X], p.degree < n ∧ q.degree < m ∧ f * p + g * q = C (f.resultant g m n) * P := by
  let P' : R[X]_(m + n) := ⟨P, mem_degreeLT.mpr hP⟩
  let pq := adjSylvester f g P'
  have key : sylvesterMap f g hf hg pq = f.resultant g m n • P' := by
    rw [← LinearMap.comp_apply, sylvesterMap_comp_adjSylvester, LinearMap.smul_apply,
      LinearMap.id_apply]
  refine ⟨pq.2, pq.1, mem_degreeLT.mp pq.2.property, mem_degreeLT.mp pq.1.property, ?_⟩
  -- By definition, `sylvesterMap f g hf hg` sends `(p, q)` to `f q + g p`.
  have hval : (sylvesterMap f g hf hg pq : R[X]) = f * pq.2 + g * pq.1 := rfl
  rw [← hval, key, Submodule.coe_smul, smul_eq_C_mul]

end Polynomial
