/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.HomogeneousSubstitution
public import TauCeti.RingTheory.Polynomial.Resultant.FormDiscriminant

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Algebra.Polynomial.Homogenize

/-!
# Covariance of the binary-form discriminant

For a product of linear forms, the fixed-degree discriminant is the product of the squared
two-by-two determinants of the coefficient rows. Each determinant acquires a factor of
`det M` under homogeneous substitution by `M`. Specialization of universal coefficients
gives the covariance law over any commutative ring, including for singular matrices and
when either the original or substituted form has roots at infinity.

## References

* I. M. Gelfand, M. M. Kapranov, A. V. Zelevinsky, *Discriminants, Resultants, and
  Multidimensional Determinants*, Birkhäuser (1994), Chapter 12, §1.
-/

public section

open Finset Matrix

namespace Polynomial

variable {R : Type*} [CommRing R]

private theorem formDiscr_prod_linear_of_field {K : Type*} [Field K] {n : ℕ}
    (a b : Fin n → K) (ha : ∀ i, a i ≠ 0) :
    (∏ i, (C (a i) * X + C (b i))).formDiscr n =
      ∏ i, ∏ j ∈ Ioi i, (a i * b j - b i * a j) ^ 2 := by
  let r (i : Fin n) := -b i / a i
  have hfac (i : Fin n) : C (a i) * X + C (b i) = C (a i) * (X - C (r i)) := by
    have h : a i * r i = -b i := by
      dsimp [r]
      field_simp [ha i]
    rw [mul_sub, ← C_mul, h, C_neg, sub_neg_eq_add]
  have hpair (i j : Fin n) :
      (a i * b j - b i * a j) ^ 2 = (a i * a j) ^ 2 * (r i - r j) ^ 2 := by
    rw [← mul_pow]
    congr 1
    dsimp [r]
    field_simp [ha i, ha j]
    ring
  -- Every leading coefficient occurs in exactly `n - 1` unordered pairs.
  have hleading : (∏ i, ∏ j ∈ Ioi i, (a i * a j) ^ 2) = (∏ i, a i) ^ (2 * n - 2) := by
    simp only [Finset.prod_pow]
    rw [prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun _ j ↦ a j)]
    simp only [card_compl, card_singleton, Fintype.card_fin, prod_const, Finset.prod_pow,
      ← pow_mul, Nat.mul_comm (n - 1) 2, Nat.mul_sub, Nat.mul_one]
  simp only [hfac, Finset.prod_mul_distrib, ← map_prod C, formDiscr_C_mul,
    formDiscr_of_natDegree_eq (by simp : (∏ i, (X - C (r i))).natDegree = n),
    discr_prod_X_sub_C, hpair, hleading]

/-- The discriminant of a product of `n` binary linear forms is the product of the squared
determinants of all pairs of coefficient rows. A factor with zero leading coefficient
represents a root at infinity. -/
theorem formDiscr_prod_linear {n : ℕ} (a b : Fin n → R) :
    (∏ i, (C (a i) * X + C (b i))).formDiscr n =
      ∏ i, ∏ j ∈ Ioi i, (a i * b j - b i * a j) ^ 2 := by
  classical
  let U := MvPolynomial (Fin n ⊕ Fin n) ℤ
  let K := FractionRing U
  let ι := algebraMap U K
  let A (i : Fin n) : U := MvPolynomial.X (.inl i)
  let B (i : Fin n) : U := MvPolynomial.X (.inr i)
  have h : (∏ i, (C (A i) * X + C (B i))).formDiscr n =
      ∏ i, ∏ j ∈ Ioi i, (A i * B j - B i * A j) ^ 2 := by
    apply IsFractionRing.injective U K
    have hA (i : Fin n) : ι (A i) ≠ 0 :=
      (map_ne_zero_iff ι (IsFractionRing.injective U K)).2 (MvPolynomial.X_ne_zero _)
    simpa only [← formDiscr_map, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_mul,
      map_C, map_X, map_prod, map_pow, map_sub, map_mul, Function.comp_apply] using
      formDiscr_prod_linear_of_field (ι ∘ A) (ι ∘ B) hA
  let φ : U →ₐ[ℤ] R := MvPolynomial.aeval (Sum.elim a b)
  have hA (i : Fin n) : φ.toRingHom (A i) = a i :=
    MvPolynomial.aeval_X (Sum.elim a b) (.inl i)
  have hB (i : Fin n) : φ.toRingHom (B i) = b i :=
    MvPolynomial.aeval_X (Sum.elim a b) (.inr i)
  simpa only [← formDiscr_map, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_mul,
    map_C, map_X, map_prod, map_pow, map_sub, map_mul, hA, hB] using congrArg φ.toRingHom h

private theorem formDiscr_homogSubst_of_factorization (M : Matrix (Fin 2) (Fin 2) R)
    {n : ℕ} (s : R) (a b : Fin n → R) (p : R[X])
    (hp : p.homogenize n =
      MvPolynomial.C s * ∏ i, (MvPolynomial.C (a i) * MvPolynomial.X 0 +
        MvPolynomial.C (b i) * MvPolynomial.X 1))
    (hdeg : p.natDegree ≤ n) :
    (p.homogSubst n M).formDiscr n = M.det ^ (n * (n - 1)) * p.formDiscr n := by
  let a' (i : Fin n) := a i * M 0 0 + b i * M 1 0
  let b' (i : Fin n) := a i * M 0 1 + b i * M 1 1
  have hbase : p = C s * ∏ i, (C (a i) * X + C (b i)) := by
    simpa [hdeg] using congrArg (MvPolynomial.aeval ![(X : R[X]), 1]) hp
  have hsub : p.homogSubst n M = C s * ∏ i, (C (a' i) * X + C (b' i)) := by
    rw [homogSubst_eq_aeval, hp]
    simp only [map_mul, map_prod, MvPolynomial.aeval_C, C_eq_algebraMap, map_add,
      MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    congr 1
    refine prod_congr rfl fun i _ ↦ ?_
    simp only [a', b', ← C_eq_algebraMap, map_add, map_mul]
    ring
  have hpair (i j : Fin n) :
      a' i * b' j - b' i * a' j = M.det * (a i * b j - b i * a j) := by
    simp only [a', b', det_fin_two]
    ring
  have hweight : (∏ i : Fin n, ∏ _j ∈ Ioi i, M.det ^ 2) = M.det ^ (n * (n - 1)) := by
    simp only [pow_two]
    rw [prod_prod_Ioi_mul_eq_prod_prod_off_diag (fun (_ _ : Fin n) ↦ M.det)]
    simp [card_compl, ← pow_mul, Nat.mul_comm (n - 1) n]
  rw [hsub, formDiscr_C_mul, formDiscr_prod_linear]
  conv_rhs => rw [hbase, formDiscr_C_mul, formDiscr_prod_linear]
  simp only [hpair, mul_pow, prod_mul_distrib, hweight]
  ring

private theorem formDiscr_homogSubst_of_splits {K : Type*} [Field K]
    {n : ℕ} (p : K[X]) (hdeg : p.natDegree = n) (hs : p.Splits)
    (M : Matrix (Fin 2) (Fin 2) K) :
    (p.homogSubst n M).formDiscr n = M.det ^ (n * (n - 1)) * p.formDiscr n := by
  classical
  have hroots := hs.natDegree_eq_card_roots.symm
  obtain ⟨r, hr⟩ := (exists_isRootEnumeration_iff_splits
    (R := K) (L := K) (f := p) (ι := Fin n) (by simpa using hdeg)).2 (by simpa using hs)
  have hr' : p.roots = (univ : Finset (Fin n)).val.map r := by
    simpa using isRootEnumeration_iff.mp hr
  apply formDiscr_homogSubst_of_factorization M p.leadingCoeff (fun _ ↦ 1) (-r) p ?_ hdeg.le
  rw [homogenize_eq_C_mul_X_pow_mul_prod hdeg.le hroots, hdeg, Nat.sub_self, pow_zero, mul_one,
    hr', Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  simp [sub_eq_add_neg]

open TauCeti in
private theorem formDiscr_homogSubst_universal (n : ℕ) :
    let U := MvPolynomial (Fin 2 × Fin 2) (MvPolynomial (Fin (n + 1)) ℤ)
    let p : U[X] := (universalPoly n).map MvPolynomial.C
    let M : Matrix (Fin 2) (Fin 2) U := fun i j ↦ MvPolynomial.X (i, j)
    (p.homogSubst n M).formDiscr n = M.det ^ (n * (n - 1)) * p.formDiscr n := by
  intro U p M
  let F := FractionRing U
  let K := AlgebraicClosure F
  let ι : U →+* K := (algebraMap F K).comp (algebraMap U F)
  have hι : Function.Injective ι :=
    (algebraMap F K).injective.comp (IsFractionRing.injective U F)
  have hdeg : (p.map ι).natDegree = n := by
    rw [natDegree_map_eq_of_injective hι]
    exact (natDegree_map_eq_of_injective (MvPolynomial.C_injective _ _) _).trans
      (natDegree_universalPoly n)
  apply hι
  simpa only [← formDiscr_map, map_homogSubst, map_mul, map_pow, RingHom.map_det,
    RingHom.mapMatrix_apply] using
    formDiscr_homogSubst_of_splits _ hdeg (IsAlgClosed.splits _) (M.map ι)

open TauCeti in
/-- Homogeneous substitution multiplies the fixed-degree binary discriminant by the
`n * (n - 1)` power of the determinant. The formula holds for every matrix over a commutative
ring, even if the substitution changes the affine degree. Only the first `n + 1` coefficients
of the input polynomial enter either side. -/
theorem formDiscr_homogSubst (p : R[X]) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    (p.homogSubst n M).formDiscr n = M.det ^ (n * (n - 1)) * p.formDiscr n := by
  let U := MvPolynomial (Fin 2 × Fin 2) (MvPolynomial (Fin (n + 1)) ℤ)
  let A : Matrix (Fin 2) (Fin 2) U := Matrix.of fun i j ↦ MvPolynomial.X (i, j)
  let g : MvPolynomial (Fin (n + 1)) ℤ →+* R :=
    (MvPolynomial.aeval (fun i : Fin (n + 1) ↦ p.coeff i)).toRingHom
  let φ : U →+* R := MvPolynomial.eval₂Hom g (Function.uncurry M)
  let P : U[X] := (universalPoly n).map MvPolynomial.C
  have hcoeff (i : ℕ) (hi : i ≤ n) : (P.map φ).coeff i = p.coeff i := by
    simp only [P, coeff_map, coeff_universalPoly_of_le hi]
    exact (MvPolynomial.eval₂Hom_C g (Function.uncurry M) _).trans
      (MvPolynomial.aeval_X (fun j : Fin (n + 1) ↦ p.coeff j) ⟨i, Nat.lt_succ_of_le hi⟩)
  have hsub : (P.map φ).homogSubst n M = p.homogSubst n M := by
    simp only [homogSubst_eq_sum]
    exact sum_congr rfl fun i hi ↦ by rw [hcoeff i (Nat.lt_succ_iff.mp (mem_range.mp hi))]
  have hM : A.map φ = M := by
    ext i j
    exact MvPolynomial.eval₂Hom_X' g (Function.uncurry M) (i, j)
  have h : φ ((P.homogSubst n A).formDiscr n) =
      φ (A.det ^ (n * (n - 1)) * P.formDiscr n) :=
    congrArg φ (formDiscr_homogSubst_universal n)
  simpa only [← formDiscr_map, map_homogSubst, hsub, formDiscr_congr hcoeff, map_mul, map_pow,
    RingHom.map_det, RingHom.mapMatrix_apply, hM] using h

end Polynomial
