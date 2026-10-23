/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Homogeneous
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import TauCeti.Algebra.MvPolynomial.Monomial

/-!
# Coefficients of polynomial laws

For a polynomial law `f : M →ₚₗ[R] N` and a finite family `m : ι → M`, the value of `f` at the
generic combination `∑ⱼ Xⱼ ⊗ mⱼ` over the polynomial ring `R[Xⱼ]` is a finite sum
`∑ₖ Xᵏ ⊗ cₖ`. The coefficients `cₖ = coeff m f k` determine `f`: after scalar extension to any
commutative `R`-algebra `S`,
`f (∑ⱼ sⱼ ⊗ mⱼ) = ∑ₖ (∏ⱼ sⱼ ^ kⱼ) ⊗ coeff m f k`.

These coefficients are the values of the linear maps out of divided powers which represent
homogeneous polynomial laws, so this file supplies the comparison tools used to construct them:
the change-of-variables formula for coefficients, the fact that a law is determined by its
coefficients, and the vanishing of the coefficients of a homogeneous law of degree `d` outside
total degree `d`.

## Main declarations

* `PolynomialLaw.coeff m`: the coefficients of a law at the generic combination of `m`, as an
  `R`-linear map to finitely supported functions on monomials.
* `PolynomialLaw.coeff_apply`: the coefficient of `Xᵏ`, extracted by `MvPolynomial.lcoeff`.
* `PolynomialLaw.toFun_sum_tmul_eq_coeff_sum`: the value of a law on any finite sum of pure
  tensors, in terms of its coefficients.
* `PolynomialLaw.coeff_eq_sum_of_sum_tmul_eq`: change of variables for coefficients.
* `PolynomialLaw.coeff_comp_equiv`, `PolynomialLaw.coeff_optionElim_zero`,
  `PolynomialLaw.coeff_optionElim_smul`, `PolynomialLaw.coeff_optionElim_optionElim_self` and
  `PolynomialLaw.coeff_optionElim_add`: coefficients are invariant under reindexing, ignore
  vectors with exponent zero, scale by `r ^ n` with a vector scaled by `r`, merge two equal
  vectors with a binomial coefficient, and split a sum of vectors along the antidiagonal.
* `PolynomialLaw.ext_coeff`: a law is determined by its coefficients on families indexed by
  `Fin n`.
* `PolynomialLaw.IsHomogeneousOfDegree.coeff_eq_zero`: a law homogeneous of degree `d` has no
  coefficients outside total degree `d`.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  Chapitre I][Roby-1963]
-/

public section

noncomputable section

universe u

open TensorProduct MvPolynomial

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

section Coeff

variable {ι : Type*} [Fintype ι]

variable (R N) in
/-- The coefficients of polynomial laws `M →ₚₗ[R] N` at the generic combination `∑ⱼ Xⱼ ⊗ mⱼ`:
`coeff m f k` is the coefficient of the monomial `Xᵏ` in `f (∑ⱼ Xⱼ ⊗ mⱼ)`, computed over the
polynomial ring `R[Xⱼ]`. -/
def coeff (m : ι → M) : (M →ₚₗ[R] N) →ₗ[R] (ι →₀ ℕ) →₀ N where
  toFun f := by
    classical
    exact TensorProduct.equivFinsuppOfBasisLeft (basisMonomials ι R)
      (f.toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j))
  map_add' f g := by simp [toFun_add_apply]
  map_smul' r f := by simp [toFun_smul]

/-- The coefficient of `Xᵏ` in `f (∑ⱼ Xⱼ ⊗ mⱼ)`, extracted by `MvPolynomial.lcoeff`. -/
theorem coeff_apply (m : ι → M) (f : M →ₚₗ[R] N) (k : ι →₀ ℕ) :
    coeff R N m f k = TensorProduct.lid R N ((lcoeff R k).rTensor N
      (f.toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j))) := by
  classical
  rw [coeff, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.equivFinsuppOfBasisLeft_apply]
  rfl

/-- The value of `f` at the generic combination `∑ⱼ Xⱼ ⊗ mⱼ` is `∑ₖ Xᵏ ⊗ coeff m f k`. -/
theorem toFun_sum_X_tmul (m : ι → M) (f : M →ₚₗ[R] N) :
    f.toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j) =
      (coeff R N m f).sum fun k n ↦ monomial k 1 ⊗ₜ[R] n := by
  classical
  have := (TensorProduct.equivFinsuppOfBasisLeft (basisMonomials ι R)).symm_apply_apply
    (f.toFun (MvPolynomial ι R) (∑ j, X j ⊗ₜ[R] m j))
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] at this
  simpa only [coeff, LinearMap.coe_mk, AddHom.coe_mk, coe_basisMonomials] using this.symm

/-- The value of a polynomial law on a finite sum of pure tensors, in terms of its coefficients:
`f (∑ⱼ sⱼ ⊗ mⱼ) = ∑ₖ (∏ⱼ sⱼ ^ kⱼ) ⊗ coeff m f k`, for a commutative `R`-algebra `S` in any
universe. -/
theorem toFun_sum_tmul_eq_coeff_sum (m : ι → M) (f : M →ₚₗ[R] N) {S : Type*} [CommSemiring S]
    [Algebra R S] (s : ι → S) :
    f.toFun S (∑ j, s j ⊗ₜ[R] m j) =
      (coeff R N m f).sum fun k n ↦ (∏ j, s j ^ k j) ⊗ₜ[R] n := by
  have hs : ∑ j, s j ⊗ₜ[R] m j =
      (aeval s).toLinearMap.rTensor M (∑ j, X j ⊗ₜ[R] m j) := by
    simp
  rw [hs, ← isCompat_apply, toFun_sum_X_tmul, map_finsuppSum]
  refine Finsupp.sum_congr fun k _ ↦ ?_
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]

/-- Change of variables for coefficients: if the generic combination of `m'` is obtained from
`∑ⱼ sⱼ ⊗ mⱼ` for polynomials `sⱼ`, then each coefficient of `f` at `m'` is a combination of the
coefficients of `f` at `m`. -/
theorem coeff_eq_sum_of_sum_tmul_eq {κ : Type*} [Fintype κ] (f : M →ₚₗ[R] N) (m : ι → M)
    (s : ι → MvPolynomial κ R) (m' : κ → M)
    (h : ∑ j, s j ⊗ₜ[R] m j = ∑ i, X i ⊗ₜ[R] m' i) (k : κ →₀ ℕ) :
    coeff R N m' f k =
      (coeff R N m f).sum fun l n ↦ (∏ j, s j ^ l j).coeff k • n := by
  rw [coeff_apply, ← h, toFun_sum_tmul_eq_coeff_sum, map_finsuppSum, map_finsuppSum]
  simp

/-- Coefficients are invariant under reindexing the family along an equivalence. -/
theorem coeff_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (m : ι → M) (f : M →ₚₗ[R] N)
    (k : ι →₀ ℕ) : coeff R N (m ∘ e) f (k.equivMapDomain e.symm) = coeff R N m f k := by
  classical
  symm
  rw [coeff_eq_sum_of_sum_tmul_eq f (m ∘ e) (fun j ↦ X (e j)) m
    (e.sum_comp fun i ↦ X i ⊗ₜ[R] m i)]
  have h (l : κ →₀ ℕ) : (∏ j, (X (e j) : MvPolynomial ι R) ^ l j).coeff k =
      if l = k.equivMapDomain e.symm then 1 else 0 := by
    rw [Fintype.prod_equiv e _ (fun i ↦ (X i : MvPolynomial ι R) ^ l (e.symm i)) (by simp),
      coeff_prod_univ_X_pow]
    congr 1
    simp only [Finsupp.ext_iff, Finsupp.equivMapDomain_apply, Equiv.symm_symm, eq_iff_iff]
    exact ⟨fun h j ↦ by simpa using h (e j), fun h i ↦ by simpa using h (e.symm i)⟩
  simp only [h, ite_smul, _root_.one_smul, _root_.zero_smul, Finsupp.sum_ite_self_eq']

/-- A vector with exponent zero does not contribute to a coefficient. -/
theorem coeff_optionElim_zero (a : M) (m : ι → M) (f : M →ₚₗ[R] N) (k : ι →₀ ℕ) :
    coeff R N (Option.elim' a m) f (k.optionElim 0) = coeff R N m f k := by
  classical
  symm
  rw [coeff_eq_sum_of_sum_tmul_eq f (Option.elim' a m) (Option.elim' 0 X) m
    (by simp [Fintype.sum_option])]
  have h (l : Option ι →₀ ℕ) :
      (∏ o, (Option.elim' 0 X o : MvPolynomial ι R) ^ l o).coeff k =
        if l = k.optionElim 0 then 1 else 0 := by
    rw [Fintype.prod_option]
    simp only [Option.elim'_none, Option.elim'_some]
    rcases Nat.eq_zero_or_pos (l none) with h0 | h0
    · rw [h0, pow_zero, one_mul, coeff_prod_univ_X_pow]
      congr 1
      simp [Finsupp.ext_iff, Option.forall, h0]
    · have hl : l ≠ k.optionElim 0 := by
        rintro rfl
        simp at h0
      simp [zero_pow h0.ne', hl]
  simp only [h, ite_smul, _root_.one_smul, _root_.zero_smul, Finsupp.sum_ite_self_eq']

/-- Scaling a vector with exponent `n` by `r` scales the coefficient by `r ^ n`. -/
theorem coeff_optionElim_smul (n : ℕ) (r : R) (a : M) (m : ι → M) (f : M →ₚₗ[R] N)
    (k : ι →₀ ℕ) :
    coeff R N (Option.elim' (r • a) m) f (k.optionElim n) =
      r ^ n • coeff R N (Option.elim' a m) f (k.optionElim n) := by
  classical
  set K : Option ι →₀ ℕ := k.optionElim n
  let s : Option ι → MvPolynomial (Option ι) R := Option.elim' (C r * X none) fun i ↦ X (some i)
  rw [coeff_eq_sum_of_sum_tmul_eq f (Option.elim' a m) s (Option.elim' (r • a) m)
    (by simp [s, Fintype.sum_option, ← smul_eq_C_mul, TensorProduct.smul_tmul])]
  have hs (l : Option ι →₀ ℕ) :
      ∏ o, s o ^ l o = C (r ^ l none) * ∏ o, (X o : MvPolynomial (Option ι) R) ^ l o := by
    simp only [s, Fintype.prod_option, Option.elim'_none, Option.elim'_some, mul_pow, map_pow,
      mul_assoc]
  have h (l : Option ι →₀ ℕ) : (∏ o, s o ^ l o).coeff K = if l = K then r ^ n else 0 := by
    rw [hs, coeff_C_mul, coeff_prod_univ_X_pow]
    by_cases hl : l = K
    · subst hl
      simp [K]
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hl, ite_eq_right_iff.mpr, mul_zero]
      exact fun h ↦ absurd (Finsupp.ext h) hl
  simp only [h, ite_smul, _root_.zero_smul]
  rw [Finsupp.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hmem, smul_zero]

/-- Two copies of the same vector, with exponents `x` and `y`, merge into one with exponent
`x + y`, at the cost of the binomial coefficient `(x + y).choose x`. -/
theorem coeff_optionElim_optionElim_self (x y : ℕ) (a : M) (m : ι → M) (f : M →ₚₗ[R] N)
    (k : ι →₀ ℕ) :
    coeff R N (Option.elim' a (Option.elim' a m)) f ((k.optionElim y).optionElim x) =
      (x + y).choose x • coeff R N (Option.elim' a m) f (k.optionElim (x + y)) := by
  classical
  let L : Option ι →₀ ℕ := k.optionElim (x + y)
  let s : Option ι → MvPolynomial (Option (Option ι)) R :=
    Option.elim' (X none + X (some none)) fun i ↦ X (some (some i))
  rw [coeff_eq_sum_of_sum_tmul_eq f (Option.elim' a m) s (Option.elim' a (Option.elim' a m))
    (by simp [s, Fintype.sum_option, TensorProduct.add_tmul, add_assoc])]
  set K : Option (Option ι) →₀ ℕ := (k.optionElim y).optionElim x
  have h (l : Option ι →₀ ℕ) :
      (∏ o, s o ^ l o).coeff K = if l = L then ((x + y).choose x : R) else 0 := by
    have hprod : ∏ o, s o ^ l o = ∑ q ∈ Finset.antidiagonal (l none), (l none).choose q.1 •
        ∏ o, (X o : MvPolynomial (Option (Option ι)) R) ^
          (Option.elim' q.1 (Option.elim' q.2 fun i ↦ l (some i)) o) := by
      rw [Fintype.prod_option]
      simp only [s, Option.elim'_none, Option.elim'_some]
      rw [(Commute.all _ _).add_pow', Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      simp [Fintype.prod_option, mul_assoc]
    have hcond (q : ℕ × ℕ) : (∀ o, Option.elim' q.1 (Option.elim' q.2 fun i ↦ l (some i)) o =
        K o) ↔ q = (x, y) ∧ ∀ i, l (some i) = k i := by
      simp [K, Option.forall, Prod.ext_iff, and_assoc]
    have hns (c : ℕ) (P : MvPolynomial (Option (Option ι)) R) :
        (c • P).coeff K = c • P.coeff K := by
      simpa using map_nsmul (coeffAddMonoidHom K) c P
    rw [hprod, coeff_sum]
    simp only [hns, coeff_prod_univ_X_pow, hcond, ite_and, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_antidiagonal, L, Finsupp.ext_iff, Option.forall,
      Finsupp.optionElim_apply_eq_elim, Option.elim_none, Option.elim_some, nsmul_eq_mul,
      mul_one]
    by_cases hxy : x + y = l none
    · simp [hxy, eq_comm]
    · simp [hxy, Ne.symm hxy]
  simp only [h, ite_smul, _root_.zero_smul]
  rw [Finsupp.sum_ite_eq']
  split_ifs with hmem
  · rw [Nat.cast_smul_eq_nsmul]
  · rw [Finsupp.notMem_support_iff.mp hmem, smul_zero]

/-- A vector `a + b` with exponent `n` splits into the vectors `a` and `b`, summed over the
exponent pairs in the antidiagonal of `n`, as in the divided-power binomial formula. -/
theorem coeff_optionElim_add (n : ℕ) (a b : M) (m : ι → M) (f : M →ₚₗ[R] N) (k : ι →₀ ℕ) :
    coeff R N (Option.elim' (a + b) m) f (k.optionElim n) =
      ∑ q ∈ Finset.antidiagonal n,
        coeff R N (Option.elim' a (Option.elim' b m)) f ((k.optionElim q.2).optionElim q.1) := by
  classical
  let L (q : ℕ × ℕ) : Option (Option ι) →₀ ℕ := (k.optionElim q.2).optionElim q.1
  let s : Option (Option ι) → MvPolynomial (Option ι) R :=
    Option.elim' (X none) (Option.elim' (X none) fun i ↦ X (some i))
  rw [coeff_eq_sum_of_sum_tmul_eq f (Option.elim' a (Option.elim' b m)) s
    (Option.elim' (a + b) m) (by simp [s, Fintype.sum_option, TensorProduct.tmul_add, add_assoc])]
  set K : Option ι →₀ ℕ := k.optionElim n
  have hs (l : Option (Option ι) →₀ ℕ) : ∏ o, s o ^ l o = ∏ o, (X o : MvPolynomial (Option ι) R) ^
      (Option.elim' (l none + l (some none)) (fun i ↦ l (some (some i))) o) := by
    simp [s, Fintype.prod_option, pow_add, mul_assoc]
  have h (l : Option (Option ι) →₀ ℕ) (c : N) :
      (∏ o, s o ^ l o).coeff K • c = ∑ q ∈ Finset.antidiagonal n, if l = L q then c else 0 := by
    rw [hs, coeff_prod_univ_X_pow]
    have hL (q : ℕ × ℕ) : l = L q ↔
        q = (l none, l (some none)) ∧ ∀ i, l (some (some i)) = k i := by
      simp [L, Finsupp.ext_iff, Option.forall, Prod.ext_iff, eq_comm, and_assoc]
    simp only [hL, ite_and, Finset.sum_ite_eq', Finset.mem_antidiagonal]
    simp only [K, Option.forall, Finsupp.optionElim_apply_eq_elim, Option.elim'_none,
      Option.elim'_some, Option.elim_none, Option.elim_some]
    split_ifs <;> simp_all
  simp only [Finsupp.sum, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Finset.sum_ite_eq', Finsupp.if_mem_support]

/-- A polynomial law is determined by its coefficients on families indexed by `Fin n`. -/
theorem ext_coeff {f g : M →ₚₗ[R] N}
    (h : ∀ (n : ℕ) (m : Fin n → M), coeff R N m f = coeff R N m g) : f = g := by
  ext S _ _ x
  rw [toFun'_eq_toFun, toFun'_eq_toFun]
  obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  rw [toFun_sum_tmul_eq_coeff_sum, toFun_sum_tmul_eq_coeff_sum, h]

/-- A law homogeneous of degree `d` has no coefficients outside total degree `d`. -/
theorem IsHomogeneousOfDegree.coeff_eq_zero {d : ℕ} {f : M →ₚₗ[R] N}
    (hf : f.IsHomogeneousOfDegree d) (m : ι → M) {k : ι →₀ ℕ} (hk : ∑ j, k j ≠ d) :
    coeff R N m f k = 0 := by
  classical
  -- Compare the coefficients of `Y ^ |k| Xᵏ` on both sides of `f (Y • x) = Y ^ d • f x`, over
  -- the polynomial ring `R[Xⱼ][Y]`, for `x = ∑ⱼ Xⱼ ⊗ mⱼ`.
  let Φ : Polynomial (MvPolynomial ι R) ⊗[R] N →ₗ[R] N :=
    TensorProduct.lid R N ∘ₗ ((lcoeff R k).restrictScalars R ∘ₗ
      (Polynomial.lcoeff (MvPolynomial ι R) (∑ j, k j)).restrictScalars R).rTensor N
  have hΦ (a : ι →₀ ℕ) (e : ℕ) (b : N) :
      Φ ((Polynomial.C (∏ j, X j ^ a j) * Polynomial.X ^ e) ⊗ₜ[R] b) =
        if a = k ∧ ∑ j, k j = e then b else 0 := by
    have hmon : ∏ j, (X j : MvPolynomial ι R) ^ a j = monomial a 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
    rw [hmon]
    simp only [Φ, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.restrictScalars_apply,
      Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp_all
  have hx := congrArg Φ (hf.toFun_smul (Polynomial.X : Polynomial (MvPolynomial ι R))
    (∑ j, Polynomial.C (X j) ⊗ₜ[R] m j))
  simp only [Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul,
    toFun_sum_tmul_eq_coeff_sum, Finsupp.smul_sum, map_finsuppSum] at hx
  have hL (a : ι →₀ ℕ) : ∏ j, (Polynomial.X * Polynomial.C (X j : MvPolynomial ι R)) ^ a j =
      Polynomial.C (∏ j, X j ^ a j) * Polynomial.X ^ ∑ j, a j := by
    rw [Finset.prod_congr rfl fun j _ ↦ mul_pow _ _ (a j), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, mul_comm, map_prod]
    simp only [map_pow]
  have hR (a : ι →₀ ℕ) : Polynomial.X ^ d * ∏ j, Polynomial.C (X j : MvPolynomial ι R) ^ a j =
      Polynomial.C (∏ j, X j ^ a j) * Polynomial.X ^ d := by
    rw [mul_comm, map_prod]
    simp only [map_pow]
  simp only [hL, hR, hΦ] at hx
  simp only [ite_and, hk, ite_false, ite_self] at hx
  simpa using hx

end Coeff

end PolynomialLaw
