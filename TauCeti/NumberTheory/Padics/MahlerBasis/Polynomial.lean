/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MahlerBasis.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Polynomial functions in Mahler coordinates

The Mahler coefficient of `x ↦ x ^ k` at index `n` is `n! S(k,n)`, where `S` is the
Stirling number of the second kind. Consequently polynomial functions have finite Mahler
expansions, and their continuous sup norm can be computed as a finite maximum of explicit
linear combinations of their monomial coefficients. This maximum need not be the monomial
Gauss norm.

The monomial formula also holds for `x ↦ x ^ k • a` with values in any complete ultrametric
module with contractive `ℤ_p` action, including torsion modules. No division by factorials is
used. We use Mathlib's `Nat.pow_eq_sum_stirlingSecond_mul_descFactorial` for the change from
powers to descending factorials, and `PadicInt.mahlerEquiv` for the coefficient isometry.
-/

public section

open scoped ZeroAtInfty
open ZeroAtInftyContinuousMap

variable {p : ℕ} [Fact p.Prime]

namespace TauCeti

/-- The finite Mahler expansion of a monomial, with Stirling coefficients. -/
theorem id_pow_eq_sum_stirlingSecond_smul_mahler (k : ℕ) :
    (ContinuousMap.id ℤ_[p]) ^ k = ∑ n ∈ Finset.range (k + 1),
      (n.factorial * k.stirlingSecond n) • mahler n := by
  apply DFunLike.coe_injective
  apply PadicInt.denseRange_natCast.equalizer (map_continuous _) (map_continuous _)
  funext m
  have h := congrArg (Nat.cast : ℕ → ℤ_[p])
    (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial m k)
  simpa [mahler_natCast_eq, Nat.descFactorial_eq_factorial_mul_choose,
    mul_assoc, mul_comm, mul_left_comm]
    using h

end TauCeti

namespace PadicInt

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]

/-- The finite Mahler expansion of a module-valued monomial. -/
theorem pow_smul_eq_sum_mahlerTerm (k : ℕ) (a : E) :
    (ContinuousMap.id ℤ_[p]) ^ k • ContinuousMap.const ℤ_[p] a =
      ∑ n ∈ Finset.range (k + 1), mahlerTerm ((n.factorial * k.stirlingSecond n) • a) n := by
  rw [TauCeti.id_pow_eq_sum_stirlingSecond_smul_mahler, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro n hn
  apply ContinuousMap.ext
  intro x
  simp only [ContinuousMap.smul_apply', ContinuousMap.smul_apply, ContinuousMap.const_apply,
    mahlerTerm_apply]
  rw [smul_assoc, smul_comm (n.factorial * k.stirlingSecond n) ((mahler n) x) a]

variable [IsUltrametricDist E] [CompleteSpace E]

/-- The Mahler coordinates of a module-valued monomial are the Stirling coefficients,
acting on its value `a`. This includes coordinates beyond the degree, where `S(k,n) = 0`. -/
@[simp]
theorem mahlerEquiv_pow_smul_apply (k n : ℕ) (a : E) :
    mahlerEquiv E ((ContinuousMap.id ℤ_[p]) ^ k • ContinuousMap.const ℤ_[p] a) n =
      (n.factorial * k.stirlingSecond n) • a := by
  rw [pow_smul_eq_sum_mahlerTerm]
  simp only [map_sum, mahlerEquiv_mahlerTerm, sum_single_apply]
  by_cases hn : n < k + 1
  · simp [hn]
  · simp [hn, Nat.stirlingSecond_eq_zero_of_lt (by omega : k < n)]

/-- The Mahler coefficient of the scalar monomial `x ^ k` is `n! S(k,n)`. -/
@[simp]
theorem mahlerEquiv_id_pow_apply (k n : ℕ) :
    mahlerEquiv ℤ_[p] ((ContinuousMap.id ℤ_[p]) ^ k) n =
      (n.factorial * k.stirlingSecond n : ℕ) := by
  simpa using mahlerEquiv_pow_smul_apply (p := p) k n (1 : ℤ_[p])

end PadicInt

namespace Polynomial

/-- The Mahler coefficients of a polynomial function are the factorial-weighted Stirling
transform of its monomial coefficients. -/
theorem mahlerEquiv_toContinuousMap_apply (P : ℤ_[p][X]) (n : ℕ) :
    PadicInt.mahlerEquiv ℤ_[p] P.toContinuousMap n =
      ∑ k ∈ P.support, P.coeff k * (n.factorial * k.stirlingSecond n : ℕ) := by
  have hP : P.toContinuousMap = ∑ k ∈ P.support,
      P.coeff k • (ContinuousMap.id ℤ_[p]) ^ k := by
    apply ContinuousMap.ext
    intro x
    simpa [Polynomial.sum, ContinuousMap.smul_apply] using P.eval_eq_sum (x := x)
  rw [hP]
  simp [PadicInt.mahlerEquiv_id_pow_apply]

/-- A polynomial has no Mahler coefficients above its degree, including the zero polynomial. -/
theorem mahlerEquiv_toContinuousMap_eq_zero_of_natDegree_lt (P : ℤ_[p][X]) {n : ℕ}
    (hn : P.natDegree < n) : PadicInt.mahlerEquiv ℤ_[p] P.toContinuousMap n = 0 := by
  rw [mahlerEquiv_toContinuousMap_apply]
  exact Finset.sum_eq_zero fun k hk ↦ by
    simp [Nat.stirlingSecond_eq_zero_of_lt ((le_natDegree_of_mem_supp k hk).trans_lt hn)]

/-- The continuous sup norm of a polynomial is the finite maximum of the norms of its
factorial-weighted Stirling coefficients, not in general of its monomial coefficients. -/
theorem nnnorm_toContinuousMap_eq_sup_stirlingSecond (P : ℤ_[p][X]) :
    ‖P.toContinuousMap‖₊ = (Finset.range (P.natDegree + 1)).sup fun n ↦
      ‖∑ k ∈ P.support, P.coeff k * (n.factorial * k.stirlingSecond n : ℕ)‖₊ := by
  have hfinite : PadicInt.mahlerEquiv ℤ_[p] P.toContinuousMap =
      ∑ n ∈ Finset.range (P.natDegree + 1),
        single n (PadicInt.mahlerEquiv ℤ_[p] P.toContinuousMap n) := by
    ext n
    rw [sum_single_apply]
    by_cases hn : n < P.natDegree + 1
    · simp [hn]
    · simp [hn, mahlerEquiv_toContinuousMap_eq_zero_of_natDegree_lt P (by omega :
        P.natDegree < n)]
  rw [← (PadicInt.mahlerEquiv ℤ_[p]).nnnorm_map P.toContinuousMap, hfinite,
    nnnorm_sum_single]
  simp only [mahlerEquiv_toContinuousMap_apply]

end Polynomial

-- The square has Mahler expansion `binom(x,1) + 2 binom(x,2)`.
example : PadicInt.mahlerEquiv ℤ_[p] ((ContinuousMap.id ℤ_[p]) ^ 2) =
    single 1 1 + single 2 2 := by
  ext n
  rw [PadicInt.mahlerEquiv_id_pow_apply]
  by_cases h : n ≤ 2
  · interval_cases n <;> norm_num [Nat.stirlingSecond, single_apply]
  · simp [Nat.stirlingSecond_eq_zero_of_lt (by omega : 2 < n),
      show n ≠ 1 by omega, show n ≠ 2 by omega]
