/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.OreExtension.Basic
public import Mathlib.Data.Finset.Lattice.Fold

import Mathlib.Tactic

/-!
# Degrees and leading coefficients of Ore polynomials

The degree filtration of an Ore extension is preserved by multiplication. At the top degree,
the skew derivation contributes nothing: the coefficient of degree `m + n` in a product with
degree bounds `m` and `n` is `coeff p m * σ^[m] (coeff q n)`. Consequently an Ore extension
over a semiring without zero divisors has no zero divisors when its coefficient endomorphism is
injective. This is the leading-term calculation used in iterated Ore presentations.

The convention `natDegree 0 = 0` agrees with ordinary polynomials.

## References

* P. M. Cohn, *Free Rings and Their Relations*, second edition, Chapter 2.
-/

public noncomputable section

namespace TauCeti.OreExtension

variable {k R : Type*} [CommSemiring k] [Semiring R] [Algebra k R]
  {σ : R →ₐ[k] R} {δ : SigmaDerivation σ}

/-- The largest index of a nonzero coefficient, with value zero for the zero polynomial. -/
def natDegree (p : OreExtension σ δ) : ℕ := p.toFinsupp.support.sup id

/-- The coefficient at the natural degree. -/
def leadingCoeff (p : OreExtension σ δ) : R := coeff p p.natDegree

/-- The natural degree is the supremum of the coefficient support. -/
theorem natDegree_def (p : OreExtension σ δ) :
    p.natDegree = p.toFinsupp.support.sup id := (rfl)

/-- The leading coefficient is the coefficient at the natural degree. -/
theorem leadingCoeff_def (p : OreExtension σ δ) :
    p.leadingCoeff = coeff p p.natDegree := (rfl)

@[simp]
theorem natDegree_zero : natDegree (0 : OreExtension σ δ) = 0 := by
  simp [natDegree_def]

/-- A degree bound is equivalent to vanishing of all higher coefficients. -/
theorem natDegree_le_iff {p : OreExtension σ δ} {n : ℕ} :
    p.natDegree ≤ n ↔ ∀ i, n < i → coeff p i = 0 := by
  simp only [natDegree_def, Finset.sup_le_iff, id_eq, Finsupp.mem_support_iff,
    ← coeff_def]
  exact ⟨fun h i hi => by_contra fun hn => (not_le_of_gt hi) (h i hn),
    fun h i hi => le_of_not_gt fun hn => hi (h i hn)⟩

/-- Coefficients above the natural degree vanish. -/
theorem coeff_eq_zero_of_natDegree_lt {p : OreExtension σ δ} {n : ℕ}
    (h : p.natDegree < n) : coeff p n = 0 :=
  natDegree_le_iff.mp le_rfl n h

/-- A nonzero coefficient gives a lower bound on the natural degree. -/
theorem le_natDegree_of_ne_zero {p : OreExtension σ δ} {n : ℕ} (h : coeff p n ≠ 0) :
    n ≤ p.natDegree :=
  le_of_not_gt fun hn => h (coeff_eq_zero_of_natDegree_lt hn)

/-- A monomial has degree at most its exponent. -/
theorem natDegree_monomial_le (n : ℕ) (a : R) :
    natDegree (monomial (σ := σ) (δ := δ) n a) ≤ n := by
  refine natDegree_le_iff.mpr fun i hi => ?_
  simp [coeff_monomial, ne_of_lt hi]

/-- A monomial with nonzero coefficient has its indicated degree. -/
@[simp]
theorem natDegree_monomial (n : ℕ) {a : R} (ha : a ≠ 0) :
    natDegree (monomial (σ := σ) (δ := δ) n a) = n := by
  refine (natDegree_monomial_le n a).antisymm (le_natDegree_of_ne_zero ?_)
  simpa using ha

@[simp]
theorem natDegree_C (a : R) : natDegree (C (σ := σ) (δ := δ) a) = 0 := by
  simpa only [monomial_zero_left] using
    Nat.eq_zero_of_le_zero (natDegree_monomial_le (σ := σ) (δ := δ) 0 a)

@[simp]
theorem natDegree_one : natDegree (1 : OreExtension σ δ) = 0 := by
  simpa using natDegree_C (σ := σ) (δ := δ) (1 : R)

@[simp]
theorem natDegree_X_pow [Nontrivial R] (n : ℕ) :
    natDegree (X (σ := σ) (δ := δ) ^ n) = n := by
  rw [X_pow_eq_monomial, natDegree_monomial n one_ne_zero]

@[simp]
theorem natDegree_X [Nontrivial R] : natDegree (X (σ := σ) (δ := δ)) = 1 := by
  simpa using natDegree_X_pow (σ := σ) (δ := δ) 1

@[simp]
theorem leadingCoeff_eq_zero {p : OreExtension σ δ} : p.leadingCoeff = 0 ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    have hs : p.toFinsupp.support.Nonempty := Finsupp.support_nonempty_iff.mpr fun hz =>
      hp (toFinsupp_injective (by simpa using hz))
    have hm := Finset.sup_mem_of_nonempty (f := id) hs
    have hm' : coeff p p.natDegree ≠ 0 := by
      simpa [natDegree_def, coeff_def] using hm
    exact hm' h
  · rintro rfl
    simp [leadingCoeff_def]

@[simp]
theorem leadingCoeff_zero : leadingCoeff (0 : OreExtension σ δ) = 0 :=
  leadingCoeff_eq_zero.mpr rfl

/-- The leading coefficient of a monomial is its coefficient, including the zero monomial. -/
@[simp]
theorem leadingCoeff_monomial (n : ℕ) (a : R) :
    leadingCoeff (monomial (σ := σ) (δ := δ) n a) = a := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [leadingCoeff_def, natDegree_monomial n ha]

@[simp]
theorem leadingCoeff_C (a : R) : leadingCoeff (C (σ := σ) (δ := δ) a) = a := by
  simpa only [monomial_zero_left] using leadingCoeff_monomial (σ := σ) (δ := δ) 0 a

@[simp]
theorem leadingCoeff_one : leadingCoeff (1 : OreExtension σ δ) = 1 := by
  simpa using leadingCoeff_C (σ := σ) (δ := δ) (1 : R)

@[simp]
theorem leadingCoeff_X_pow (n : ℕ) :
    leadingCoeff (X (σ := σ) (δ := δ) ^ n) = 1 := by
  rw [X_pow_eq_monomial, leadingCoeff_monomial]

@[simp]
theorem leadingCoeff_X : leadingCoeff (X (σ := σ) (δ := δ)) = 1 := by
  simpa using leadingCoeff_X_pow (σ := σ) (δ := δ) 1

/-- Adding Ore polynomials cannot increase the largest of their degree bounds. -/
theorem natDegree_add_le (p q : OreExtension σ δ) :
    (p + q).natDegree ≤ max p.natDegree q.natDegree := by
  refine natDegree_le_iff.mpr fun n hn => ?_
  simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_left _ _) hn),
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_right _ _) hn)]

/-- Left multiplication by the variable raises a degree bound by at most one. -/
theorem natDegree_X_mul_le (p : OreExtension σ δ) :
    (X * p).natDegree ≤ p.natDegree + 1 := by
  refine natDegree_le_iff.mpr fun n hn => ?_
  cases n with
  | zero => omega
  | succ n =>
    rw [coeff_X_mul_succ, coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega), map_zero, map_zero, add_zero]

/-- Left multiplication by `Xᵐ` raises a degree bound by at most `m`. -/
theorem natDegree_X_pow_mul_le (p : OreExtension σ δ) (m : ℕ) :
    (X ^ m * p).natDegree ≤ m + p.natDegree := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc]
    exact (natDegree_X_mul_le _).trans (by omega)

/-- At the shifted top degree only the iterated coefficient endomorphism contributes. -/
theorem coeff_X_pow_mul_add (p : OreExtension σ δ) (m n : ℕ) (hp : p.natDegree ≤ n) :
    coeff (X ^ m * p) (m + n) = (σ : R → R)^[m] (coeff p n) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : (X ^ m * p).natDegree < m + n + 1 :=
      lt_of_le_of_lt (natDegree_X_pow_mul_le p m) (by omega)
    rw [pow_succ', mul_assoc, Nat.add_right_comm m 1 n, coeff_X_mul_succ, ih,
      coeff_eq_zero_of_natDegree_lt h, map_zero, add_zero, Function.iterate_succ_apply']

/-- Multiplication preserves the sum of the degree bounds, without injectivity assumptions. -/
theorem natDegree_mul_le (p q : OreExtension σ δ) :
    (p * q).natDegree ≤ p.natDegree + q.natDegree := by
  refine natDegree_le_iff.mpr fun n hn => ?_
  rw [← sum_monomial_eq p, Finset.sum_mul, finsetSum_coeff]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i ≤ p.natDegree :=
    le_natDegree_of_ne_zero (by simpa only [coeff_def] using Finsupp.mem_support_iff.mp hi)
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_X_pow_mul_le q i) (by omega)),
    mul_zero]

/-- The coefficient at the sum of two degree bounds in an Ore product. -/
theorem coeff_mul_add_eq_of_natDegree_le {p q : OreExtension σ δ} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    coeff (p * q) (m + n) = coeff p m * (σ : R → R)^[m] (coeff q n) := by
  conv_lhs => rw [← sum_monomial_eq p, Finset.sum_mul, finsetSum_coeff]
  calc
    _ = coeff (monomial m (coeff p m) * q) (m + n) := by
      apply Finset.sum_eq_single m
      · intro i hi him
        have hi' : i ≤ m := (le_natDegree_of_ne_zero (by
          simpa only [coeff_def] using Finsupp.mem_support_iff.mp hi)).trans hp
        rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul,
          coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (natDegree_X_pow_mul_le q i) (by omega)), mul_zero]
      · intro hm
        have hm' : coeff p m = 0 := by
          simpa only [coeff_def] using Finsupp.notMem_support_iff.mp hm
        rw [hm', map_zero, zero_mul, coeff_zero]
    _ = _ := by
      rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul_add q m n hq]

/-- The coefficient at the sum of the natural degrees is the twisted leading product. -/
theorem coeff_mul_degree_add_degree (p q : OreExtension σ δ) :
    coeff (p * q) (p.natDegree + q.natDegree) =
      p.leadingCoeff * (σ : R → R)^[p.natDegree] q.leadingCoeff :=
  coeff_mul_add_eq_of_natDegree_le le_rfl le_rfl

section NoZeroDivisors

variable [NoZeroDivisors R]

/-- An Ore product has additive natural degree if both factors are nonzero and the coefficient
endomorphism is injective. -/
theorem natDegree_mul (hσ : Function.Injective σ) {p q : OreExtension σ δ}
    (hp : p ≠ 0) (hq : q ≠ 0) : (p * q).natDegree = p.natDegree + q.natDegree := by
  refine (natDegree_mul_le p q).antisymm (le_natDegree_of_ne_zero ?_)
  rw [coeff_mul_degree_add_degree]
  refine mul_ne_zero (leadingCoeff_eq_zero.not.mpr hp) ?_
  exact fun h => hq (leadingCoeff_eq_zero.mp
    ((hσ.iterate _).eq_iff.mp (h.trans (iterate_map_zero σ _).symm)))

/-- The leading coefficient of a product over a semiring without zero divisors. -/
theorem leadingCoeff_mul (hσ : Function.Injective σ) (p q : OreExtension σ δ) :
    (p * q).leadingCoeff = p.leadingCoeff * (σ : R → R)^[p.natDegree] q.leadingCoeff := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq, iterate_map_zero]
  rw [leadingCoeff_def, natDegree_mul hσ hp hq, coeff_mul_degree_add_degree]

/-- An injective coefficient endomorphism preserves absence of zero divisors in an Ore
extension. The skew derivation is arbitrary. -/
theorem noZeroDivisors (hσ : Function.Injective σ) : NoZeroDivisors (OreExtension σ δ) where
  eq_zero_or_eq_zero_of_mul_eq_zero {p q} hpq := by
    by_cases hp : p = 0
    · exact Or.inl hp
    refine Or.inr ?_
    have ht := congrArg (fun r => coeff r (p.natDegree + q.natDegree)) hpq
    rw [coeff_mul_degree_add_degree, coeff_zero] at ht
    have hq := (mul_eq_zero.mp ht).resolve_left (leadingCoeff_eq_zero.not.mpr hp)
    exact leadingCoeff_eq_zero.mp
      ((hσ.iterate _).eq_iff.mp (hq.trans (iterate_map_zero σ _).symm))

end NoZeroDivisors

/-- An Ore extension of a domain by an injective endomorphism is a domain. -/
theorem isDomain {S : Type*} [Ring S] [Algebra k S] {τ : S →ₐ[k] S}
    {ε : SigmaDerivation τ} [IsDomain S] (hτ : Function.Injective τ) :
    IsDomain (OreExtension τ ε) := by
  let := noZeroDivisors (δ := ε) hτ
  exact NoZeroDivisors.to_isDomain _

end TauCeti.OreExtension
