/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Taylor

import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Polynomial.Taylor

/-!
# Depressed polynomials and their coprime splitting

A polynomial `p` of degree `m` over a field is *depressed* when its subleading coefficient
`p.nextCoeff` vanishes. When `m` is invertible, the Tschirnhaus shift `X ↦ X + r` with
`r = -p.nextCoeff / (m * p.leadingCoeff)` depresses `p`.

A monic depressed polynomial of invertible degree `m` that splits and is not `X ^ m` cannot be a
power `(X - a) ^ m` of a single linear factor: for `a ≠ 0` its subleading coefficient would be
`-m a ≠ 0`, and for `a = 0` it would be `X ^ m`. So it has a nonzero root `a` of multiplicity `r`
with `0 < r < m`, and `p = (X - a) ^ r * q` with `q` monic and coprime to `(X - a) ^ r`.

This is the factor-splitting input of the Newton–Puiseux algorithm: after normalization, the
reduction modulo `t` of a monic depressed polynomial over `K⟦t⟧` has this shape, and Hensel's lemma
lifts the coprime splitting (`Polynomial.Monic.exists_monic_mul_eq_of_nextCoeff_map_eq_zero` in
`TauCeti.RingTheory.PowerSeries.Hensel`).

## Main results

* `Polynomial.nextCoeff_taylor_neg_div_eq_zero`: the Tschirnhaus shift depresses a polynomial whose
  degree is invertible.
* `Polynomial.Monic.exists_isCoprime_mul_eq_of_nextCoeff_eq_zero`: a monic depressed polynomial
  that splits, has invertible degree and is not a power of `X` is a product of two coprime monic
  factors of positive degree.

## References

* H. Mannaa and T. Coquand, *Dynamic Newton–Puiseux Theorem*, arXiv:1304.6770, §1, for the
  centered polynomial and its coprime splitting in the Newton–Puiseux algorithm.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- The Tschirnhaus shift: if the degree `m` of `p` is invertible, then `p(X + r)` with
`r = -p.nextCoeff / (m * p.leadingCoeff)` has vanishing subleading coefficient. -/
theorem nextCoeff_taylor_neg_div_eq_zero {p : K[X]} (hp : (p.natDegree : K) ≠ 0) :
    (taylor (-p.nextCoeff / (p.natDegree * p.leadingCoeff)) p).nextCoeff = 0 := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 fun h ↦ hp (by simp [h])
  rw [nextCoeff_taylor]
  field_simp
  ring

/-- A monic polynomial `p` with vanishing subleading coefficient that splits, whose degree is
invertible, and which is not `X ^ p.natDegree`, factors as `p = g * h` with `g` and `h` monic,
coprime and of positive degree. -/
theorem Monic.exists_isCoprime_mul_eq_of_nextCoeff_eq_zero {p : K[X]} (hp : p.Monic)
    (hs : p.Splits) (hm : (p.natDegree : K) ≠ 0) (hnext : p.nextCoeff = 0)
    (hX : p ≠ X ^ p.natDegree) :
    ∃ g h : K[X], g.Monic ∧ h.Monic ∧ IsCoprime g h ∧ g * h = p ∧
      0 < g.natDegree ∧ 0 < h.natDegree := by
  have hp0 : p ≠ 0 := hp.ne_zero
  -- Some root of `p` is nonzero, since otherwise `p = X ^ p.natDegree`.
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ p.roots, a ≠ 0 := by
    by_contra! H
    refine hX ?_
    conv_lhs => rw [hs.eq_prod_roots_of_monic hp, Multiset.eq_replicate_of_mem H]
    simp [hs.natDegree_eq_card_roots]
  have hgh := pow_mul_divByMonic_rootMultiplicity_eq p a
  set r := p.rootMultiplicity a
  have hX_sub := monic_X_sub_C a
  have hdeg : ((X - C a) ^ r).natDegree = r := by simp
  have hg : ((X - C a) ^ r).Monic := hX_sub.pow r
  have hh : (p /ₘ (X - C a) ^ r).Monic := hg.of_mul_monic_left (by rwa [hgh])
  refine ⟨(X - C a) ^ r, p /ₘ (X - C a) ^ r, hg, hh, ?_, hgh, ?_, ?_⟩
  · refine IsCoprime.pow_left ((irreducible_X_sub_C a).coprime_iff_not_dvd.2 ?_)
    rw [dvd_iff_isRoot]
    exact eval_divByMonic_pow_rootMultiplicity_ne_zero a hp0
  · rw [hdeg]
    exact (rootMultiplicity_pos hp0).2 (isRoot_of_mem_roots ha)
  · -- If the cofactor were constant, `p = (X - a) ^ r` would have subleading coefficient `-r a`.
    by_contra! h0
    rw [Nat.le_zero, hh.natDegree_eq_zero] at h0
    rw [h0, mul_one] at hgh
    have hr : (r : K) ≠ 0 := by rwa [← hdeg, hgh]
    simp [← hgh, nextCoeff_pow hX_sub, hr, ha0] at hnext

end Polynomial
