/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basic
public import TauCeti.RingTheory.DividedPowers.Associative
public import TauCeti.Algebra.Module.Rat
public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.NoncommRing

/-!
# PBW leading terms of Cartan binomials

The binomial generator `Ring.choose (ι h) n` has the same leading PBW term as the divided
power `(ι h) ^ n / n!`. The difference has strictly smaller degree, with the preceding step
in degree zero taken to be bottom. This comparison persists in ordered products and between
arbitrary filtered left and right factors. In particular it applies to the toral block of
an ordered negative-root, toral, positive-root product.

These statements are rational filtered comparisons. They do not identify an integral span
with the Kostant form, assert integral straightening, or require the supplied Lie vectors to
commute. They supply the leading-term calculation used to compare mixed binomial/divided-power
monomials with PBW monomials.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§17 and 26.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι ℚ (L := L)

/-- The factorial multiple of a Cartan binomial differs from the corresponding ordinary
power only in strictly smaller PBW degree. -/
theorem factorial_smul_ringChoose_ι_sub_pow_mem_pbwFiltrationPrevious (x : L) (n : ℕ) :
    (n.factorial : ℚ) • Ring.choose (ι x) n - (ι x) ^ n ∈
      pbwFiltrationPrevious ℚ L n := by
  have hpow (k : ℕ) : (ι x) ^ k ∈ pbwFiltration ℚ L k := by
    simpa using prod_map_ι_mem_pbwFiltration ℚ L (l := List.replicate k x) (by simp)
  have hpoch (k : ℕ) : (descPochhammer ℤ k).smeval (ι x) =
      (k.factorial : ℚ) • Ring.choose (ι x) k := by
    simpa only [Nat.cast_smul_eq_nsmul] using Ring.descPochhammer_eq_factorial_smul_choose (ι x) k
  rw [← hpoch]
  induction n with
  | zero => simp [descPochhammer_zero]
  | succ n ih =>
    rw [descPochhammer_succ_right, Polynomial.smeval_mul,
      Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_succ,
      pbwFiltrationPrevious_succ]
    have hdrop := mul_mem_pbwFiltrationPrevious_left ℚ L ih (ι_mem_pbwFiltration_one ℚ L x)
    rw [pbwFiltrationPrevious_succ] at hdrop
    have htop : (descPochhammer ℤ n).smeval (ι x) ∈ pbwFiltration ℚ L n := by
      have hle : pbwFiltrationPrevious ℚ L n ≤ pbwFiltration ℚ L n := by
        rw [pbwFiltrationPrevious_def, pbwFiltration_def]
        exact Algebra.wordFiltrationPrevious_le _ n
      simpa only [sub_add_cancel] using (pbwFiltration ℚ L n).add_mem (hle ih) (hpow n)
    have hscalar := mul_mem_pbwFiltration ℚ L htop
      (algebraMap_mem_pbwFiltration ℚ L (n : ℚ) 0)
    simp only [add_zero, map_natCast] at hscalar
    simp only [pow_zero, nsmul_eq_mul, mul_one]
    convert (pbwFiltration ℚ L n).sub_mem hdrop hscalar using 1; noncomm_ring

/-- A Cartan binomial lies in the PBW filtration step given by its lower index. -/
theorem ringChoose_ι_mem_pbwFiltration (x : L) (n : ℕ) :
    Ring.choose (ι x) n ∈ pbwFiltration ℚ L n := by
  have hpow : (ι x) ^ n ∈ pbwFiltration ℚ L n := by
    simpa using prod_map_ι_mem_pbwFiltration ℚ L (l := List.replicate n x) (by simp)
  have hle : pbwFiltrationPrevious ℚ L n ≤ pbwFiltration ℚ L n := by
    rw [pbwFiltrationPrevious_def, pbwFiltration_def]
    exact Algebra.wordFiltrationPrevious_le _ n
  have h := hle (factorial_smul_ringChoose_ι_sub_pow_mem_pbwFiltrationPrevious x n)
  have hs := (pbwFiltration ℚ L n).add_mem h hpow
  rw [sub_add_cancel] at hs
  have hi := (pbwFiltration ℚ L n).smul_mem ((n.factorial : ℚ)⁻¹) hs
  simpa [smul_smul, Nat.factorial_ne_zero] using hi

/-- An ordered product of Cartan binomials has PBW degree at most the sum of its indices. -/
theorem list_prod_ringChoose_ι_mem_pbwFiltration (l : List (L × ℕ)) :
    (l.map (fun p ↦ Ring.choose (ι p.1) p.2)).prod ∈
      pbwFiltration ℚ L (l.map Prod.snd).sum := by
  induction l with
  | nil => simpa using one_mem_pbwFiltration ℚ L 0
  | cons p l ih =>
    simpa only [List.map_cons, List.prod_cons, List.sum_cons] using
      mul_mem_pbwFiltration ℚ L (ringChoose_ι_mem_pbwFiltration p.1 p.2) ih

/-- A Cartan binomial and a divided power have the same leading PBW term. -/
theorem ringChoose_ι_sub_dividedPower_mem_pbwFiltrationPrevious (x : L) (n : ℕ) :
    Ring.choose (ι x) n - Associative.dividedPower n (ι x) ∈
      pbwFiltrationPrevious ℚ L n := by
  have h := (pbwFiltrationPrevious ℚ L n).smul_mem ((n.factorial : ℚ)⁻¹)
    (factorial_smul_ringChoose_ι_sub_pow_mem_pbwFiltrationPrevious x n)
  simpa [smul_sub, smul_smul, Nat.factorial_ne_zero, Associative.dividedPower_def] using h

/-- An ordered product of divided powers has PBW degree at most the sum of its exponents. -/
theorem list_prod_dividedPower_ι_mem_pbwFiltration (l : List (L × ℕ)) :
    (l.map (fun p ↦ Associative.dividedPower p.2 (ι p.1))).prod ∈
      pbwFiltration ℚ L (l.map Prod.snd).sum := by
  induction l with
  | nil => simpa using one_mem_pbwFiltration ℚ L 0
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    apply mul_mem_pbwFiltration ℚ L _ ih
    rw [Associative.dividedPower_def]
    apply Submodule.smul_mem
    simpa using prod_map_ι_mem_pbwFiltration ℚ L
      (l := List.replicate p.2 p.1) (by simp)

/-- Replacing every binomial in an ordered toral block by its divided power changes the product
only in strictly smaller total PBW degree. No commutativity of the Lie vectors is required. -/
theorem list_prod_ringChoose_ι_sub_list_prod_dividedPower_mem_pbwFiltrationPrevious
    (l : List (L × ℕ)) :
    (l.map (fun p ↦ Ring.choose (ι p.1) p.2)).prod -
        (l.map (fun p ↦ Associative.dividedPower p.2 (ι p.1))).prod ∈
      pbwFiltrationPrevious ℚ L (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hleft := mul_mem_pbwFiltrationPrevious_left ℚ L
      (ringChoose_ι_sub_dividedPower_mem_pbwFiltrationPrevious p.1 p.2)
      (list_prod_dividedPower_ι_mem_pbwFiltration l)
    have hright := mul_mem_pbwFiltrationPrevious_right ℚ L
      (ringChoose_ι_mem_pbwFiltration p.1 p.2) ih
    convert (pbwFiltrationPrevious ℚ L (p.2 + (l.map Prod.snd).sum)).add_mem
      hleft hright using 1; noncomm_ring

/-- The leading-term replacement of the toral block remains valid inside a mixed filtered
product, including the negative-root and positive-root blocks of a Kostant monomial. -/
theorem mul_list_prod_ringChoose_ι_mul_sub_mem_pbwFiltrationPrevious
    (l : List (L × ℕ)) {a c : U} {r s : ℕ}
    (ha : a ∈ pbwFiltration ℚ L r) (hc : c ∈ pbwFiltration ℚ L s) :
    a * (l.map (fun p ↦ Ring.choose (ι p.1) p.2)).prod * c -
        a * (l.map (fun p ↦ Associative.dividedPower p.2 (ι p.1))).prod * c ∈
      pbwFiltrationPrevious ℚ L (r + (l.map Prod.snd).sum + s) := by
  have h := mul_mem_pbwFiltrationPrevious_left ℚ L
    (mul_mem_pbwFiltrationPrevious_right ℚ L ha
      (list_prod_ringChoose_ι_sub_list_prod_dividedPower_mem_pbwFiltrationPrevious l)) hc
  simpa only [mul_sub, sub_mul] using h

end

end TauCeti.UniversalEnvelopingAlgebra
