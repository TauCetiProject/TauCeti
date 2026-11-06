/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Extension
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Splitting a real polynomial along the imaginary axis

A nonzero real polynomial `p` factors as `p = f * g`, where every complex root of `f` lies in the
open left half-plane `re z < 0` and every complex root of `g` lies in the closed right half-plane
`0 ≤ re z`. The two factors have no common complex root, so they are coprime.

The factors are products of the monic irreducible real factors of `p`. An irreducible real
polynomial has degree one or two, and its complex roots are a real number or a pair of complex
conjugates, so they all have the same real part
(`Polynomial.re_eq_of_irreducible_of_aeval_eq_zero`); each irreducible factor therefore goes
entirely into `f` or entirely into `g`.

For an operator `A` annihilated by `p`, a Bézout identity `a * f + b * g = 1` turns this
factorization into the idempotent `(b * g)(A)`, which commutes with `A` and satisfies
`f(A) (b * g)(A) = 0` and `g(A) (a * f)(A) = 0`. This is how the stable and unstable parts of a
hyperbolic linear flow are separated in `TauCeti.Analysis.ODE.ExponentialDichotomy.Hyperbolic`.

## Main results

* `Polynomial.re_eq_of_irreducible_of_aeval_eq_zero`: all complex roots of an irreducible real
  polynomial have the same real part.
* `Polynomial.exists_eq_mul_isCoprime_re_neg_re_nonneg`: a nonzero real polynomial is the product
  of two coprime real polynomials whose complex roots lie in the open left half-plane and the
  closed right half-plane respectively.
-/

public section

open Polynomial

namespace Polynomial

/-- All complex roots of an irreducible real polynomial have the same real part: they are either a
single real root or a pair of complex conjugate roots. -/
theorem re_eq_of_irreducible_of_aeval_eq_zero {p : ℝ[X]} (hp : Irreducible p) {z w : ℂ}
    (hz : aeval z p = 0) (hw : aeval w p = 0) : w.re = z.re := by
  have hw' : aeval w (minpoly ℝ z) = 0 := by
    rw [← minpoly.eq_of_irreducible hp hz, map_mul, hw, zero_mul]
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
    (fun s : ℂ ↦ ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hw'
  rcases Complex.real_algHom_eq_id_or_conj φ with rfl | rfl <;> simp [← hφ]

/-- **Splitting a real polynomial along the imaginary axis.** A nonzero real polynomial is the
product `f * g` of two coprime real polynomials, where the complex roots of `f` have negative real
part and those of `g` have nonnegative real part. -/
theorem exists_eq_mul_isCoprime_re_neg_re_nonneg {p : ℝ[X]} (hp : p ≠ 0) :
    ∃ f g : ℝ[X], p = f * g ∧ IsCoprime f g ∧ (∀ z : ℂ, aeval z f = 0 → z.re < 0) ∧
      ∀ z : ℂ, aeval z g = 0 → 0 ≤ z.re := by
  classical
  set S := UniqueFactorizationMonoid.normalizedFactors p
  set P : ℝ[X] → Prop := fun q ↦ ∀ z : ℂ, aeval z q = 0 → z.re < 0
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hp
  have hroot {s : Multiset ℝ[X]} {z : ℂ} (h : aeval z s.prod = 0) : ∃ q ∈ s, aeval z q = 0 := by
    rwa [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at h
  have hf (z : ℂ) (hz : aeval z ((S.filter P).prod * (u : ℝ[X])) = 0) : z.re < 0 := by
    rw [map_mul, mul_eq_zero] at hz
    rcases hz with hz | hz
    · obtain ⟨q, hq, hqz⟩ := hroot hz
      exact (Multiset.mem_filter.1 hq).2 z hqz
    · exact absurd hz (u.isUnit.map (aeval z)).ne_zero
  have hg (z : ℂ) (hz : aeval z (S.filter (fun q ↦ ¬ P q)).prod = 0) : 0 ≤ z.re := by
    obtain ⟨q, hq, hqz⟩ := hroot hz
    obtain ⟨hqS, hqP⟩ := Multiset.mem_filter.1 hq
    obtain ⟨w, hw, hwre⟩ := not_forall₂.1 hqP
    rw [re_eq_of_irreducible_of_aeval_eq_zero
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor q hqS) hw hqz]
    exact not_lt.1 hwre
  refine ⟨(S.filter P).prod * (u : ℝ[X]), (S.filter (fun q ↦ ¬ P q)).prod, ?_, ?_, hf, hg⟩
  · rw [← hu, ← Multiset.prod_filter_mul_prod_filter_not P]
    ring
  · refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ _ _).2 fun z ↦ ?_
    by_contra! h
    exact (hf z h.1).not_ge (hg z h.2)

end Polynomial
