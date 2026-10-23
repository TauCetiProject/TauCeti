/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.FieldTheory.Normal.Closure
import TauCeti.NumberTheory.Transcendental.Lindemann.Galois

/-!
# The Lindemann–Weierstrass theorem

This file proves the Lindemann–Weierstrass theorem for algebraic numbers, in the two classical
forms. Here the field of algebraic numbers is `integralClosure ℚ ℂ`.

* `linearIndependent_exp`: the exponentials of pairwise distinct algebraic numbers are linearly
  independent over the algebraic numbers (Baker's form of the theorem).
* `algebraicIndependent_exp`: the exponentials of `ℚ`-linearly independent algebraic numbers are
  algebraically independent over the algebraic numbers. The hypothesis is stated as linear
  independence over `ℕ`, which for the `ℚ`-vector space of algebraic numbers is equivalent to
  linear independence over `ℚ`. It says exactly that distinct monomials
  `∏ (exp uᵢ) ^ mᵢ = exp (∑ mᵢ uᵢ)` have distinct exponents, so that the first form applies.

Both are deduced from the injectivity of exponential evaluation over a number field that is
Galois over `ℚ` (`LindemannWeierstrass.expEval_injective`), in the form of linear independence of
exponentials (`LindemannWeierstrass.linearIndependent_exp_algebraMap`): the finitely many exponents
and coefficients of a given linear relation lie in such a field
(`exists_isGalois_superset_of_isAlgClosed`).

## References

* J.-H. Evertse, *Diophantine Approximation* (2019), ch. 4, §4.2, Theorem 4.8, its deduction from
  Theorem 4.11, and Corollary 4.10.
* Y. Zhao, formalization of the Lindemann–Weierstrass theorem in Lean, `Basic.lean`, theorems
  `linearIndependent_exp` and `algebraicIndependent_exp`, whose statements are followed here.
-/

public section

open Complex

namespace TauCeti

/-- **The Lindemann–Weierstrass theorem**, in Baker's form. The exponentials of pairwise distinct
algebraic numbers are linearly independent over the field `integralClosure ℚ ℂ` of algebraic
numbers. -/
theorem linearIndependent_exp {ι : Type*} (u : ι → integralClosure ℚ ℂ) (u_inj : u.Injective) :
    LinearIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i) := by
  classical
  refine linearIndependent_iff'.2 fun s g hg i hi ↦ ?_
  -- The exponents `u j` and the coefficients `g j`, `j ∈ s`, lie in a finite Galois subfield `K`
  -- of `ℂ`.
  set T : Set ℂ := ↑((s.image fun j ↦ (u j : ℂ)) ∪ s.image fun j ↦ (g j : ℂ))
  obtain ⟨K, hK, hKgal, hTK⟩ := exists_isGalois_superset_of_isAlgClosed (F := ℚ) T.toFinite
    fun t ht ↦ by
      simp only [T, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe] at ht
      rcases ht with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩
      exacts [(u j).2.isAlgebraic, (g j).2.isAlgebraic]
  have : NumberField K := { }
  have hu (j : s) : (u j : ℂ) ∈ K :=
    hTK (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ j.2)))
  have hg' (j : s) : (g j : ℂ) ∈ K :=
    hTK (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ j.2)))
  -- Over `K`, the exponentials `exp (u j)`, `j ∈ s`, are linearly independent.
  have hind : LinearIndependent K fun j : s ↦ exp (u j) := by
    have := LindemannWeierstrass.linearIndependent_exp_algebraMap.comp
      (fun j : s ↦ (⟨u j, hu j⟩ : K)) fun j k hjk ↦
        Subtype.ext (u_inj (Subtype.ext congr(($hjk : ℂ))))
    simpa only [Function.comp_def, IntermediateField.algebraMap_apply] using this
  have h := Fintype.linearIndependent_iff.1 hind (fun j ↦ ⟨g j, hg' j⟩) (by
    simpa only [← s.sum_coe_sort, IntermediateField.smul_def, Subalgebra.smul_def] using hg)
    ⟨i, hi⟩
  exact Subtype.ext congr(($h : ℂ))

/-- **The Lindemann–Weierstrass theorem**, algebraic independence form. If the algebraic numbers
`u i` are linearly independent over `ℕ` (equivalently, over `ℚ`), then their exponentials are
algebraically independent over the field `integralClosure ℚ ℂ` of algebraic numbers. -/
theorem algebraicIndependent_exp {ι : Type*} (u : ι → integralClosure ℚ ℂ)
    (hu : LinearIndependent ℕ u) :
    AlgebraicIndependent (integralClosure ℚ ℂ) fun i ↦ exp (u i) := by
  classical
  refine algebraicIndependent_iff.2 fun p hp ↦ ?_
  -- The monomial `∏ exp (u i) ^ m i` is the exponential of `∑ m i • u i`, and distinct exponents
  -- `m` give distinct values of this sum.
  have hlin := linearIndependent_iff'.1 (linearIndependent_exp _ hu) p.support
    (fun m ↦ p.coeff m) (by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq] at hp
      refine Eq.trans (Finset.sum_congr rfl fun m _ ↦ ?_) hp
      simp [Finsupp.linearCombination_apply, Finsupp.sum, exp_sum, exp_nat_mul,
        Subalgebra.smul_def])
  by_contra hp0
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hp0
  exact hm (hlin m (MvPolynomial.mem_support_iff.2 hm))

end TauCeti
