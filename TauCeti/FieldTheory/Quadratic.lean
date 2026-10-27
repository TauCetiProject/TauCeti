/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

-- Proof-only: construct a quadratic extension with a root and identify it with the supplied one.
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.LinearCombination

/-!
# Quadratic roots in finite-field extensions

Over a finite field `F`, a quadratic `X² - t X + d` without a root in `F` has a root in every
quadratic field extension `E/F` (`TauCeti.exists_mul_self_eq_of_finite`). The quadratic is
irreducible, so `AdjoinRoot` is a degree-two extension, and any two extensions of a finite field
of the same degree are isomorphic (`FiniteField.algEquivExtension`).

These roots supply the elliptic conjugacy normal forms of `GL₂(F)`. Their trace and norm are
computed in `TauCeti.RingTheory.Norm.Quadratic`, where the formulas apply to arbitrary quadratic
algebras over a field.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F]

/-- **Over a finite field a quadratic without a root has a root in every degree-`2` extension.**
A quadratic with no root in `F` is irreducible, so `AdjoinRoot` of it is a degree-`2` extension of
`F`; over a finite field any two extensions of the same degree are isomorphic, so the supplied `E`
already contains a root. -/
theorem exists_mul_self_eq_of_finite [Finite F] (E : Type*) [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {t d : F} (hroot : ∀ a : F, a * a ≠ t * a - d) :
    ∃ x : E, x * x = algebraMap F E t * x - algebraMap F E d := by
  classical
  have key : ∃ y : E, (Polynomial.aeval y) (X ^ 2 - C t * X + C d : F[X]) = 0 := by
    set p : F[X] := X ^ 2 - C t * X + C d with hpdef
    have hdeg : p.natDegree = 2 := by rw [hpdef]; compute_degree!
    have hmonic : p.Monic := by rw [hpdef]; monicity!
    have hirr : Irreducible p := by
      refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) fun a ha => ?_
      refine hroot a ?_
      rw [Polynomial.IsRoot, hpdef] at ha
      simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X] at ha
      linear_combination ha
    have : Fact (Irreducible p) := ⟨hirr⟩
    have hfr : Module.finrank F (AdjoinRoot p) = 2 := by
      rw [PowerBasis.finrank (AdjoinRoot.powerBasis hmonic.ne_zero), AdjoinRoot.powerBasis_dim,
        hdeg]
    obtain ⟨q, hq⟩ := CharP.exists F
    have : Fact q.Prime := ⟨CharP.char_is_prime F q⟩
    let e : AdjoinRoot p ≃ₐ[F] E :=
      (FiniteField.algEquivExtension F q 2 (AdjoinRoot p) hfr).trans
        (FiniteField.algEquivExtension F q 2 E
          (Algebra.IsQuadraticExtension.finrank_eq_two F E)).symm
    refine ⟨e (AdjoinRoot.root p), ?_⟩
    rw [Polynomial.aeval_algHom_apply e, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  obtain ⟨y, hy⟩ := key
  simp only [map_add, map_sub, map_pow, map_mul, aeval_C, aeval_X] at hy
  exact ⟨y, by linear_combination hy⟩

end TauCeti
