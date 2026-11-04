/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

-- Proof-only: construct a quadratic extension with a root and embed it into the supplied one.
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.LinearCombination

/-!
# Quadratic roots in finite-field extensions

Over a finite field `F`, every quadratic `X² - t X + d` has a root in every quadratic field
extension `E/F` (`TauCeti.exists_mul_self_eq_of_finite`). A root already in `F` maps into `E`.
Otherwise the quadratic is irreducible, so `AdjoinRoot` is a degree-two extension and embeds
into `E` by `FiniteField.nonempty_algHom_of_finrank_dvd`.

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

/-- Over a finite field, every monic quadratic has a root in every degree-two field extension. -/
theorem exists_mul_self_eq_of_finite [Finite F] (E : Type*) [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] (t d : F) :
    ∃ x : E, x * x = algebraMap F E t * x - algebraMap F E d := by
  classical
  by_cases hroot : ∃ a : F, a * a = t * a - d
  · obtain ⟨a, ha⟩ := hroot
    exact ⟨algebraMap F E a, by simpa only [map_mul, map_sub] using congrArg (algebraMap F E) ha⟩
  push Not at hroot
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
    have : Finite E := Module.finite_of_finite F
    obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
      (F := F) (K := AdjoinRoot p) (L := E)
      (by rw [hfr, Algebra.IsQuadraticExtension.finrank_eq_two F E])
    refine ⟨e (AdjoinRoot.root p), ?_⟩
    rw [Polynomial.aeval_algHom_apply e, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  obtain ⟨y, hy⟩ := key
  simp only [map_add, map_sub, map_pow, map_mul, aeval_C, aeval_X] at hy
  exact ⟨y, by linear_combination hy⟩

end TauCeti
