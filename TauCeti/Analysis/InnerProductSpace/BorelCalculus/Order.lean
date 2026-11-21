/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic

/-!
# Self-adjointness and Loewner order bounds in the Borel functional calculus

A bounded measurable real-valued function `g : spectrum ℂ a → ℝ` on the spectrum of a normal
bounded operator `a : H →L[ℂ] H` defines a self-adjoint bounded Borel symbol
`BoundedBorelFunction.ofRealFunction g hg hbound`. When `g` is nonnegative everywhere,
`BoundedBorelFunction.exists_star_mul_self_ofRealFunction` factors it as `star s * s`; since every
star homomorphism into `H →L[ℂ] H` sends `star s * s` to a nonnegative operator in the Loewner
order, pointwise bounds `m ≤ g ≤ M` on the spectrum become operator inequalities
`m • 1 ≤ g(a) ≤ M • 1`.

## Main declarations

* `ContinuousLinearMap.isSelfAdjoint_borelCalculus_ofRealFunction`: real-valued symbols produce
  self-adjoint operators.
* `ContinuousLinearMap.borelCalculus_ofRealFunction_nonneg`,
  `ContinuousLinearMap.smul_one_le_borelCalculus_ofRealFunction`,
  `ContinuousLinearMap.borelCalculus_ofRealFunction_le_smul_one`: Loewner order bounds for real
  Borel symbols.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 12.24.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped CStarAlgebra InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : H →L[ℂ] H) [IsStarNormal a]

/-- The Borel functional calculus sends real-valued symbols to self-adjoint operators. -/
theorem isSelfAdjoint_borelCalculus_ofRealFunction (g : spectrum ℂ a → ℝ) (hg : Measurable g)
    (hbound) :
    IsSelfAdjoint (a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound)) :=
  (BoundedBorelFunction.isSelfAdjoint_ofRealFunction g hg hbound).map a.borelCalculus

/-- A nonnegative real-valued Borel symbol produces a nonnegative operator in the Loewner order. -/
theorem borelCalculus_ofRealFunction_nonneg {g : spectrum ℂ a → ℝ} (hg : Measurable g) (hbound)
    (h0 : ∀ x, 0 ≤ g x) :
    0 ≤ a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) := by
  obtain ⟨s, hs⟩ := BoundedBorelFunction.exists_star_mul_self_ofRealFunction hg hbound h0
  rw [hs, map_mul, map_star]
  exact star_mul_self_nonneg (a.borelCalculus s)

/-- A lower bound `m ≤ g x` on the spectrum gives the Loewner lower bound `m • 1 ≤ g(a)`. -/
theorem smul_one_le_borelCalculus_ofRealFunction {g : spectrum ℂ a → ℝ} (hg : Measurable g)
    (hbound) {m : ℝ} (hm : ∀ x, m ≤ g x) :
    m • (1 : H →L[ℂ] H) ≤ a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) := by
  obtain ⟨M, _, hgM⟩ := id hbound
  have hsub_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x - m| ≤ C :=
    ⟨M + |m|, by positivity, fun x ↦ (abs_sub _ _).trans (add_le_add (hgM x) le_rfl)⟩
  have hsym : BoundedBorelFunction.ofRealFunction g hg hbound -
      algebraMap ℂ (BoundedBorelFunction (spectrum ℂ a)) m =
      BoundedBorelFunction.ofRealFunction (fun x ↦ g x - m)
        (hg.sub measurable_const) hsub_bound := by
    ext x
    simp
  rw [← sub_nonneg]
  have hop : a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) -
      m • (1 : H →L[ℂ] H) =
      a.borelCalculus (BoundedBorelFunction.ofRealFunction (fun x ↦ g x - m)
        (hg.sub measurable_const) hsub_bound) := by
    have := congrArg a.borelCalculus hsym
    rwa [map_sub, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, Complex.coe_smul] at this
  rw [hop]
  exact a.borelCalculus_ofRealFunction_nonneg _ hsub_bound fun x ↦ sub_nonneg.2 (hm x)

/-- An upper bound `g x ≤ M` on the spectrum gives the Loewner upper bound `g(a) ≤ M • 1`. -/
theorem borelCalculus_ofRealFunction_le_smul_one {g : spectrum ℂ a → ℝ} (hg : Measurable g)
    (hbound) {M : ℝ} (hM : ∀ x, g x ≤ M) :
    a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) ≤ M • (1 : H →L[ℂ] H) := by
  obtain ⟨B, _, hgB⟩ := id hbound
  have hsub_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |M - g x| ≤ C :=
    ⟨|M| + B, by positivity, fun x ↦ (abs_sub _ _).trans (add_le_add le_rfl (hgB x))⟩
  have hsym : algebraMap ℂ (BoundedBorelFunction (spectrum ℂ a)) M -
      BoundedBorelFunction.ofRealFunction g hg hbound =
      BoundedBorelFunction.ofRealFunction (fun x ↦ M - g x)
        (measurable_const.sub hg) hsub_bound := by
    ext x
    simp
  rw [← sub_nonneg]
  have hop : M • (1 : H →L[ℂ] H) -
      a.borelCalculus (BoundedBorelFunction.ofRealFunction g hg hbound) =
      a.borelCalculus (BoundedBorelFunction.ofRealFunction (fun x ↦ M - g x)
        (measurable_const.sub hg) hsub_bound) := by
    have := congrArg a.borelCalculus hsym
    rwa [map_sub, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, Complex.coe_smul] at this
  rw [hop]
  exact a.borelCalculus_ofRealFunction_nonneg _ hsub_bound fun x ↦ sub_nonneg.2 (hM x)

end ContinuousLinearMap
