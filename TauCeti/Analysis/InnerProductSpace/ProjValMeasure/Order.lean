/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Integral

/-!
# Self-adjointness and Loewner order bounds for projection-valued measure integrals

A bounded measurable real-valued function `g : X → ℝ` defines a self-adjoint bounded Borel symbol
`BoundedBorelFunction.ofRealFunction g hg hbound`. Integrating against any projection-valued
measure `P : ProjValMeasure X H` sends real-valued symbols to self-adjoint operators and preserves
positivity (`BoundedBorelFunction.exists_star_mul_self_ofRealFunction`), so pointwise bounds
`m ≤ g ≤ M` become Loewner order inequalities `m • 1 ≤ ∫ g dP ≤ M • 1`.

## Main declarations

* `TauCeti.ProjValMeasure.isSelfAdjoint_integral_ofRealFunction`: real-valued symbols integrate to
  self-adjoint operators.
* `TauCeti.ProjValMeasure.integral_ofRealFunction_nonneg`,
  `TauCeti.ProjValMeasure.smul_one_le_integral_ofRealFunction`,
  `TauCeti.ProjValMeasure.integral_ofRealFunction_le_smul_one`: Loewner order bounds for
  integrals of real-valued bounded Borel symbols.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 12.24.
-/

public section

noncomputable section

open MeasureTheory
open scoped CStarAlgebra InnerProductSpace

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Integrating a real-valued bounded Borel symbol against a projection-valued measure yields a
self-adjoint operator. -/
theorem isSelfAdjoint_integral_ofRealFunction (P : ProjValMeasure X H) (g : X → ℝ)
    (hg : Measurable g) (hbound) :
    IsSelfAdjoint (P.integral (BoundedBorelFunction.ofRealFunction g hg hbound)) :=
  (BoundedBorelFunction.isSelfAdjoint_ofRealFunction g hg hbound).map P.integral

/-- Integrating a nonnegative real-valued bounded Borel symbol against a projection-valued measure
yields a nonnegative operator in the Loewner order. -/
theorem integral_ofRealFunction_nonneg (P : ProjValMeasure X H) {g : X → ℝ} (hg : Measurable g)
    (hbound) (h0 : ∀ x, 0 ≤ g x) :
    0 ≤ P.integral (BoundedBorelFunction.ofRealFunction g hg hbound) := by
  obtain ⟨s, hs⟩ := BoundedBorelFunction.exists_star_mul_self_ofRealFunction hg hbound h0
  rw [hs, map_mul, map_star]
  exact star_mul_self_nonneg (P.integral s)

/-- A pointwise lower bound `m ≤ g x` gives the Loewner lower bound `m • 1 ≤ ∫ g dP`. -/
theorem smul_one_le_integral_ofRealFunction (P : ProjValMeasure X H) {g : X → ℝ}
    (hg : Measurable g) (hbound) {m : ℝ} (hm : ∀ x, m ≤ g x) :
    m • (1 : H →L[ℂ] H) ≤ P.integral (BoundedBorelFunction.ofRealFunction g hg hbound) := by
  obtain ⟨M, _, hgM⟩ := id hbound
  have hsub_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x - m| ≤ C :=
    ⟨M + |m|, by positivity, fun x ↦ (abs_sub _ _).trans (add_le_add (hgM x) le_rfl)⟩
  have hsym : BoundedBorelFunction.ofRealFunction g hg hbound -
      algebraMap ℂ (BoundedBorelFunction X) m =
      BoundedBorelFunction.ofRealFunction (fun x ↦ g x - m)
        (hg.sub measurable_const) hsub_bound := by
    ext x
    simp
  rw [← sub_nonneg]
  have hop : P.integral (BoundedBorelFunction.ofRealFunction g hg hbound) -
      m • (1 : H →L[ℂ] H) =
      P.integral (BoundedBorelFunction.ofRealFunction (fun x ↦ g x - m)
        (hg.sub measurable_const) hsub_bound) := by
    have := congrArg P.integral hsym
    rwa [map_sub, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, Complex.coe_smul] at this
  rw [hop]
  exact P.integral_ofRealFunction_nonneg _ hsub_bound fun x ↦ sub_nonneg.2 (hm x)

/-- A pointwise upper bound `g x ≤ M` gives the Loewner upper bound `∫ g dP ≤ M • 1`. -/
theorem integral_ofRealFunction_le_smul_one (P : ProjValMeasure X H) {g : X → ℝ}
    (hg : Measurable g) (hbound) {M : ℝ} (hM : ∀ x, g x ≤ M) :
    P.integral (BoundedBorelFunction.ofRealFunction g hg hbound) ≤ M • (1 : H →L[ℂ] H) := by
  have hneg_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |(-g) x| ≤ C := by
    simpa [abs_neg] using hbound
  have h := P.smul_one_le_integral_ofRealFunction hg.neg hneg_bound (m := -M)
    fun x ↦ neg_le_neg (hM x)
  have hneg : BoundedBorelFunction.ofRealFunction (-g) hg.neg hneg_bound =
      -BoundedBorelFunction.ofRealFunction g hg hbound := by
    ext x
    simp
  rw [hneg, map_neg, neg_smul, neg_le_neg_iff] at h
  exact h

end ProjValMeasure
end TauCeti
