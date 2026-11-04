/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Beta.Reflection
import TauCeti.Probability.Distributions.Dirichlet.Marginal
import TauCeti.Probability.Distributions.Dirichlet.StickBreaking

/-!
# Products of independent Beta variables

The product of independent `Beta(a, b)` and `Beta(a + b, c)` variables has law
`Beta(a, b + c)` when all three shapes are positive. This combines nested proportions:
a proportion within a block multiplied by the proportion occupied by that block.
In particular, it combines the independent squared radius and squared direction coordinate
in the coordinate laws of a uniform point in a ball.

The proof takes a coordinate of the three-coordinate Dirichlet stick-breaking construction,
using `map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure` and the Dirichlet marginal
law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- Multiplying independent Beta variables with shapes `(a, b)` and `(a + b, c)` gives
the Beta law with shapes `(a, b + c)`. -/
theorem map_mul_prod_betaMeasure {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((betaMeasure a b).prod (betaMeasure (a + b) c)).map (fun z ↦ z.1 * z.2) =
      betaMeasure a (b + c) := by
  let shapes : Option (Fin 2) → ℝ := fun i ↦ Option.elim i c ![a, b]
  have hshapes : ∀ i, 0 < shapes i := by
    rintro (_ | i)
    · exact hc
    · fin_cases i <;> assumption
  have htwo : ∀ i : Fin 2, 0 < ![a, b] i := by
    intro i
    fin_cases i <;> assumption
  have hins :
      ((betaMeasure c (a + b)).prod (dirichletMeasure ![a, b])).map
        (fun z ↦ (1 - z.1) * z.2 0) = betaMeasure a (b + c) := by
    have h := congrArg
      (Measure.map (fun x : EuclideanSpace ℝ (Option (Fin 2)) ↦ x (some 0)))
      (map_dirichletStickInsert_prod_betaMeasure_dirichletMeasure hshapes)
    rw [Measure.map_map (by fun_prop) measurable_dirichletStickInsert,
      map_eval_dirichletMeasure hshapes] at h
    have hsum : (∑ j with j ≠ some 0, shapes j) = b + c := by
      simp [shapes, Finset.sum_filter, Fintype.sum_option]
      ring
    rw [hsum] at h
    simpa [Function.comp_def, dirichletStickInsert_some, shapes, Fin.sum_univ_two] using h
  have := isProbabilityMeasure_dirichletMeasure htwo
  have := isProbabilityMeasureBeta ha hb
  have := isProbabilityMeasureBeta (add_pos ha hb) hc
  have hmargin : (dirichletMeasure ![a, b]).map (fun x ↦ x 0) = betaMeasure a b := by
    simpa using map_eval_zero_dirichletMeasure_fin_two htwo
  have hprod :
      (((betaMeasure c (a + b)).prod (dirichletMeasure ![a, b])).map
        (fun z ↦ (z.2 0, 1 - z.1))) =
      (betaMeasure a b).prod (betaMeasure (a + b) c) := by
    calc
      _ = (((betaMeasure c (a + b)).prod (dirichletMeasure ![a, b])).map
          (Prod.map (fun x : ℝ ↦ 1 - x) (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0))).map
          Prod.swap := by
        rw [Measure.map_map measurable_swap (by fun_prop)]
        rfl
      _ = _ := by
        rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
          betaMeasure_map_one_sub, hmargin,
          Measure.prod_swap]
  rw [← hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_def, mul_comm] using hins

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- The product of independent Beta variables with shapes `(a, b)` and `(a + b, c)` has
shapes `(a, b + c)`. -/
theorem IndepFun.hasLaw_mul_betaMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} {a b c : ℝ} (hXY : IndepFun X Y P)
    (hX : HasLaw X (betaMeasure a b) P) (hY : HasLaw Y (betaMeasure (a + b) c) P)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    HasLaw (fun ω ↦ X ω * Y ω) (betaMeasure a (b + c)) P := by
  have := isProbabilityMeasureBeta ha hb
  have := hX.isProbabilityMeasure
  exact (HasLaw.mk (by fun_prop) (map_mul_prod_betaMeasure ha hb hc)).comp
    (hXY.hasLaw_prod hX hY)

end ProbabilityTheory
