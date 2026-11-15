/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gumbel.Basic
public import TauCeti.Probability.Distributions.Logistic.Basic
import TauCeti.Probability.Distributions.Beta.Uniform
import TauCeti.Probability.Distributions.Gamma.Beta

/-!
# Differences of independent Gumbel variables

The difference of independent Gumbel variables with a common positive scale `s` has a logistic
law with scale `s` and location the difference of the two locations. We give the product-measure
pushforward identity and its random-variable formulation.

The construction uses the Gamma–Beta factorization: for independent rate-one exponentials
`E₁, E₂`, the ratio `E₂ / (E₁ + E₂)` is uniform on the unit interval. Its logit is
`log E₂ - log E₁`, giving the Gumbel difference. Positivity holds almost surely, so the
totalized logarithm and division at zero do not affect the law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), ch. 23.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The difference map sends the product of two Gumbel laws with the same positive scale to
the logistic law with that scale and the difference of the locations. -/
theorem map_sub_prod_gumbelMeasure {s : ℝ} (hs : 0 < s) (m₁ m₂ : ℝ) :
    ((gumbelMeasure m₁ s).prod (gumbelMeasure m₂ s)).map
        (fun z => z.1 - z.2) = logisticMeasure (m₁ - m₂) s := by
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hratio : ((expMeasure 1).prod (expMeasure 1)).map
      (fun z => z.2 / (z.1 + z.2)) = uniformMeasure 0 1 := by
    calc
      _ = ((expMeasure 1).prod (expMeasure 1)).map
          (fun z => z.1 / (z.1 + z.2)) := by
        conv_lhs => rw [← Measure.prod_swap (μ := expMeasure 1) (ν := expMeasure 1)]
        rw [Measure.map_map (by fun_prop) measurable_swap]
        congr 1
        funext z
        simp [add_comm]
      _ = uniformMeasure 0 1 := by
        rw [expMeasure, map_div_add_gammaMeasure one_pos one_pos one_pos, betaMeasure_one_one]
  rw [gumbelMeasure_of_pos hs, gumbelMeasure_of_pos hs,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), logisticMeasure_of_pos hs, ← hratio,
    Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop))).2
  filter_upwards [ae_pos_expMeasure 1] with x hx
  filter_upwards [ae_pos_expMeasure 1] with y hy
  have hsum : x + y ≠ 0 := (add_pos hx hy).ne'
  have hquot : (y / (x + y)) / (1 - y / (x + y)) = y / x := by
    field_simp [hsum, hx.ne']
    ring
  simp only [Function.comp_apply, Prod.map_apply, hquot, Real.log_div hy.ne' hx.ne']
  ring

end TauCeti.Probability

namespace ProbabilityTheory.IndepFun

/-- Independent Gumbel variables with equal positive scales have a logistic difference,
allowing arbitrary and unequal locations. -/
theorem hasLaw_sub_gumbelMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} {m₁ m₂ s : ℝ} (hXY : IndepFun X Y P) (hs : 0 < s)
    (hX : HasLaw X (TauCeti.Probability.gumbelMeasure m₁ s) P)
    (hY : HasLaw Y (TauCeti.Probability.gumbelMeasure m₂ s) P) :
    HasLaw (fun ω => X ω - Y ω) (TauCeti.Probability.logisticMeasure (m₁ - m₂) s) P := by
  let _ := TauCeti.Probability.isProbabilityMeasure_gumbelMeasure hs m₁
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hsub : HasLaw (fun z : ℝ × ℝ => z.1 - z.2)
      (TauCeti.Probability.logisticMeasure (m₁ - m₂) s)
      ((TauCeti.Probability.gumbelMeasure m₁ s).prod
        (TauCeti.Probability.gumbelMeasure m₂ s)) :=
    ⟨by fun_prop, TauCeti.Probability.map_sub_prod_gumbelMeasure hs m₁ m₂⟩
  exact hsub.fun_comp (hXY.hasLaw_prod hX hY)

end ProbabilityTheory.IndepFun
