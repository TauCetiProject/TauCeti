/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.BetaPrime.Basic
public import TauCeti.Probability.Distributions.Gamma.Beta

/-!
# Beta-prime laws from independent Gamma variables

For independent Gamma variables `X` and `Y` with positive shapes `a` and `b` and a common
positive rate `r`, the quotient `X / Y` has law `betaPrimeMeasure a b`. The common rate cancels.
The quotient is also independent of `X + Y`, which has Gamma shape `a + b` and rate `r`.

The primary result `map_div_sum_prod_gammaMeasure` gives this joint law as a product-measure
pushforward. Its marginal `map_div_gammaMeasure` and the `HasLaw` theorems let callers construct
beta-prime variables without unfolding their Beta-pushforward definition.

The construction reuses `map_div_add_prod_gammaMeasure`: apply the odds map to the Beta
coordinate of the Gamma--Beta factorization. Positivity makes the zero-total branch null.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {a b r : ℝ}

/-- The quotient and sum of independent Gamma variables with a common positive rate have the
product of a beta-prime law and a Gamma law. -/
theorem map_div_sum_prod_gammaMeasure (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map
        (fun z ↦ (z.1 / z.2, z.1 + z.2)) =
      (betaPrimeMeasure a b).prod (gammaMeasure (a + b) r) := by
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have h := congrArg (Measure.map (Prod.map (fisherSnedecorMap 2 2) id))
    (map_div_add_prod_gammaMeasure ha hb hr)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (measurable_fisherSnedecorMap 2 2) measurable_id,
    Measure.map_id, ← betaPrimeMeasure_eq_map ha hb] at h
  refine (Measure.map_congr ?_).trans h
  filter_upwards [ae_mem_prod_Ioi_gammaMeasure ha hb hr hr] with z hz
  have htotal : z.1 + z.2 ≠ 0 := (add_pos hz.1 hz.2).ne'
  simp only [Function.comp_apply, Prod.map_apply, id_eq,
    fisherSnedecorMap_div_add htotal, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]

/-- The quotient of independent Gamma variables with a common positive rate has a beta-prime
law with their respective shapes. -/
theorem map_div_gammaMeasure (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map (fun z ↦ z.1 / z.2) =
      betaPrimeMeasure a b := by
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have h := congrArg (Measure.map Prod.fst) (map_div_sum_prod_gammaMeasure ha hb hr)
  rw [Measure.map_map measurable_fst (by fun_prop)] at h
  simpa only [Function.comp_def, Measure.map_fst_prod, measure_univ, one_smul] using h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}

/-- For independent Gamma variables with a common positive rate, the quotient and sum have
the product of a beta-prime law and a Gamma law. -/
theorem hasLaw_div_sum_prod_gammaMeasure_of_indepFun
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hXY : IndepFun X Y P)
    (hX : HasLaw X (gammaMeasure a r) P) (hY : HasLaw Y (gammaMeasure b r) P) :
    HasLaw (fun ω ↦ (X ω / Y ω, X ω + Y ω))
      ((betaPrimeMeasure a b).prod (gammaMeasure (a + b) r)) P := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hmap : HasLaw (fun z : ℝ × ℝ ↦ (z.1 / z.2, z.1 + z.2))
      ((betaPrimeMeasure a b).prod (gammaMeasure (a + b) r))
      ((gammaMeasure a r).prod (gammaMeasure b r)) :=
    ⟨by fun_prop, map_div_sum_prod_gammaMeasure ha hb hr⟩
  exact hmap.fun_comp (hXY.hasLaw_prod hX hY)

/-- The quotient of independent Gamma variables with a common positive rate is beta-prime
distributed; its law does not depend on the common rate. -/
theorem hasLaw_betaPrime_of_gammaMeasure
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hXY : IndepFun X Y P)
    (hX : HasLaw X (gammaMeasure a r) P) (hY : HasLaw Y (gammaMeasure b r) P) :
    HasLaw (fun ω ↦ X ω / Y ω) (betaPrimeMeasure a b) P := by
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have hfst : HasLaw Prod.fst (betaPrimeMeasure a b)
      ((betaPrimeMeasure a b).prod (gammaMeasure (a + b) r)) :=
    MeasureTheory.measurePreserving_fst.hasLaw
  exact hfst.fun_comp (hasLaw_div_sum_prod_gammaMeasure_of_indepFun ha hb hr hXY hX hY)

/-- The quotient of independent Gamma variables with a common positive rate is independent
of their sum. -/
theorem indepFun_div_sum_of_hasLaw_gammaMeasure
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hXY : IndepFun X Y P)
    (hX : HasLaw X (gammaMeasure a r) P) (hY : HasLaw Y (gammaMeasure b r) P) :
    IndepFun (fun ω ↦ X ω / Y ω) (fun ω ↦ X ω + Y ω) P := by
  let _ := isProbabilityMeasure_betaPrimeMeasure ha hb
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have hjoint := hasLaw_div_sum_prod_gammaMeasure_of_indepFun ha hb hr hXY hX hY
  let _ : IsProbabilityMeasure P := hjoint.isProbabilityMeasure
  have hratio := hasLaw_betaPrime_of_gammaMeasure ha hb hr hXY hX hY
  have hsnd : HasLaw Prod.snd (gammaMeasure (a + b) r)
      ((betaPrimeMeasure a b).prod (gammaMeasure (a + b) r)) :=
    MeasureTheory.measurePreserving_snd.hasLaw
  exact (indepFun_iff_hasLaw_prodMk_prod hratio (hsnd.fun_comp hjoint)).2 hjoint

end TauCeti.Probability
