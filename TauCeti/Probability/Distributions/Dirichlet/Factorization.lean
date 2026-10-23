/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Density

/-!
# Gamma–Dirichlet factorization

Normalize a nonempty finite family of independent Gamma variables with positive shapes and a
common positive rate. The normalized vector has Dirichlet law and is independent of its total,
which has Gamma law with the sum of the shapes and the original rate. In particular the
normalized law does not depend on the common rate. The total is almost surely positive, so the
zero-denominator value of `dirichletNormalize` does not contribute to any of these laws.

The primary result is `map_dirichletNormalize_sum_pi_gammaMeasure`. The random-variable versions
give the joint law, the Dirichlet marginal, and independence. These identities allow one to
separate the proportions and magnitude of a Gamma vector, including when there is only one
coordinate.

The proof uses the change of variables in `Dirichlet.Density`: the total and the deleted
coordinates have a product density. Common-rate scaling then gives the result at every positive
rate without repeating the Jacobian calculation.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private theorem map_dirichletNormalize_sum_pi_gammaMeasure_one {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    (Measure.pi fun i ↦ gammaMeasure (a i) 1).map
        (fun x ↦ (dirichletNormalize x, ∑ i, x i)) =
      (dirichletMeasure a).prod (gammaMeasure (∑ i, a i) 1) := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  have hsplit := measurePreserving_piSplitAt (fun i ↦ gammaMeasure (a i) 1) i₀
  have hchart : Measurable fun z : ℝ × ({i // i ≠ i₀} → ℝ) ↦
      (dirichletChart i₀ z.2, z.1) := by fun_prop
  calc
    _ = ((gammaMeasure (a i₀) 1).prod
          (Measure.pi fun j : {i // i ≠ i₀} ↦ gammaMeasure (a j) 1)).map
        ((fun z ↦ (dirichletChart i₀ z.2, z.1)) ∘ dirichletChartCoords i₀) := by
      rw [← hsplit.map_eq, Measure.map_map
        (hchart.comp (measurable_dirichletChartCoords i₀)) hsplit.measurable]
      exact Measure.map_congr (ae_dirichletNormalize_sum_eq_dirichletChart a (fun _ ↦ 1) i₀)
    _ = ((gammaMeasure (∑ i, a i) 1).prod
          ((volume : Measure ({i // i ≠ i₀} → ℝ)).withDensity (dirichletChartPDF a i₀))).map
        (fun z ↦ (dirichletChart i₀ z.2, z.1)) := by
      rw [← Measure.map_map hchart (measurable_dirichletChartCoords i₀),
        map_dirichletChartCoords_prod_gammaMeasure ha i₀]
    _ = _ := by
      rw [← Measure.prod_swap]
      have hswap : (fun z : ℝ × ({i // i ≠ i₀} → ℝ) ↦ (dirichletChart i₀ z.2, z.1)) ∘
          Prod.swap = Prod.map (dirichletChart i₀) id := rfl
      rw [Measure.map_map (by fun_prop) measurable_swap, hswap,
        ← Measure.map_prod_map _ _ measurable_dirichletChart measurable_id, Measure.map_id,
        ← dirichletMeasure_eq_map_withDensity_dirichletChartPDF ha i₀]

/-- The normalized coordinates and the total of independent Gamma laws at a common positive
rate have the product of a Dirichlet law and a Gamma law. -/
theorem map_dirichletNormalize_sum_pi_gammaMeasure {a : ι → ℝ} {r : ℝ}
    (ha : ∀ i, 0 < a i) (hr : 0 < r) :
    (Measure.pi fun i ↦ gammaMeasure (a i) r).map
        (fun x ↦ (dirichletNormalize x, ∑ i, x i)) =
      (dirichletMeasure a).prod (gammaMeasure (∑ i, a i) r) := by
  have hA : 0 < ∑ i, a i := Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  let _ i := isProbabilityMeasure_gammaMeasure (ha i) one_pos
  let _ i := isProbabilityMeasure_gammaMeasure (ha i) hr
  have hscale : (Measure.pi fun i ↦ gammaMeasure (a i) 1).map
      (fun x i ↦ r⁻¹ * x i) = Measure.pi fun i ↦ gammaMeasure (a i) r := by
    rw [Measure.pi_map_pi (fun _ ↦ (measurable_const_mul r⁻¹).aemeasurable)]
    simp_rw [gammaMeasure_map_const_mul (ha _) one_pos (inv_pos.mpr hr), one_div, inv_inv]
  have hcomm : (fun x : ι → ℝ ↦ (dirichletNormalize (fun i ↦ r⁻¹ * x i),
      ∑ i, r⁻¹ * x i)) =
      (Prod.map id (r⁻¹ * ·)) ∘ (fun x ↦ (dirichletNormalize x, ∑ i, x i)) := by
    funext x
    simp [dirichletNormalize_const_mul (inv_ne_zero hr.ne'), Finset.mul_sum]
  calc
    _ = (Measure.pi fun i ↦ gammaMeasure (a i) 1).map
        ((Prod.map id (r⁻¹ * ·)) ∘ (fun x ↦ (dirichletNormalize x, ∑ i, x i))) := by
      rw [← hscale, Measure.map_map (by fun_prop) (by fun_prop), Function.comp_def, hcomm]
    _ = ((dirichletMeasure a).prod (gammaMeasure (∑ i, a i) 1)).map
        (Prod.map id (r⁻¹ * ·)) := by
      rw [← Measure.map_map (by fun_prop) (by fun_prop),
        map_dirichletNormalize_sum_pi_gammaMeasure_one ha]
    _ = _ := by
      rw [← Measure.map_prod_map _ _ measurable_id (measurable_const_mul r⁻¹), Measure.map_id,
        gammaMeasure_map_const_mul hA one_pos (inv_pos.mpr hr)]
      simp

/-- Normalizing independent Gamma coordinates gives a Dirichlet law at every common positive
rate. -/
theorem map_dirichletNormalize_pi_gammaMeasure {a : ι → ℝ} {r : ℝ}
    (ha : ∀ i, 0 < a i) (hr : 0 < r) :
    (Measure.pi fun i ↦ gammaMeasure (a i) r).map dirichletNormalize = dirichletMeasure a := by
  have hA : 0 < ∑ i, a i := Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
  let _ := isProbabilityMeasure_gammaMeasure hA hr
  have h := congrArg (Measure.map Prod.fst) (map_dirichletNormalize_sum_pi_gammaMeasure ha hr)
  rw [Measure.map_map measurable_fst (by fun_prop)] at h
  simpa only [Function.comp_def, Measure.map_fst_prod, measure_univ, one_smul] using h

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ}
  {a : ι → ℝ} {r : ℝ}

/-- The proportions and total of independent Gamma random variables have the joint
Dirichlet–Gamma product law. -/
theorem hasLaw_dirichletNormalize_sum_prod_gammaMeasure_of_iIndepFun
    (ha : ∀ i, 0 < a i) (hr : 0 < r)
    (h_ind : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (gammaMeasure (a i) r) P) :
    HasLaw (fun ω ↦ (dirichletNormalize (fun i ↦ X i ω), ∑ i, X i ω))
      ((dirichletMeasure a).prod (gammaMeasure (∑ i, a i) r)) P := by
  have hmap : HasLaw (fun x : ι → ℝ ↦ (dirichletNormalize x, ∑ i, x i))
      ((dirichletMeasure a).prod (gammaMeasure (∑ i, a i) r))
      (Measure.pi fun i ↦ gammaMeasure (a i) r) :=
    ⟨by fun_prop, map_dirichletNormalize_sum_pi_gammaMeasure ha hr⟩
  exact hmap.fun_comp (h_ind.hasLaw_pi hX)

/-- The normalized vector of independent Gamma random variables has Dirichlet law. -/
theorem hasLaw_dirichletNormalize_gammaMeasure_of_iIndepFun (ha : ∀ i, 0 < a i) (hr : 0 < r)
    (h_ind : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (gammaMeasure (a i) r) P) :
    HasLaw (fun ω ↦ dirichletNormalize (fun i ↦ X i ω)) (dirichletMeasure a) P := by
  have hmap : HasLaw dirichletNormalize (dirichletMeasure a)
      (Measure.pi fun i ↦ gammaMeasure (a i) r) :=
    ⟨measurable_dirichletNormalize.aemeasurable, map_dirichletNormalize_pi_gammaMeasure ha hr⟩
  exact hmap.fun_comp (h_ind.hasLaw_pi hX)

/-- The normalized vector of independent Gamma random variables is independent of their total.
This includes a one-coordinate family, whose normalized vector is constant. -/
theorem indepFun_dirichletNormalize_sum_of_hasLaw_gammaMeasure (ha : ∀ i, 0 < a i) (hr : 0 < r)
    (h_ind : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (gammaMeasure (a i) r) P) :
    IndepFun (fun ω ↦ dirichletNormalize (fun i ↦ X i ω)) (fun ω ↦ ∑ i, X i ω) P := by
  let _ : IsProbabilityMeasure P := h_ind.isProbabilityMeasure
  have hsum : HasLaw (fun ω ↦ ∑ i, X i ω) (gammaMeasure (∑ i, a i) r) P :=
    h_ind.hasLaw_sum_gammaMeasure hr Finset.univ_nonempty
      (fun i _ ↦ ha i) (fun i _ ↦ hX i)
  exact (indepFun_iff_hasLaw_prodMk_prod
    (hasLaw_dirichletNormalize_gammaMeasure_of_iIndepFun ha hr h_ind hX) hsum).2
      (hasLaw_dirichletNormalize_sum_prod_gammaMeasure_of_iIndepFun ha hr h_ind hX)

end TauCeti.Probability
