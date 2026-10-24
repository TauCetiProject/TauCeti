/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Hyperexponential.Basic

/-!
# Transforms of hyperexponential distributions

The exponential-integrability domain of a valid hyperexponential law is the intersection
of the half-lines `t < rᵢ` over its positive-weight components. On this exact domain the mgf
is the weighted sum `∑ i, pᵢ rᵢ / (rᵢ - t)` and the cgf is its logarithm.
The characteristic function is the corresponding weighted sum with `t` replaced by `I * t`.

Zero-weight components impose no rate or integrability restriction, even at a pole of the
displayed rational expressions. Repeated rates are allowed.

## References

* S. Asmussen, *Applied Probability and Queues*, 2nd ed., Springer (2003), Chapter III, §4.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {p : StdSimplex ℝ≥0 ι} {r : ι → ℝ} {t : ℝ}

/-- An exponential moment exists exactly below every active rate. In particular, the
endpoint at any smallest active rate is excluded. -/
@[simp]
theorem integrable_exp_mul_hyperexponentialMeasure_iff
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    Integrable (fun x ↦ exp (t * x)) (hyperexponentialMeasure p r) ↔
      ∀ i, 0 < p.weights i → t < r i := by
  rw [integrable_hyperexponentialMeasure_iff hr]
  exact forall_congr' fun i ↦ forall_congr' fun hi ↦
    integrable_exp_mul_expMeasure_iff (hr i hi)

/-- The exact exponential-integrability domain ignores all zero-weight components. -/
@[simp]
theorem integrableExpSet_id_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    integrableExpSet id (hyperexponentialMeasure p r) =
      {t | ∀ i, 0 < p.weights i → t < r i} := by
  ext t
  exact integrable_exp_mul_hyperexponentialMeasure_iff hr

/-- The mgf is the weighted sum of the exponential mgfs on its finiteness domain. -/
@[simp]
theorem mgf_id_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i)
    (ht : ∀ i, 0 < p.weights i → t < r i) :
    mgf id (hyperexponentialMeasure p r) t =
      ∑ i, (p.weights i : ℝ) * r i / (r i - t) := by
  have hf := (integrable_exp_mul_hyperexponentialMeasure_iff hr).mpr ht
  simp only [mgf, id_eq]
  rw [integral_hyperexponentialMeasure hr hf]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hwi : p.weights i = 0
  · simp [hwi]
  · have hpos := pos_iff_ne_zero.mpr hwi
    have hcomponent := mgf_id_expMeasure (hr i hpos) (ht i hpos)
    simp only [mgf, id_eq] at hcomponent
    rw [hcomponent]
    simp only [smul_eq_mul, mul_div_assoc]

/-- The cgf is the logarithm of the weighted mgf sum, on the exact finiteness domain. -/
@[simp]
theorem cgf_id_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i)
    (ht : ∀ i, 0 < p.weights i → t < r i) :
    cgf id (hyperexponentialMeasure p r) t =
      log (∑ i, (p.weights i : ℝ) * r i / (r i - t)) := by
  rw [cgf, mgf_id_hyperexponentialMeasure hr ht]

/-- The characteristic function is the weighted sum of the exponential characteristic
functions, with no restriction on the frequency. -/
@[simp]
theorem charFun_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) (t : ℝ) :
    charFun (hyperexponentialMeasure p r) t =
      ∑ i, (p.weights i : ℂ) * r i / (r i - Complex.I * t) := by
  have hf : Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
      (hyperexponentialMeasure p r) :=
    (integrable_const (1 : ℂ)).mono (by fun_prop) (by
      filter_upwards with x
      simp [← Complex.ofReal_mul])
  rw [charFun_apply_real, integral_hyperexponentialMeasure hr hf]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hwi : p.weights i = 0
  · simp [hwi]
  · rw [← charFun_apply_real, charFun_expMeasure (hr i (pos_iff_ne_zero.mpr hwi))]
    simp only [Complex.real_smul, mul_div_assoc]

end TauCeti.Probability
