/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Geometric.Basic

/-!
# Observable formulas for the geometric distribution

This file transfers the elementary generating-function and transform theory of the geometric
measure to random variables carrying that law. It keeps the native natural-valued law for the
probability-generating function and uses the real cast for exponential moments and characteristic
functions. The totalized zero-success parameter is handled separately: Mathlib's geometric law is
then the Dirac mass at zero.

## Main results

* `ProbabilityTheory.HasLaw.integrable_pow_geometricMeasure_iff` gives the sharp native
  power-integrability domain;
* `ProbabilityTheory.HasLaw.pgf_geometricMeasure` gives the probability-generating function on its
  sharp convergence domain;
* `ProbabilityTheory.HasLaw.integrable_exp_mul_id_map_cast_geometricMeasure_iff` and
  `ProbabilityTheory.HasLaw.integrableExpSet_id_map_cast_geometricMeasure` give the exact
  exponential-integrability domain of the real cast;
* `ProbabilityTheory.HasLaw.mgf_id_map_cast_geometricMeasure`,
  `ProbabilityTheory.HasLaw.cgf_id_map_cast_geometricMeasure`, and
  `ProbabilityTheory.HasLaw.charFun_map_cast_geometricMeasure` give the transforms;
* the corresponding `_zero` theorems cover the totalized zero parameter.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed.,
  Wiley, 2005.
-/

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Powers of the argument are integrable for a natural-valued geometric random variable exactly
on the open interval determined by the geometric-series ratio. -/
theorem integrable_pow_geometricMeasure_iff {X : Ω → ℕ} {p : unitInterval}
    (hX : HasLaw X (geometricMeasure p) P) (hp : p ≠ 0) (t : ℝ) :
    Integrable (fun ω ↦ t ^ X ω) P ↔ |(1 - (p : ℝ)) * t| < 1 := by
  rw [← TauCeti.Probability.integrable_pow_geometricMeasure_iff hp t, ← hX.map_eq,
    integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

/-- A natural-valued geometric random variable has the geometric probability-generating function
on its sharp convergence domain. -/
theorem pgf_geometricMeasure {X : Ω → ℕ} {p : unitInterval}
    (hX : HasLaw X (geometricMeasure p) P) (hp : p ≠ 0) {t : ℝ}
    (ht : |(1 - (p : ℝ)) * t| < 1) :
    pgf X P t = (p : ℝ) / (1 - (1 - (p : ℝ)) * t) := by
  rw [TauCeti.Probability.HasLaw.pgf_eq hX,
    TauCeti.Probability.pgf_geometricMeasure hp ht]

/-- At the totalized zero-success parameter, the probability-generating function of a geometric
random variable is identically one. -/
theorem pgf_geometricMeasure_zero {X : Ω → ℕ}
    (hX : HasLaw X (geometricMeasure 0) P) (t : ℝ) : pgf X P t = 1 := by
  rw [TauCeti.Probability.HasLaw.pgf_eq hX,
    TauCeti.Probability.pgf_geometricMeasure_zero]

/-- The exponential integrand of a real random variable with a nonzero-parameter geometric law is
integrable exactly below the pole of the geometric series. -/
theorem integrable_exp_mul_id_map_cast_geometricMeasure_iff {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) P) (hp : p ≠ 0) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P ↔
      (1 - (p : ℝ)) * Real.exp t < 1 := by
  rw [← TauCeti.Probability.integrable_exp_mul_id_map_cast_geometricMeasure_iff hp t,
    ← hX.map_eq, integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

/-- The exact exponential-integrability domain of a real random variable with a
nonzero-parameter geometric law. -/
theorem integrableExpSet_id_map_cast_geometricMeasure {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) P) (hp : p ≠ 0) :
    integrableExpSet X P = {t | (1 - (p : ℝ)) * Real.exp t < 1} := by
  ext t
  exact hX.integrable_exp_mul_id_map_cast_geometricMeasure_iff hp t

/-- The moment-generating function of a real random variable with a nonzero-parameter geometric
law, on its exact domain. -/
theorem mgf_id_map_cast_geometricMeasure {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) P) (hp : p ≠ 0)
    {t : ℝ} (ht : (1 - (p : ℝ)) * Real.exp t < 1) :
    mgf X P t = (p : ℝ) / (1 - (1 - (p : ℝ)) * Real.exp t) := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq,
    TauCeti.Probability.mgf_id_map_cast_geometricMeasure hp ht]

/-- The cumulant-generating function of a real random variable with a nonzero-parameter geometric
law, on its exact domain. -/
theorem cgf_id_map_cast_geometricMeasure {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) P) (hp : p ≠ 0)
    {t : ℝ} (ht : (1 - (p : ℝ)) * Real.exp t < 1) :
    cgf X P t = Real.log ((p : ℝ) / (1 - (1 - (p : ℝ)) * Real.exp t)) := by
  rw [cgf, hX.mgf_id_map_cast_geometricMeasure hp ht]

/-- The characteristic function of a real random variable with a nonzero-parameter geometric
law. -/
theorem charFun_map_cast_geometricMeasure {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) P) (hp : p ≠ 0) (t : ℝ) :
    charFun (P.map X) t =
      (p : ℂ) / (1 - (1 - (p : ℂ)) * Complex.exp (Complex.I * t)) := by
  rw [hX.map_eq, TauCeti.Probability.charFun_map_cast_geometricMeasure hp]

/-- At the totalized zero-success parameter, every exponential moment of a real random variable
with the cast geometric law is integrable. -/
theorem integrableExpSet_id_map_cast_geometricMeasure_zero {X : Ω → ℝ}
    (hX : HasLaw X ((geometricMeasure 0).map (Nat.cast : ℕ → ℝ)) P) :
    integrableExpSet X P = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  apply hX.integrable_fun_comp (f := fun x : ℝ ↦ Real.exp (t * x))
  have ht : t ∈ integrableExpSet id
      ((geometricMeasure 0).map (Nat.cast : ℕ → ℝ)) := by
    rw [TauCeti.Probability.integrableExpSet_id_map_cast_geometricMeasure_zero]
    exact Set.mem_univ t
  simpa only [integrableExpSet, Set.mem_ofPred_eq, id_eq] using ht

/-- At the totalized zero-success parameter, the moment-generating function of a real random
variable with the cast geometric law is identically one. -/
theorem mgf_id_map_cast_geometricMeasure_zero {X : Ω → ℝ}
    (hX : HasLaw X ((geometricMeasure 0).map (Nat.cast : ℕ → ℝ)) P) (t : ℝ) :
    mgf X P t = 1 := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq,
    TauCeti.Probability.mgf_id_map_cast_geometricMeasure_zero]

/-- At the totalized zero-success parameter, the cumulant-generating function of a real random
variable with the cast geometric law is identically zero. -/
theorem cgf_id_map_cast_geometricMeasure_zero {X : Ω → ℝ}
    (hX : HasLaw X ((geometricMeasure 0).map (Nat.cast : ℕ → ℝ)) P) (t : ℝ) :
    cgf X P t = 0 := by
  rw [cgf, hX.mgf_id_map_cast_geometricMeasure_zero]
  simp

/-- At the totalized zero-success parameter, the characteristic function of a real random
variable with the cast geometric law is identically one. -/
theorem charFun_map_cast_geometricMeasure_zero {X : Ω → ℝ}
    (hX : HasLaw X ((geometricMeasure 0).map (Nat.cast : ℕ → ℝ)) P) (t : ℝ) :
    charFun (P.map X) t = 1 := by
  rw [hX.map_eq, TauCeti.Probability.charFun_map_cast_geometricMeasure_zero]

end ProbabilityTheory.HasLaw
