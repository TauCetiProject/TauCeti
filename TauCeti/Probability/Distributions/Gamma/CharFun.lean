/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gamma.Basic
public import TauCeti.Probability.Moments.ComplexMGF

/-!
# Characteristic function of the gamma distribution

This file computes the characteristic function of a gamma law with positive shape `a` and
positive rate `r`:

`charFun (gammaMeasure a r) t = (1 - I * t / r) ^ (-a)`.

The power is the principal complex power. Its base stays in the open right half-plane, so there
is no branch-cut ambiguity. The proof analytically continues the moment-generating function from
the real interval `(-∞, r)` to the half-plane `re z < r`, then evaluates the continuation on the
imaginary axis.

## Main result

* `TauCeti.charFun_gammaMeasure` gives the characteristic function of the gamma law.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, **Gamma**.
* The continuation step is `TauCeti.eqOn_complexMGF_of_eqOn_mgf`.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 17.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal Topology

namespace TauCeti

variable {a r : ℝ}

/-- The holomorphic extension of the gamma moment-generating function to `re z < r`. -/
private def gammaComplexMGF (a r : ℝ) (z : ℂ) : ℂ :=
  (1 - z / r) ^ (-(a : ℂ))

/-- The proposed complex moment-generating function is analytic on the half-plane `re z < r`.

On this half-plane the base `1 - z / r` has positive real part, so it lies in the slit plane on
which the principal complex power is holomorphic. -/
private theorem analyticOnNhd_gammaComplexMGF (hr : 0 < r) :
    AnalyticOnNhd ℂ (gammaComplexMGF a r) {z : ℂ | z.re ∈ Set.Iio r} := by
  unfold gammaComplexMGF
  have hdiff : DifferentiableOn ℂ (fun z : ℂ ↦ 1 - z / r) {z : ℂ | z.re < r} := by
    fun_prop
  refine (hdiff.cpow_const ?_).analyticOnNhd (isOpen_lt Complex.continuous_re continuous_const)
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  left
  simp only [Complex.sub_re, Complex.one_re, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, Complex.normSq_ofReal]
  have hzr : z.re / r < 1 := (div_lt_one hr).2 hz
  convert sub_pos.mpr hzr using 1
  field_simp
  ring

/-- On the real part of its domain, `gammaComplexMGF` agrees with the gamma mgf. -/
private theorem gammaComplexMGF_ofReal (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    gammaComplexMGF a r (t : ℂ) = mgf id (gammaMeasure a r) t := by
  rw [mgf_id_gammaMeasure ha hr ht]
  have hbase : 0 ≤ 1 - t / r := (sub_pos.mpr ((div_lt_one hr).2 ht)).le
  rw [gammaComplexMGF, Complex.ofReal_cpow hbase]
  push_cast
  rfl

/-- The characteristic function of a gamma law with positive shape `a` and positive rate `r`.

The right-hand side uses the principal complex power. Since `r > 0`, the real part of
`1 - I * t / r` is `1`, so its value never meets the branch cut. -/
@[simp]
theorem charFun_gammaMeasure (ha : 0 < a) (hr : 0 < r) (t : ℝ) :
    charFun (gammaMeasure a r) t =
      (1 - Complex.I * t / r) ^ (-(a : ℂ)) := by
  have hsub : Set.Iio r ⊆ integrableExpSet id (gammaMeasure a r) := by
    rw [integrableExpSet_id_gammaMeasure ha hr]
  have hEq : Set.EqOn (complexMGF id (gammaMeasure a r)) (gammaComplexMGF a r)
      {z : ℂ | z.re ∈ Set.Iio r} :=
    eqOn_complexMGF_of_eqOn_mgf isOpen_Iio (convex_Iio r) hsub
      (analyticOnNhd_gammaComplexMGF hr) fun _ hx ↦ gammaComplexMGF_ofReal ha hr hx
  have hit : ((t : ℂ) * Complex.I) ∈ {z : ℂ | z.re ∈ Set.Iio r} := by simpa using hr
  have := hEq hit
  rw [complexMGF_id_mul_I] at this
  simpa only [gammaComplexMGF, mul_comm] using this

end TauCeti
