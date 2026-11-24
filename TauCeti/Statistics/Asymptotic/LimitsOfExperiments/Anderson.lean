/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.MeasureTheory.Integral.Layercake
import TauCeti.Probability.Distributions.Gaussian.PrekopaLeindler

/-!
# Anderson's lemma

A loss `ℓ : EuclideanSpace ℝ ι → ℝ≥0∞`, for a finite index type `ι`, is bowl-shaped when its
sublevel sets are convex and symmetric about the origin. Anderson's lemma says that for a
bowl-shaped loss, the risk under a centered Gaussian law is no larger than under its convolution
with any probability law.

The proof applies Anderson's inequality for sets,
`TauCeti.Probability.multivariateGaussian_preimage_add_le`, to the strict sublevel sets of the
loss, passes to the loss by the layer-cake formula, and integrates the shifted risk over the
convolving law. The loss may be unbounded or take the value `∞`, and the covariance matrix may be
degenerate.

## Main results

* `TauCeti.lintegral_multivariateGaussian_le_lintegral_add`: a bowl-shaped loss has minimal risk
  under a centered Gaussian law at zero shift.
* `TauCeti.lintegral_multivariateGaussian_le_conv`: **Anderson's lemma**.

## References

* T. W. Anderson, *The integral of a symmetric unimodal function over a symmetric convex set and
  some probability inequalities*, Proc. Amer. Math. Soc. **6** (1955), 170–176.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Lemma 8.5.

The proofs are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Asymptotics/LAN/GaussianAnderson.lean`.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bowl-shaped loss has minimal risk under a centered multivariate Gaussian law at zero
shift: `∫ ℓ dN(0, S) ≤ ∫ ℓ (a + x) dN(0, S)`. The loss may be unbounded or take the value `∞`,
and the covariance matrix may be degenerate. -/
theorem lintegral_multivariateGaussian_le_lintegral_add (S : Matrix ι ι ℝ)
    (ℓ : EuclideanSpace ℝ ι → ℝ≥0∞) (hℓ : Measurable ℓ) (hsymm : ∀ x, ℓ (-x) = ℓ x)
    (hconv : ∀ c, Convex ℝ {x | ℓ x ≤ c}) (a : EuclideanSpace ℝ ι) :
    ∫⁻ x, ℓ x ∂(multivariateGaussian 0 S) ≤ ∫⁻ x, ℓ (a + x) ∂(multivariateGaussian 0 S) := by
  have hℓa : Measurable fun x ↦ ℓ (a + x) := hℓ.comp (measurable_const_add a)
  rw [lintegral_eq_lintegral_measure_ofReal_le _ hℓ.aemeasurable,
    lintegral_eq_lintegral_measure_ofReal_le _ hℓa.aemeasurable]
  refine lintegral_mono fun t ↦ ?_
  -- The strict sublevel set below `t` is measurable, convex and symmetric.
  set C := {x | ℓ x < ENNReal.ofReal t}
  have hC : MeasurableSet C := measurableSet_lt hℓ measurable_const
  have hCc : Convex ℝ C := by
    simpa [C] using (convex_univ.quasiconvexOn_of_convex_le hconv).convex_lt (ENNReal.ofReal t)
  have hCa : MeasurableSet ((a + ·) ⁻¹' C) := measurable_const_add a hC
  have h := multivariateGaussian_preimage_add_le S hC hCc
    (fun x hx ↦ by simpa [C, hsymm] using hx) a
  have hcompl : multivariateGaussian 0 S Cᶜ ≤ multivariateGaussian 0 S ((a + ·) ⁻¹' C)ᶜ := by
    rw [measure_compl hC (measure_ne_top _ _), measure_compl hCa (measure_ne_top _ _)]
    exact tsub_le_tsub_left h _
  simpa [C, Set.compl_ofPred, not_lt] using hcompl

/-- **Anderson's lemma.** For a measurable bowl-shaped loss `ℓ`, that is one whose sublevel sets
are convex and symmetric about the origin, a matrix `S` and a probability measure `M`, the risk
under `N(0, S)` is at most the risk under the convolution `N(0, S) ∗ M`. The loss may be
unbounded or take the value `∞`. No positive semidefiniteness of `S` is needed: otherwise
`multivariateGaussian 0 S` is the Dirac mass at `0`, for which the statement still holds. -/
theorem lintegral_multivariateGaussian_le_conv (S : Matrix ι ι ℝ)
    (ℓ : EuclideanSpace ℝ ι → ℝ≥0∞) (hℓ : Measurable ℓ)
    (hsymm : ∀ x, ℓ (-x) = ℓ x) (hconv : ∀ c, Convex ℝ {x | ℓ x ≤ c})
    (M : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure M] :
    ∫⁻ x, ℓ x ∂(multivariateGaussian 0 S) ≤
      ∫⁻ x, ℓ x ∂((multivariateGaussian 0 S).conv M) := by
  rw [Measure.conv_comm, Measure.lintegral_conv hℓ]
  calc ∫⁻ x, ℓ x ∂(multivariateGaussian 0 S)
      = ∫⁻ _, ∫⁻ x, ℓ x ∂(multivariateGaussian 0 S) ∂M := by simp
    _ ≤ _ := lintegral_mono fun a ↦
      lintegral_multivariateGaussian_le_lintegral_add S ℓ hℓ hsymm hconv a

end TauCeti
