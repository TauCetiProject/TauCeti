/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# One-sided derivatives from one-sided derivative limits

A function continuous at `t₀` from one side, whose derivative tends to a non-zero `L` from that
side, has one-sided derivative `L` at `t₀`. Mathlib's `hasDerivWithinAt_Ici_of_tendsto_deriv`
states this over a set containing a right neighbourhood on which the function is differentiable;
here that differentiability comes for free, since `deriv γ t = 0` wherever `γ` is not
differentiable and the non-zero limit makes `deriv γ` eventually non-zero. This is the form in
which the one-sided tangents of a piecewise-`C¹` immersion arrive.

## Main results

* `TauCeti.hasDerivWithinAt_Ioi_of_tendsto_deriv_of_ne_zero` — the right-sided derivative from
  a non-zero right derivative limit and right continuity.
* `TauCeti.hasDerivWithinAt_Iio_of_tendsto_deriv_of_ne_zero` — the left counterpart.

## Provenance

Adapted from `hasDerivWithinAt_Ioi_of_tendsto` and `hasDerivWithinAt_Iio_of_tendsto` of
`FlatnessConditions.lean` in the AINTLIB `LeanModularForms` development. Prerequisite for the
crossing analysis of the generalized residue theorem on the roadmap, where the one-sided
tangents of a piecewise-`C¹` curve are recovered from derivative limits.
-/

public section

namespace TauCeti

open Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function continuous from the right at `t₀` whose derivative tends to a non-zero `L` from
the right has right derivative `L` at `t₀`. No differentiability hypothesis is needed: since
`deriv γ t = 0` wherever `γ` is not differentiable, the non-zero limit makes `γ` differentiable on
a punctured right neighbourhood of `t₀`. -/
theorem hasDerivWithinAt_Ioi_of_tendsto_deriv_of_ne_zero {γ : ℝ → E} {t₀ : ℝ} {L : E}
    (hγ_cont : ContinuousWithinAt γ (Ici t₀) t₀) (hL_ne : L ≠ 0)
    (hL : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Ioi t₀) t₀ :=
  hasDerivWithinAt_Ioi_iff_Ici.mpr <|
    hasDerivWithinAt_Ici_of_tendsto_deriv (s := {t | deriv γ t ≠ 0} ∩ Ioi t₀)
      (fun _ ht => (differentiableAt_of_deriv_ne_zero ht.1).differentiableWithinAt)
      (hγ_cont.mono (inter_subset_right.trans Ioi_subset_Ici_self))
      (inter_mem (hL.eventually_ne hL_ne) self_mem_nhdsWithin) hL

/-- A function continuous from the left at `t₀` whose derivative tends to a non-zero `L` from
the left has left derivative `L` at `t₀`; the left counterpart of
`hasDerivWithinAt_Ioi_of_tendsto_deriv_of_ne_zero`. -/
theorem hasDerivWithinAt_Iio_of_tendsto_deriv_of_ne_zero {γ : ℝ → E} {t₀ : ℝ} {L : E}
    (hγ_cont : ContinuousWithinAt γ (Iic t₀) t₀) (hL_ne : L ≠ 0)
    (hL : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Iio t₀) t₀ :=
  hasDerivWithinAt_Iio_iff_Iic.mpr <|
    hasDerivWithinAt_Iic_of_tendsto_deriv (s := {t | deriv γ t ≠ 0} ∩ Iio t₀)
      (fun _ ht => (differentiableAt_of_deriv_ne_zero ht.1).differentiableWithinAt)
      (hγ_cont.mono (inter_subset_right.trans Iio_subset_Iic_self))
      (inter_mem (hL.eventually_ne hL_ne) self_mem_nhdsWithin) hL

end TauCeti
