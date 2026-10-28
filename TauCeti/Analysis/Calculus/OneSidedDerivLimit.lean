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

A function continuous at `t₀` from one side, differentiable on a punctured neighbourhood on that
side, whose derivative tends to `L` from that side, has one-sided derivative `L` at `t₀`.
Mathlib's `hasDerivWithinAt_Ici_of_tendsto_deriv` states this over a set containing a right
neighbourhood; these wrappers put it in the `𝓝[>] t₀` / `𝓝[<] t₀` eventual form in which
piecewise-`C¹` curve data arrives.

## Main results

* `TauCeti.hasDerivWithinAt_Ioi_of_tendsto_deriv` — the right-sided derivative from a right
  derivative limit.
* `TauCeti.hasDerivWithinAt_Iio_of_tendsto_deriv` — the left counterpart.

## Provenance

Migrated from `hasDerivWithinAt_Ioi_of_tendsto` and `hasDerivWithinAt_Iio_of_tendsto` of
`FlatnessConditions.lean` in the AINTLIB `LeanModularForms` development. Prerequisite for the
crossing analysis of the generalized residue theorem on the roadmap, where the one-sided
tangents of a piecewise-`C¹` curve are recovered from derivative limits.
-/

public section

namespace TauCeti

open Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function continuous from the right at `t₀`, eventually differentiable on the right, whose
derivative tends to `L` from the right, has right derivative `L` at `t₀`. -/
theorem hasDerivWithinAt_Ioi_of_tendsto_deriv {γ : ℝ → E} {t₀ : ℝ} {L : E}
    (hγ_cont : ContinuousWithinAt γ (Ici t₀) t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t)
    (hL : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Ioi t₀) t₀ :=
  hasDerivWithinAt_Ioi_iff_Ici.mpr <|
    hasDerivWithinAt_Ici_of_tendsto_deriv (s := {t | DifferentiableAt ℝ γ t} ∩ Ioi t₀)
      (fun _ ht => ht.1.differentiableWithinAt)
      (hγ_cont.mono (inter_subset_right.trans Ioi_subset_Ici_self))
      (inter_mem hγ_diff self_mem_nhdsWithin) hL

/-- A function continuous from the left at `t₀`, eventually differentiable on the left, whose
derivative tends to `L` from the left, has left derivative `L` at `t₀`. -/
theorem hasDerivWithinAt_Iio_of_tendsto_deriv {γ : ℝ → E} {t₀ : ℝ} {L : E}
    (hγ_cont : ContinuousWithinAt γ (Iic t₀) t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t)
    (hL : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Iio t₀) t₀ :=
  hasDerivWithinAt_Iio_iff_Iic.mpr <|
    hasDerivWithinAt_Iic_of_tendsto_deriv (s := {t | DifferentiableAt ℝ γ t} ∩ Iio t₀)
      (fun _ ht => ht.1.differentiableWithinAt)
      (hγ_cont.mono (inter_subset_right.trans Iio_subset_Iic_self))
      (inter_mem hγ_diff self_mem_nhdsWithin) hL

end TauCeti
