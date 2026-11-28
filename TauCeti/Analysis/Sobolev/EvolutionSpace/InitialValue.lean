/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Sobolev.EvolutionSpace.Basic
import TauCeti.Analysis.Normed.Operator.EssentialLimit
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Initial values outside `V` force blow-up

Let `ι : V →L[𝕜] H` be a bounded operator from a reflexive normed space, such as the inclusion
`V ↪ H` of a Gelfand triple. An element `u` of the energy space
`TauCeti.EvolutionSpace ι a b = L²(a, b; V) ∩ H¹(a, b; V*)` has a representative continuous on
`[a, b]` with values in `H` (`TauCeti.EvolutionSpace.toContinuousMap`), but its values `u(t)` lie in
`V` only for almost every `t`. This file shows that the continuity into `H` cannot be improved to
continuity into `V` in general: if the initial value `u(a) ∈ H` is not of the form `ι v`, then

`‖u(t)‖_V → ∞` as `t → a⁺`, essentially,

that is, along the filter `𝓝[>] a ⊓ ae volume` of times close to `a` on the right outside a null
set (`TauCeti.EvolutionSpace.tendsto_norm_value_atTop`). Whether or not `V` is reflexive, `u` has
no representative with values in `V` that is continuous from the right at `a`
(`TauCeti.EvolutionSpace.not_exists_continuousWithinAt_ae_eq`), since `ι` of such a representative
would tend to `u(a)`.

The argument does not use the equation: it needs only a function `u : ℝ → V` and a representative
`w` of `ι ∘ u` continuous from the right at `a`
(`TauCeti.tendsto_norm_atTop_of_eventuallyEq_of_notMem_range` and
`TauCeti.not_exists_continuousWithinAt_eventuallyEq_of_notMem_range`). If `‖u(t)‖ ≤ M` at times
`t → a⁺` with `ι (u t) = w t`, then `w a`, a limit of such values `ι (u t)`, lies in the image of
the closed ball of radius `M`, which is closed by reflexivity
(`ContinuousLinearMap.isClosed_image_closedBall`), so `w a` lies in the range of `ι`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2, Theorem 3 (the embedding of the
  energy space into `C([0, T]; L²)`).
-/

public section

namespace TauCeti

open MeasureTheory Filter Set Topology NormedSpace

namespace EvolutionSpace

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι : V →L[ℝ] H} {a b : ℝ}

/-- **Blow-up in the energy space.** Let `V` be reflexive and let `u` be an element of the energy
space `L²(a, b; V) ∩ H¹(a, b; V*)` whose initial value `u(a) ∈ H`, the value at `a` of its
continuous representative, is not of the form `ι v`. Then `‖u(t)‖_V → ∞` as `t → a⁺`, outside a
null set. -/
theorem tendsto_norm_value_atTop (hV : Function.Surjective (inclusionInDoubleDual ℝ V))
    (hab : a < b) (u : EvolutionSpace ι a b)
    (hu : toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ ∉ range ι) :
    Tendsto (fun t ↦ ‖value u t‖) (𝓝[>] a ⊓ ae volume) atTop :=
  tendsto_norm_atTop_of_eventuallyEq_of_notMem_range hV
    ((toContinuousMap hab u).continuous.comp continuous_projIcc).continuousWithinAt
    ((value_ae_eq_toContinuousMap hab u).filter_mono (nhdsGT_inf_ae_le_ae_restrict_Ioo hab))
    (by simpa only [Function.comp_apply, projIcc_left])

/-- **The energy space is not contained in `C([a, b]; V)`.** Let `u` be an element of the energy
space whose initial value `u(a) ∈ H` is not of the form `ι v`. Then `u` has no representative with
values in `V` that is continuous from the right at `a`, let alone one continuous on `[a, b]`. -/
theorem not_exists_continuousWithinAt_ae_eq (hab : a < b) (u : EvolutionSpace ι a b)
    (hu : toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ ∉ range ι) :
    ¬ ∃ v : ℝ → V, ContinuousWithinAt v (Ioi a) a ∧
      value u =ᵐ[volume.restrict (Ioo a b)] v := fun ⟨v, hv, huv⟩ ↦
  not_exists_continuousWithinAt_eventuallyEq_of_notMem_range
    ((toContinuousMap hab u).continuous.comp continuous_projIcc).continuousWithinAt
    ((value_ae_eq_toContinuousMap hab u).filter_mono (nhdsGT_inf_ae_le_ae_restrict_Ioo hab))
    (by simpa only [Function.comp_apply, projIcc_left])
    ⟨v, hv, huv.filter_mono (nhdsGT_inf_ae_le_ae_restrict_Ioo hab)⟩

end EvolutionSpace

end TauCeti
