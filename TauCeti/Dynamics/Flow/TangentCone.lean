/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import TauCeti.Dynamics.Flow.Variational
import TauCeti.Analysis.Calculus.TangentCone.Chart
import TauCeti.Dynamics.Flow.Stable

/-!
# Tangent spaces of invariant sets along a flow

Let `ϕ` be a flow on a real normed space whose time maps are differentiable. A flow-invariant set
`S`, such as the stable or unstable set of a rest point, is carried onto itself by each time map
`ϕ t`, a homeomorphism with invertible derivative `Dϕ_t(x)` (`Flow.isInvertible_fderiv`). So
`Dϕ_t(x)` carries the tangent space of `S` at `x`, the span of its tangent cone, onto its tangent
space at `ϕ t x`. In particular, the transversality of two invariant sets, the condition that
their tangent spaces together span the whole space, holds at one point of an orbit if and only if
it holds at every point of that orbit.

## Main results

* `Flow.span_tangentConeAt_apply`: `Dϕ_t(x)` carries the tangent space of a flow-invariant set at
  `x` onto its tangent space at `ϕ t x`.
* `Flow.span_tangentConeAt_sup_span_tangentConeAt_apply_eq_top_iff`: two invariant sets are
  transverse at `ϕ t x` if and only if they are transverse at `x`.
-/

public section

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ϕ : Flow ℝ E} {t : ℝ} {x : E}

/-- **Tangent spaces of invariant sets along a flow.** When the time-`t` map is differentiable at
`x` and the time-`(-t)` map at `ϕ t x`, the derivative `Dϕ_t(x)` carries the tangent space at `x`
of a flow-invariant set onto its tangent space at `ϕ t x`. -/
theorem span_tangentConeAt_apply {S : Set E} (hS : IsInvariant ϕ S)
    (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x)) (ht : DifferentiableAt ℝ (ϕ t) x) :
    Submodule.span ℝ (tangentConeAt ℝ S (ϕ t x)) =
      (Submodule.span ℝ (tangentConeAt ℝ S x)).map (fderiv ℝ (ϕ t) x : E →ₗ[ℝ] E) := by
  obtain ⟨A, hA⟩ := ϕ.isInvertible_fderiv hs ht
  have hΦ : ⇑(ϕ.toHomeomorph t) = ϕ t := funext (ϕ.toHomeomorph_apply t)
  have hAd : HasFDerivAt (ϕ.toHomeomorph t) (A : E →L[ℝ] E) x := by
    rw [hΦ, hA]
    exact ht.hasFDerivAt
  have hST : ϕ.toHomeomorph t ⁻¹' S = S :=
    Set.ext fun z ↦ by rw [Set.mem_preimage, hΦ]; exact hS.flow_apply_mem_iff t
  rw [← hA, Submodule.map_span, ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe,
    TauCeti.image_tangentConeAt_eq_of_preimage_eq hST hAd, hΦ]

/-- **Transversality propagates along a flow.** When the time-`t` map is differentiable at `x`
and the time-`(-t)` map at `ϕ t x`, the tangent spaces of two flow-invariant sets span `E` at
`ϕ t x` if and only if they span `E` at `x`. -/
theorem span_tangentConeAt_sup_span_tangentConeAt_apply_eq_top_iff {S T : Set E}
    (hS : IsInvariant ϕ S) (hT : IsInvariant ϕ T) (hs : DifferentiableAt ℝ (ϕ (-t)) (ϕ t x))
    (ht : DifferentiableAt ℝ (ϕ t) x) :
    Submodule.span ℝ (tangentConeAt ℝ S (ϕ t x)) ⊔
        Submodule.span ℝ (tangentConeAt ℝ T (ϕ t x)) = ⊤ ↔
      Submodule.span ℝ (tangentConeAt ℝ S x) ⊔ Submodule.span ℝ (tangentConeAt ℝ T x) = ⊤ := by
  obtain ⟨A, hA⟩ := ϕ.isInvertible_fderiv hs ht
  rw [span_tangentConeAt_apply hS hs ht, span_tangentConeAt_apply hT hs ht, ← Submodule.map_sup,
    ← hA]
  exact Submodule.map_eq_top_iff

end Flow
