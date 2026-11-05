/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Calculus.TangentCone.Chart
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Transverse discs in a flattened set

Let a chart `e` flatten a set `S` onto a closed linear subspace `L` near a point `y` of `S`, and
let `π : E →L[𝕜] G` be a continuous linear surjection onto a finite-dimensional space. If the
tangent space of `S` at `y` and the kernel of `π` together span `E`, then `π` maps the tangent
space of `S` onto `G`, and `S` contains a disc through `y` that `π` sees as a chart of `G`: a map
`ψ : G → E` with `ψ 0 = y`, strictly differentiable at `0` with derivative `ψ'` satisfying
`π ∘ ψ' = id`, whose values near `0` lie in `S`.

When `π` is the projection of a product onto one factor, the disc is parametrized by that factor
and its derivative is a section of the projection. Discs of this kind, in an unstable manifold
crossing the stable plane of a hyperbolic box, are the input of the gluing of broken Morse
trajectories. The disc is `z ↦ e⁻¹ (e y + s z)` for a continuous linear right inverse
`s : G → L` of the restriction of `π ∘ A⁻¹` to `L`, where `A` is the derivative of `e` at `y`.

## Main results

* `TauCeti.IsSliceChart.exists_hasStrictFDerivAt_comp_eq_id`: a flattened set transverse to the
  kernel of a surjection onto a finite-dimensional space contains a disc on which the surjection
  restricts to a chart.

## References

* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §5.
-/

public section

open Filter Set Topology

namespace TauCeti

namespace IsSliceChart

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {e : OpenPartialHomeomorph E F} {L : Submodule 𝕜 F} {S : Set E} {y : E} {A : E ≃L[𝕜] F}

/-- **A transverse disc in a flattened set.** Let the chart `e`, strictly differentiable at `y`
with invertible derivative `A`, flatten `S` onto a closed subspace `L` near the point `y` of `S`.
If the tangent space of `S` at `y` and the kernel of a continuous linear surjection `π` onto a
finite-dimensional space span `E`, then there is a map `ψ` with `ψ 0 = y`, strictly differentiable
at `0` with derivative `ψ'` such that `π ∘ ψ' = id`, whose values near `0` lie in `S`. -/
theorem exists_hasStrictFDerivAt_comp_eq_id (h : IsSliceChart e (L : Set F) S)
    (hL : IsClosed (L : Set F)) (hy : y ∈ e.source) (hyS : y ∈ S)
    (hA : HasStrictFDerivAt e (A : E →L[𝕜] F) y) {π : E →L[𝕜] G} (hπ : π.range = ⊤)
    (htr : Submodule.span 𝕜 (tangentConeAt 𝕜 S y) ⊔ π.ker = ⊤) :
    ∃ (ψ : G → E) (ψ' : G →L[𝕜] E), HasStrictFDerivAt ψ ψ' 0 ∧
      π ∘L ψ' = ContinuousLinearMap.id 𝕜 G ∧ ψ 0 = y ∧ ∀ᶠ z in 𝓝 0, ψ z ∈ S := by
  rw [h.span_tangentConeAt_eq_comap hL hy hyS hA.hasFDerivAt] at htr
  -- `π` maps the tangent space `A⁻¹ L` onto `G`, so `π ∘ A⁻¹` has a right inverse on `L`.
  set P : L →L[𝕜] G := π ∘L (A.symm : F →L[𝕜] E) ∘L L.subtypeL with hPdef
  have hP : P.range = ⊤ := by
    refine eq_top_iff.2 fun g _ ↦ ?_
    obtain ⟨x, rfl⟩ : g ∈ π.range := hπ ▸ Submodule.mem_top
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (htr ▸ Submodule.mem_top : x ∈ _)
    refine ⟨⟨A u, hu⟩, ?_⟩
    simp_all [P]
  obtain ⟨s, hs⟩ := P.exists_rightInverse_of_surjective hP
  have hey : e y ∈ L := (h.mem_iff hy).1 hyS
  have hyt : e y ∈ e.target := e.map_source hy
  have hlin : HasStrictFDerivAt (fun z ↦ e y + (s z : F)) (L.subtypeL ∘L s) 0 :=
    (L.subtypeL ∘L s).hasStrictFDerivAt.const_add (e y)
  refine ⟨fun z ↦ e.symm (e y + (s z : F)), (A.symm : F →L[𝕜] E) ∘L L.subtypeL ∘L s, ?_, ?_,
    by simp [e.left_inv hy], ?_⟩
  · have hsymm : HasStrictFDerivAt e.symm (A.symm : F →L[𝕜] E) (e y + (s 0 : F)) := by
      simpa using e.hasStrictFDerivAt_symm hyt (by rwa [e.left_inv hy])
    exact hsymm.comp 0 hlin
  · rw [← hs, hPdef, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
  · -- Near `0`, the point `e y + s z` lies in `L` and in the target of `e`.
    have ht : ∀ᶠ z in 𝓝 (0 : G), e y + (s z : F) ∈ e.target :=
      hlin.continuousAt.preimage_mem_nhds (by simpa using e.open_target.mem_nhds hyt)
    filter_upwards [ht] with z hz
    rw [h.mem_iff (e.map_target hz), e.right_inv hz]
    exact L.add_mem hey (s z).2

end IsSliceChart

end TauCeti
