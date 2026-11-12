/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.FiniteDimensional
public import TauCeti.Analysis.Calculus.TangentCone.Chart
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Complement

/-!
# Parametric transversality to a flattened set

Let `G : V × Λ → E` be a parametrized map of real normed spaces, with `V` and `Λ`
finite-dimensional, and `S ⊆ E` a set which is flattened near each of its points met by `G`, onto a
fixed linear subspace `L` of a finite-dimensional model space `F`, by a chart that is `C^n` along
`S` with inverse differentiable along `S`. The tangent space of `S` at such a point is the span of
its tangent cone, `Submodule.span ℝ (tangentConeAt ℝ S y)`. This file proves the transversality
theorem in its measure form for this situation: if the total derivative of `G` is transverse to `S`
at every point of a set `U` that `G` sends into `S`, then for almost every parameter `l` the partial
derivative in `V` is transverse to `S` at every such point of `U` over `l`.

This is `TauCeti.ae_isRegularParameterOn` applied, chart by chart, to the level equation
`P ∘ e ∘ G = 0`, where `e` is a flattening chart and `P` projects onto a complement of `L` along
`L`: near a point of `S` this equation cuts out `G⁻¹ S`, and its derivative is surjective exactly
when the derivative of `G` is transverse to `S` there
(`TauCeti.IsSliceChart.span_tangentConeAt_eq_comap`). Countably many charts suffice, since the set
of points to be covered is Lindelöf.

## Main results

* `TauCeti.IsSliceChart.ae_range_fderiv_comp_inl_sup_span_tangentConeAt_eq_top`: the statement
  for the points that `G` sends into the source of one flattening chart.
* `TauCeti.ae_range_fderiv_comp_inl_sup_span_tangentConeAt_eq_top`: for almost every parameter,
  the partial derivatives in `V` are transverse to `S`.

## References

* V. Guillemin, A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 2 §3.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 3, Theorem 2.7.
-/

public section

open Filter Function MeasureTheory Module Set
open scoped ContDiff Topology

namespace TauCeti

/-- A composite `f ∘ g` with `f` surjective is surjective exactly when the range of `g` and the
kernel of `f` together span. -/
private theorem surjective_comp_iff_range_sup_ker_eq_top {X Y F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Y →L[ℝ] F} (hf : LinearMap.range (f : Y →ₗ[ℝ] F) = ⊤) (g : X →L[ℝ] Y) :
    Surjective (f.comp g) ↔
      LinearMap.range (g : X →ₗ[ℝ] Y) ⊔ LinearMap.ker (f : Y →ₗ[ℝ] F) = ⊤ := by
  rw [← LinearMap.map_eq_top_iff hf, ← LinearMap.range_comp]
  exact LinearMap.range_eq_top.symm

variable {V Λ E F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

variable [MeasurableSpace Λ] [BorelSpace Λ] (ν : Measure Λ) [Measure.IsAddHaarMeasure ν]

/-- **Parametric transversality in one chart.** Let `e : E → F` be a chart flattening `S` onto a
linear subspace `L` of `F`, which is `C^n` at the points of `S` with inverse differentiable at their
images. If, at each point of `U` sent into `S` within the source of `e`, the map `G` is `C^n` and
its derivative is transverse to `S`, then for almost every parameter `l` the partial derivative of
`G` in `V` is transverse to `S` at every point of `U` over `l` sent into `S` within the source of
`e`. The smoothness order must exceed `max (dim V - codim L, 0)`. -/
theorem IsSliceChart.ae_range_fderiv_comp_inl_sup_span_tangentConeAt_eq_top {G : V × Λ → E}
    {U : Set (V × Λ)} {S : Set E} {L : Submodule ℝ F} {n : ℕ∞ω} {e : OpenPartialHomeomorph E F}
    (hS : IsSliceChart e (L : Set F) S) (he : ∀ y ∈ e.source, y ∈ S → ContDiffAt ℝ n e y)
    (hes : ∀ y ∈ e.source, y ∈ S → DifferentiableAt ℝ e.symm (e y))
    (hcont : ∀ z ∈ U, G z ∈ e.source → G z ∈ S → ContDiffAt ℝ n G z)
    (htotal : ∀ z ∈ U, G z ∈ e.source → G z ∈ S →
      LinearMap.range (fderiv ℝ G z : V × Λ →ₗ[ℝ] E) ⊔
        Submodule.span ℝ (tangentConeAt ℝ S (G z)) = ⊤)
    (hn : ((finrank ℝ V - (finrank ℝ F - finrank ℝ L) + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ l ∂ν, ∀ v, (v, l) ∈ U → G (v, l) ∈ e.source → G (v, l) ∈ S →
      LinearMap.range ((fderiv ℝ G (v, l)).comp (ContinuousLinearMap.inl ℝ V Λ) : V →ₗ[ℝ] E) ⊔
        Submodule.span ℝ (tangentConeAt ℝ S (G (v, l))) = ⊤ := by
  have hn0 : n ≠ 0 := fun h ↦ by simp [h] at hn
  -- The level equation `P ∘ e ∘ G = 0`, with `P` the projection onto a complement `C` of `L`.
  obtain ⟨C, hLC⟩ := L.exists_isCompl
  have hCL := (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hLC
    L.isClosed_of_finiteDimensional).symm
  set P : F →L[ℝ] C := C.projectionOntoL L hCL
  have hfinrank : finrank ℝ C = finrank ℝ F - finrank ℝ L := by
    rw [← Submodule.finrank_add_eq_of_isCompl hLC, Nat.add_sub_cancel_left]
  set W := U ∩ G ⁻¹' e.source
  have hsol : ∀ w ∈ W, P (e (G w)) = 0 ↔ G w ∈ S := fun w hw ↦ by
    rw [Submodule.projectionOntoL_apply_eq_zero_iff, ← SetLike.mem_coe, ← hS.mem_iff hw.2]
  -- At a solution the chart has an invertible derivative `A`, and `P ∘ A` is a surjection whose
  -- kernel is the tangent space of `S`.
  have hderiv : ∀ w ∈ W, G w ∈ S → ∃ A : E ≃L[ℝ] F,
      HasFDerivAt (fun w ↦ P (e (G w))) ((P.comp (A : E →L[ℝ] F)).comp (fderiv ℝ G w)) w ∧
      LinearMap.range (P.comp (A : E →L[ℝ] F) : E →ₗ[ℝ] C) = ⊤ ∧
      Submodule.span ℝ (tangentConeAt ℝ S (G w)) =
        LinearMap.ker (P.comp (A : E →L[ℝ] F) : E →ₗ[ℝ] C) := by
    intro w hw hwS
    obtain ⟨A, hA⟩ := e.exists_hasFDerivAt_of_chart hw.2 ((he _ hw.2 hwS).differentiableAt hn0)
      (hes _ hw.2 hwS)
    refine ⟨A, (P.hasFDerivAt.comp (G w) hA).comp w
      ((hcont w hw.1 hw.2 hwS).differentiableAt hn0).hasFDerivAt,
      LinearMap.range_eq_top.2 <| (Submodule.projectionOntoL_surjective hCL).comp A.surjective, ?_⟩
    rw [hS.span_tangentConeAt_eq_comap L.isClosed_of_finiteDimensional hw.2 hwS hA]
    ext v
    simp [P]
  have hreg : ∀ᵐ l ∂ν, IsRegularParameterOn (fun w ↦ P (e (G w))) W 0 l := by
    refine ae_isRegularParameterOn ν (n := n) (fun w hw hw0 ↦ ?_) (fun w hw hw0 ↦ ?_)
      (by rwa [hfinrank])
    · have hwS := (hsol w hw).1 hw0
      exact P.contDiff.contDiffAt.comp w ((he _ hw.2 hwS).comp w (hcont w hw.1 hw.2 hwS))
    · have hwS := (hsol w hw).1 hw0
      obtain ⟨A, hg, hrange, hker⟩ := hderiv w hw hwS
      rw [hg.fderiv, surjective_comp_iff_range_sup_ker_eq_top hrange, ← hker]
      exact htotal w hw.1 hw.2 hwS
  filter_upwards [hreg] with l hl v hvU hve hvS
  obtain ⟨A, hg, hrange, hker⟩ := hderiv (v, l) ⟨hvU, hve⟩ hvS
  have h := isRegularParameterOn_iff.1 hl v ⟨hvU, hve⟩ ((hsol _ ⟨hvU, hve⟩).2 hvS)
  rwa [hg.fderiv, ContinuousLinearMap.comp_assoc, surjective_comp_iff_range_sup_ker_eq_top hrange,
    ← hker] at h

/-- **Parametric transversality to a flattened set, measure form.** Let `G : V × Λ → E` be a
parametrized map and `S` a set flattened onto a linear subspace `L`, by a chart that is `C^n` along
`S` with inverse differentiable along `S`, around each point of `S` that `G` reaches from `U`. If,
at each point of `U` sent into `S`, `G` is `C^n` and its derivative is transverse to `S`, then for
almost every parameter `l` the partial derivative of `G` in `V` is transverse to `S` at every point
of `U` over `l` sent into `S`.

The smoothness order must exceed `max (dim V - codim L, 0)`, the Morse--Sard threshold of
`TauCeti.ae_isRegularParameterOn` for the level equations cutting out `G⁻¹ S`. -/
theorem ae_range_fderiv_comp_inl_sup_span_tangentConeAt_eq_top {G : V × Λ → E}
    {U : Set (V × Λ)} {S : Set E} {L : Submodule ℝ F} {n : ℕ∞ω}
    (hcont : ∀ z ∈ U, G z ∈ S → ContDiffAt ℝ n G z)
    (hchart : ∀ z ∈ U, G z ∈ S → ∃ e : OpenPartialHomeomorph E F, G z ∈ e.source ∧
      (∀ y ∈ e.source, y ∈ S → ContDiffAt ℝ n e y) ∧
      (∀ y ∈ e.source, y ∈ S → DifferentiableAt ℝ e.symm (e y)) ∧ IsSliceChart e (L : Set F) S)
    (htotal : ∀ z ∈ U, G z ∈ S →
      LinearMap.range (fderiv ℝ G z : V × Λ →ₗ[ℝ] E) ⊔
        Submodule.span ℝ (tangentConeAt ℝ S (G z)) = ⊤)
    (hn : ((finrank ℝ V - (finrank ℝ F - finrank ℝ L) + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ l ∂ν, ∀ v, (v, l) ∈ U → G (v, l) ∈ S →
      LinearMap.range ((fderiv ℝ G (v, l)).comp (ContinuousLinearMap.inl ℝ V Λ) : V →ₗ[ℝ] E) ⊔
        Submodule.span ℝ (tangentConeAt ℝ S (G (v, l))) = ⊤ := by
  -- A chart around each point to be covered, with an open neighbourhood mapped into its source.
  set Z := {z | z ∈ U ∧ G z ∈ S}
  have key : ∀ z : Z, ∃ e : OpenPartialHomeomorph E F,
      (∀ y ∈ e.source, y ∈ S → ContDiffAt ℝ n e y) ∧
      (∀ y ∈ e.source, y ∈ S → DifferentiableAt ℝ e.symm (e y)) ∧ IsSliceChart e (L : Set F) S ∧
      (z : V × Λ) ∈ interior (G ⁻¹' e.source) := fun z ↦ by
    obtain ⟨e, hze, he, hes, hS⟩ := hchart z z.2.1 z.2.2
    refine ⟨e, he, hes, hS, mem_interior_iff_mem_nhds.2 ?_⟩
    exact ((hcont z z.2.1 z.2.2).continuousAt).preimage_mem_nhds (e.open_source.mem_nhds hze)
  choose e he hes hS hze using key
  -- Countably many of these neighbourhoods cover, and each chart contributes a null set.
  obtain ⟨T, hTc, hTZ⟩ := (HereditarilyLindelofSpace.isLindelof Z).elim_countable_subcover
    (fun z : Z ↦ interior (G ⁻¹' (e z).source)) (fun _ ↦ isOpen_interior)
    fun z hz ↦ mem_iUnion.2 ⟨⟨z, hz⟩, hze ⟨z, hz⟩⟩
  have : Countable T := hTc.to_subtype
  filter_upwards [ae_all_iff.2 fun z : T ↦
    (hS z).ae_range_fderiv_comp_inl_sup_span_tangentConeAt_eq_top ν (he z) (hes z)
      (fun z hz _ ↦ hcont z hz) (fun z hz _ ↦ htotal z hz) hn]
    with l hl v hvU hvS
  obtain ⟨z, hzT, hvz⟩ := mem_iUnion₂.1 (hTZ ⟨hvU, hvS⟩)
  exact hl ⟨z, hzT⟩ v hvU (mem_preimage.1 (interior_subset hvz)) hvS

end TauCeti
