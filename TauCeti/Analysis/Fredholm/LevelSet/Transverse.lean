/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.FiniteDimensional
public import TauCeti.Analysis.Calculus.TangentCone.Chart
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Parametric transversality to a flattened set

Let `G : V × Λ → E` be a parametrized map between finite-dimensional real normed spaces and
`S ⊆ E` a set which is flattened near each of its points met by `G` by a `C^n` chart, with `C^n`
inverse, onto a fixed linear subspace `L`. The tangent space of `S` at such a point is the span of
its tangent cone, `Submodule.span ℝ (tangentConeAt ℝ S y)`. This file proves the transversality
theorem in its measure form for this situation: if the total derivative of `G` is transverse to
`S` at every point of a set `U` that `G` sends into `S`, then for almost every parameter `l` the
partial derivative in `V` is transverse to `S` at every such point of `U` over `l`.

This is `TauCeti.ae_isRegularParameterOn` applied, chart by chart, to the level equation
`P ∘ e ∘ G = 0`, where `e` is a flattening chart and `P` projects onto a complement of `L` along
`L`: near a point of `S` this equation cuts out `G⁻¹ S`, and its derivative is surjective exactly
when the derivative of `G` is transverse to `S` there
(`TauCeti.IsSliceChart.span_tangentConeAt_eq_comap`). Countably many charts suffice, since the set
of points to be covered is Lindelöf.

## Main results

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

variable {V Λ E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A composite `Q ∘ B` of linear maps is surjective exactly when `Q` is surjective and the range
of `B` together with the kernel of `Q` spans the middle space. -/
private theorem range_comp_eq_top_iff {R X Y Z : Type*} [Ring R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] {B : X →ₗ[R] Y} {Q : Y →ₗ[R] Z}
    (hQ : Surjective Q) :
    LinearMap.range (Q ∘ₗ B) = ⊤ ↔ LinearMap.range B ⊔ LinearMap.ker Q = ⊤ := by
  refine ⟨fun h ↦ eq_top_iff.2 fun y _ ↦ ?_, fun h ↦ eq_top_iff.2 fun z _ ↦ ?_⟩
  · obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 h (Q y)
    have hy : y = B x + (y - B x) := by abel
    rw [hy]
    refine Submodule.add_mem_sup (LinearMap.mem_range_self B x) ?_
    rw [LinearMap.mem_ker, map_sub, ← hx, LinearMap.comp_apply, sub_self]
  · obtain ⟨y, rfl⟩ := hQ z
    obtain ⟨b, ⟨x, rfl⟩, k, hk, rfl⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : y ∈ _)
    exact ⟨x, by rw [LinearMap.comp_apply, map_add, LinearMap.mem_ker.1 hk, add_zero]⟩

variable [MeasurableSpace Λ] [BorelSpace Λ] (ν : Measure Λ) [Measure.IsAddHaarMeasure ν]

/-- **Parametric transversality to a flattened set, measure form.** Let `G : V × Λ → E` be a
parametrized map and `S` a set flattened onto a linear subspace `L` by a `C^n` chart with `C^n`
inverse around each point of `S` that `G` reaches from `U`. If, at each point of `U` sent into `S`,
`G` is `C^n` and its derivative is transverse to `S`, then for almost every parameter `l` the
partial derivative of `G` in `V` is transverse to `S` at every point of `U` over `l` sent into `S`.

The smoothness order must exceed `max (dim V - codim L, 0)`, the Morse--Sard threshold of
`TauCeti.ae_isRegularParameterOn` for the level equations cutting out `G⁻¹ S`. -/
theorem ae_range_fderiv_comp_inl_sup_span_tangentConeAt_eq_top {G : V × Λ → E}
    {U : Set (V × Λ)} {S : Set E} {L : Submodule ℝ E} {n : ℕ∞ω}
    (hcont : ∀ z ∈ U, G z ∈ S → ContDiffAt ℝ n G z)
    (hchart : ∀ z ∈ U, G z ∈ S → ∃ e : OpenPartialHomeomorph E E, G z ∈ e.source ∧
      (∀ y ∈ e.source, ContDiffAt ℝ n e y) ∧ (∀ y ∈ e.target, ContDiffAt ℝ n e.symm y) ∧
      IsSliceChart e (L : Set E) S)
    (htotal : ∀ z ∈ U, G z ∈ S →
      LinearMap.range (fderiv ℝ G z : V × Λ →ₗ[ℝ] E) ⊔
        Submodule.span ℝ (tangentConeAt ℝ S (G z)) = ⊤)
    (hn : ((finrank ℝ V - (finrank ℝ E - finrank ℝ L) + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ l ∂ν, ∀ v, (v, l) ∈ U → G (v, l) ∈ S →
      LinearMap.range ((fderiv ℝ G (v, l)).comp (ContinuousLinearMap.inl ℝ V Λ) : V →ₗ[ℝ] E) ⊔
        Submodule.span ℝ (tangentConeAt ℝ S (G (v, l))) = ⊤ := by
  have hn0 : n ≠ 0 := fun h ↦ by simp [h] at hn
  -- A projection `P` onto a complement `C` of `L`, with kernel `L`.
  obtain ⟨C, hLC⟩ := L.exists_isCompl
  have hLC' := Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hLC
    L.closed_of_finiteDimensional
  set P : E →L[ℝ] C := C.projectionOntoL L hLC'.symm
  have hP : ∀ v, P v = 0 ↔ v ∈ L := fun v ↦ Submodule.projectionOntoL_apply_eq_zero_iff _
  have hPs : Surjective P := Submodule.projectionOntoL_surjective _
  have hfinrank : finrank ℝ C = finrank ℝ E - finrank ℝ L := by
    rw [← Submodule.finrank_add_eq_of_isCompl hLC, Nat.add_sub_cancel_left]
  -- A chart around each point to be covered, and an open neighbourhood mapped into its source.
  set Z := {z | z ∈ U ∧ G z ∈ S}
  have key : ∀ z : Z, ∃ e : OpenPartialHomeomorph E E, (∀ y ∈ e.source, ContDiffAt ℝ n e y) ∧
      (∀ y ∈ e.target, ContDiffAt ℝ n e.symm y) ∧ IsSliceChart e (L : Set E) S ∧
      (z : V × Λ) ∈ interior (G ⁻¹' e.source) := fun z ↦ by
    obtain ⟨e, hze, he, hes, hS⟩ := hchart z z.2.1 z.2.2
    refine ⟨e, he, hes, hS, mem_interior_iff_mem_nhds.2 ?_⟩
    exact ((hcont z z.2.1 z.2.2).continuousAt).preimage_mem_nhds (e.open_source.mem_nhds hze)
  choose e he hes hS hze using key
  obtain ⟨T, hTc, hTZ⟩ := (HereditarilyLindelofSpace.isLindelof Z).elim_countable_subcover
    (fun z : Z ↦ interior (G ⁻¹' (e z).source)) (fun _ ↦ isOpen_interior)
    fun z hz ↦ mem_iUnion.2 ⟨⟨z, hz⟩, hze ⟨z, hz⟩⟩
  -- The level equation of each chart: on the neighbourhood, it cuts out `G⁻¹ S`.
  set g : Z → V × Λ → C := fun z w ↦ P (e z (G w))
  set W : Z → Set (V × Λ) := fun z ↦ U ∩ interior (G ⁻¹' (e z).source)
  have hsol : ∀ z, ∀ w ∈ W z, g z w = 0 ↔ G w ∈ S := fun z w hw ↦ by
    have hwe : w ∈ G ⁻¹' (e z).source := interior_subset hw.2
    rw [hP, ← SetLike.mem_coe, ← (hS z).mem_iff hwe]
  -- The chart derivative is invertible, and transversality is surjectivity of the level equation.
  have hderiv : ∀ z, ∀ w ∈ W z, G w ∈ S → ∃ A : E ≃L[ℝ] E,
      HasFDerivAt (g z) (P.comp ((A : E →L[ℝ] E).comp (fderiv ℝ G w))) w ∧
      Submodule.span ℝ (tangentConeAt ℝ S (G w)) =
        LinearMap.ker (P.comp (A : E →L[ℝ] E) : E →ₗ[ℝ] C) := by
    intro z w hw hwS
    have hwe : w ∈ G ⁻¹' (e z).source := interior_subset hw.2
    obtain ⟨A, hA⟩ := (e z).exists_hasFDerivAt_of_chart hwe ((he z _ hwe).differentiableAt hn0)
      ((hes z _ ((e z).map_source hwe)).differentiableAt hn0)
    refine ⟨A, P.hasFDerivAt.comp w (hA.comp w
      ((hcont w hw.1 hwS).differentiableAt hn0).hasFDerivAt), ?_⟩
    rw [(hS z).span_tangentConeAt_eq_comap L.closed_of_finiteDimensional hwe hwS hA]
    ext v
    simp [hP]
  have hreg : ∀ z, ∀ᵐ l ∂ν, IsRegularParameterOn (g z) (W z) 0 l := fun z ↦ by
    refine ae_isRegularParameterOn ν (n := n) (fun w hw hw0 ↦ ?_) (fun w hw hw0 ↦ ?_)
      (by rwa [hfinrank])
    · have hwS := (hsol z w hw).1 hw0
      have hwe : w ∈ G ⁻¹' (e z).source := interior_subset hw.2
      exact P.contDiff.contDiffAt.comp w ((he z _ hwe).comp w (hcont w hw.1 hwS))
    · obtain ⟨A, hg, hker⟩ := hderiv z w hw ((hsol z w hw).1 hw0)
      rw [hg.fderiv]
      exact LinearMap.range_eq_top.1 ((range_comp_eq_top_iff
        (B := (fderiv ℝ G w : V × Λ →ₗ[ℝ] E)) (Q := (P.comp (A : E →L[ℝ] E) : E →ₗ[ℝ] C))
        (hPs.comp A.surjective)).2
        (by rw [← hker]; exact htotal w hw.1 ((hsol z w hw).1 hw0)))
  have hT : Countable T := hTc.to_subtype
  filter_upwards [(ae_all_iff.2 fun z : T ↦ hreg z)] with l hl v hvU hvS
  obtain ⟨z, hzT, hvz⟩ := mem_iUnion₂.1 (hTZ ⟨hvU, hvS⟩)
  have hw : (v, l) ∈ W z := ⟨hvU, hvz⟩
  obtain ⟨A, hg, hker⟩ := hderiv z (v, l) hw hvS
  have h := isRegularParameterOn_iff.1 (hl ⟨z, hzT⟩) v hw ((hsol z _ hw).2 hvS)
  rw [hg.fderiv] at h
  rw [hker]
  exact (range_comp_eq_top_iff (B := ((fderiv ℝ G (v, l)).comp
    (ContinuousLinearMap.inl ℝ V Λ) : V →ₗ[ℝ] E)) (Q := (P.comp (A : E →L[ℝ] E) : E →ₗ[ℝ] C))
    (hPs.comp A.surjective)).1
    (LinearMap.range_eq_top.2 h)

end TauCeti
