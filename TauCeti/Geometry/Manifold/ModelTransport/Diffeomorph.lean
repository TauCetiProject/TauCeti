/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.ModelTransport.Homeomorph

/-!
# Changing the model space along a diffeomorphism

Let `Φ : H ≃ₘ^n⟮I, I'⟯ H'` be a `C^n` diffeomorphism between two model spaces. Conjugating a
`C^n` chart change of `H` by `Φ` gives a `C^n` chart change of `H'`
(`Diffeomorph.symm_trans_trans_mem_contDiffGroupoid`). Consequently, a `C^n` manifold modelled
on `I` is a `C^n` manifold modelled on `I'` for the charts `Φ.toHomeomorph.chartedSpaceComp M`
(`Diffeomorph.isManifold_chartedSpaceComp`), and the identity of `M` is a `C^n` diffeomorphism
between the two atlases (`Diffeomorph.chartedSpaceCompDiffeomorph`).

For instance, a model with corners described as a subset of `ℂ` can be compared with Mathlib's
native half-spaces in this way.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}

namespace Diffeomorph

/-- Conjugating a member of the `C^n` groupoid of `I` by a `C^n` diffeomorphism of models gives a
member of the `C^n` groupoid of `I'`. -/
theorem symm_trans_trans_mem_contDiffGroupoid (Φ : H ≃ₘ^n⟮I, I'⟯ H')
    {e : OpenPartialHomeomorph H H} (he : e ∈ contDiffGroupoid n I) :
    Φ.toHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
        (e ≫ₕ Φ.toHomeomorph.toOpenPartialHomeomorph) ∈ contDiffGroupoid n I' := by
  -- Each groupoid member `f` read through `Φ` is `C^n` where `Φ.symm` lands in its source.
  have key : ∀ f ∈ contDiffGroupoid n I,
      ContMDiffOn I' I' n (Φ ∘ f ∘ Φ.symm) (Φ.symm ⁻¹' f.source) := fun f hf ↦
    Φ.contMDiff.comp_contMDiffOn
      ((contMDiffOn_of_mem_contDiffGroupoid hf).comp Φ.symm.contMDiff.contMDiffOn fun _ hv ↦ hv)
  have hrefl : OpenPartialHomeomorph.refl H' ∈ IsManifold.maximalAtlas I' n H' :=
    StructureGroupoid.subset_maximalAtlas _ (chartedSpaceSelf_atlas.mpr rfl)
  have h := symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn hrefl hrefl
    (f := Φ.toHomeomorph.toOpenPartialHomeomorph.symm ≫ₕ
      (e ≫ₕ Φ.toHomeomorph.toOpenPartialHomeomorph)) ?_ ?_
  · simpa only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans,
      OpenPartialHomeomorph.trans_refl] using h
  · refine (key e he).congr_mono (fun v _ ↦ ?_) fun v hv ↦ ?_
    · simp [OpenPartialHomeomorph.coe_trans]
    · simpa [OpenPartialHomeomorph.trans_source] using hv
  · refine (key e.symm ((contDiffGroupoid n I).symm he)).congr_mono (fun v _ ↦ ?_)
      fun v hv ↦ ?_
    · simp [OpenPartialHomeomorph.coe_trans_symm]
    · simpa [OpenPartialHomeomorph.trans_target] using hv

/-- A `C^n` manifold modelled on `I` is a `C^n` manifold modelled on `I'` for the charts
`Φ.toHomeomorph.chartedSpaceComp M` obtained by following its charts with a `C^n`
diffeomorphism of models `Φ`. -/
theorem isManifold_chartedSpaceComp (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I n M] :
    letI := Φ.toHomeomorph.chartedSpaceComp M
    IsManifold I' n M := by
  let := Φ.toHomeomorph.chartedSpaceComp M
  refine { compatible := ?_ }
  rw [Φ.toHomeomorph.atlas_chartedSpaceComp M]
  rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc c.symm]
  exact Φ.symm_trans_trans_mem_contDiffGroupoid (HasGroupoid.compatible hc hc')

/-- The identity of a `C^n` manifold `M` modelled on `I` is a `C^n` diffeomorphism from the charts
`Φ.toHomeomorph.chartedSpaceComp M`, modelled on `I'`, to the charts of `M`. -/
def chartedSpaceCompDiffeomorph (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I n M] :
    letI := Φ.toHomeomorph.chartedSpaceComp M
    M ≃ₘ^n⟮I', I⟯ M :=
  letI := Φ.toHomeomorph.chartedSpaceComp M
  haveI := Φ.isManifold_chartedSpaceComp M
  { toEquiv := Equiv.refl M
    contMDiff_toFun := fun x ↦ by
      -- Near `x`, the identity is the new chart at `x`, then `Φ⁻¹`, then the old chart inverse.
      have hc := Φ.toHomeomorph.chartAt_chartedSpaceComp x
      have h : ContMDiffOn I' I n ((chartAt H x).symm ∘ Φ.symm ∘ chartAt H' x)
          (chartAt H' x).source :=
        contMDiffOn_chart_symm.comp (Φ.symm.contMDiff.comp_contMDiffOn contMDiffOn_chart)
          fun y hy ↦ by simpa [hc] using (chartAt H x).map_source (by simpa [hc] using hy)
      refine (h.congr fun y hy ↦ ?_).contMDiffAt (chart_source_mem_nhds H' x)
      simpa [hc] using ((chartAt H x).left_inv (by simpa [hc] using hy)).symm
    contMDiff_invFun := fun x ↦ by
      -- Near `x`, the identity is the old chart at `x`, then `Φ`, then the new chart inverse.
      have hc := Φ.toHomeomorph.chartAt_chartedSpaceComp x
      have h : ContMDiffOn I I' n ((chartAt H' x).symm ∘ Φ ∘ chartAt H x)
          (chartAt H x).source :=
        contMDiffOn_chart_symm.comp (Φ.contMDiff.comp_contMDiffOn contMDiffOn_chart)
          fun y hy ↦ by simpa [hc] using (chartAt H x).map_source hy
      refine (h.congr fun y hy ↦ ?_).contMDiffAt (chart_source_mem_nhds H x)
      simpa [hc] using ((chartAt H x).left_inv hy).symm }

/-- The diffeomorphism `Φ.chartedSpaceCompDiffeomorph M` is the identity of `M`. -/
@[simp]
theorem coe_chartedSpaceCompDiffeomorph (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I n M] :
    letI := Φ.toHomeomorph.chartedSpaceComp M
    ⇑(Φ.chartedSpaceCompDiffeomorph M) = id :=
  (rfl)

/-- The inverse of `Φ.chartedSpaceCompDiffeomorph M` is the identity of `M`. -/
@[simp]
theorem coe_chartedSpaceCompDiffeomorph_symm (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M] :
    letI := Φ.toHomeomorph.chartedSpaceComp M
    ⇑(Φ.chartedSpaceCompDiffeomorph M).symm = id :=
  (rfl)

end Diffeomorph
