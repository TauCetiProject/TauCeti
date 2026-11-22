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
(`Diffeomorph.isManifold_chartedSpaceComp`). For any charted space `M` on `H`, the identity of `M`
is a `C^n` diffeomorphism between the two atlases (`Diffeomorph.chartedSpaceCompDiffeomorph`), so
`C^n` smoothness of maps into `M` is unchanged (`Diffeomorph.contMDiffAt_chartedSpaceComp_iff`,
`Diffeomorph.contMDiff_chartedSpaceComp_iff`).

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

/-- The identity of a charted space `M` on `H` is a `C^n` diffeomorphism from the charts
`Φ.toHomeomorph.chartedSpaceComp M`, modelled on `I'`, to the charts of `M`, modelled on `I`. -/
def chartedSpaceCompDiffeomorph (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] :
    letI := Φ.toHomeomorph.chartedSpaceComp M
    M ≃ₘ^n⟮I', I⟯ M :=
  letI := Φ.toHomeomorph.chartedSpaceComp M
  { toEquiv := Equiv.refl M
    contMDiff_toFun := fun x ↦ by
      -- In the charts at `x`, the identity reads as `Φ⁻¹` on the target of the new chart.
      have hc := Φ.toHomeomorph.chartAt_chartedSpaceComp x
      refine contMDiffAt_iff.2 ⟨continuousAt_id, ?_⟩
      have h := (contMDiffAt_iff.1 (Φ.symm.contMDiff (Φ (chartAt H x x)))).2
      simp only [mfld_simps] at h
      have hx : extChartAt I' x x = I' (Φ (chartAt H x x)) := by simp [hc]
      have ht := extChartAt_target_mem_nhdsWithin (I := I') x
      rw [hx] at ht ⊢
      refine h.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [ht] with y hy
        simp only [hc, mfld_simps] at hy
        have hy' : Φ.symm (I'.symm y) ∈ (chartAt H x).target := hy.2
        simp [hc, (chartAt H x).right_inv hy']
      · simp [hc]
    contMDiff_invFun := fun x ↦ by
      -- In the charts at `x`, the identity reads as `Φ` on the target of the old chart.
      have hc := Φ.toHomeomorph.chartAt_chartedSpaceComp x
      refine contMDiffAt_iff.2 ⟨continuousAt_id, ?_⟩
      have h := (contMDiffAt_iff.1 (Φ.contMDiff (chartAt H x x))).2
      simp only [mfld_simps] at h
      refine h.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
        simp only [mfld_simps] at hy
        simp [hc, (chartAt H x).right_inv hy.2]
      · simp [hc] }

/-- The diffeomorphism `Φ.chartedSpaceCompDiffeomorph M` is the identity of `M`. -/
@[simp]
theorem coe_chartedSpaceCompDiffeomorph (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] :
    letI := Φ.toHomeomorph.chartedSpaceComp M
    ⇑(Φ.chartedSpaceCompDiffeomorph M) = id :=
  (rfl)

/-- The inverse of `Φ.chartedSpaceCompDiffeomorph M` is the identity of `M`. -/
@[simp]
theorem coe_chartedSpaceCompDiffeomorph_symm (Φ : H ≃ₘ^n⟮I, I'⟯ H') (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] :
    letI := Φ.toHomeomorph.chartedSpaceComp M
    ⇑(Φ.chartedSpaceCompDiffeomorph M).symm = id :=
  (rfl)

/-- Changing the model space of `M` along a `C^n` diffeomorphism of models `Φ : H ≃ₘ^n⟮I, I'⟯ H'`
leaves `C^n` smoothness at `x` of any map `f : X → M` unchanged. -/
theorem contMDiffAt_chartedSpaceComp_iff (Φ : H ≃ₘ^n⟮I, I'⟯ H')
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H'' X]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {f : X → M} {x : X} :
    (letI := Φ.toHomeomorph.chartedSpaceComp M
     ContMDiffAt I'' I' n f x) ↔ ContMDiffAt I'' I n f x :=
  letI := Φ.toHomeomorph.chartedSpaceComp M
  ((Φ.chartedSpaceCompDiffeomorph M).contMDiffAt_diffeomorph_comp_iff le_rfl).symm

/-- Changing the model space of `M` along a `C^n` diffeomorphism of models `Φ : H ≃ₘ^n⟮I, I'⟯ H'`
leaves `C^n` smoothness of any map `f : X → M` unchanged. -/
theorem contMDiff_chartedSpaceComp_iff (Φ : H ≃ₘ^n⟮I, I'⟯ H')
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H'' X]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {f : X → M} :
    (letI := Φ.toHomeomorph.chartedSpaceComp M
     ContMDiff I'' I' n f) ↔ ContMDiff I'' I n f :=
  forall_congr' fun _ ↦ Φ.contMDiffAt_chartedSpaceComp_iff

end Diffeomorph
