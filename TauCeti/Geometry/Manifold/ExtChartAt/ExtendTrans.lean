/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Transported extended charts

For a boundaryless model `I`, a chart `c` read in the model vector space and then moved by a
homeomorphism `Ψ` is again a chart, `OpenPartialHomeomorph.extendTrans`. When the charts lie in the
maximal atlas and `Ψ` is smooth with smooth inverse, the transition maps between such charts are
smooth; such charts are recorded by `OpenPartialHomeomorph.IsExtendTransChart`.

## Main results

* `OpenPartialHomeomorph.extendTrans` and `OpenPartialHomeomorph.contDiffOn_extendTrans_comp_symm`:
  charts read in the model vector space and moved by a homeomorphism, and their smooth transition
  maps; `OpenPartialHomeomorph.coe_extendTrans` and
  `OpenPartialHomeomorph.toPartialEquiv_extendTrans_refl` relate them to
  `OpenPartialHomeomorph.extend`.
* `OpenPartialHomeomorph.IsExtendTransChart`, with its characterisation
  `OpenPartialHomeomorph.isExtendTransChart_iff`, its intro lemma
  `OpenPartialHomeomorph.isExtendTransChart_extendTrans` and its smooth transition maps
  `OpenPartialHomeomorph.IsExtendTransChart.contDiffOn_comp_symm`.
-/

public section

open scoped ContDiff Manifold Topology

namespace OpenPartialHomeomorph

section ExtendTrans

variable {𝕜 E F H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [TopologicalSpace H]
  [TopologicalSpace M]

/-- A chart `c` of `M`, read in the vector space `E` of a boundaryless model `I` and then moved to
`F` by a homeomorphism `Ψ`. Its coordinates are `Ψ ∘ c.extend I`. -/
noncomputable def extendTrans (c : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H)
    [I.Boundaryless] (Ψ : E ≃ₜ F) : OpenPartialHomeomorph M F :=
  (c.trans I.toHomeomorph.toOpenPartialHomeomorph).trans Ψ.toOpenPartialHomeomorph

variable (c : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  (Ψ : E ≃ₜ F)

/-- The source of `c.extendTrans I Ψ` is the source of `c`. -/
@[simp]
theorem extendTrans_source : (c.extendTrans I Ψ).source = c.source := by
  simp [extendTrans, mfld_simps]

/-- The target of `c.extendTrans I Ψ` is the target of `c`, read in `E` and moved by `Ψ`. -/
@[simp]
theorem extendTrans_target :
    (c.extendTrans I Ψ).target = Ψ.symm ⁻¹' (I.symm ⁻¹' c.target) := by
  ext v
  simp [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply]

/-- The chart `c.extendTrans I Ψ` reads a point through `c`, then `I`, then `Ψ`. -/
@[simp]
theorem extendTrans_apply (w : M) : c.extendTrans I Ψ w = Ψ (I (c w)) := by
  simp [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_apply]

/-- The inverse of `c.extendTrans I Ψ` is the inverse of `Ψ`, then of `I`, then of `c`. -/
@[simp]
theorem extendTrans_symm_apply (v : F) :
    (c.extendTrans I Ψ).symm v = c.symm (I.symm (Ψ.symm v)) := by
  simp [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply]

/-- The coordinates of `c.extendTrans I Ψ` are those of the extended chart `c.extend I`, moved
by `Ψ`. -/
theorem coe_extendTrans : ⇑(c.extendTrans I Ψ) = Ψ ∘ c.extend I := by
  funext w
  simp

/-- Moved by the identity, the chart `c.extendTrans I` is the extended chart `c.extend I`. -/
theorem toPartialEquiv_extendTrans_refl :
    (c.extendTrans I (Homeomorph.refl E)).toPartialEquiv = c.extend I :=
  PartialEquiv.ext (fun w ↦ by simp) (fun v ↦ by simp) (by simp)

/-- Moved by the identity, the coordinates of `c.extendTrans I` are those of the extended chart
`c.extend I`. -/
theorem coe_extendTrans_refl : ⇑(c.extendTrans I (Homeomorph.refl E)) = c.extend I :=
  congrArg (⇑) (c.toPartialEquiv_extendTrans_refl I)

/-- A chart with values in a normed space, read in its own self model and moved by the identity,
is the chart itself. -/
@[simp]
theorem extendTrans_modelWithCornersSelf_refl (e : OpenPartialHomeomorph M E) :
    e.extendTrans 𝓘(𝕜, E) (Homeomorph.refl E) = e := by
  refine OpenPartialHomeomorph.ext _ _ (fun w ↦ ?_) (fun v ↦ ?_) (extendTrans_source _ _ _)
  · simp
  · simp

/-- The transition map between two charts `c.extendTrans I Ψ` is `C^m` when `c` runs over the
maximal atlas of `M` and `Ψ` over homeomorphisms that are `C^m` with `C^m` inverses. -/
theorem contDiffOn_extendTrans_comp_symm [NormedSpace 𝕜 F] [ChartedSpace H M] {m : ℕ∞ω}
    {c₁ c₂ : OpenPartialHomeomorph M H} (hc₁ : c₁ ∈ IsManifold.maximalAtlas I m M)
    (hc₂ : c₂ ∈ IsManifold.maximalAtlas I m M) {Ψ₁ Ψ₂ : E ≃ₜ F}
    (hΨ₁ : ContDiff 𝕜 m Ψ₁.symm) (hΨ₂ : ContDiff 𝕜 m Ψ₂) :
    ContDiffOn 𝕜 m (c₂.extendTrans I Ψ₂ ∘ (c₁.extendTrans I Ψ₁).symm)
      ((c₁.extendTrans I Ψ₁).symm ≫ₕ c₂.extendTrans I Ψ₂).source := by
  have hmaps : Set.MapsTo Ψ₁.symm ((c₁.extendTrans I Ψ₁).symm ≫ₕ c₂.extendTrans I Ψ₂).source
      (I.extendCoordChange c₁ c₂).source := by
    intro v hv
    simp only [extendTrans, mfld_simps, ModelWithCorners.toHomeomorph_symm_apply] at hv ⊢
    exact ⟨⟨by simp [I.range_eq_univ], hv.1⟩, hv.2⟩
  refine (hΨ₂.comp_contDiffOn ((I.contDiffOn_extendCoordChange hc₁ hc₂).comp
    hΨ₁.contDiffOn hmaps)).congr fun v _ ↦ ?_
  simp [mfld_simps]

end ExtendTrans

section IsExtendTransChart

variable {𝕜 E F H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

/-- `e` is a chart `c.extendTrans I Ψ`: a chart `c` of `M` from its maximal atlas for `C^m`, read in
the model vector space `E` and moved to `F` by a `C^m` homeomorphism `Ψ` with `C^m` inverse. The
transition maps between such charts are `C^m`
(`OpenPartialHomeomorph.contDiffOn_extendTrans_comp_symm`). -/
def IsExtendTransChart (e : OpenPartialHomeomorph M F) (I : ModelWithCorners 𝕜 E H)
    [I.Boundaryless] (m : ℕ∞ω) : Prop :=
  ∃ (c : OpenPartialHomeomorph M H) (Ψ : E ≃ₜ F),
    c ∈ IsManifold.maximalAtlas I m M ∧ ContDiff 𝕜 m Ψ ∧ ContDiff 𝕜 m Ψ.symm ∧
      e = c.extendTrans I Ψ

variable {I : ModelWithCorners 𝕜 E H} [I.Boundaryless] {m : ℕ∞ω}

/-- Characterisation of `OpenPartialHomeomorph.IsExtendTransChart`: `e` is `c.extendTrans I Ψ` for
a chart `c` from the maximal atlas for `C^m` and a `C^m` homeomorphism `Ψ` with `C^m` inverse. -/
theorem isExtendTransChart_iff {e : OpenPartialHomeomorph M F} :
    e.IsExtendTransChart I m ↔ ∃ (c : OpenPartialHomeomorph M H) (Ψ : E ≃ₜ F),
      c ∈ IsManifold.maximalAtlas I m M ∧ ContDiff 𝕜 m Ψ ∧ ContDiff 𝕜 m Ψ.symm ∧
        e = c.extendTrans I Ψ :=
  Iff.rfl

/-- A chart `c` from the maximal atlas for `C^m`, moved by a `C^m` homeomorphism `Ψ` with `C^m`
inverse, satisfies `OpenPartialHomeomorph.IsExtendTransChart`. -/
theorem isExtendTransChart_extendTrans {c : OpenPartialHomeomorph M H}
    (hc : c ∈ IsManifold.maximalAtlas I m M) {Ψ : E ≃ₜ F} (hΨ : ContDiff 𝕜 m Ψ)
    (hΨ' : ContDiff 𝕜 m Ψ.symm) : (c.extendTrans I Ψ).IsExtendTransChart I m :=
  ⟨c, Ψ, hc, hΨ, hΨ', rfl⟩

/-- The transition map between two charts satisfying `OpenPartialHomeomorph.IsExtendTransChart`
for `C^m` is `C^m`. -/
theorem IsExtendTransChart.contDiffOn_comp_symm {e₁ e₂ : OpenPartialHomeomorph M F}
    (he₁ : e₁.IsExtendTransChart I m) (he₂ : e₂.IsExtendTransChart I m) :
    ContDiffOn 𝕜 m (e₂ ∘ e₁.symm) (e₁.symm ≫ₕ e₂).source := by
  obtain ⟨c₁, Ψ₁, hc₁, -, hΨ₁, rfl⟩ := he₁
  obtain ⟨c₂, Ψ₂, hc₂, hΨ₂, -, rfl⟩ := he₂
  exact contDiffOn_extendTrans_comp_symm I hc₁ hc₂ hΨ₁ hΨ₂

end IsExtendTransChart

end OpenPartialHomeomorph
