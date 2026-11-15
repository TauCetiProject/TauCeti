/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.ModelWithCorners.ModelHomeomorph

/-!
# Immersions and diffeomorphisms across a linear change of models

Mathlib's `Manifold.IsImmersionAtOfComplement.comp_diffeomorph`, and Tau Ceti's
`TauCeti.isImmersionAtOfComplement_comp_diffeomorph`, compose an immersion with a diffeomorphism
for a *single* model with corners. A diffeomorphism between manifolds modelled on different
models gives no map between their model spaces, so its charts cannot be transported in general.

They can when the two models are related by a continuous linear equivalence `A : E₁ ≃L E` of
their vector spaces carrying the range of one model onto the range of the other: then
`h ↦ I.symm (A (I₁ h))` is a homeomorphism of the model spaces, read linearly through the models
(`ContinuousLinearEquiv.modelHomeomorph`).
A chart of the old manifold, followed by this homeomorphism and pulled back along the
diffeomorphism, is a chart of the new one, and a normal form `u ↦ (u, 0)` read in the old charts
becomes the normal form for the conjugated linear equivalence in the new ones. The basic example
is the product of a boundaryless model with the half-line, which is linearly the half-space one
dimension up: a diffeomorphism from a product with an interval onto a manifold with boundary
modelled on a half-space moves immersions between the two models.

## Main results

* `TauCeti.isImmersionAtOfComplement_comp_diffeomorph_of_image_range_eq` and
  `TauCeti.isImmersionAt_comp_diffeomorph_of_image_range_eq`: precomposing with a diffeomorphism
  whose source model is linearly related to the old one preserves immersions.
* `TauCeti.isImmersionAtOfComplement_diffeomorph_comp_of_image_range_eq` and
  `TauCeti.isImmersionAt_diffeomorph_comp_of_image_range_eq`: the same for postcomposing.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, for immersions of
  manifolds with boundary and their behaviour under composition.
-/

public section

noncomputable section

namespace TauCeti

open Manifold Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {H : Type*} [TopologicalSpace H] {H₁ : Type*} [TopologicalSpace H₁]
  {I : ModelWithCorners 𝕜 E H} {I₁ : ModelWithCorners 𝕜 E₁ H₁}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {E₁' : Type*} [NormedAddCommGroup E₁'] [NormedSpace 𝕜 E₁']
  {G : Type*} [TopologicalSpace G] {G₁ : Type*} [TopologicalSpace G₁]
  {J : ModelWithCorners 𝕜 E' G} {J₁ : ModelWithCorners 𝕜 E₁' G₁}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N₁ : Type*} [TopologicalSpace N₁] [ChartedSpace G₁ N₁]
  {n m : ℕ∞ω} {f : M → N}

/-! ### Precomposing with a diffeomorphism -/

/-- Precomposing a `C^n` immersion with a `C^m` diffeomorphism `e : M₁ ≃ₘ M`, `n ≤ m`, preserves
the immersion normal form at a point, when the model of `M₁` is related to that of `M` by a
continuous linear equivalence `A : E₁ ≃L E` carrying the range of one model onto the range of the
other. The complement stays the same, and the linear equivalence of the normal form is precomposed
with `A × id`. -/
theorem isImmersionAtOfComplement_comp_diffeomorph_of_image_range_eq [IsManifold I₁ n M₁]
    (A : E₁ ≃L[𝕜] E) (hA : A '' range I₁ = range I) (e : M₁ ≃ₘ^m⟮I₁, I⟯ M) (hnm : n ≤ m)
    {x : M₁}
    (h : IsImmersionAtOfComplement F I J n f (e x)) :
    IsImmersionAtOfComplement F I₁ J n (f ∘ e) x := by
  have hA' : A.symm '' range I = range I₁ := by
    rw [← hA, ← image_comp]
    simp
  set φ' := (e.toHomeomorph.transOpenPartialHomeomorph h.domChart).transHomeomorph
    (A.symm.modelHomeomorph hA')
  have hsource : φ'.source = ⇑e ⁻¹' h.domChart.source := rfl
  refine IsImmersionAtOfComplement.mk_of_charts
    ((A.prodCongr (ContinuousLinearEquiv.refl 𝕜 F)).trans h.equiv) φ' h.codChart
    (by rw [hsource]; exact h.mem_domChart_source) h.mem_codChart_source
    (A.symm.transHomeomorph_modelHomeomorph_mem_maximalAtlas hA' e hnm
      h.domChart_mem_maximalAtlas)
    h.codChart_mem_maximalAtlas
    (by rw [hsource]; exact fun _ hy ↦ h.source_subset_preimage_source hy) fun u hu ↦ ?_
  -- A point of the new chart target is `A⁻¹` of a point of the old chart target.
  rw [OpenPartialHomeomorph.extend_target'] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  -- The targets of `transOpenPartialHomeomorph` and `transHomeomorph` are those of their
  -- partial-equivalence constructions, which unfold to the preimage of the old target.
  have hw : (A.symm.modelHomeomorph hA').symm w ∈ h.domChart.target := hw
  have hv : A (I₁ w) ∈ (h.domChart.extend I).target := by
    rw [OpenPartialHomeomorph.extend_target']
    refine ⟨(A.symm.modelHomeomorph hA').symm w, hw, ?_⟩
    rw [ContinuousLinearEquiv.model_modelHomeomorph_symm, ContinuousLinearEquiv.symm_symm]
  have hmh : (A.symm.modelHomeomorph hA').symm w = I.symm (A (I₁ w)) := by
    have := ContinuousLinearEquiv.model_modelHomeomorph_symm A.symm hA' w
    rw [ContinuousLinearEquiv.symm_symm] at this
    rw [← this, I.left_inv]
  have hsymm : (φ'.extend I₁).symm (I₁ w) =
      e.symm ((h.domChart.extend I).symm (A (I₁ w))) := by
    simp only [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, I₁.left_inv]
    -- The inverse of `φ'` is `e⁻¹ ∘ h.domChart⁻¹ ∘ (modelHomeomorph A⁻¹)⁻¹` by construction.
    rw [← hmh]
    rfl
  simp only [Function.comp_apply, hsymm, _root_.Diffeomorph.apply_symm_apply]
  rw [show h.codChart.extend J (f ((h.domChart.extend I).symm (A (I₁ w)))) =
    h.equiv (A (I₁ w), 0) from h.writtenInCharts hv]
  simp

/-- Precomposing a `C^n` immersion at a point with a `C^m` diffeomorphism, `n ≤ m`, whose source
model is linearly related to the old one gives an immersion at the corresponding point. -/
theorem isImmersionAt_comp_diffeomorph_of_image_range_eq [IsManifold I₁ n M₁]
    (A : E₁ ≃L[𝕜] E) (hA : A '' range I₁ = range I) (e : M₁ ≃ₘ^m⟮I₁, I⟯ M) (hnm : n ≤ m)
    {x : M₁} (h : IsImmersionAt I J n f (e x)) : IsImmersionAt I₁ J n (f ∘ e) x :=
  (isImmersionAtOfComplement_comp_diffeomorph_of_image_range_eq A hA e hnm
    h.isImmersionAtOfComplement_complement).isImmersionAt

/-! ### Postcomposing with a diffeomorphism -/

/-- Postcomposing a `C^n` immersion with a `C^m` diffeomorphism `e : N ≃ₘ N₁`, `n ≤ m`, preserves
the immersion normal form at a point, when the model of `N₁` is related to that of `N` by a
continuous linear equivalence `B : E' ≃L E₁'` carrying the range of one model onto the range of
the other. The complement stays the same, and the linear equivalence of the normal form is
followed by `B`. -/
theorem isImmersionAtOfComplement_diffeomorph_comp_of_image_range_eq [IsManifold J₁ n N₁]
    (B : E' ≃L[𝕜] E₁') (hB : B '' range J = range J₁) (e : N ≃ₘ^m⟮J, J₁⟯ N₁) (hnm : n ≤ m)
    {x : M}
    (h : IsImmersionAtOfComplement F I J n f x) :
    IsImmersionAtOfComplement F I J₁ n (e ∘ f) x := by
  set ψ' := (e.symm.toHomeomorph.transOpenPartialHomeomorph h.codChart).transHomeomorph
    (B.modelHomeomorph hB)
  have hsource : ψ'.source = ⇑e.symm ⁻¹' h.codChart.source := rfl
  refine IsImmersionAtOfComplement.mk_of_charts (h.equiv.trans B) h.domChart ψ'
    h.mem_domChart_source ?_ h.domChart_mem_maximalAtlas
    (B.transHomeomorph_modelHomeomorph_mem_maximalAtlas hB e.symm hnm
      h.codChart_mem_maximalAtlas) ?_ fun u hu ↦ ?_
  · rw [hsource]
    simpa using h.mem_codChart_source
  · rw [hsource]
    intro y hy
    simpa using h.source_subset_preimage_source hy
  · -- `ψ'` reads `e y` as the model homeomorphism applied to `h.codChart (e.symm (e y))`; both
    -- constructions are compositions of functions, so this holds by definition.
    have hψ' (y : N) : ψ' (e y) = B.modelHomeomorph hB (h.codChart y) := by
      change B.modelHomeomorph hB (h.codChart (e.symm (e y))) = _
      rw [_root_.Diffeomorph.symm_apply_apply]
    simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe, hψ',
      ContinuousLinearEquiv.model_modelHomeomorph,
      ContinuousLinearEquiv.trans_apply]
    congr 1
    simpa using h.writtenInCharts hu

/-- Postcomposing a `C^n` immersion at a point with a `C^m` diffeomorphism, `n ≤ m`, whose target
model is linearly related to the old one gives an immersion at that point. -/
theorem isImmersionAt_diffeomorph_comp_of_image_range_eq [IsManifold J₁ n N₁]
    (B : E' ≃L[𝕜] E₁') (hB : B '' range J = range J₁) (e : N ≃ₘ^m⟮J, J₁⟯ N₁) (hnm : n ≤ m)
    {x : M} (h : IsImmersionAt I J n f x) : IsImmersionAt I J₁ n (e ∘ f) x :=
  (isImmersionAtOfComplement_diffeomorph_comp_of_image_range_eq B hB e hnm
    h.isImmersionAtOfComplement_complement).isImmersionAt

end TauCeti
