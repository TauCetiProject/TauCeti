/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Core.Basic
public import TauCeti.Topology.VectorBundle.Descent

/-!
# Morphisms in point-indexed bundle coordinates

`pointIndexedCoreHomEquiv` identifies compatible chart operators of the point-indexed
cores with continuous fibrewise linear maps between the original bundles. Its forward
map conjugates preferred-coordinate operators by `pointIndexedCoreFiberEquiv`.
The inverse recovers coordinates from an actual map of total spaces. Identity and
composition are preserved, so this comparison supplies the morphism part of the small
coordinate presentation, independently of the original fibre universes.

Only the source model must be finite-dimensional; the target model can be arbitrary.
No separation, compactness or finite-cover assumption on the base is required.

This combines the reconstruction `pointIndexedCoreHomeomorph` with
`VectorBundleCore.CoordinateHom.fiberMapEquiv` and Mathlib's
`ContinuousLinearEquiv.arrowCongrEquiv`.
-/

public section

open Bundle

namespace TauCeti

variable {𝕜 B F G : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {E : B → Type*} {E' : B → Type*}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ x, AddCommMonoid (E' x)] [∀ x, Module 𝕜 (E' x)]
  [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace G E')]
  [FiberBundle G E'] [VectorBundle 𝕜 G E']

private theorem continuous_pointIndexedCore_conjugate_iff (f : B → F →L[𝕜] G) :
    Continuous (fun p : (pointIndexedCore 𝕜 F E).TotalSpace ↦
      TotalSpace.mk' G (E := (pointIndexedCore 𝕜 G E').Fiber) p.proj (f p.proj p.2)) ↔
    Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' G p.proj
      (((pointIndexedCoreFiberEquiv 𝕜 F E p.proj).arrowCongrEquiv
        (pointIndexedCoreFiberEquiv 𝕜 G E' p.proj)) (f p.proj) p.2)) := by
  let h := pointIndexedCoreHomeomorph 𝕜 F E
  let h' := pointIndexedCoreHomeomorph 𝕜 G E'
  let g := fun p : (pointIndexedCore 𝕜 F E).TotalSpace ↦
    TotalSpace.mk' G (E := (pointIndexedCore 𝕜 G E').Fiber) p.proj (f p.proj p.2)
  have hmap : (fun p : TotalSpace F E ↦ TotalSpace.mk' G p.proj
      (((pointIndexedCoreFiberEquiv 𝕜 F E p.proj).arrowCongrEquiv
        (pointIndexedCoreFiberEquiv 𝕜 G E' p.proj)) (f p.proj) p.2)) =
      h' ∘ g ∘ h.symm := by
    funext p
    dsimp only [h, h', g, Function.comp_def]
    rw [pointIndexedCoreHomeomorph_symm_apply, pointIndexedCoreHomeomorph_apply]
    exact congrArg (fun g ↦ TotalSpace.mk' G p.proj (g p.2))
      (ContinuousLinearEquiv.arrowCongrEquiv_apply
        (pointIndexedCoreFiberEquiv 𝕜 F E p.proj)
        (pointIndexedCoreFiberEquiv 𝕜 G E' p.proj) (f p.proj))
  rw [hmap, h'.comp_continuous_iff, h.symm.comp_continuous_iff']

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- Compatible coordinate morphisms of the reconstructed cores correspond exactly to
continuous fibrewise linear maps of the original bundles. The fibre universes of the
original bundles need not agree with each other or with the coordinate universe. -/
noncomputable def pointIndexedCoreHomEquiv :
    VectorBundleCore.CoordinateHom (pointIndexedCore 𝕜 F E) (pointIndexedCore 𝕜 G E') ≃
      {f : ∀ x, E x →L[𝕜] E' x //
        Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' G p.proj (f p.proj p.2))} :=
  (VectorBundleCore.CoordinateHom.fiberMapEquiv _ _).trans <|
    Equiv.subtypeEquiv (Equiv.piCongrRight fun x ↦
      (pointIndexedCoreFiberEquiv 𝕜 F E x).arrowCongrEquiv
        (pointIndexedCoreFiberEquiv 𝕜 G E' x)) fun f ↦
      (continuous_hom_bundle_iff (E₁ := (pointIndexedCore 𝕜 F E).Fiber)
        (E₂ := (pointIndexedCore 𝕜 G E').Fiber) f).trans
          (continuous_pointIndexedCore_conjugate_iff f)

@[simp] theorem pointIndexedCoreHomEquiv_apply
    (a : VectorBundleCore.CoordinateHom
      (pointIndexedCore 𝕜 F E) (pointIndexedCore 𝕜 G E')) (x : B) (v : E x) :
    (pointIndexedCoreHomEquiv a).1 x v =
      pointIndexedCoreFiberEquiv 𝕜 G E' x
        (a.fiberMap x ((pointIndexedCoreFiberEquiv 𝕜 F E x).symm v)) := by
  simp only [pointIndexedCoreHomEquiv, Equiv.trans_apply, Equiv.subtypeEquiv_apply,
    VectorBundleCore.CoordinateHom.coe_fiberMapEquiv_apply]
  -- The dependent-function equivalence evaluates pointwise; its core fibres have models F and G.
  exact congrArg (fun g ↦ g v) (ContinuousLinearEquiv.arrowCongrEquiv_apply
    (pointIndexedCoreFiberEquiv 𝕜 F E x) (pointIndexedCoreFiberEquiv 𝕜 G E' x) (a.fiberMap x))

@[simp] theorem pointIndexedCoreHomEquiv_symm_fiberMap
    (f : {f : ∀ x, E x →L[𝕜] E' x //
      Continuous (fun p : TotalSpace F E ↦ TotalSpace.mk' G p.proj (f p.proj p.2))})
    (x : B) (v : F) :
    (pointIndexedCoreHomEquiv.symm f).fiberMap x v =
      (pointIndexedCoreFiberEquiv 𝕜 G E' x).symm
        (f.1 x (pointIndexedCoreFiberEquiv 𝕜 F E x v)) := by
  simp only [pointIndexedCoreHomEquiv, Equiv.symm_trans_apply, Equiv.subtypeEquiv_symm,
    Equiv.subtypeEquiv_apply, VectorBundleCore.CoordinateHom.fiberMapEquiv_symm_apply,
    VectorBundleCore.CoordinateHom.fiberMap_ofContinuous]
  -- The inverse dependent-function equivalence evaluates pointwise in the model fibres.
  exact congrArg (fun g ↦ g v) (ContinuousLinearEquiv.arrowCongrEquiv_symm_apply
    (pointIndexedCoreFiberEquiv 𝕜 F E x) (pointIndexedCoreFiberEquiv 𝕜 G E' x) (f.1 x))

/-- The coordinate identity reconstructs the actual identity on each original fibre. -/
@[simp] theorem pointIndexedCoreHomEquiv_id (x : B) :
    (pointIndexedCoreHomEquiv
      (VectorBundleCore.CoordinateHom.id (pointIndexedCore 𝕜 F E))).1 x =
      ContinuousLinearMap.id 𝕜 (E x) := by
  ext v
  simp only [pointIndexedCoreHomEquiv_apply, VectorBundleCore.CoordinateHom.fiberMap_id,
    ContinuousLinearMap.id_apply]
  exact (pointIndexedCoreFiberEquiv 𝕜 F E x).apply_symm_apply v

section Comp

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {E'' : B → Type*}
  [∀ x, AddCommMonoid (E'' x)] [∀ x, Module 𝕜 (E'' x)]
  [∀ x, TopologicalSpace (E'' x)] [TopologicalSpace (TotalSpace H E'')]
  [FiberBundle H E''] [VectorBundle 𝕜 H E'']

/-- Reconstructing a composite coordinate morphism is fibrewise composition of the
reconstructed maps, for finite-dimensional source models. -/
@[simp] theorem pointIndexedCoreHomEquiv_comp [FiniteDimensional 𝕜 G]
    (b : VectorBundleCore.CoordinateHom
      (pointIndexedCore 𝕜 G E') (pointIndexedCore 𝕜 H E''))
    (a : VectorBundleCore.CoordinateHom
      (pointIndexedCore 𝕜 F E) (pointIndexedCore 𝕜 G E')) (x : B) :
    (pointIndexedCoreHomEquiv (b.comp a)).1 x =
      ((pointIndexedCoreHomEquiv b).1 x).comp ((pointIndexedCoreHomEquiv a).1 x) := by
  ext v
  simp only [pointIndexedCoreHomEquiv_apply, VectorBundleCore.CoordinateHom.fiberMap_comp,
    ContinuousLinearMap.comp_apply]
  -- Cancellation takes place in the reconstructed middle fibre, whose model is G.
  exact congrArg (fun w ↦ pointIndexedCoreFiberEquiv 𝕜 H E'' x (b.fiberMap x w))
    ((pointIndexedCoreFiberEquiv 𝕜 G E' x).symm_apply_apply
      (a.fiberMap x ((pointIndexedCoreFiberEquiv 𝕜 F E x).symm v))).symm

end Comp

end TauCeti
