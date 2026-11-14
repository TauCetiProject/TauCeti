/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Topology.Instances.Shrink
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Universe change, fibrewise equivalence transport, and empty-base vector bundles

Fibrewise homeomorphisms `φ : ∀ b, E' b ≃ₜ E b` whose induced total-space bijection is
topological-inducing transfer `FiberBundle F E` to `E'` (`TauCeti.fiberBundleOfHomeomorph`) via
`TauCeti.totalSpaceHomeomorphOfIsInducing`. For continuous linear equivalences
`φ : ∀ b, E' b ≃L[𝕜] E b`, precomposed charts stay `𝕜`-linear with identical overlap coordinate
changes (`Bundle.Trivialization.compHomeomorph_isLinear`,
`Bundle.Trivialization.compHomeomorph_coordChangeL_eq`), giving
`TauCeti.vectorBundleOfContinuousLinearEquiv` without completeness or finite-dimensionality
hypotheses. Empty-base (`TauCeti.fiberBundleOfIsEmpty`, `TauCeti.vectorBundleOfIsEmpty`), `ULift`,
and `Shrink` instances follow as specializations.
-/

public section

open Bundle Set Topology

namespace TauCeti

section Transport

universe u v w w'

variable {B : Type u} (F : Type v) {E : B → Type w} {E' : B → Type w'}
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F E')]

/-- A family of bijections on fibres induces a homeomorphism on total spaces whenever the forward
total-space map is topological-inducing. -/
-- Expose the base projection so `e.compHomeomorph` has projection `π F E'` definitionally.
@[expose]
def totalSpaceHomeomorphOfIsInducing (φ : ∀ b, E' b ≃ E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E))) :
    TotalSpace F E' ≃ₜ TotalSpace F E :=
  ({ toFun p := ⟨p.proj, φ p.proj p.2⟩
     invFun p := ⟨p.proj, (φ p.proj).symm p.2⟩
     left_inv := fun ⟨_, _⟩ ↦ by simp only [Equiv.symm_apply_apply]
     right_inv := fun ⟨_, _⟩ ↦ by simp only [Equiv.apply_symm_apply] } :
    TotalSpace F E' ≃ TotalSpace F E).toHomeomorphOfIsInducing ht

@[simp] theorem totalSpaceHomeomorphOfIsInducing_apply (φ : ∀ b, E' b ≃ E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F E') :
    totalSpaceHomeomorphOfIsInducing F φ ht p = ⟨p.proj, φ p.proj p.2⟩ := (rfl)

@[simp] theorem totalSpaceHomeomorphOfIsInducing_symm_apply (φ : ∀ b, E' b ≃ E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F E) :
    (totalSpaceHomeomorphOfIsInducing F φ ht).symm p = ⟨p.proj, (φ p.proj).symm p.2⟩ := (rfl)

/-- Transfer a `FiberBundle` structure along fibrewise homeomorphisms whose total-space map is
inducing. -/
@[instance_reducible]
noncomputable def fiberBundleOfHomeomorph [TopologicalSpace B] [TopologicalSpace F]
    [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F E]
    (φ : ∀ b, E' b ≃ₜ E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E))) :
    FiberBundle F E' :=
  let h := totalSpaceHomeomorphOfIsInducing F (fun b ↦ (φ b).toEquiv) ht
  { trivializationAtlas' :=
      {e' | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
        e' = e.compHomeomorph h}
    trivializationAt' b := (trivializationAt F E b).compHomeomorph h
    mem_baseSet_trivializationAt' b := mem_baseSet_trivializationAt F E b
    trivialization_mem_atlas' b := ⟨trivializationAt F E b, inferInstance, rfl⟩
    totalSpaceMk_isInducing' b :=
      h.isInducing.of_comp_iff.mp ((FiberBundle.totalSpaceMk_isInducing F E b).comp
        (φ b).isInducing) }

end Transport

end TauCeti

namespace Bundle.Trivialization

universe u v w w'

variable {B : Type u} {F : Type v} {E : B → Type w} {E' : B → Type w'}
  [TopologicalSpace B] [NormedAddCommGroup F]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F E')]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)] [∀ b, TopologicalSpace (E' b)]

/-- Precomposing a `𝕜`-linear trivialization with a total-space homeomorphism given fibrewise by
`𝕜`-linear equivalences preserves `Trivialization.IsLinear`. -/
theorem compHomeomorph_isLinear (e : Trivialization F (π F E)) [e.IsLinear 𝕜]
    (φ : ∀ b, E' b ≃L[𝕜] E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E))) :
    ((e.compHomeomorph (TauCeti.totalSpaceHomeomorphOfIsInducing F
      (fun b ↦ (φ b).toHomeomorph.toEquiv) ht) : Trivialization F (π F E'))).IsLinear 𝕜 where
  linear b hb :=
    { map_add v w := by
        -- Unfold `e.compHomeomorph` to `e` after `totalSpaceHomeomorphOfIsInducing`.
        change (e ⟨b, φ b (v + w)⟩).2 = (e ⟨b, φ b v⟩).2 + (e ⟨b, φ b w⟩).2
        rw [map_add]; exact (e.linear 𝕜 hb).map_add (φ b v) (φ b w)
      map_smul c v := by
        change (e ⟨b, φ b (c • v)⟩).2 = c • (e ⟨b, φ b v⟩).2
        rw [map_smul]; exact (e.linear 𝕜 hb).map_smul c (φ b v) }

/-- Precomposing two `𝕜`-linear trivializations with the same fibrewise continuous-linear
total-space homeomorphism leaves their overlap coordinate-change operator unchanged. -/
theorem compHomeomorph_coordChangeL_eq
    (e₁ e₂ : Trivialization F (π F E)) [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] (φ : ∀ b, E' b ≃L[𝕜] E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E)))
    {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) :
    let h := TauCeti.totalSpaceHomeomorphOfIsInducing F (fun b ↦ (φ b).toHomeomorph.toEquiv) ht
    let e₁' : Trivialization F (π F E') := e₁.compHomeomorph h
    let e₂' : Trivialization F (π F E') := e₂.compHomeomorph h
    have : e₁'.IsLinear 𝕜 := e₁.compHomeomorph_isLinear φ ht
    have : e₂'.IsLinear 𝕜 := e₂.compHomeomorph_isLinear φ ht
    e₁'.coordChangeL 𝕜 e₂' b = e₁.coordChangeL 𝕜 e₂ b := by
  intro h e₁' e₂'
  have : e₁'.IsLinear 𝕜 := e₁.compHomeomorph_isLinear φ ht
  have : e₂'.IsLinear 𝕜 := e₂.compHomeomorph_isLinear φ ht
  ext v
  rw [e₁'.coordChangeL_apply' e₂' hb, e₁.coordChangeL_apply' e₂ hb]
  -- Both `e₁'` and `e₂'` precompose with `h`, so `h` and `h.symm` cancel on the overlap.
  change (e₂ (h (h.symm (e₁.toOpenPartialHomeomorph.symm (b, v))))).2 =
    (e₂ (e₁.toOpenPartialHomeomorph.symm (b, v))).2
  rw [h.apply_symm_apply]

end Bundle.Trivialization

namespace TauCeti

section VectorBundleTransport

universe u v w w'

variable {B : Type u} {F : Type v} {E : B → Type w} {E' : B → Type w'}
  [TopologicalSpace B] [NormedAddCommGroup F]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F E')]

/-- Transfer a `VectorBundle` structure along fibrewise continuous linear equivalences whose
total-space map is inducing, equipping `E'` with `fiberBundleOfHomeomorph`. -/
theorem vectorBundleOfContinuousLinearEquiv (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [∀ b, TopologicalSpace (E b)] [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (φ : ∀ b, E' b ≃L[𝕜] E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E))) :
    let _ : FiberBundle F E' := fiberBundleOfHomeomorph F (fun b ↦ (φ b).toHomeomorph) ht
    VectorBundle 𝕜 F E' := by
  let _ : FiberBundle F E' := fiberBundleOfHomeomorph F (fun b ↦ (φ b).toHomeomorph) ht
  refine ⟨?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    have : MemTrivializationAtlas e := he
    exact e.compHomeomorph_isLinear φ ht
  · rintro _ _ ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, rfl⟩
    have : MemTrivializationAtlas e₁ := he₁; have : MemTrivializationAtlas e₂ := he₂
    have := e₁.compHomeomorph_isLinear φ ht; have := e₂.compHomeomorph_isLinear φ ht
    exact (continuousOn_coordChange 𝕜 e₁ e₂).congr fun b hb ↦
      congrArg ContinuousLinearEquiv.toContinuousLinearMap
        (e₁.compHomeomorph_coordChangeL_eq e₂ φ ht hb)

end VectorBundleTransport

section EmptyBase

universe u v w

variable {B : Type u} [TopologicalSpace B] [IsEmpty B] (F : Type v) (E : B → Type w)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]

/-- Any fibre family over an empty base is a `FiberBundle` with empty trivialization atlas. -/
@[instance_reducible]
def fiberBundleOfIsEmpty [TopologicalSpace F] : FiberBundle F E where
  trivializationAtlas' := ∅
  trivializationAt' b := isEmptyElim b
  mem_baseSet_trivializationAt' b := isEmptyElim b
  trivialization_mem_atlas' b := isEmptyElim b
  totalSpaceMk_isInducing' b := isEmptyElim b

/-- Over an empty base, `fiberBundleOfIsEmpty` is a `VectorBundle`. -/
theorem vectorBundleOfIsEmpty (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] :
    let _ : FiberBundle F E := fiberBundleOfIsEmpty F E
    VectorBundle 𝕜 F E :=
  let _ : FiberBundle F E := fiberBundleOfIsEmpty F E
  { trivialization_linear' := fun _ he ↦ False.elim he.out
    continuousOn_coordChange' := fun _ _ he _ ↦ False.elim he.out }

end EmptyBase

section ULiftShrink

universe u v w w'

variable {B : Type u} (F : Type v) (E : B → Type w) [TopologicalSpace (TotalSpace F E)]

/-- Equip the total space of `fun b ↦ ULift.{w'} (E b)` with the topology induced by `ULift.down`
on fibres. -/
instance instTopologicalSpaceTotalSpaceULift :
    TopologicalSpace (TotalSpace F (fun b ↦ ULift.{w'} (E b))) :=
  TopologicalSpace.induced
    (fun p : TotalSpace F (fun b ↦ ULift.{w'} (E b)) ↦ (⟨p.proj, p.2.down⟩ : TotalSpace F E))
    inferInstance

/-- The total space of `fun b ↦ ULift.{w'} (E b)` is homeomorphic to `TotalSpace F E` over `B`. -/
def uliftTotalSpaceHomeomorph : TotalSpace F (fun b ↦ ULift.{w'} (E b)) ≃ₜ TotalSpace F E :=
  totalSpaceHomeomorphOfIsInducing F (fun _ ↦ Equiv.ulift) ⟨rfl⟩

@[simp] theorem uliftTotalSpaceHomeomorph_apply (p : TotalSpace F (fun b ↦ ULift.{w'} (E b))) :
    uliftTotalSpaceHomeomorph F E p = ⟨p.proj, p.2.down⟩ := (rfl)

@[simp] theorem uliftTotalSpaceHomeomorph_symm_apply (p : TotalSpace F E) :
    (uliftTotalSpaceHomeomorph.{u, v, w, w'} F E).symm p = ⟨p.proj, ULift.up p.2⟩ := (rfl)

noncomputable instance instFiberBundleULift
    [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] :
    FiberBundle F (fun b ↦ ULift.{w'} (E b)) :=
  fiberBundleOfHomeomorph F (fun _ ↦ Homeomorph.ulift) ⟨rfl⟩

instance instVectorBundleULift {𝕜 : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E] :
    VectorBundle 𝕜 F (fun b ↦ ULift.{w'} (E b)) :=
  vectorBundleOfContinuousLinearEquiv 𝕜 (fun _ ↦ ContinuousLinearEquiv.ulift) ⟨rfl⟩

/-- Equip the total space of `fun b ↦ Shrink.{w'} (E b)` with the topology induced by
`(equivShrink (E b)).symm` on fibres. -/
noncomputable instance instTopologicalSpaceTotalSpaceShrink [∀ b, Small.{w'} (E b)] :
    TopologicalSpace (TotalSpace F (fun b ↦ Shrink.{w'} (E b))) :=
  TopologicalSpace.induced
    (fun p : TotalSpace F (fun b ↦ Shrink.{w'} (E b)) ↦
      (⟨p.proj, (equivShrink (E p.proj)).symm p.2⟩ : TotalSpace F E)) inferInstance

/-- The total space of `fun b ↦ Shrink.{w'} (E b)` is homeomorphic to `TotalSpace F E` over `B`. -/
noncomputable def shrinkTotalSpaceHomeomorph [∀ b, Small.{w'} (E b)] :
    TotalSpace F (fun b ↦ Shrink.{w'} (E b)) ≃ₜ TotalSpace F E :=
  totalSpaceHomeomorphOfIsInducing F (fun b ↦ (equivShrink (E b)).symm) ⟨rfl⟩

@[simp] theorem shrinkTotalSpaceHomeomorph_apply [∀ b, Small.{w'} (E b)]
    (p : TotalSpace F (fun b ↦ Shrink.{w'} (E b))) :
    shrinkTotalSpaceHomeomorph F E p = ⟨p.proj, (equivShrink (E p.proj)).symm p.2⟩ := (rfl)

@[simp] theorem shrinkTotalSpaceHomeomorph_symm_apply [∀ b, Small.{w'} (E b)]
    (p : TotalSpace F E) :
    (shrinkTotalSpaceHomeomorph.{u, v, w, w'} F E).symm p =
      ⟨p.proj, equivShrink (E p.proj) p.2⟩ := (rfl)

noncomputable instance instFiberBundleShrink [TopologicalSpace B] [TopologicalSpace F]
    [∀ b, TopologicalSpace (E b)] [∀ b, Small.{w'} (E b)] [FiberBundle F E] :
    FiberBundle F (fun b ↦ Shrink.{w'} (E b)) :=
  fiberBundleOfHomeomorph F (fun b ↦ (Shrink.homeomorph (E b)).symm) ⟨rfl⟩

instance instVectorBundleShrink {𝕜 : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [∀ b, TopologicalSpace (E b)] [∀ b, Small.{w'} (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E] :
    VectorBundle 𝕜 F (fun b ↦ Shrink.{w'} (E b)) :=
  vectorBundleOfContinuousLinearEquiv 𝕜 (fun b ↦ Shrink.continuousLinearEquiv 𝕜 (E b)) ⟨rfl⟩

end ULiftShrink

end TauCeti
