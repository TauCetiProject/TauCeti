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
`φ : ∀ b, E' b ≃L[R] E b` over a semiring `R`, precomposed charts stay `R`-linear with identical
overlap coordinate changes (`Bundle.Trivialization.compHomeomorph_isLinear`,
`Bundle.Trivialization.compHomeomorph_coordChangeL_eq`), giving
`TauCeti.vectorBundleOfContinuousLinearEquiv` over a normed scalar field without completeness or
finite-dimensionality hypotheses, with `ULift` and `Shrink` instances as specializations.
Separately, over an empty base `TauCeti.fiberBundleOfIsEmpty` and `TauCeti.vectorBundleOfIsEmpty`
construct `FiberBundle` and `VectorBundle` structures directly with an empty trivialization atlas.
-/

public section

open Bundle Set Topology

namespace ContinuousLinearEquiv

universe u v

variable {R : Type*} {M : Type u} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

@[simp] theorem ulift_apply (x : ULift.{v} M) :
    (ContinuousLinearEquiv.ulift : ULift.{v} M ≃L[R] M) x = x.down := by rfl
@[simp] theorem ulift_symm_apply (x : M) :
    (ContinuousLinearEquiv.ulift : ULift.{v} M ≃L[R] M).symm x = ULift.up x := by rfl

end ContinuousLinearEquiv

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
  ({ toFun p := ⟨p.proj, φ p.proj p.2⟩, invFun p := ⟨p.proj, (φ p.proj).symm p.2⟩
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
  { trivializationAtlas' := {e' | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
      e' = e.compHomeomorph h}
    trivializationAt' b := (trivializationAt F E b).compHomeomorph h
    mem_baseSet_trivializationAt' b := mem_baseSet_trivializationAt F E b
    trivialization_mem_atlas' b := ⟨trivializationAt F E b, inferInstance, rfl⟩
    totalSpaceMk_isInducing' b := h.isInducing.of_comp_iff.mp
      ((FiberBundle.totalSpaceMk_isInducing F E b).comp (φ b).isInducing) }

/-- The chosen trivialization of `fiberBundleOfHomeomorph` at `b` is obtained by precomposing
`trivializationAt F E b` with `totalSpaceHomeomorphOfIsInducing`. -/
@[simp] theorem trivializationAt_fiberBundleOfHomeomorph [TopologicalSpace B] [TopologicalSpace F]
    [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F E]
    (φ : ∀ b, E' b ≃ₜ E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E)))
    (b : B) :
    let _ : FiberBundle F E' := fiberBundleOfHomeomorph F φ ht
    trivializationAt F E' b = (trivializationAt F E b).compHomeomorph
      (totalSpaceHomeomorphOfIsInducing F (fun b ↦ (φ b).toEquiv) ht) :=
  (rfl)

/-- A trivialization belongs to the atlas of `fiberBundleOfHomeomorph` if and only if it is
obtained by precomposing an atlas trivialization of `E` with `totalSpaceHomeomorphOfIsInducing`. -/
@[simp] theorem mem_trivializationAtlas_fiberBundleOfHomeomorph_iff [TopologicalSpace B]
    [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
    [FiberBundle F E] (φ : ∀ b, E' b ≃ₜ E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E)))
    (e' : Trivialization F (π F E')) :
    let _ : FiberBundle F E' := fiberBundleOfHomeomorph F φ ht
    e' ∈ trivializationAtlas F E' ↔
      ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
        e' = e.compHomeomorph (totalSpaceHomeomorphOfIsInducing F (fun b ↦ (φ b).toEquiv) ht) :=
  (Iff.rfl)

end Transport
end TauCeti

namespace Bundle.Trivialization

universe u v w w'

variable {B : Type u} {F : Type v} {E : B → Type w} {E' : B → Type w'}
  [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F E')]
  {R : Type*} [Semiring R] [AddCommMonoid F] [Module R F]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module R (E' b)] [∀ b, TopologicalSpace (E' b)]

/-- Precomposing an `R`-linear trivialization with a total-space homeomorphism given fibrewise by
`R`-linear equivalences preserves `Trivialization.IsLinear`. -/
theorem compHomeomorph_isLinear (e : Trivialization F (π F E)) [e.IsLinear R]
    (φ : ∀ b, E' b ≃L[R] E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E))) :
    ((e.compHomeomorph (TauCeti.totalSpaceHomeomorphOfIsInducing F
      (fun b ↦ (φ b).toHomeomorph.toEquiv) ht) : Trivialization F (π F E'))).IsLinear R where
  linear b hb :=
    { map_add v w := by
        -- Unfold `e.compHomeomorph` and `toHomeomorph.toEquiv` to `e` and `φ b`.
        change (e ⟨b, φ b (v + w)⟩).2 = (e ⟨b, φ b v⟩).2 + (e ⟨b, φ b w⟩).2
        rw [map_add]; exact (e.linear R hb).map_add (φ b v) (φ b w)
      map_smul c v := by
        -- Unfold `e.compHomeomorph` and `toHomeomorph.toEquiv` to `e` and `φ b`.
        change (e ⟨b, φ b (c • v)⟩).2 = c • (e ⟨b, φ b v⟩).2
        rw [map_smul]; exact (e.linear R hb).map_smul c (φ b v) }

/-- Precomposing two `R`-linear trivializations with the same fibrewise continuous-linear
total-space homeomorphism leaves their overlap coordinate-change operator unchanged. -/
theorem compHomeomorph_coordChangeL_eq
    (e₁ e₂ : Trivialization F (π F E)) [e₁.IsLinear R] [e₂.IsLinear R] (φ : ∀ b, E' b ≃L[R] E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F E)))
    {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) :
    let h := TauCeti.totalSpaceHomeomorphOfIsInducing F (fun b ↦ (φ b).toHomeomorph.toEquiv) ht
    let e₁' : Trivialization F (π F E') := e₁.compHomeomorph h
    let e₂' : Trivialization F (π F E') := e₂.compHomeomorph h
    have : e₁'.IsLinear R := e₁.compHomeomorph_isLinear φ ht
    have : e₂'.IsLinear R := e₂.compHomeomorph_isLinear φ ht
    e₁'.coordChangeL R e₂' b = e₁.coordChangeL R e₂ b := by
  intro h e₁' e₂'
  have : e₁'.IsLinear R := e₁.compHomeomorph_isLinear φ ht
  have : e₂'.IsLinear R := e₂.compHomeomorph_isLinear φ ht
  ext v; rw [e₁'.coordChangeL_apply' e₂' hb, e₁.coordChangeL_apply' e₂ hb]
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
    have : MemTrivializationAtlas e := he; exact e.compHomeomorph_isLinear φ ht
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
  trivializationAt' := isEmptyElim
  mem_baseSet_trivializationAt' := isEmptyElim
  trivialization_mem_atlas' := isEmptyElim
  totalSpaceMk_isInducing' := isEmptyElim

/-- The trivialization atlas of `fiberBundleOfIsEmpty` is empty. -/
@[simp] theorem trivializationAtlas_fiberBundleOfIsEmpty [TopologicalSpace F] :
    let _ : FiberBundle F E := fiberBundleOfIsEmpty F E
    trivializationAtlas F E = ∅ :=
  (rfl)

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
  TopologicalSpace.induced (fun p : TotalSpace F (fun b ↦ Shrink.{w'} (E b)) ↦
    (⟨p.proj, (equivShrink (E p.proj)).symm p.2⟩ : TotalSpace F E)) inferInstance

/-- The total space of `fun b ↦ Shrink.{w'} (E b)` is homeomorphic to `TotalSpace F E` over `B`. -/
noncomputable def shrinkTotalSpaceHomeomorph [∀ b, Small.{w'} (E b)] :
    TotalSpace F (fun b ↦ Shrink.{w'} (E b)) ≃ₜ TotalSpace F E :=
  totalSpaceHomeomorphOfIsInducing F (fun b ↦ (equivShrink (E b)).symm) ⟨rfl⟩

@[simp] theorem shrinkTotalSpaceHomeomorph_apply [∀ b, Small.{w'} (E b)]
    (p : TotalSpace F (fun b ↦ Shrink.{w'} (E b))) :
    shrinkTotalSpaceHomeomorph F E p = ⟨p.proj, (equivShrink (E p.proj)).symm p.2⟩ := (rfl)
@[simp] theorem shrinkTotalSpaceHomeomorph_symm_apply [∀ b, Small.{w'} (E b)]
    (p : TotalSpace F E) : (shrinkTotalSpaceHomeomorph.{u, v, w, w'} F E).symm p =
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
