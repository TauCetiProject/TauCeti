/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SingularSet
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Codiscrete
public import TauCeti.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Small models of simplicial homotopy types

A simplicial set can have a small homotopy type without having small sets of simplices.
`TauCeti.SmallSpaceModel` records a Kan complex in an independently specified universe `u`,
comparison maps after lifting both the model and the ambient simplicial set in universe `v`
to the common universe `max u v`, and simplicial homotopies from both composites to the identities.
`TauCeti.HasSmallSpaceModel` asserts the existence of such data. These models provide the
universe control needed when representing mapping spaces by small Kan complexes.

The nerve of the codiscrete category on any nonempty type admits the point as a small model,
even when its vertices do not form a small type. Since homotopic maps induce the same map on
connected components, a simplicial set with a small model has a small set of connected
components (`TauCeti.HasSmallSpaceModel.small_π₀`). For a discrete simplicial set this is the only
obstruction: the discrete simplicial set on a type has a small model exactly when the type is small
(`TauCeti.hasSmallSpaceModel_const_iff`), the model being the singular simplicial set of the
discrete space on a small copy of the type.

## References

* J. Lurie, *Higher Topos Theory*, Corollary 5.4.1.5 and Proposition 5.4.1.7.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open scoped SSet.modelCategoryQuillen

universe u v

namespace TauCeti

/-- A small Kan model of a simplicial set, with comparison maps inverse up to simplicial
homotopy. Only the model's simplices are required to lie in universe `u`. -/
structure SmallSpaceModel (X : SSet.{v}) where
  /-- The small simplicial set representing the homotopy type. -/
  model : SSet.{u}
  /-- The model is a Kan complex. -/
  kanComplex : SSet.KanComplex model
  /-- The comparison from the universe lift of the model. -/
  hom : SSet.uliftFunctor.{v, u}.obj model ⟶ SSet.uliftFunctor.{u, v}.obj X
  /-- The comparison back to the universe lift of the model. -/
  inv : SSet.uliftFunctor.{u, v}.obj X ⟶ SSet.uliftFunctor.{v, u}.obj model
  /-- The first composite is simplicially homotopic to the identity. -/
  homotopyHomInvId : SSet.Homotopy (hom ≫ inv) (𝟙 _)
  /-- The second composite is simplicially homotopic to the identity. -/
  homotopyInvHomId : SSet.Homotopy (inv ≫ hom) (𝟙 _)

attribute [instance] SmallSpaceModel.kanComplex

/-- The homotopy type of `X` admits a Kan model in an independently specified universe `u`,
with explicit comparison maps inverse up to simplicial homotopy after lifting both the model
and `X` to the common universe `max u v`. -/
def HasSmallSpaceModel (X : SSet.{v}) : Prop := Nonempty (SmallSpaceModel.{u, v} X)

/-- Introduce or extract the data of a small Kan model. -/
lemma hasSmallSpaceModel_iff_nonempty (X : SSet.{v}) :
    HasSmallSpaceModel.{u, v} X ↔ Nonempty (SmallSpaceModel.{u, v} X) := Iff.rfl

namespace SmallSpaceModel

/-- An isomorphism from a lifted small Kan complex supplies a small space model.
This constructor is transparent so the source of its dependent comparison maps is `Y`. -/
noncomputable abbrev ofIso (Y : SSet.{u}) [SSet.KanComplex Y]
    {X : SSet.{v}}
    (e : SSet.uliftFunctor.{v, u}.obj Y ≅ SSet.uliftFunctor.{u, v}.obj X) :
    SmallSpaceModel.{u, v} X where
  model := Y
  kanComplex := inferInstance
  hom := e.hom
  inv := e.inv
  homotopyHomInvId := SSet.RelativeMorphism.Homotopy.ofEq
    (congrArg SSet.RelativeMorphism.botEquiv.symm e.hom_inv_id)
  homotopyInvHomId := SSet.RelativeMorphism.Homotopy.ofEq
    (congrArg SSet.RelativeMorphism.botEquiv.symm e.inv_hom_id)

@[simp]
lemma ofIso_model (Y : SSet.{u}) [SSet.KanComplex Y]
    {X : SSet.{v}}
    (e : SSet.uliftFunctor.{v, u}.obj Y ≅ SSet.uliftFunctor.{u, v}.obj X) :
    (ofIso Y e).model = Y := (rfl)

@[simp]
lemma ofIso_hom (Y : SSet.{u}) [SSet.KanComplex Y]
    {X : SSet.{v}}
    (e : SSet.uliftFunctor.{v, u}.obj Y ≅ SSet.uliftFunctor.{u, v}.obj X) :
    (ofIso Y e).hom = e.hom := (rfl)

@[simp]
lemma ofIso_inv (Y : SSet.{u}) [SSet.KanComplex Y]
    {X : SSet.{v}}
    (e : SSet.uliftFunctor.{v, u}.obj Y ≅ SSet.uliftFunctor.{u, v}.obj X) :
    (ofIso Y e).inv = e.inv := (rfl)

/-- Transport a small space model along an isomorphism of ambient simplicial sets.
This constructor is transparent so it preserves the model of its dependent comparison maps. -/
noncomputable abbrev transport {X Z : SSet.{v}} (M : SmallSpaceModel.{u, v} X)
    (e : X ≅ Z) : SmallSpaceModel.{u, v} Z where
  model := M.model
  kanComplex := M.kanComplex
  hom := M.hom ≫ (SSet.uliftFunctor.{u, v}.mapIso e).hom
  inv := (SSet.uliftFunctor.{u, v}.mapIso e).inv ≫ M.inv
  homotopyHomInvId :=
    { h := M.homotopyHomInvId.h
      h₀ := by simp
      h₁ := M.homotopyHomInvId.h₁
      rel := M.homotopyHomInvId.rel }
  homotopyInvHomId :=
    { h := (SSet.uliftFunctor.{u, v}.mapIso e).inv ▷ Δ[1] ≫
        M.homotopyInvHomId.h ≫ (SSet.uliftFunctor.{u, v}.mapIso e).hom
      h₀ := by simp
      h₁ := by simp
      rel := by
        ext n ⟨⟨x, hx⟩, t⟩
        exact hx.elim }

@[simp]
lemma transport_model {X Z : SSet.{v}} (M : SmallSpaceModel.{u, v} X) (e : X ≅ Z) :
    (M.transport e).model = M.model := (rfl)

@[simp]
lemma transport_hom {X Z : SSet.{v}} (M : SmallSpaceModel.{u, v} X) (e : X ≅ Z) :
    (M.transport e).hom = M.hom ≫ SSet.uliftFunctor.map e.hom := (rfl)

@[simp]
lemma transport_inv {X Z : SSet.{v}} (M : SmallSpaceModel.{u, v} X) (e : X ≅ Z) :
    (M.transport e).inv = SSet.uliftFunctor.map e.inv ≫ M.inv := (rfl)

end SmallSpaceModel

/-- A small Kan complex has a small space model. -/
lemma hasSmallSpaceModel_self (Y : SSet.{u}) [SSet.KanComplex Y] :
    HasSmallSpaceModel.{u, u} Y :=
  ⟨SmallSpaceModel.ofIso Y (Iso.refl _)⟩

/-- Existence of a small Kan model is invariant under isomorphism. -/
lemma hasSmallSpaceModel_iff_of_iso {X Z : SSet.{v}} (e : X ≅ Z) :
    HasSmallSpaceModel.{u, v} X ↔ HasSmallSpaceModel.{u, v} Z :=
  ⟨fun ⟨M⟩ ↦ ⟨M.transport e⟩, fun ⟨M⟩ ↦ ⟨M.transport e.symm⟩⟩

/-- A nonempty codiscrete nerve has a small homotopy type in every universe. The model is the
point, regardless of the size of the type of objects. -/
lemma hasSmallSpaceModel_nerveCodiscrete (A : Type v) [Nonempty A] :
    HasSmallSpaceModel.{u, v} (nerve (Codiscrete A)) := by
  refine ⟨{
    model := 𝟙_ SSet.{u}
    kanComplex := (HomotopicalAlgebra.isFibrant_iff_of_isTerminal (𝟙 (𝟙_ SSet.{u}))
      isTerminalTensorUnit).mpr inferInstance
    hom := SSet.const
      (ULift.up (nerveEquiv.symm (Codiscrete.mk (Classical.choice ‹Nonempty A›))))
    inv := SSet.const (ULift.up PUnit.unit)
    homotopyHomInvId := SSet.RelativeMorphism.Homotopy.ofEq
      (congrArg SSet.RelativeMorphism.botEquiv.symm (by ext n ⟨⟨⟩⟩; rfl))
    homotopyInvHomId := (nonempty_homotopy_ulift_nerveCodiscrete _ _).some }⟩

/-- Small homotopy type does not force the vertices to form a small type. -/
lemma exists_hasSmallSpaceModel_not_small_vertices :
    ∃ X : SSet.{u + 1}, HasSmallSpaceModel.{u, u + 1} X ∧ ¬ Small.{u} (X _⦋0⦌) := by
  refine ⟨nerve (Codiscrete (Type u)), hasSmallSpaceModel_nerveCodiscrete _, ?_⟩
  intro h
  exact not_small_type ((small_congr (nerveEquiv.trans codiscreteEquiv)).mp h)

/-- A simplicial set with a small Kan model has a small set of connected components: the comparison
maps induce mutually inverse bijections between its connected components and those of the
model, since homotopic maps induce the same map on connected components. -/
lemma HasSmallSpaceModel.small_π₀ {X : SSet.{v}} (h : HasSmallSpaceModel.{u, v} X) :
    Small.{u} (SSet.π₀ X) := by
  obtain ⟨M⟩ := h
  have hinj : Function.Injective (SSet.mapπ₀ M.inv) :=
    Function.LeftInverse.injective (g := SSet.mapπ₀ M.hom) fun c ↦ by
      rw [← SSet.mapπ₀_comp_apply, M.homotopyInvHomId.mapπ₀_eq, SSet.mapπ₀_id_apply]
  have : Small.{u} (SSet.π₀ (SSet.uliftFunctor.{v, u}.obj M.model)) :=
    small_of_injective (SSet.π₀UliftEquiv M.model).injective
  have : Small.{u} (SSet.π₀ (SSet.uliftFunctor.{u, v}.obj X)) := small_of_injective hinj
  exact small_of_injective (SSet.π₀UliftEquiv X).symm.injective

/-- The discrete simplicial set on a type has a Kan model in universe `u` exactly when the type
is `u`-small. A model is the singular simplicial set of the discrete space on a `u`-small copy of
the type, which is a Kan complex isomorphic to the discrete simplicial set. -/
lemma hasSmallSpaceModel_const_iff (ι : Type v) :
    HasSmallSpaceModel.{u, v} ((Functor.const SimplexCategoryᵒᵖ).obj ι) ↔ Small.{u} ι := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ?_⟩
  · have := h.small_π₀
    exact small_of_injective (SSet.constπ₀Equiv ι).symm.injective
  · let : TopologicalSpace (Shrink.{u} ι) := ⊥
    have : DiscreteTopology (Shrink.{u} ι) := ⟨rfl⟩
    let e : ULift.{v} (Shrink.{u} ι) ≃ ULift.{u} ι :=
      Equiv.ulift.trans ((equivShrink ι).symm.trans Equiv.ulift.symm)
    exact ⟨SmallSpaceModel.ofIso (TopCat.toSSet.obj (TopCat.of (Shrink.{u} ι)))
      (SSet.uliftFunctor.mapIso (TopCat.toSSetIsoConst (TopCat.of (Shrink.{u} ι))) ≪≫
        Functor.constComp SimplexCategoryᵒᵖ (Shrink.{u} ι) uliftFunctor.{v, u} ≪≫
        (Functor.const _).mapIso e.toIso ≪≫
        (Functor.constComp SimplexCategoryᵒᵖ ι uliftFunctor.{u, v}).symm)⟩

end TauCeti
