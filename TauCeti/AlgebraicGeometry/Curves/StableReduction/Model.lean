/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Models over discrete valuation rings

This file packages a model of a scheme over the fraction field of a discrete valuation ring.
A model includes its total space, a flat morphism of finite presentation to the spectrum of the
ring, and an explicit identification of its generic fibre with the prescribed scheme.  Thus a
morphism of models is required to induce the identity on that prescribed generic fibre.

Models form a category.  Properness is deliberately kept as an additional predicate: many
constructions first produce a model and establish properness separately.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

namespace TauCeti

universe u

-- The categorical packaging below adapts the target signature in
-- `TauCetiRoadmap/StableReduction/Suggested.lean`.  We additionally record
-- quasi-separatedness, the third constituent of finite presentation in Mathlib.

/-- The scalar extension of a scheme over `R` to a field `K`, regarded as a scheme over `K`.
When `K` is a fraction field of `R`, this is the generic fibre. -/
noncomputable abbrev genericFiber (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    Over (Spec (.of K)) :=
  Over.mk (pullback.snd toBase (Spec.map (CommRingCat.ofHom (algebraMap R K))))

/-- The canonical morphism from the scalar-extended fibre to the original total space. -/
noncomputable abbrev genericFiberι (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (genericFiber R K toBase).left ⟶ X :=
  pullback.fst toBase (Spec.map (CommRingCat.ofHom (algebraMap R K)))

/-- A flat finitely presented model over a discrete valuation ring, together with an explicit
identification of its generic fibre with a fixed scheme over the fraction field.

Finite presentation is recorded by Mathlib's three constituent properties:
`LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`. -/
structure Model (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Scheme.{u}) (toK : C ⟶ Spec (.of K)) where
  /-- The total space of the model. -/
  total : Scheme.{u}
  /-- The structure morphism of the model. -/
  toBase : total ⟶ Spec (.of R)
  /-- The structure morphism is flat. -/
  flat : Flat toBase
  /-- The structure morphism is locally of finite presentation. -/
  locallyOfFinitePresentation : LocallyOfFinitePresentation toBase
  /-- The structure morphism is quasi-compact. -/
  quasiCompact : QuasiCompact toBase
  /-- The structure morphism is quasi-separated. -/
  quasiSeparated : QuasiSeparated toBase
  /-- The chosen identification of the generic fibre with the prescribed scheme over `K`. -/
  genericFiberIso : genericFiber R K toBase ≅ Over.mk toK

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

attribute [instance] Model.flat Model.locallyOfFinitePresentation Model.quasiCompact
  Model.quasiSeparated

/-- Properness of the structure morphism is an additional property of a model. -/
abbrev IsProper (M : Model R K C toK) : Prop :=
  AlgebraicGeometry.IsProper M.toBase

/-- The morphism on generic fibres induced by a morphism over the base. -/
def baseChangeHom {M N : Model R K C toK} (f : M.total ⟶ N.total)
    (overBase : f ≫ N.toBase = M.toBase) :
    (genericFiber R K M.toBase).left ⟶ (genericFiber R K N.toBase).left :=
  pullback.lift (genericFiberι R K M.toBase ≫ f) (genericFiber R K M.toBase).hom (by
    rw [Category.assoc, overBase]
    exact pullback.condition)

@[reassoc (attr := simp)]
lemma baseChangeHom_genericFiberι {M N : Model R K C toK} (f : M.total ⟶ N.total)
    (overBase : f ≫ N.toBase = M.toBase) :
    baseChangeHom f overBase ≫ genericFiberι R K N.toBase =
      genericFiberι R K M.toBase ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeHom_snd {M N : Model R K C toK} (f : M.total ⟶ N.total)
    (overBase : f ≫ N.toBase = M.toBase) :
    baseChangeHom f overBase ≫
        pullback.snd N.toBase (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      pullback.snd M.toBase (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  pullback.lift_snd _ _ _

/-- A morphism of models is a morphism over the DVR that respects the chosen identification of
the generic fibre. -/
structure Hom (M N : Model R K C toK) where
  /-- The morphism of total spaces. -/
  hom : M.total ⟶ N.total
  /-- The morphism commutes with the structure maps to the DVR. -/
  overBase : hom ≫ N.toBase = M.toBase
  /-- On generic fibres, the morphism respects the chosen identifications with `C`. -/
  genericFiber :
    baseChangeHom hom overBase ≫ N.genericFiberIso.hom.left = M.genericFiberIso.hom.left

@[ext]
lemma Hom.ext {M N : Model R K C toK} {f g : Hom M N} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

@[simp]
lemma baseChangeHom_id (M : Model R K C toK) :
    baseChangeHom (M := M) (N := M) (𝟙 M.total) (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp [baseChangeHom]
  · simp [baseChangeHom]

@[simp]
lemma baseChangeHom_comp {M N P : Model R K C toK} (f : Hom M N) (g : Hom N P) :
    baseChangeHom (f.hom ≫ g.hom) (by rw [Category.assoc, g.overBase, f.overBase]) =
      baseChangeHom f.hom f.overBase ≫ baseChangeHom g.hom g.overBase := by
  apply pullback.hom_ext
  · simp only [baseChangeHom, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc]
  · simp only [baseChangeHom, pullback.lift_snd, Category.assoc]
    exact (baseChangeHom_snd f.hom f.overBase).symm

/-- Models of a fixed scheme over the fraction field form a category. -/
instance : Category (Model R K C toK) where
  Hom := Hom
  id M :=
    { hom := 𝟙 M.total
      overBase := by simp
      genericFiber := by
        dsimp only [genericFiber]
        rw [baseChangeHom_id, Category.id_comp] }
  comp f g :=
    { hom := f.hom ≫ g.hom
      overBase := by rw [Category.assoc, g.overBase, f.overBase]
      genericFiber := by
        dsimp only [genericFiber] at f g ⊢
        rw [baseChangeHom_comp, Category.assoc, g.genericFiber, f.genericFiber] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

@[simp]
lemma id_hom (M : Model R K C toK) : Hom.hom (𝟙 M) = 𝟙 M.total :=
  rfl

@[simp]
lemma comp_hom {M N P : Model R K C toK} (f : M ⟶ N) (g : N ⟶ P) :
    Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

/-- Isomorphisms of models are categorical isomorphisms, hence automatically preserve the
chosen generic-fibre identification in both directions. -/
abbrev Iso (M N : Model R K C toK) := M ≅ N

/-- The faithful functor sending a model to its total space. -/
@[expose]
def forget : Model R K C toK ⥤ Scheme.{u} where
  obj M := M.total
  map f := f.hom
  map_id M := id_hom M
  map_comp f g := comp_hom f g

instance : (forget (R := R) (K := K) (C := C) (toK := toK)).Faithful where
  map_injective {_ _} _ _ h := Hom.ext h

@[simp]
lemma forget_obj (M : Model R K C toK) :
    (forget (R := R) (K := K) (C := C) (toK := toK)).obj M = M.total :=
  rfl

@[simp]
lemma forget_map {M N : Model R K C toK} (f : M ⟶ N) :
    (forget (R := R) (K := K) (C := C) (toK := toK)).map f = f.hom :=
  rfl

end Model

end TauCeti
