/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Grothendieck.Pushforward

/-!
# Intertwiners of represented actions over different bases

An intertwiner consists of a change of base, a natural transformation of label
fibers and a comparison of represented coefficient diagrams. It sends a section
to its pullback followed by pushforward. The coefficient comparison induces a map
between the original and transported section limits, without requiring a limit
of the intermediate restricted diagram. Vertical labels commute with this map.

The construction uses the existing strict sections, their pullback and pushforward,
and `CategoryTheory.NatTrans.reindexLimitMap`. Naturality of the pullback
identification and of coefficient pushforward gives label-equivariance before
and after taking limits.

## Attribution

Adapted from `Mei/CategoryTheory/Grothendieck/Intertwiner/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original author credit is retained; the file uses the required Tau Ceti copyright header.
-/

public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Grothendieck CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ w z v u

namespace TauCeti

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
  {V : Type u} [Category.{v} V]
  {C : D ⥤ Cat.{w, z}} {C' : E ⥤ Cat.{w, z}}
  {A : Grothendieck C ⥤ V} {A' : Grothendieck C' ⥤ V}

/-- A comparison of represented actions, with a prescribed change of base. -/
@[ext]
structure ActionIntertwiner (G : E ⥤ D) (A : Grothendieck C ⥤ V)
    (A' : Grothendieck C' ⥤ V) where
  /-- The functors on label fibers, natural in the new base. -/
  labelMap : G ⋙ C ⟶ C'
  /-- The comparison of represented coefficients on the reindexed total category. -/
  coefficient : pre C G ⋙ A ⟶ Grothendieck.map labelMap ⋙ A'

namespace ActionIntertwiner

open TauCeti.CategoryTheory.Grothendieck (Section)

variable {G : E ⥤ D}

/-- Transport a section by pullback on the base and pushforward on the fibers. -/
-- Keep section objects reducible in the types of transported vertical labels.
abbrev mapSection (f : ActionIntertwiner G A A') (s : Section C) : Section C' :=
  Section.pushforward f.labelMap (Section.pullback G s)

/-- Transport sections and their vertical labels functorially. -/
-- The object map must compute to `mapSection` when inferring the target limit.
abbrev sectionFunctor (f : ActionIntertwiner G A A') : Section C ⥤ Section C' where
  obj s := f.mapSection s
  map α := Section.pushforwardHom f.labelMap (Section.pullbackHom G α)
  map_id s := (Section.pullbackFunctor G ⋙ Section.pushforwardFunctor f.labelMap).map_id s
  map_comp α β := (Section.pullbackFunctor G ⋙ Section.pushforwardFunctor f.labelMap).map_comp α β

@[simp]
theorem sectionFunctor_obj (f : ActionIntertwiner G A A') (s : Section C) :
    f.sectionFunctor.obj s = f.mapSection s := (rfl)

/-- A transported label is its pulled-back label followed by the fiber functors. -/
@[simp]
theorem sectionFunctor_map (f : ActionIntertwiner G A A')
    {s t : Section C} (α : s ⟶ t) :
    f.sectionFunctor.map α = Section.pushforwardHom f.labelMap (Section.pullbackHom G α) := (rfl)

/-- The coefficient transformation along a transported section. -/
def sectionComparison (f : ActionIntertwiner G A A') (s : Section C) :
    G ⋙ (s.toFunctor ⋙ A) ⟶ (f.mapSection s).toFunctor ⋙ A' :=
  (Section.coefficientPullbackIso G A s).hom ≫
    Section.coefficientPushforward f.labelMap f.coefficient (Section.pullback G s)

/-- At each new base object, transport identifies the old section object and then
applies the represented coefficient comparison. -/
@[simp]
theorem sectionComparison_app (f : ActionIntertwiner G A A') (s : Section C) (e : E) :
    (f.sectionComparison s).app e =
      A.map (eqToHom (Functor.congr_obj (Section.pullback_comp_pre G s) e).symm) ≫
        f.coefficient.app ((Section.pullback G s).toFunctor.obj e) := by
  unfold sectionComparison
  -- The pushforward section wrapper conceals the common coefficient objects.
  erw [NatTrans.comp_app, Section.coefficientPullbackIso_hom_app,
    Section.coefficientPushforward_app]
  rfl

/-- The induced map on completed coefficient objects. Only its two endpoint limits
are required, even if restriction along the base functor has no chosen limit. -/
noncomputable def limitMap (f : ActionIntertwiner G A A') (s : Section C)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit ((f.mapSection s).toFunctor ⋙ A')] :
    limit (s.toFunctor ⋙ A) ⟶ limit ((f.mapSection s).toFunctor ⋙ A') :=
  (f.sectionComparison s).reindexLimitMap

/-- Projections compute the coefficient map at the corresponding old section object. -/
@[reassoc (attr := simp)]
theorem limitMap_π (f : ActionIntertwiner G A A') (s : Section C)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit ((f.mapSection s).toFunctor ⋙ A')] (e : E) :
    f.limitMap s ≫ limit.π ((f.mapSection s).toFunctor ⋙ A') e =
      limit.π (s.toFunctor ⋙ A) (G.obj e) ≫ (f.sectionComparison s).app e :=
  NatTrans.reindexLimitMap_π _ e

/-- When the intermediate limit exists, the comparison factors through restriction
and then through the coefficient pushforward. -/
theorem limitMap_eq (f : ActionIntertwiner G A A') (s : Section C)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit ((f.mapSection s).toFunctor ⋙ A')]
    [HasLimit ((Section.pullback G s).toFunctor ⋙ pre C G ⋙ A)] :
    f.limitMap s = Section.coefficientRestriction G A s ≫
      Section.coefficientPushforwardLimit f.labelMap f.coefficient (Section.pullback G s) := by
  apply limit.hom_ext
  intro e
  simp only [Category.assoc, limitMap_π, sectionComparison_app,
    Section.coefficientPushforwardLimit_π]
  -- Identify the pullback coefficient diagram through its strict-section wrapper.
  erw [Section.coefficientRestriction_π_assoc]
  rfl

/-- The section comparison intertwines vertical labels before taking limits. -/
@[reassoc]
theorem sectionComparison_naturality (f : ActionIntertwiner G A A')
    {s t : Section C} (α : s ⟶ t) :
    whiskerLeft G (whiskerRight (Section.hom α) A) ≫ f.sectionComparison t =
      f.sectionComparison s ≫
        whiskerRight (Section.hom (f.sectionFunctor.map α)) A' := by
  unfold sectionComparison
  rw [← Category.assoc, Section.coefficientPullbackIso_naturality, Category.assoc,
    Section.coefficientPushforward_naturality]
  exact (Category.assoc _ _ _).symm

/-- Comparisons of completed coefficients are equivariant for completed labels. -/
@[reassoc]
theorem limitMap_naturality (f : ActionIntertwiner G A A')
    {s t : Section C} (α : s ⟶ t)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)]
    [HasLimit ((f.mapSection s).toFunctor ⋙ A')] [HasLimit ((f.mapSection t).toFunctor ⋙ A')] :
    limMap (whiskerRight (Section.hom α) A) ≫ f.limitMap t =
      f.limitMap s ≫ limMap (whiskerRight (Section.hom (f.sectionFunctor.map α)) A') := by
  apply limit.hom_ext
  intro e
  simp only [Category.assoc, limitMap_π, limMap_π_assoc, limMap_π,
    limitMap_π_assoc]
  exact congrArg (limit.π (s.toFunctor ⋙ A) (G.obj e) ≫ ·)
    (NatTrans.congr_app (f.sectionComparison_naturality α) e)

/-- An invertible represented comparison remains invertible along each section. -/
instance isIso_sectionComparison (f : ActionIntertwiner G A A') [IsIso f.coefficient]
    (s : Section C) : IsIso (f.sectionComparison s) := by
  unfold sectionComparison
  infer_instance

/-- An invertible represented comparison along an initial base functor identifies
completed coefficient objects. No equivalence assumption on label fibers is needed. -/
instance isIso_limitMap (f : ActionIntertwiner G A A') [IsIso f.coefficient] [G.Initial]
    (s : Section C) [HasLimit (s.toFunctor ⋙ A)]
    [HasLimit ((f.mapSection s).toFunctor ⋙ A')] : IsIso (f.limitMap s) := by
  unfold limitMap
  infer_instance

end ActionIntertwiner
end TauCeti
