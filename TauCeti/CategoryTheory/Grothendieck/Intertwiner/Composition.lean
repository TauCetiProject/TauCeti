/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Grothendieck.Intertwiner.Basic

/-!
# Identity and composition of represented-action intertwiners

Represented coefficient comparisons can be composed even when their base categories
are different. The composite first applies the old coefficient comparison at the
reindexed object, then the new comparison. Its transported sections and induced
maps of limits agree with successive transport and comparison.

We use Mathlib's `Grothendieck.pre_comp_map` and `Grothendieck.map_comp_eq`
to identify the total-category functors, and the existing section pullback,
pushforward and reindexed limit maps.

## Attribution

Adapted from `Mei/CategoryTheory/Grothendieck/Intertwiner/Composition.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original author credit is retained; the file uses the required Tau Ceti copyright header.
-/

public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Grothendieck CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ w z v u

namespace TauCeti.ActionIntertwiner

open TauCeti.CategoryTheory.Grothendieck (Section)

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
  {B : Type u₃} [Category.{v₃} B] {V : Type u} [Category.{v} V]
  {C : D ⥤ Cat.{w, z}} {C' : E ⥤ Cat.{w, z}} {C'' : B ⥤ Cat.{w, z}}
  {A : Grothendieck C ⥤ V} {A' : Grothendieck C' ⥤ V}
  {A'' : Grothendieck C'' ⥤ V} {G : E ⥤ D} {H : B ⥤ E}

/-- The identity comparison of a represented action. -/
-- The label map must compute in dependent coefficient-component types.
@[expose]
def id (A : Grothendieck C ⥤ V) : ActionIntertwiner (𝟭 D) A A where
  labelMap := 𝟙 C
  coefficient := eqToHom (by rw [pre_id, Grothendieck.map_id_eq (F := C)]; rfl)

@[simp]
theorem id_labelMap : (id A).labelMap = 𝟙 C := (rfl)

/-- Compose comparisons, applying `f` before `g`. The base functor is `H ⋙ G`. -/
-- Expose the label map for dependent types; coefficient simplification uses the app lemma.
@[expose]
def comp (g : ActionIntertwiner H A' A'') (f : ActionIntertwiner G A A') :
    ActionIntertwiner (H ⋙ G) A A'' where
  labelMap := whiskerLeft H f.labelMap ≫ g.labelMap
  coefficient :=
    eqToHom (by rw [pre_comp]; rfl) ≫
      whiskerLeft (pre (G ⋙ C) H) f.coefficient ≫
        eqToHom (pre_comp_map_assoc H f.labelMap A') ≫
          whiskerLeft (Grothendieck.map (whiskerLeft H f.labelMap)) g.coefficient ≫
            eqToHom (by rw [map_comp_eq]; rfl)

@[simp]
theorem comp_labelMap (g : ActionIntertwiner H A' A'')
    (f : ActionIntertwiner G A A') :
    (g.comp f).labelMap = whiskerLeft H f.labelMap ≫ g.labelMap := (rfl)

/-- Composition evaluates the first comparison after forgetting the new base,
then the second comparison after applying the first fiber functor. -/
@[simp]
theorem comp_coefficient_app (g : ActionIntertwiner H A' A'')
    (f : ActionIntertwiner G A A') (X : Grothendieck ((H ⋙ G) ⋙ C)) :
    (g.comp f).coefficient.app X =
      f.coefficient.app ((pre (G ⋙ C) H).obj X) ≫
        g.coefficient.app ((Grothendieck.map (whiskerLeft H f.labelMap)).obj X) := by
  simp only [comp, NatTrans.comp_app, whiskerLeft_app, eqToHom_app]
  -- The functor identifications have equal objects; only their arrow maps differ.
  erw [eqToHom_refl, eqToHom_refl, eqToHom_refl,
    Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

/-- The identity comparison has identity coefficient components. -/
@[simp]
theorem id_coefficient_app (X : Grothendieck C) :
    (id A).coefficient.app X = 𝟙 (A.obj X) := by
  simp only [id, eqToHom_app]
  -- The total-category functors agree on objects; evaluate their equality component.
  erw [eqToHom_refl]
  rfl

/-- The identity intertwiner leaves every section unchanged. -/
@[simp]
theorem mapSection_id (s : Section C) : (id A).mapSection s = s := by
  simp only [mapSection, Section.pullback_id]
  exact Section.pushforward_id s

/-- Postcomposing by the identity intertwiner changes no data. -/
@[simp]
theorem id_comp (f : ActionIntertwiner G A A') : (id A').comp f = f := by
  apply ActionIntertwiner.ext
  · ext e
    rfl
  · apply heq_of_eq
    ext X
    exact (comp_coefficient_app (id A') f X).trans
      ((congrArg (f.coefficient.app _ ≫ ·) (id_coefficient_app _)).trans
        (Category.comp_id _))

/-- Precomposing by the identity intertwiner changes no data. -/
@[simp]
theorem comp_id (f : ActionIntertwiner G A A') : f.comp (id A) = f := by
  apply ActionIntertwiner.ext
  · ext e
    rfl
  · apply heq_of_eq
    ext X
    exact (comp_coefficient_app f (id A) X).trans
      ((congrArg (· ≫ f.coefficient.app _) (id_coefficient_app _)).trans
        (Category.id_comp _))

/-- Composition of intertwiners is associative, including its change of base. -/
theorem comp_assoc {B' : Type*} [Category* B'] {C''' : B' ⥤ Cat.{w, z}}
    {A''' : Grothendieck C''' ⥤ V} {K : B' ⥤ B}
    (h : ActionIntertwiner K A'' A''') (g : ActionIntertwiner H A' A'')
    (f : ActionIntertwiner G A A') :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ActionIntertwiner.ext
  · ext e
    rfl
  · apply heq_of_eq
    ext X
    have hl := comp_coefficient_app (h.comp g) f X
    have hr := comp_coefficient_app h (g.comp f) X
    -- Nested base changes give the same objects through differently associated functors.
    erw [comp_coefficient_app h g] at hl
    erw [comp_coefficient_app g f] at hr
    exact hl.trans ((Category.assoc _ _ _).symm.trans hr.symm)

/-- Successive intertwiners transport sections by their composite. -/
@[simp]
theorem mapSection_comp (g : ActionIntertwiner H A' A'')
    (f : ActionIntertwiner G A A') (s : Section C) :
    (g.comp f).mapSection s = g.mapSection (f.mapSection s) := by
  dsimp only [mapSection]
  rw [comp_labelMap, Section.pushforward_comp, Section.pullback_comp,
    ← Section.pullback_pushforward]

/-- Identity comparisons induce the identity transformation after identifying
its transported section with the original section. -/
@[simp, reassoc]
theorem sectionComparison_id (s : Section C) :
    (id A).sectionComparison s ≫
      eqToHom (congrArg (fun t : Section C => t.toFunctor ⋙ A) (mapSection_id s)) =
        (Functor.leftUnitor (s.toFunctor ⋙ A)).hom := by
  ext d
  simp only [NatTrans.comp_app, sectionComparison_app,
    eqToHom_app, Functor.leftUnitor_hom_app]
  simp only [id, eqToHom_app, eqToHom_map, eqToHom_trans]
  -- Both transports now identify the same section object through its Fiber.mk wrapper.
  erw [eqToHom_trans, eqToHom_refl]
  rfl

/-- The comparison along a composite is the successive coefficient comparison,
with the transported section identified by `mapSection_comp`. -/
@[reassoc]
theorem sectionComparison_comp (g : ActionIntertwiner H A' A'')
    (f : ActionIntertwiner G A A') (s : Section C) :
    (g.comp f).sectionComparison s ≫
      eqToHom (congrArg (fun t : Section C'' => t.toFunctor ⋙ A'') (mapSection_comp g f s)) =
        whiskerLeft H (f.sectionComparison s) ≫ g.sectionComparison (f.mapSection s) := by
  ext b
  simp only [NatTrans.comp_app, sectionComparison_app, comp_coefficient_app,
    whiskerLeft_app, eqToHom_app]
  have hf : (pre (G ⋙ C) H).obj ((Section.pullback (H ⋙ G) s).toFunctor.obj b) =
      (Section.pullback G s).toFunctor.obj (H.obj b) := by
    rw [Section.pullback_comp]
    exact pre_obj_liftObj H _ _
      (base_eq_of_comp_forget (𝟭 E) (Section.pullback G s).toFunctor_comp_forget (H.obj b))
  have hg : (Grothendieck.map (whiskerLeft H f.labelMap)).obj
      ((Section.pullback (H ⋙ G) s).toFunctor.obj b) =
        (Section.pullback H (f.mapSection s)).toFunctor.obj b := by
    rw [mapSection, Section.pullback_pushforward, Section.pullback_comp]
    rfl
  rw [f.coefficient.congr hf, g.coefficient.congr hg]
  simp only [Functor.comp_map, eqToHom_map]
  -- State the transport identity with explicit endpoints: the section wrappers above
  -- hide these endpoints from simp's restricted definitional-equality matching.
  have normalize {W X X' Y Y' Z Z' T : V}
      (p : W = X) (q : X = X') (r : Y = Y') (t : Y' = Z) (u : Z' = T)
      (a : X' ⟶ Y) (b : Z ⟶ Z') :
      (eqToHom p ≫ (eqToHom q ≫ a ≫ eqToHom r) ≫ eqToHom t ≫ b ≫ eqToHom u) ≫
          eqToHom u.symm = (eqToHom (p.trans q) ≫ a) ≫ eqToHom (r.trans t) ≫ b := by
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
  exact normalize _ _ _ _ _
    (f.coefficient.app ((Section.pullback G s).toFunctor.obj (H.obj b)))
    (g.coefficient.app ((Section.pullback H (f.mapSection s)).toFunctor.obj b))

/-- Identity intertwiners act identically on coefficient limits, after the
canonical identification of the transported coefficient diagram. -/
@[simp, reassoc]
theorem limitMap_id (s : Section C) [HasLimit (s.toFunctor ⋙ A)]
    [HasLimit (((id A).mapSection s).toFunctor ⋙ A)] :
    (id A).limitMap s ≫
      limMap (eqToHom (congrArg (fun t : Section C => t.toFunctor ⋙ A) (mapSection_id s))) =
        𝟙 (limit (s.toFunctor ⋙ A)) := by
  apply limit.hom_ext
  intro d
  simp only [Category.assoc, limMap_π, limitMap_π_assoc, Category.id_comp]
  have h := NatTrans.congr_app (sectionComparison_id (A := A) s) d
  have h' := congrArg (limit.π (s.toFunctor ⋙ A) d ≫ ·) h
  simp only [NatTrans.comp_app, Functor.leftUnitor_hom_app, Category.comp_id] at h'
  exact h'

/-- The map on coefficient limits induced by a composite is the composite of
its two limit maps, with the final diagrams canonically identified. -/
@[reassoc]
theorem limitMap_comp (g : ActionIntertwiner H A' A'')
    (f : ActionIntertwiner G A A') (s : Section C)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit ((f.mapSection s).toFunctor ⋙ A')]
    [HasLimit (((g.comp f).mapSection s).toFunctor ⋙ A'')]
    [HasLimit ((g.mapSection (f.mapSection s)).toFunctor ⋙ A'')] :
    (g.comp f).limitMap s ≫
      limMap (eqToHom
        (congrArg (fun t : Section C'' => t.toFunctor ⋙ A'') (mapSection_comp g f s))) =
          f.limitMap s ≫ g.limitMap (f.mapSection s) := by
  apply limit.hom_ext
  intro b
  simp only [Category.assoc, limMap_π, limitMap_π_assoc, limitMap_π]
  exact congrArg (limit.π (s.toFunctor ⋙ A) (G.obj (H.obj b)) ≫ ·)
    (NatTrans.congr_app (sectionComparison_comp g f s) b)

end TauCeti.ActionIntertwiner
