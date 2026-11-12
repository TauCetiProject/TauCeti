/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Limits.Reindex
public import TauCeti.CategoryTheory.Grothendieck.Section

/-!
# Pulling back sections of a Grothendieck construction

A section can be restricted along any functor of base categories. The resulting
section of the reindexed Grothendieck construction has the original objects and
arrows after applying `Grothendieck.pre`. This is the section transport needed
to compare represented coefficient diagrams over different bases.

The construction uses Mathlib's `Grothendieck.pre` and `Functor.Fiber`, retaining
strict sections and vertical natural transformations on their existing carriers.
`Section.pullbackFunctor` restricts sections and labels, and `Section.pullback_id`
and `Section.pullback_comp` give its laws under changes of base.

For a represented coefficient diagram, `Section.coefficientRestriction` maps the
old section limit to the new one. Its projection formula and label-equivariance
law characterize restriction of matching families. It is invertible for an
initial base functor. This uses `NatTrans.reindexLimitMap` from
`TauCeti.CategoryTheory.Limits.Reindex`, without requiring limits along sections
other than those being compared.

## Attribution

Adapted from `Mei/CategoryTheory/Grothendieck/Pullback.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original author credit is retained; the file uses the required Tau Ceti copyright header.
-/

public section

open CategoryTheory CategoryTheory.Functor

universe v u v' u' w z

namespace CategoryTheory.Grothendieck

variable {D : Type u} [Category.{v} D] {E : Type u'} [Category.{v'} E]
  {C : D ⥤ Cat.{w, z}} (G : E ⥤ D)

/-- Reindex an object whose base is in the image of `G`. -/
abbrev liftObj (X : Grothendieck C) (e : E) (h : X.base = G.obj e) :
    Grothendieck (G ⋙ C) := ⟨e, cast (congrArg (fun d => ↥(C.obj d)) h) X.fiber⟩

/-- Forgetting the new base recovers the original object. -/
@[simp]
theorem pre_obj_liftObj (X : Grothendieck C) (e : E) (h : X.base = G.obj e) :
    (pre C G).obj (liftObj G X e h) = X := by
  cases X with | mk d x =>
  dsimp at h
  subst d
  rfl

/-- Reindex a morphism with prescribed base arrow. -/
def liftHom {X Y : Grothendieck C} {e e' : E} (f : X ⟶ Y) (g : e ⟶ e')
    (hX : X.base = G.obj e) (hY : Y.base = G.obj e')
    (hf : f.base = eqToHom hX ≫ G.map g ≫ eqToHom hY.symm) :
    liftObj G X e hX ⟶ liftObj G Y e' hY := by
  cases X with | mk d x =>
  cases Y with | mk d' y =>
  dsimp at hX hY
  subst d
  subst d'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  exact ⟨g, eqToHom (by rw [hf]; rfl) ≫ f.fiber⟩

@[simp]
theorem liftHom_base {X Y : Grothendieck C} {e e' : E} (f : X ⟶ Y) (g : e ⟶ e')
    (hX : X.base = G.obj e) (hY : Y.base = G.obj e') (hf) :
    (liftHom G f g hX hY hf).base = g := by
  cases X with | mk d x =>
  cases Y with | mk d' y =>
  dsimp at hX hY
  subst d
  subst d'
  rfl

/-- Forgetting the new base recovers the original morphism with its endpoints identified. -/
@[simp]
theorem pre_map_liftHom {X Y : Grothendieck C} {e e' : E} (f : X ⟶ Y) (g : e ⟶ e')
    (hX : X.base = G.obj e) (hY : Y.base = G.obj e') (hf) :
    (pre C G).map (liftHom G f g hX hY hf) =
      eqToHom (pre_obj_liftObj G X e hX) ≫ f ≫
        eqToHom (pre_obj_liftObj G Y e' hY).symm := by
  cases X with | mk d x =>
  cases Y with | mk d' y =>
  dsimp at hX hY
  subst d
  subst d'
  simp only [liftObj, pre, cast_eq, eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext _ _ ?_ ?_
  · simpa using hf.symm
  · dsimp [liftHom]
    -- The reindexed and original fiber categories are definitionally the same.
    erw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- Base arrows together with their images under `pre` determine a morphism. -/
theorem hom_ext_of_pre {X Y : Grothendieck (G ⋙ C)} {f g : X ⟶ Y}
    (hb : f.base = g.base) (hf : (pre C G).map f = (pre C G).map g) : f = g := by
  apply Grothendieck.ext _ _ hb
  have h := Grothendieck.congr hf
  simpa only [pre_map_fiber, eqToHom_comp_iff] using h

/-- Reindexing a morphism twice agrees with reindexing along the composite base functor. -/
theorem liftHom_comp {B : Type*} [Category* B] (H : B ⥤ E)
    {X Y : Grothendieck C} {b b' : B} (f : X ⟶ Y) (g : b ⟶ b')
    (hX : X.base = G.obj (H.obj b)) (hY : Y.base = G.obj (H.obj b')) (hf) :
    liftHom (H ⋙ G) f g hX hY hf =
      liftHom H (liftHom G f (H.map g) hX hY hf) g rfl rfl (by simp) := by
  cases X with | mk d x =>
  cases Y with | mk d' y =>
  dsimp at hX hY
  subst d
  subst d'
  simp only [liftHom, Functor.comp_obj, Functor.comp_map, cast_eq]
  congr 1
  -- Nested lifts compose equality transports in the same reindexed fiber category.
  erw [eqToHom_trans_assoc]

/-- Reindexing commutes with a natural transformation of the fibers on objects. -/
@[simp]
theorem liftObj_map {C' : D ⥤ Cat.{w, z}} (h : C ⟶ C')
    (X : Grothendieck C) (e : E) (hx : X.base = G.obj e) :
    liftObj G ((Grothendieck.map h).obj X) e hx =
      (Grothendieck.map (whiskerLeft G h)).obj (liftObj G X e hx) := by
  cases X with | mk d x =>
  dsimp at hx
  subst d
  rfl

/-- Reindexing commutes with fiber functors on morphisms, with the endpoints
identified by `liftObj_map`. -/
theorem liftHom_map {C' : D ⥤ Cat.{w, z}} (h : C ⟶ C') {X Y : Grothendieck C} {e e' : E}
    (f : X ⟶ Y) (g : e ⟶ e')
    (hx : X.base = G.obj e) (hy : Y.base = G.obj e')
    (hf : f.base = eqToHom hx ≫ G.map g ≫ eqToHom hy.symm) :
    HEq (liftHom G ((Grothendieck.map h).map f) g hx hy hf)
      ((Grothendieck.map (whiskerLeft G h)).map (liftHom G f g hx hy hf)) := by
  cases X with | mk d x =>
  cases Y with | mk d' y =>
  dsimp at hx hy
  subst d d'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  cases f with | mk b k =>
  dsimp at hf
  subst b
  dsimp [liftHom]
  -- The endpoint casts disappear after substituting the prescribed base objects.
  apply heq_of_eq
  refine Grothendieck.ext _ _ (by simp) ?_
  simp only [Grothendieck.map_map_fiber, whiskerLeft_app,
    Category.id_comp]
  erw [eqToHom_refl, Category.id_comp]
  erw [Category.id_comp, Category.id_comp]

/-- The object of a functor over `G` lies over the corresponding object of `G`. -/
theorem base_eq_of_comp_forget {S : E ⥤ Grothendieck C}
    (hS : S ⋙ forget C = G) (e : E) : (S.obj e).base = G.obj e :=
  Functor.congr_obj hS e

/-- Lift a functor over `G` to the reindexed Grothendieck construction. -/
-- The object formula must compute to type liftFunctor_map and vertical base identities.
@[expose]
def liftFunctor (S : E ⥤ Grothendieck C) (hS : S ⋙ forget C = G) :
    E ⥤ Grothendieck (G ⋙ C) where
  obj e := liftObj G (S.obj e) e (base_eq_of_comp_forget G hS e)
  map f := liftHom G (S.map f) f
    (base_eq_of_comp_forget G hS _)
    (base_eq_of_comp_forget G hS _)
    (by convert Functor.congr_hom hS f using 1 <;> rfl)
  map_id e := by
    apply hom_ext_of_pre G
    · simp
    · simp
  map_comp f g := by
    apply hom_ext_of_pre G
    · simp
    · simp [Category.assoc]

/-- The lifted object is the original object with its base reindexed. -/
@[simp]
theorem liftFunctor_obj (S : E ⥤ Grothendieck C) (hS : S ⋙ forget C = G) (e : E) :
    (liftFunctor G S hS).obj e =
      liftObj G (S.obj e) e (base_eq_of_comp_forget G hS e) := (rfl)

/-- The lifted arrow retains its prescribed arrow in the new base. -/
@[simp]
theorem liftFunctor_map (S : E ⥤ Grothendieck C) (hS : S ⋙ forget C = G)
    {e e' : E} (f : e ⟶ e') :
    (liftFunctor G S hS).map f = liftHom G (S.map f) f
      (base_eq_of_comp_forget G hS e) (base_eq_of_comp_forget G hS e')
      (by convert Functor.congr_hom hS f using 1 <;> rfl) := (rfl)

/-- The lifted functor lies over the identity of its new base. -/
@[simp]
theorem liftFunctor_comp_forget (S : E ⥤ Grothendieck C) (hS : S ⋙ forget C = G) :
    liftFunctor G S hS ⋙ forget (G ⋙ C) = 𝟭 E := by
  refine Functor.hext (fun e => by simp) ?_
  intro e e' f
  -- The projection has the same objects as the identity after unfolding the lift.
  dsimp
  exact heq_of_eq (liftHom_base G _ _ _ _ _)

/-- Composing a lift with `pre` gives the original functor. -/
@[simp]
theorem liftFunctor_comp_pre (S : E ⥤ Grothendieck C) (hS : S ⋙ forget C = G) :
    liftFunctor G S hS ⋙ pre C G = S := by
  refine Functor.ext (fun e => pre_obj_liftObj G (S.obj e) e
    (base_eq_of_comp_forget G hS e)) ?_
  intro e e' f
  exact pre_map_liftHom G (S.map f) f _ _ _

/-- Lifting a functor over the base commutes with applying fiber functors. -/
theorem liftFunctor_comp_map {C' : D ⥤ Cat.{w, z}} (h : C ⟶ C') (S : E ⥤ Grothendieck C)
    (hs : S ⋙ forget C = G) :
    liftFunctor G (S ⋙ Grothendieck.map h) (by rw [Functor.assoc, functor_comp_forget]; exact hs) =
      liftFunctor G S hs ⋙ Grothendieck.map (whiskerLeft G h) := by
  refine Functor.hext (fun e => ?_) (fun e e' f => ?_)
  · exact liftObj_map G h (S.obj e) e (base_eq_of_comp_forget G hs e)
  · exact liftHom_map G h (S.map f) f
      (base_eq_of_comp_forget G hs e)
      (base_eq_of_comp_forget G hs e')
      (by convert Functor.congr_hom hs f using 1 <;> rfl)

variable {S T : E ⥤ Grothendieck C} (hS : S ⋙ forget C = G) (hT : T ⋙ forget C = G)

/-- A vertical transformation of functors over `G` lifts to the reindexed construction. -/
def liftNatTrans (α : S ⟶ T)
    (hα : whiskerRight α (forget C) = eqToHom hS ≫ eqToHom hT.symm) :
    liftFunctor G S hS ⟶ liftFunctor G T hT where
  app e := liftHom G (α.app e) (𝟙 e)
    (base_eq_of_comp_forget G hS e)
    (base_eq_of_comp_forget G hT e) (by
      -- Whiskering presents the same base arrows through the forgetful functor.
      convert NatTrans.congr_app hα e using 1 <;> simp <;> rfl)
  naturality e e' f := by
    -- Compute the lifted endpoints before simplifying compositions in their common fiber.
    apply hom_ext_of_pre G
    · simp [liftFunctor]
    · simp [liftFunctor, Category.assoc]

variable (α : S ⟶ T) (hα : whiskerRight α (forget C) = eqToHom hS ≫ eqToHom hT.symm)

/-- A lifted component recovers the original component under the canonical identifications. -/
@[simp]
theorem pre_map_liftNatTrans_app (e : E) :
    (pre C G).map ((liftNatTrans G hS hT α hα).app e) =
      eqToHom (Functor.congr_obj (liftFunctor_comp_pre G S hS) e) ≫ α.app e ≫
        eqToHom (Functor.congr_obj (liftFunctor_comp_pre G T hT) e).symm := by
  dsimp [liftNatTrans]
  exact pre_map_liftHom G _ _ _ _ _

/-- A lifted transformation lies over the identity of the new base. -/
theorem liftNatTrans_over :
    whiskerRight (liftNatTrans G hS hT α hα) (forget (G ⋙ C)) =
      eqToHom (liftFunctor_comp_forget G S hS) ≫
        eqToHom (liftFunctor_comp_forget G T hT).symm := by
  ext e
  -- Whiskering and liftHom use definitionally equal presentations of the endpoints.
  convert liftHom_base G (α.app e) (𝟙 e)
    (base_eq_of_comp_forget G hS e)
    (base_eq_of_comp_forget G hT e)
    (by convert NatTrans.congr_app hα e using 1 <;> simp <;> rfl) using 1
  · rfl
  · rfl
  · -- Evaluate the functor equalities before identifying the fiber objects.
    erw [NatTrans.comp_app, eqToHom_app, eqToHom_app]
    dsimp [liftFunctor]
    erw [eqToHom_trans, eqToHom_refl]
    rfl

end CategoryTheory.Grothendieck

namespace TauCeti.CategoryTheory.Grothendieck
namespace Section

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Grothendieck

variable {D : Type u} [Category.{v} D] {E : Type u'} [Category.{v'} E]
  {C : D ⥤ Cat.{w, z}} (G : E ⥤ D)

/-- Reindexing the underlying functor of a section gives a functor over the new base map. -/
theorem comp_toFunctor_comp_forget (s : Section C) :
    (G ⋙ s.toFunctor) ⋙ forget C = G := by
  rw [Functor.assoc, s.toFunctor_comp_forget, Functor.comp_id]

/-- Restriction of a section to a new base category. -/
@[expose]
def pullback (s : Section C) : Section (G ⋙ C) :=
  Functor.Fiber.mk (liftFunctor_comp_forget G (G ⋙ s.toFunctor)
    (comp_toFunctor_comp_forget G s))

/-- The underlying functor of a restricted section is the lift of the reindexed functor. -/
theorem pullback_toFunctor (s : Section C) :
    (pullback G s).toFunctor = liftFunctor G (G ⋙ s.toFunctor)
      (comp_toFunctor_comp_forget G s) := (rfl)

/-- A restricted section recovers the original one after applying the base functor. -/
@[simp]
theorem pullback_comp_pre (s : Section C) :
    (pullback G s).toFunctor ⋙ pre C G = G ⋙ s.toFunctor :=
  liftFunctor_comp_pre G _ (comp_toFunctor_comp_forget G s)

/-- Restriction along the identity leaves a section unchanged. -/
@[simp]
theorem pullback_id (s : Section C) : pullback (𝟭 D) s = s := by
  apply Functor.Fiber.fiberInclusion_obj_inj
  simpa only [pre_id, Functor.comp_id, Functor.id_comp] using pullback_comp_pre (𝟭 D) s

/-- Successive changes of base give the section restricted along the composite. -/
@[simp]
theorem pullback_comp {B : Type*} [Category* B] (H : B ⥤ E) (s : Section C) :
    pullback (H ⋙ G) s = pullback H (pullback G s) := by
  apply Subtype.ext
  suffices h : (pullback (H ⋙ G) s).toFunctor = (pullback H (pullback G s)).toFunctor by
    convert h using 1 <;> rfl
  rw [pullback_toFunctor (H ⋙ G) s, pullback_toFunctor H (pullback G s)]
  simp_rw [pullback_toFunctor G s]
  refine Functor.hext (fun b => ?_) (fun b b' f => ?_)
  · -- Compute the nested casts of fiber objects after identifying both base maps.
    simp [liftFunctor, liftObj]
  · simp only [Functor.comp_map, liftFunctor_map]
    exact heq_of_eq (liftHom_comp G H _ f _ _ _)

/-- Restriction of a vertical label to the new base. -/
def pullbackHom {s t : Section C} (α : s ⟶ t) : pullback G s ⟶ pullback G t :=
  homMk (liftNatTrans G
    (comp_toFunctor_comp_forget G s)
    (comp_toFunctor_comp_forget G t)
    (whiskerLeft G (hom α)) (by
      ext e
      -- Evaluate the whiskered section identities at G.obj e in the same base category.
      convert NatTrans.congr_app (whiskerRight_hom_forget α) (G.obj e) using 1
      · rfl
      · rfl
      · -- Reduce the Fiber.mk endpoints to compare the two equality components.
        erw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app, eqToHom_app,
          eqToHom_app, eqToHom_app]))
    (liftNatTrans_over G _ _ _ _)

/-- After applying `pre`, a restricted label is the original label at the reindexed object. -/
@[simp]
theorem pre_map_hom_pullbackHom {s t : Section C} (α : s ⟶ t) (e : E) :
    (pre C G).map ((hom (pullbackHom G α)).app e) =
      eqToHom (Functor.congr_obj (pullback_comp_pre G s) e) ≫ (hom α).app (G.obj e) ≫
        eqToHom (Functor.congr_obj (pullback_comp_pre G t) e).symm := by
  dsimp only [pullbackHom]
  -- Reduce Fiber.mk so hom_homMk sees the endpoints of the lifted transformation.
  erw [hom_homMk]
  exact pre_map_liftNatTrans_app G _ _ _ _ e

/-- A restricted label is vertical over the new base object. -/
@[simp]
theorem hom_pullbackHom_app_base {s t : Section C} (α : s ⟶ t) (e : E) :
    ((hom (pullbackHom G α)).app e).base = 𝟙 e := by
  dsimp only [pullbackHom]
  -- Reduce Fiber.mk so hom_homMk sees the endpoints of the lifted transformation.
  erw [hom_homMk]
  dsimp only [liftNatTrans]
  exact liftHom_base G _ _ _ _ _

/-- Restriction is a functor on sections and their vertical labels. -/
@[expose]
def pullbackFunctor : Section C ⥤ Section (G ⋙ C) where
  obj s := pullback G s
  map α := pullbackHom G α
  map_id s := by
    apply hom_ext
    intro e
    apply hom_ext_of_pre G
    · simp only [hom_pullbackHom_app_base, hom_id, NatTrans.id_app, id_base]
      -- The lifted section object has new base e by its defining liftObj.
      rfl
    · simp
  map_comp α β := by
    apply hom_ext
    intro e
    apply hom_ext_of_pre G
    · simp only [hom_comp, NatTrans.comp_app, comp_base,
        hom_pullbackHom_app_base]
      exact (Category.id_comp (𝟙 e)).symm
    · simp [Category.assoc]

@[simp]
theorem pullbackFunctor_obj (s : Section C) :
    (pullbackFunctor G).obj s = pullback G s := (rfl)

@[simp]
theorem pullbackFunctor_map {s t : Section C} (α : s ⟶ t) :
    (pullbackFunctor G).map α = pullbackHom G α := (rfl)

variable {V : Type*} [Category* V] (A : Grothendieck C ⥤ V)

/-- The reindexed coefficient diagram is canonically isomorphic to the pulled-back one. -/
def coefficientPullbackIso (s : Section C) :
    G ⋙ (s.toFunctor ⋙ A) ≅ (pullback G s).toFunctor ⋙ pre C G ⋙ A :=
  (Functor.associator G s.toFunctor A).symm ≪≫
    eqToIso (congrArg (fun F => F ⋙ A) (pullback_comp_pre G s).symm) ≪≫
      Functor.associator (pullback G s).toFunctor (pre C G) A

@[simp]
theorem coefficientPullbackIso_hom_app (s : Section C) (e : E) :
    (coefficientPullbackIso G A s).hom.app e =
      A.map (eqToHom (Functor.congr_obj (pullback_comp_pre G s) e).symm) := by
  simp [coefficientPullbackIso, eqToHom_map, eqToHom_app]

@[simp]
theorem coefficientPullbackIso_inv_app (s : Section C) (e : E) :
    (coefficientPullbackIso G A s).inv.app e =
      A.map (eqToHom (Functor.congr_obj (pullback_comp_pre G s) e)) := by
  simp [coefficientPullbackIso, eqToHom_map, eqToHom_app]

/-- The identification of reindexed coefficient diagrams is natural in vertical labels. -/
@[reassoc]
theorem coefficientPullbackIso_naturality {s t : Section C} (α : s ⟶ t) :
    whiskerLeft G (whiskerRight (hom α) A) ≫ (coefficientPullbackIso G A t).hom =
      (coefficientPullbackIso G A s).hom ≫
        whiskerRight (hom (pullbackHom G α)) (pre C G ⋙ A) := by
  ext e
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    coefficientPullbackIso_hom_app, Functor.comp_map]
  rw [pre_map_hom_pullbackHom, Functor.map_comp, Functor.map_comp]
  simp [← Functor.map_comp]

/-- Restriction of coefficients to a new base on the actual completed coefficient objects. -/
noncomputable def coefficientRestriction (s : Section C)
    [Limits.HasLimit (s.toFunctor ⋙ A)]
    [Limits.HasLimit ((pullback G s).toFunctor ⋙ pre C G ⋙ A)] :
    Limits.limit (s.toFunctor ⋙ A) ⟶
      Limits.limit ((pullback G s).toFunctor ⋙ pre C G ⋙ A) :=
  (coefficientPullbackIso G A s).hom.reindexLimitMap

/-- Restriction evaluates the old matching family at the reindexed object. -/
@[reassoc (attr := simp)]
theorem coefficientRestriction_π (s : Section C)
    [Limits.HasLimit (s.toFunctor ⋙ A)]
    [Limits.HasLimit ((pullback G s).toFunctor ⋙ pre C G ⋙ A)] (e : E) :
    coefficientRestriction G A s ≫
      Limits.limit.π ((pullback G s).toFunctor ⋙ pre C G ⋙ A) e =
        Limits.limit.π (s.toFunctor ⋙ A) (G.obj e) ≫
          A.map (eqToHom (Functor.congr_obj (pullback_comp_pre G s) e).symm) := by
  rw [coefficientRestriction, NatTrans.reindexLimitMap_π]
  rw [coefficientPullbackIso_hom_app]

/-- Restriction intertwines the coefficient maps represented by vertical labels. -/
@[reassoc]
theorem coefficientRestriction_naturality {s t : Section C} (α : s ⟶ t)
    [Limits.HasLimit (s.toFunctor ⋙ A)] [Limits.HasLimit (t.toFunctor ⋙ A)]
    [Limits.HasLimit ((pullback G s).toFunctor ⋙ pre C G ⋙ A)]
    [Limits.HasLimit ((pullback G t).toFunctor ⋙ pre C G ⋙ A)] :
    Limits.limMap (whiskerRight (hom α) A) ≫ coefficientRestriction G A t =
      coefficientRestriction G A s ≫
        Limits.limMap (whiskerRight (hom (pullbackHom G α)) (pre C G ⋙ A)) := by
  apply Limits.limit.hom_ext
  intro e
  simp only [Category.assoc, coefficientRestriction_π, Limits.limMap_π, Limits.limMap_π_assoc,
    whiskerRight_app, Functor.comp_map, coefficientRestriction_π_assoc]
  simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    coefficientPullbackIso_hom_app, Functor.comp_map, Category.assoc] using
    congrArg (Limits.limit.π (s.toFunctor ⋙ A) (G.obj e) ≫ ·)
      (NatTrans.congr_app (coefficientPullbackIso_naturality G A α) e)

/-- An initial change of base identifies the completed coefficient objects. -/
instance isIso_coefficientRestriction (s : Section C) [G.Initial]
    [Limits.HasLimit (s.toFunctor ⋙ A)]
    [Limits.HasLimit ((pullback G s).toFunctor ⋙ pre C G ⋙ A)] :
    IsIso (coefficientRestriction G A s) :=
  NatTrans.isIso_reindexLimitMap _

end Section
end TauCeti.CategoryTheory.Grothendieck
