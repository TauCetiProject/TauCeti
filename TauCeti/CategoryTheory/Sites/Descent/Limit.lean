/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.Limit
public import TauCeti.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.CategoryTheory.Sites.Descent.StrongTrans

/-!
# Descent for pseudo-limits

The pseudo-limit `TauCeti.Stack.limit D` is computed fiberwise. Descent of morphisms can
therefore be checked on its projections: morphisms descend in each factor, and faithfulness
of descent in the target of each transition checks their compatibility. Objects are glued by
descending their components and transition isomorphisms; faithfulness also checks the identity
and composition laws of those transitions. Thus pseudo-limits of stacks are stacks.

This extends the componentwise descent constructions for `TauCeti.Stack.pi` and
`TauCeti.Stack.twoFiberProduct` to diagrams of arbitrary shape, using the fibrewise pseudo-limit
and its universal property from `TauCeti.CategoryTheory.Bicategory.Functor.Limit`. No pullbacks
or smallness hypotheses on the site are needed. The universe of the index category must fit
within the fibre hom universe; here both fibre universes include the index universe `w`.
The descent projection is
`StrongTrans.mapDescentData` applied to a limit projection. The comparison
`StrongTrans.toDescentDataCompMapDescentDataIso` identifies canonical descent data under these
projections and glues the transition isomorphisms. Taking the index category in universe `u`,
the site to be `Over S` for `S : Scheme.{u}`, and values in `Cat.{u, u + 1}` gives the big-site
case.

## Main declarations

* `TauCeti.Stack.limit.fullyFaithfulToDescentData`: descent of morphisms for a pseudo-limit.
* `TauCeti.Stack.limit.descentDataTransitionIso`: transitions between projected descent data.
* `TauCeti.Stack.limit.essSurj_toDescentData`: effectivity of descent for a pseudo-limit.
* `TauCeti.Stack.limit.isPrestack`, `TauCeti.Stack.limit.isStack`: pseudo-limits of prestacks,
  respectively stacks, are prestacks, respectively stacks.
-/

open CategoryTheory Bicategory Opposite
open scoped Pseudofunctor.StrongTrans

universe t w z v' v u

public section

namespace TauCeti.Stack.limit

open Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {I : Type w} [SmallCategory I]
  {D : Pseudofunctor (LocallyDiscrete I)
    (Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max w v', max w v' z})}

@[simp]
lemma pullHom_hom ⦃X₁ X₂ : C⦄ ⦃M₁ : (limit D).obj (.mk (op X₁))⦄
    ⦃M₂ : (limit D).obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((limit D).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((limit D).map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (i : I) :
    (pullHom φ g gf₁ gf₂ hgf₁ hgf₂).hom i =
      pullHom (F := D.obj (.mk i)) (φ.hom i) g gf₁ gf₂ hgf₁ hgf₂ := by
  simp only [pullHom, comp_hom', map_map_hom, mapComp'_hom_app_hom,
    mapComp'_inv_app_hom]
  -- The compositions have definitionally equal implicit objects.
  rfl

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ a, X a ⟶ S)

@[simp]
lemma mapDescentData_π_obj_hom (i : I) (d : (limit D).DescentData f) ⦃Y : C⦄ (q : Y ⟶ S)
    ⦃a b : ι⦄ (f₁ : Y ⟶ X a) (f₂ : Y ⟶ X b)
    (hf₁ : f₁ ≫ f a = q) (hf₂ : f₂ ≫ f b = q) :
    (((π D i).mapDescentData f).obj d).hom q f₁ f₂ hf₁ hf₂ = (d.hom q f₁ f₂ hf₁ hf₂).hom i := by
  simp only [StrongTrans.mapPullHom_def, π_naturality_inv_app,
    π_naturality_hom_app, π_app_toFunctor]
  -- The identity components are between definitionally equal projected objects.
  erw [Category.id_comp, Category.comp_id]
  rfl

@[simp]
lemma toDescentData_obj_hom_hom (M : (limit D).obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S)
    ⦃a b : ι⦄ (f₁ : Y ⟶ X a) (f₂ : Y ⟶ X b)
    (hf₁ : f₁ ≫ f a = q) (hf₂ : f₂ ≫ f b = q) (i : I) :
    ((((limit D).toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂).hom i =
      (((D.obj (.mk i)).toDescentData f).obj (M.obj i)).hom q f₁ f₂ hf₁ hf₂ := by
  simp only [DescentData.toDescentData_obj_hom, compIso_inv, compIso_hom,
    comp_hom', mapComp'_inv_app_hom, mapComp'_hom_app_hom]
  rfl

/-- The projection of a morphism between canonical descent data. -/
private def homπ {M N : (limit D).obj (.mk (op S))}
    (Φ : ((limit D).toDescentData f).obj M ⟶ ((limit D).toDescentData f).obj N) (i : I) :
    ((D.obj (.mk i)).toDescentData f).obj (M.obj i) ⟶
      ((D.obj (.mk i)).toDescentData f).obj (N.obj i) :=
  ((π D i).toDescentDataCompMapDescentDataIso f).inv.app M ≫
    ((π D i).mapDescentData f).map Φ ≫
      ((π D i).toDescentDataCompMapDescentDataIso f).hom.app N

private lemma homπ_hom {M N : (limit D).obj (.mk (op S))}
    (Φ : ((limit D).toDescentData f).obj M ⟶ ((limit D).toDescentData f).obj N)
    (i : I) (a : ι) : (homπ f Φ i).hom a = (Φ.hom a).hom i := by
  -- Give the comparison components their factor-category endpoints before cancellation.
  have h : (homπ f Φ i).hom a =
      ((π D i).naturality (f a).op.toLoc).inv.toNatTrans.app M ≫
        (Φ.hom a).hom i ≫
          ((π D i).naturality (f a).op.toLoc).hom.toNatTrans.app N := by
    dsimp only [homπ]
    erw [DescentData.comp_hom, DescentData.comp_hom,
      StrongTrans.toDescentDataCompMapDescentDataIso_inv_app_hom,
      StrongTrans.toDescentDataCompMapDescentDataIso_hom_app_hom,
      StrongTrans.mapDescentData_map_hom]
    simp only [π_app_toFunctor]
    exact congrArg (fun m ↦
      ((π D i).naturality (f a).op.toLoc).inv.toNatTrans.app M ≫
        m ≫ ((π D i).naturality (f a).op.toLoc).hom.toNatTrans.app N)
      (Fiber.eval_map D (op (X a)) i (Φ.hom a))
  simp only [π_naturality_inv_app, π_naturality_hom_app] at h
  have hc : (𝟙 _ ≫ (Φ.hom a).hom i ≫ 𝟙 _) = (Φ.hom a).hom i := by simp
  exact h.trans hc

private lemma homπ_toDescentData_map {M N : (limit D).obj (.mk (op S))} (φ : M ⟶ N)
    (i : I) :
    homπ f (((limit D).toDescentData f).map φ) i =
      ((D.obj (.mk i)).toDescentData f).map (φ.hom i) := by
  exact NatIso.naturality_1 ((π D i).toDescentDataCompMapDescentDataIso f) φ

variable {f}

/-- If descent of morphisms holds in each factor along a family, it holds in the pseudo-limit
along that family. -/
noncomputable def fullyFaithfulToDescentData
    (hD : ∀ i, ((D.obj (.mk i)).toDescentData f).FullyFaithful) :
    ((limit D).toDescentData f).FullyFaithful where
  preimage {M N} Φ :=
    { hom i := (hD i).preimage (homπ f Φ i)
      comm {i j} g := (hD j).map_injective (by
        ext a
        apply (map_transition_comp_iso_hom_iff (f a).op g _ _).mpr
        simp only [DescentData.toDescentData_preimage_hom, homπ_hom]
        exact (Φ.hom a).comm g) }
  map_preimage {M N} Φ := by
    apply DescentData.hom_ext
    intro a
    apply Fiber.hom_ext
    intro i
    exact (DescentData.toDescentData_preimage_hom (hD i) (homπ f Φ i) a).trans
      (homπ_hom f Φ i a)
  preimage_map {M N} φ := by
    apply Fiber.hom_ext
    intro i
    simpa only [homπ_toDescentData_map] using (hD i).preimage_map (φ.hom i)

section effectivity

variable (f) (d : (limit D).DescentData f)

/-- The transitions in the pseudo-limit induce a natural isomorphism between the projection
to the source factor followed by the transition and the projection to the target factor. -/
def descentDataTransitionIso {i j : I} (g : i ⟶ j) :
    (π D i).mapDescentData f ⋙ (D.map g.toLoc).mapDescentData f ≅
      (π D j).mapDescentData f :=
  ((π D i).mapDescentDataComp f (D.map g.toLoc)).symm ≪≫
    StrongTrans.mapDescentDataIso f (πCompMap D g)

/-- The transition on projected descent data is the corresponding transition in each fibre. -/
@[simp]
lemma descentDataTransitionIso_hom_app_hom {i j : I} (g : i ⟶ j) (a : ι) :
    ((descentDataTransitionIso f g).hom.app d).hom a = ((d.obj a).iso g).hom := by
  simp only [descentDataTransitionIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    DescentData.comp_hom, StrongTrans.mapDescentDataComp_inv_app_hom,
    StrongTrans.mapDescentDataIso_hom_app_hom, πCompMap_hom_as_app]
  exact Category.id_comp _

/-- The inverse transition on projected descent data is the inverse transition in each fibre. -/
@[simp]
lemma descentDataTransitionIso_inv_app_hom {i j : I} (g : i ⟶ j) (a : ι) :
    ((descentDataTransitionIso f g).inv.app d).hom a = ((d.obj a).iso g).inv := by
  simp only [descentDataTransitionIso, Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
    DescentData.comp_hom, StrongTrans.mapDescentDataComp_hom_app_hom,
    StrongTrans.mapDescentDataIso_inv_app_hom, πCompMap_inv_as_app]
  exact Category.comp_id _

variable (M : ∀ i, (D.obj (.mk i)).obj (.mk (op S)))
  (e : ∀ i, ((D.obj (.mk i)).toDescentData f).obj (M i) ≅ ((π D i).mapDescentData f).obj d)
  (hD : ∀ i, ((D.obj (.mk i)).toDescentData f).FullyFaithful)

/-- The transition isomorphisms on chosen descents of the components of a descent datum. -/
private noncomputable def glueTransitionIso {i j : I} (g : i ⟶ j) :
    (transition D g (op S)).obj (M i) ≅ M j :=
  (hD j).preimageIso
    ((((D.map g.toLoc).toDescentDataCompMapDescentDataIso f).app (M i)).symm ≪≫
      ((D.map g.toLoc).mapDescentData f).mapIso (e i) ≪≫
        (descentDataTransitionIso f g).app d ≪≫ (e j).symm)

private lemma map_glueTransitionIso_hom {i j : I} (g : i ⟶ j) (a : ι) :
    ((D.obj (.mk j)).map (f a).op.toLoc).toFunctor.map
        (glueTransitionIso f d M e hD g).hom =
      ((D.map g.toLoc).naturality (f a).op.toLoc).inv.toNatTrans.app (M i) ≫
        (transition D g (op (X a))).map ((e i).hom.hom a) ≫
          ((d.obj a).iso g).hom ≫ (e j).inv.hom a := by
  have h := DescentData.toDescentData_preimage_hom (hD j)
    ((((D.map g.toLoc).toDescentDataCompMapDescentDataIso f).app (M i)).inv ≫
      ((D.map g.toLoc).mapDescentData f).map (e i).hom ≫
        ((descentDataTransitionIso f g).app d).hom ≫ (e j).inv) a
  simp only [DescentData.comp_hom, Iso.app_inv,
    StrongTrans.toDescentDataCompMapDescentDataIso_inv_app_hom,
    Iso.app_hom, descentDataTransitionIso_hom_app_hom] at h
  have hm : (((D.map g.toLoc).mapDescentData f).map (e i).hom).hom a =
      (transition D g (op (X a))).map ((e i).hom.hom a) :=
    StrongTrans.mapDescentData_map_hom _ _ _ _
  exact h.trans (congrArg (fun m ↦
    ((D.map g.toLoc).naturality (f a).op.toLoc).inv.toNatTrans.app (M i) ≫
      m ≫ ((d.obj a).iso g).hom ≫ (e j).inv.hom a) hm)

private lemma glueTransitionIso_comm {i j : I} (g : i ⟶ j) (a : ι) :
    (transition D g (op (X a))).map ((e i).hom.hom a) ≫ ((d.obj a).iso g).hom =
      ((D.map g.toLoc).naturality (f a).op.toLoc).hom.toNatTrans.app (M i) ≫
        ((D.obj (.mk j)).map (f a).op.toLoc).toFunctor.map
          (glueTransitionIso f d M e hD g).hom ≫ (e j).hom.hom a := by
  rw [map_glueTransitionIso_hom]
  let ea (i : I) :
      ((D.obj (.mk i)).map (f a).op.toLoc).toFunctor.obj (M i) ≅ (d.obj a).obj i :=
    DescentData.isoApp (e i) a
  let n := (D.map g.toLoc).naturalityObjIso (f a).op.toLoc (M i)
  have h : n.hom ≫ (n.inv ≫ (transition D g (op (X a))).map (ea i).hom ≫
      ((d.obj a).iso g).hom ≫ (ea j).inv) ≫ (ea j).hom =
        (transition D g (op (X a))).map (ea i).hom ≫ ((d.obj a).iso g).hom := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  -- Explicit component types let simplification cancel the two isomorphisms.
  dsimp only [n, ea] at h
  simp only [StrongTrans.naturalityObjIso_hom, StrongTrans.naturalityObjIso_inv,
    DescentData.isoApp_hom, DescentData.isoApp_inv] at h
  exact h.symm

include hD in
/-- Equality can be checked after restriction and transport through the chosen local descents. -/
private lemma glue_hom_ext {i j : I} (g : i ⟶ j)
    {φ ψ : (transition D g (op S)).obj (M i) ⟶ M j}
    (h : ∀ a, ((D.map g.toLoc).naturality (f a).op.toLoc).hom.toNatTrans.app (M i) ≫
      ((D.obj (.mk j)).map (f a).op.toLoc).toFunctor.map φ ≫ (e j).hom.hom a =
        ((D.map g.toLoc).naturality (f a).op.toLoc).hom.toNatTrans.app (M i) ≫
          ((D.obj (.mk j)).map (f a).op.toLoc).toFunctor.map ψ ≫ (e j).hom.hom a) :
    φ = ψ := by
  apply (hD j).map_injective
  apply DescentData.hom_ext
  intro a
  apply (cancel_mono (DescentData.isoApp (e j) a).hom).mp
  apply (cancel_epi
    (((D.map g.toLoc).naturality (f a).op.toLoc).hom.toNatTrans.app (M i))).mp
  simp only [toDescentData_map_hom, DescentData.isoApp_hom]
  exact h a

private lemma glueTransitionIso_id (i : I) :
    (glueTransitionIso f d M e hD (𝟙 i)).hom = (transitionIdIso D i (op S) (M i)).hom := by
  apply glue_hom_ext f d M e hD (𝟙 i)
  intro a
  let da : Fiber D (op (X a)) := d.obj a
  let ea : ((D.obj (.mk i)).map (f a).op.toLoc).toFunctor.obj (M i) ⟶
      da.obj i := (e i).hom.hom a
  -- Give the local components their factor-category types: rewriting cannot see through
  -- the implicit objects of the canonical descent data and the limit projection.
  change _ ≫ _ ≫ ea = _ ≫ _ ≫ ea
  refine (glueTransitionIso_comm f d M e hD (𝟙 i) a).symm.trans ?_
  calc
    (transition D (𝟙 i) (op (X a))).map ea ≫ (da.iso (𝟙 i)).hom =
        (transitionIdIso D i (op (X a)) _).hom ≫ ea := by
      rw [da.iso_id, transitionIdIso_hom_naturality]
    _ = _ := by simp only [transitionIdIso_naturality, Category.assoc]

private lemma glueTransitionIso_comp {i j k : I} (g : i ⟶ j) (h : j ⟶ k) :
    (glueTransitionIso f d M e hD (g ≫ h)).hom =
      (transitionCompIso D g h (op S) (M i)).hom ≫
        (transition D h (op S)).map (glueTransitionIso f d M e hD g).hom ≫
          (glueTransitionIso f d M e hD h).hom := by
  apply glue_hom_ext f d M e hD (g ≫ h)
  intro a
  let da : Fiber D (op (X a)) := d.obj a
  let ea (i : I) : ((D.obj (.mk i)).map (f a).op.toLoc).toFunctor.obj (M i) ⟶
      da.obj i := (e i).hom.hom a
  -- Normalize the same implicit component objects as in the unit check.
  change _ ≫ _ ≫ ea k = _ ≫ _ ≫ ea k
  have hcomm {i j : I} (g : i ⟶ j) :
      (transition D g (op (X a))).map (ea i) ≫ (da.iso g).hom =
        ((D.map g.toLoc).naturality (f a).op.toLoc).hom.toNatTrans.app (M i) ≫
          ((D.obj (.mk j)).map (f a).op.toLoc).toFunctor.map
            (glueTransitionIso f d M e hD g).hom ≫ ea j :=
    glueTransitionIso_comm f d M e hD g a
  refine (glueTransitionIso_comm f d M e hD (g ≫ h) a).symm.trans ?_
  calc
    (transition D (g ≫ h) (op (X a))).map (ea i) ≫ (da.iso (g ≫ h)).hom =
        (transitionCompIso D g h (op (X a)) _).hom ≫
          (transition D h (op (X a))).map
            ((transition D g (op (X a))).map (ea i) ≫ (da.iso g).hom) ≫
              (da.iso h).hom := by
      rw [da.iso_comp]
      have hc := transitionCompIso_hom_naturality_assoc D g h (op (X a)) (ea i)
        ((transition D h (op (X a))).map (da.iso g).hom ≫ (da.iso h).hom)
      simp only [Functor.map_comp, Category.assoc]
      exact hc
    _ = (transitionCompIso D g h (op (X a)) _).hom ≫
        (transition D h (op (X a))).map
          (((D.map g.toLoc).naturality (f a).op.toLoc).hom.toNatTrans.app (M i)) ≫
            ((D.map h.toLoc).naturality (f a).op.toLoc).hom.toNatTrans.app
              ((transition D g (op S)).obj (M i)) ≫
                ((D.obj (.mk k)).map (f a).op.toLoc).toFunctor.map
                  ((transition D h (op S)).map (glueTransitionIso f d M e hD g).hom) ≫
                    ((D.obj (.mk k)).map (f a).op.toLoc).toFunctor.map
                      (glueTransitionIso f d M e hD h).hom ≫ ea k := by
      rw [hcomm g]
      simp only [Functor.map_comp, Category.assoc]
      rw [hcomm h]
      have hn := StrongTrans.naturalityObjIso_hom_naturality_assoc (D.map h.toLoc)
        (f a).op.toLoc (glueTransitionIso f d M e hD g).hom
        (((D.obj (.mk k)).map (f a).op.toLoc).toFunctor.map
          (glueTransitionIso f d M e hD h).hom ≫ ea k)
      simp only [StrongTrans.naturalityObjIso_hom] at hn
      rw [hn]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc, transitionCompIso_naturality_assoc]

private noncomputable def glueObj : (limit D).obj (.mk (op S)) where
  obj := M
  iso g := glueTransitionIso f d M e hD g
  iso_id i := glueTransitionIso_id f d M e hD i
  iso_comp g h := glueTransitionIso_comp f d M e hD g h

private noncomputable def glueIso :
    ((limit D).toDescentData f).obj (glueObj f d M e hD) ≅ d := by
  -- Use the explicit fibre carriers so component rewriting does not unfold `limit`.
  let L : Fiber D (op S) := glueObj f d M e hD
  let da (a : ι) : Fiber D (op (X a)) := d.obj a
  let ea (a : ι) (i : I) : ((map D (f a).op).obj L).obj i ≅ (da a).obj i :=
    DescentData.isoApp (e i) a
  have hea (a : ι) (i : I) : (ea a i).hom = (e i).hom.hom a :=
    DescentData.isoApp_hom _ _
  let E (a : ι) : (map D (f a).op).obj L ≅ da a :=
    Fiber.isoMk (ea a) (fun i j g ↦ by
      have h : (transition D g (op (X a))).map ((e i).hom.hom a) ≫
          ((d.obj a).iso g).hom =
          (Fiber.iso (((limit D).map (f a).op.toLoc).toFunctor.obj
            (glueObj f d M e hD)) g).hom ≫ (e j).hom.hom a := by
        rw [map_obj_iso_hom]
        exact (glueTransitionIso_comm f d M e hD g a).trans (Category.assoc _ _ _).symm
      simp only [hea]
      exact h)
  have hE (a : ι) (i : I) : (E a).hom.hom i = (e i).hom.hom a := by
    dsimp only [E]
    rw [Fiber.isoMk_hom_hom, hea]
  refine DescentData.isoMk E ?_
  intro Y q a b f₁ f₂ hf₁ hf₂
  apply Fiber.hom_ext
  intro i
  have h := (e i).hom.comm q f₁ f₂ hf₁ hf₂
  rw [mapDescentData_π_obj_hom] at h
  simp only [comp_hom', map_map_hom, hE, toDescentData_obj_hom_hom]
  exact h

end effectivity

/-- If the descent functors of the factors are fully faithful and essentially surjective along
a family, descent in the pseudo-limit along that family is effective. -/
lemma essSurj_toDescentData [∀ i, ((D.obj (.mk i)).toDescentData f).EssSurj]
    (hD : ∀ i, ((D.obj (.mk i)).toDescentData f).FullyFaithful) :
    ((limit D).toDescentData f).EssSurj where
  mem_essImage d := by
    let M i := ((D.obj (.mk i)).toDescentData f).objPreimage (((π D i).mapDescentData f).obj d)
    let e i := ((D.obj (.mk i)).toDescentData f).objObjPreimageIso
      (((π D i).mapDescentData f).obj d)
    exact ⟨glueObj f d M e hD, ⟨glueIso f d M e hD⟩⟩

variable {J : GrothendieckTopology C}

/-- Pseudo-limits of prestacks are prestacks. -/
instance isPrestack [∀ i, (D.obj (.mk i)).IsPrestack J] : (limit D).IsPrestack J :=
  IsPrestack.of_isPrestackFor fun _ R hR ↦
    ⟨⟨fullyFaithfulToDescentData fun i ↦ ((D.obj (.mk i)).isPrestackFor' R hR).fullyFaithful⟩⟩

/-- Pseudo-limits of stacks are stacks. -/
instance isStack [∀ i, (D.obj (.mk i)).IsStack J] : (limit D).IsStack J where
  essSurj_of_sieve R hR :=
    have := fun i ↦ IsStack.essSurj_of_sieve (D.obj (.mk i)) R hR
    essSurj_toDescentData fun i ↦ ((D.obj (.mk i)).isPrestackFor' R hR).fullyFaithful

end TauCeti.Stack.limit
