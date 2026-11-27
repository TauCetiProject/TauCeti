/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.Subgroup.Center
public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.ComponentCenter
public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.Constant

/-!
# Central sections of a connected constant fixture

Let `G` be a group and `I` a type. The groupoid `Codiscrete I × SingleObj G` is connected: its
objects are the `(i, ⋆)`, any two of them are isomorphic (`ConnectedBandFixtures.connectedIso`),
and the automorphisms of each are the elements of `G` (`ConnectedBandFixtures.connectedAut`). A
central element `a` of `G` gives the central endomorphism of the identity functor acting by `a` on
every object (`ConnectedBandFixtures.connectedCenter`), a unit of the categorical centre
(`ConnectedBandFixtures.connectedCenterUnit`). When `I` is nonempty, every centre unit arises from
a unique central element: the units of the centre are the centre of `G`
(`ConnectedBandFixtures.connectedCenterEquiv`). The chosen element of `I` is needed: for empty `I`
the categorical centre is trivial.

So the central sections of the constant pseudofunctor with this fibre, over any object `U` of any
category, are the centre of `G` (`ConnectedBandFixtures.connectedSectionsEquiv`). Evaluation of
central sections at an object is injective (`ConnectedBandFixtures.connected_eval_injective`), with
image the automorphisms whose group component is central
(`ConnectedBandFixtures.connected_eval_image`); it is surjective exactly when the centre of `G` is
all of `G` (`ConnectedBandFixtures.connected_eval_surjective_iff`).
For `G = S₃` evaluation is injective but not surjective, the nonabelian obstruction to banding a
connected gerbe. No topology or terminal object is used.

## Main definitions

In the namespace `CategoryTheory.Pseudofunctor.ConnectedBandFixtures`:

* `connectedCenter a`, `connectedCenterUnit a`: the central endomorphism `(𝟙, a)` of a central `a`.
* `connectedCenterEquiv i : Subgroup.center G ≃* (CatCenter (Codiscrete I × SingleObj G))ˣ`.
* `connectedSectionsEquiv C i U`: the central sections of the constant pseudofunctor over `U`.
* `connectedAut x g`, `connectedIso x y`: the automorphism `(𝟙, g)` and the isomorphism `(⋆, 1)`.

## Main results

* `connected_eval_injective`, `connected_eval_image`, `connected_eval_surjective_iff`.

## References

* [The Stacks Project, Definition 8.11.1 (06NZ)](https://stacks.math.columbia.edu/tag/06NZ)
* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite

namespace CategoryTheory.Pseudofunctor.ConnectedBandFixtures

variable {I : Type u'} {G : Type v'} [Group G]

/-- The **centre of a central element** `a` of `G`: the natural endomorphism of the identity of
`Codiscrete I × SingleObj G` with component `(𝟙, a)` at every object. It is natural because `a`
commutes with every element of `G`. -/
def connectedCenter (a : Subgroup.center G) : CatCenter (Codiscrete I × SingleObj G) :=
  .of
    { app x := (𝟙 x.1, ((a : G) : SingleObj.star G ⟶ SingleObj.star G))
      naturality x y f := by
        refine Prod.hom_ext (Subsingleton.elim _ _) ?_
        simp only [Functor.id_obj, Functor.id_map, prod_comp_snd, SingleObj.comp_as_mul]
        exact (Subgroup.mem_center_iff.1 a.property _).symm }

/-- The component of the centre of a central element at every object is `(𝟙, a)`. -/
theorem connectedCenter_app (a : Subgroup.center G) (x : Codiscrete I × SingleObj G) :
    (connectedCenter a).app x = (𝟙 x.1, ((a : G) : SingleObj.star G ⟶ SingleObj.star G)) :=
  (rfl)

/-- The group component of the centre of a central element at every object is `a`. -/
@[simp]
theorem connectedCenter_app_snd (a : Subgroup.center G) (x : Codiscrete I × SingleObj G) :
    ((connectedCenter a).app x).2 = ((a : G) : SingleObj.star G ⟶ SingleObj.star G) :=
  (rfl)

/-- The centre of a product of central elements is the product of their centres. -/
@[simp]
theorem connectedCenter_mul (a b : Subgroup.center G) :
    connectedCenter (I := I) (a * b) = connectedCenter a * connectedCenter b :=
  BandFixtures.catCenter_ext_prod_singleObj fun x ↦ by
    simp only [connectedCenter_app_snd, CatCenter.mul_app', prod_comp_snd, SingleObj.comp_as_mul,
      Subgroup.coe_mul]

/-- The centre of the identity element is the identity. -/
@[simp]
theorem connectedCenter_one : connectedCenter (I := I) (1 : Subgroup.center G) = 1 :=
  BandFixtures.catCenter_ext_prod_singleObj fun _ ↦ by simp [CatCenter.app_one, SingleObj.id_as_one]

/-- The **centre unit of a central element** `a`, with inverse the centre of `a⁻¹`. -/
def connectedCenterUnit (a : Subgroup.center G) : (CatCenter (Codiscrete I × SingleObj G))ˣ :=
  MonoidHom.toHomUnits
    { toFun := connectedCenter, map_one' := connectedCenter_one,
      map_mul' := connectedCenter_mul } a

@[simp]
theorem val_connectedCenterUnit (a : Subgroup.center G) :
    (connectedCenterUnit (I := I) a).val = connectedCenter a :=
  (rfl)

/-- The inverse value of the centre unit of `a` is the centre of `a⁻¹`. -/
theorem val_inv_connectedCenterUnit (a : Subgroup.center G) :
    (connectedCenterUnit (I := I) a)⁻¹.val = connectedCenter a⁻¹ :=
  (rfl)

/-- The centre unit of a product of central elements is the product of their centre units. -/
@[simp]
theorem connectedCenterUnit_mul (a b : Subgroup.center G) :
    connectedCenterUnit (I := I) (a * b) = connectedCenterUnit a * connectedCenterUnit b :=
  Units.ext (connectedCenter_mul a b)

/-- The centre unit of the identity element is the identity. -/
@[simp]
theorem connectedCenterUnit_one : connectedCenterUnit (I := I) (1 : Subgroup.center G) = 1 :=
  Units.ext connectedCenter_one

/-- The inverse of the centre unit of `a` is the centre unit of `a⁻¹`. -/
@[simp]
theorem connectedCenterUnit_inv (a : Subgroup.center G) :
    (connectedCenterUnit (I := I) a)⁻¹ = connectedCenterUnit a⁻¹ :=
  Units.ext (val_inv_connectedCenterUnit a)

/-- The group component of a centre unit is central, by naturality along the automorphisms of
one object. -/
theorem app_snd_mem_center (z : (CatCenter (Codiscrete I × SingleObj G))ˣ)
    (x : Codiscrete I × SingleObj G) :
    ((z.val.app x).2 : G) ∈ Subgroup.center G := by
  refine Subgroup.mem_center_iff.2 fun g ↦ ?_
  have h := congrArg _root_.Prod.snd
    (CatCenter.naturality z.val (X := x) (Y := x) (𝟙 x.1, (g : SingleObj.star G ⟶ _)))
  simp only [prod_comp_snd, SingleObj.comp_as_mul] at h
  exact h.symm

/-- The group components of a centre unit at any two objects agree, by naturality along the
isomorphism between them. -/
theorem app_snd_eq (z : (CatCenter (Codiscrete I × SingleObj G))ˣ)
    (x y : Codiscrete I × SingleObj G) :
    ((z.val.app x).2 : G) = (z.val.app y).2 := by
  have h := congrArg _root_.Prod.snd (CatCenter.naturality z.val
    ((Codiscrete.iso x.1 y.1).hom, (1 : G)))
  simp only [prod_comp_snd, SingleObj.comp_as_mul, mul_one, one_mul] at h
  exact h.symm

variable (I G) in
/-- **The centre units of `Codiscrete I × SingleObj G` are the centre of `G`**, for nonempty
`I`. The inverse reads the group component of a centre unit at `(i, ⋆)`. -/
def connectedCenterEquiv (i : I) :
    Subgroup.center G ≃* (CatCenter (Codiscrete I × SingleObj G))ˣ where
  toFun := connectedCenterUnit
  invFun z := ⟨(z.val.app (⟨i⟩, SingleObj.star G)).2, app_snd_mem_center z _⟩
  left_inv _ := rfl
  right_inv z := Units.ext <| BandFixtures.catCenter_ext_prod_singleObj fun x ↦
    app_snd_eq z (⟨i⟩, SingleObj.star G) x
  map_mul' := connectedCenterUnit_mul

@[simp]
theorem connectedCenterEquiv_apply (i : I) (a : Subgroup.center G) :
    connectedCenterEquiv I G i a = connectedCenterUnit a :=
  (rfl)

/-- The inverse of `connectedCenterEquiv` reads the group component at `(i, ⋆)`. -/
@[simp]
theorem coe_connectedCenterEquiv_symm_apply (i : I)
    (z : (CatCenter (Codiscrete I × SingleObj G))ˣ) :
    (((connectedCenterEquiv I G i).symm z : Subgroup.center G) : G) =
      (z.val.app (⟨i⟩, SingleObj.star G)).2 :=
  (rfl)

/-! ### Automorphisms and isomorphisms of the fibre -/

/-- The automorphism `(𝟙, g)` of an object `x` of `Codiscrete I × SingleObj G`, with inverse
`(𝟙, g⁻¹)`, as a group homomorphism `G →* Aut x`: the automorphism `Units.toAut` of the unique
object of `SingleObj G`, carried to `x` by `Functor.mapAut` along `Prod.sectR x.1`. The product in
`Aut x` composes in the order of `Function.comp` and composition in `SingleObj G` multiplies in
the opposite order, so the two reversals cancel. -/
def connectedAut (x : Codiscrete I × SingleObj G) : G →* Aut x :=
  ((Prod.sectR x.1 (SingleObj G)).mapAut (SingleObj.star G)).comp
    ((Units.toAut G).toMonoidHom.comp (toUnits : G ≃* Gˣ).toMonoidHom)

/-- The forward arrow of `connectedAut x g` is `(𝟙, g)`. -/
@[simp]
theorem connectedAut_asIso_hom (x : Codiscrete I × SingleObj G) (g : G) :
    (connectedAut x g).asIso.hom = (𝟙 x.1, (g : SingleObj.star G ⟶ SingleObj.star G)) :=
  (rfl)

/-- The inverse arrow of `connectedAut x g` is `(𝟙, g⁻¹)`. -/
@[simp]
theorem connectedAut_asIso_inv (x : Codiscrete I × SingleObj G) (g : G) :
    (connectedAut x g).asIso.inv = (𝟙 x.1, (g⁻¹ : SingleObj.star G ⟶ SingleObj.star G)) :=
  (rfl)

/-- `connectedAut x` is injective: an automorphism determines its group component. -/
theorem connectedAut_injective (x : Codiscrete I × SingleObj G) :
    Function.Injective (connectedAut x) := fun _ _ h ↦
  congrArg (fun e : Aut x ↦ (e.asIso.hom.2 : G)) h

/-- The group component of `connectedAut x g` is `g`. -/
theorem connectedAut_asIso_hom_snd (x : Codiscrete I × SingleObj G) (g : G) :
    ((connectedAut x g).asIso.hom.2 : G) = g :=
  (rfl)

/-- Every automorphism of an object of `Codiscrete I × SingleObj G` is `connectedAut` of its
group component. -/
theorem connectedAut_snd_asIso_hom (x : Codiscrete I × SingleObj G) (e : Aut x) :
    connectedAut x (e.asIso.hom.2 : G) = e :=
  Aut.ext <| Iso.ext <| Prod.hom_ext (Subsingleton.elim _ _) rfl

/-- The isomorphism between two objects of `Codiscrete I × SingleObj G`: the codiscrete
isomorphism on the first factor and the identity of the unique object on the second. -/
def connectedIso (x y : Codiscrete I × SingleObj G) : x ≅ y :=
  (Codiscrete.iso x.1 y.1).prod (eqToIso (Subsingleton.elim (α := SingleObj G) x.2 y.2))

@[simp]
theorem connectedIso_hom_fst (x y : Codiscrete I × SingleObj G) :
    (connectedIso x y).hom.1 = (Codiscrete.iso x.1 y.1).hom :=
  (rfl)

theorem connectedIso_hom_snd (x y : Codiscrete I × SingleObj G) :
    (connectedIso x y).hom.2 = eqToHom (Subsingleton.elim (α := SingleObj G) x.2 y.2) :=
  (rfl)

/-- The group component of the isomorphism between two objects is the identity element. -/
@[simp]
theorem connectedIso_hom_snd_eq_one (x y : Codiscrete I × SingleObj G) :
    ((connectedIso x y).hom.2 : G) = 1 :=
  (rfl)

/-- The group component of the inverse of the isomorphism between two objects is the identity
element. -/
@[simp]
theorem connectedIso_inv_snd_eq_one (x y : Codiscrete I × SingleObj G) :
    ((connectedIso x y).inv.2 : G) = 1 :=
  (rfl)

/-! ### Central sections of the constant pseudofunctor -/

variable (C : Type u) [Category.{v} C]

/-- **The central sections of the connected constant fixture** over `U` are the centre of `G`:
`connectedCenterEquiv` followed by `BandFixtures.constantSectionsEquiv`. -/
def connectedSectionsEquiv (i : I) (U : C) :
    Subgroup.center G ≃*
      IntrinsicBandSections (constant C (Codiscrete I × SingleObj G)) U :=
  (connectedCenterEquiv I G i).trans (BandFixtures.constantSectionsEquiv C _ U)

variable {C}

/-- The section of a central element `a` has value the centre unit of `a` at every arrow. -/
@[simp]
theorem val_connectedSectionsEquiv (i : I) (U : C) (a : Subgroup.center G) {V : C}
    (f : V ⟶ U) :
    (connectedSectionsEquiv C i U a).val V f = connectedCenterUnit a := by
  rw [connectedSectionsEquiv, MulEquiv.trans_apply, BandFixtures.constantSectionsEquiv_apply,
    BandFixtures.val_constantSection, connectedCenterEquiv_apply]

/-- The central element of a section is the group component at `(i, ⋆)` of its value at the
identity arrow. -/
@[simp]
theorem coe_connectedSectionsEquiv_symm_apply (i : I) (U : C)
    (s : IntrinsicBandSections (constant C (Codiscrete I × SingleObj G)) U) :
    (((connectedSectionsEquiv C i U).symm s : Subgroup.center G) : G) =
      ((s.val U (𝟙 U)).val.app (⟨i⟩, SingleObj.star G)).2 := by
  rw [connectedSectionsEquiv, MulEquiv.symm_trans_apply,
    BandFixtures.constantSectionsEquiv_symm_apply]
  exact coe_connectedCenterEquiv_symm_apply i _

/-- Restriction along any arrow carries the section of `a` to the section of `a`. -/
@[simp]
theorem restrict_connectedSectionsEquiv (i : I) {U V : C} (f : V ⟶ U) (a : Subgroup.center G) :
    IntrinsicBandSections.restrict f (connectedSectionsEquiv C i U a) =
      connectedSectionsEquiv C i V a := by
  simp only [connectedSectionsEquiv, MulEquiv.trans_apply, BandFixtures.constantSectionsEquiv_apply,
    BandFixtures.restrict_constantSection]

/-- The evaluation of the section of `a` at any arrow and object is the automorphism `(𝟙, a)`. -/
@[simp]
theorem evaluation_connectedSectionsEquiv (i : I) {U V : C} (f : V ⟶ U)
    (x : Codiscrete I × SingleObj G) (a : Subgroup.center G) :
    IntrinsicBandSections.evaluation (F := constant C (Codiscrete I × SingleObj G)) f x
        (connectedSectionsEquiv C i U a) =
      connectedAut x (a : G) :=
  Aut.ext <| Iso.ext <| (IntrinsicBandSections.evaluation_asIso_hom f x _).trans (by
    rewrite [val_connectedSectionsEquiv i U a f, val_connectedCenterUnit]
    exact (connectedCenter_app a x).trans (connectedAut_asIso_hom x a).symm)

/-- **Evaluation is injective** on the central sections of the connected constant fixture, at
every object, for an arbitrary group `G`. -/
theorem connected_eval_injective (U : C) (x : Codiscrete I × SingleObj G) :
    Function.Injective
      (IntrinsicBandSections.evaluation (F := constant C (Codiscrete I × SingleObj G)) (𝟙 U)
        x) := by
  intro s t hst
  obtain ⟨a, rfl⟩ := (connectedSectionsEquiv C x.1.as U).surjective s
  obtain ⟨b, rfl⟩ := (connectedSectionsEquiv C x.1.as U).surjective t
  rw [evaluation_connectedSectionsEquiv, evaluation_connectedSectionsEquiv] at hst
  rw [Subtype.ext (connectedAut_injective x hst)]

/-- **The image of evaluation**: an automorphism `e` of an object is the evaluation of a central
section exactly when its group component is central. -/
theorem connected_eval_image (U : C) (x : Codiscrete I × SingleObj G) (e : Aut x) :
    (∃ s, IntrinsicBandSections.evaluation (F := constant C (Codiscrete I × SingleObj G)) (𝟙 U) x
        s = e) ↔
      (e.asIso.hom.2 : G) ∈ Subgroup.center G := by
  refine ⟨?_, fun h ↦ ⟨connectedSectionsEquiv C x.1.as U ⟨_, h⟩, ?_⟩⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨a, rfl⟩ := (connectedSectionsEquiv C x.1.as U).surjective s
    rw [evaluation_connectedSectionsEquiv]
    exact a.property
  · rw [evaluation_connectedSectionsEquiv]
    exact connectedAut_snd_asIso_hom x e

/-- **Evaluation is surjective** onto the automorphisms of an object exactly when the centre of
`G` is all of `G`. -/
theorem connected_eval_surjective_iff (U : C) (x : Codiscrete I × SingleObj G) :
    Function.Surjective
      (IntrinsicBandSections.evaluation (F := constant C (Codiscrete I × SingleObj G)) (𝟙 U) x) ↔
      Subgroup.center G = ⊤ := by
  refine ⟨fun h ↦ eq_top_iff.2 fun g _ ↦ ?_, fun h e ↦ ?_⟩
  · simpa using (connected_eval_image U x (connectedAut x g)).1 (h _)
  · exact (connected_eval_image U x e).2 (h ▸ Subgroup.mem_top _)

end CategoryTheory.Pseudofunctor.ConnectedBandFixtures
