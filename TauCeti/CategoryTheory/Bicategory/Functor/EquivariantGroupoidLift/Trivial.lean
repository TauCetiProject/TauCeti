/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Basic
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import TauCeti.CategoryTheory.Monoidal.Action.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

/-!
# Equivariant groupoid lifts of trivial actions

A coherent equivariant lift (`TauCeti.EquivariantGroupoidLift`) of a family of categorical
actions of a monoid `H` along a category `Γ` contains in particular a coherent transport along
`Γ`: its transport functors form a pseudofunctor `LocallyDiscrete Γ ⥤ᵖ Cat`
(`TauCeti.EquivariantGroupoidLift.transportPseudofunctor`). This file goes the other way when
`H` acts trivially. A pseudofunctor `F : LocallyDiscrete Γ ⥤ᵖ Cat` gives a lift
`F.toEquivariantGroupoidLift H` of the trivial actions (`TauCeti.trivialAction`) of `H` on the
categories `F p`: its joint pseudofunctor is the composite of `F` with the projection
`Γ × SingleObj H ⥤ Γ`, and its fiber comparisons have identity components. Its transport
pseudofunctor recovers `F`: there are strong transformations in both directions between them with
identity components, whose naturality isomorphisms identify the transport functor along `g` with
`F g`, and both composites are isomorphic to identities by invertible modifications with unitor
components. So the transport pseudofunctor and `F` are equivalent in the bicategory of
pseudofunctors.

For the trivial monoid this compares coherent transport along `Γ` without a symmetry group with
equivariant lifts: every pseudofunctor on `Γ` is, up to these strong transformations, the
transport pseudofunctor of a lift of the trivial actions on its values. The coherence of the
transport data of such a lift is then exactly that of `F`; for identity transport functors and
central composition isomorphisms it is the `2`-cocycle condition of
`TauCeti.centralUnitIso_associativity_iff`. For an arbitrary monoid `H`,
`F.toEquivariantGroupoidLift H` is the lift of a family of categories with trivial `H`-symmetry.

## Main declarations

* `CategoryTheory.Pseudofunctor.restrictFiberFst`: the comparison, with identity components and
  naturality isomorphisms given by the unit comparison of `F`, between the restriction of the
  composite of `F` with the projection to the fiber `{p} × SingleObj H` and the trivial action
  on `F p`;
* `CategoryTheory.Pseudofunctor.toEquivariantGroupoidLift`: the lift of the trivial actions
  attached to a pseudofunctor on `Γ`;
* `CategoryTheory.Pseudofunctor.toEquivariantGroupoidLiftTransportIso`: the isomorphism between
  its transport functor along `g` and `F g`;
* `CategoryTheory.Pseudofunctor.toEquivariantGroupoidLiftTransportHom`,
  `CategoryTheory.Pseudofunctor.toEquivariantGroupoidLiftTransportInv`: the strong
  transformations, with identity components, between its transport pseudofunctor and `F`;
* `CategoryTheory.Pseudofunctor.toEquivariantGroupoidLiftTransportHomInvIso`,
  `CategoryTheory.Pseudofunctor.toEquivariantGroupoidLiftTransportInvHomIso`: their composites
  are isomorphic to identities.

## References

* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007), §1.3: families of local categories over
  a groupoid of parameters, and the role of coherence of their transport functors.
* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 4: pseudofunctors and strong
  transformations.
-/

public section

universe w v u₂ v₁ u₁

namespace CategoryTheory.Pseudofunctor

open Bicategory TauCeti TauCeti.EquivariantGroupoidLift

variable {Γ : Type u₁} [Category.{v₁} Γ] (F : LocallyDiscrete Γ ⥤ᵖ Cat.{v, w})
  (H : Type u₂) [Monoid H]

/-! ### The lift of the trivial actions -/

/-- The comparison of the restriction to the fiber `{p} × SingleObj H` of the composite of `F`
with the projection `Γ × SingleObj H ⥤ Γ` with the trivial action of `H` on `F p`. The
restriction sends every `a : H` to `F (𝟙 p)`; the component is the identity of `F p`, and the
naturality isomorphism at `a` is the unit comparison `F (𝟙 p) ≅ 𝟙` of `F`. -/
-- The body is exposed so that the fiber comparisons of `F.toEquivariantGroupoidLift H` are
-- definitionally identity functors, as the transport formulas below require.
@[expose] noncomputable def restrictFiberFst (p : Γ) :
    StrongTrans (((CategoryTheory.Prod.fst Γ (SingleObj H)).toPseudofunctor.comp F).restrictFiber p)
      (trivialAction H (F.obj ⟨p⟩)) where
  app _ := 𝟙 _
  naturality _ := ρ_ _ ≪≫ F.mapId ⟨p⟩ ≪≫ (λ_ _).symm
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    exact Bicategory.id_whiskerRight_comp_eq_comp_whiskerLeft_id _ _ _ _ _
  -- The unit and composition conditions are proved for arbitrary `2`-cells of
  -- `LocallyDiscrete Γ`, which are then found by unification with the unfolded goal.
  naturality_id _ := by
    have key {o : LocallyDiscrete Γ} {u : o ⟶ o} (η₁ : 𝟙 o ⟶ u) (η₂ : u ⟶ 𝟙 o) :
        (ρ_ (F.map (𝟙 o)) ≪≫ F.mapId o ≪≫ (λ_ _).symm).hom ≫
            𝟙 (F.obj o) ◁ (Iso.refl (𝟙 (F.obj o))).hom =
          (F.map₂ η₁ ≫ F.map₂ η₂ ≫ (F.mapId o).hom) ▷ 𝟙 (F.obj o) ≫
            (λ_ (𝟙 (F.obj o))).hom ≫ (ρ_ (𝟙 (F.obj o))).inv := by
      obtain rfl := obj_ext_of_isDiscrete η₁
      obtain rfl := Subsingleton.elim η₁ (𝟙 _)
      obtain rfl := Subsingleton.elim η₂ (𝟙 _)
      ext X
      simp
    exact key _ _
  naturality_comp _ _ := by
    have key {o : LocallyDiscrete Γ} {u : o ⟶ o} (η₁ : 𝟙 o ⟶ u) (η₂ : u ⟶ 𝟙 o ≫ 𝟙 o) :
        (ρ_ (F.map (𝟙 o)) ≪≫ F.mapId o ≪≫ (λ_ _).symm).hom ≫
            𝟙 (F.obj o) ◁ (λ_ (𝟙 (F.obj o))).inv =
          (F.map₂ η₁ ≫ F.map₂ η₂ ≫ (F.mapComp (𝟙 o) (𝟙 o)).hom) ▷ 𝟙 (F.obj o) ≫
            (α_ _ _ _).hom ≫
              F.map (𝟙 o) ◁ (ρ_ (F.map (𝟙 o)) ≪≫ F.mapId o ≪≫ (λ_ _).symm).hom ≫
                (α_ _ _ _).inv ≫
                  (ρ_ (F.map (𝟙 o)) ≪≫ F.mapId o ≪≫ (λ_ _).symm).hom ▷ 𝟙 (F.obj o) ≫
                    (α_ _ _ _).hom := by
      obtain rfl := obj_ext_of_isDiscrete η₁
      obtain rfl := Subsingleton.elim η₁ (𝟙 _)
      obtain rfl := Subsingleton.elim η₂ (λ_ (𝟙 o)).inv
      rw [F.mapComp_id_left_hom, PrelaxFunctor.map₂_inv_hom_assoc]
      ext X
      simp
    exact key _ _

@[simp]
lemma restrictFiberFst_app (p : Γ) (a : LocallyDiscrete (SingleObj H)) :
    (F.restrictFiberFst H p).app a = 𝟙 _ :=
  rfl

/-- The naturality isomorphisms of `restrictFiberFst` are the unit comparison of `F`. -/
@[simp]
lemma restrictFiberFst_naturality_hom_app (p : Γ) {a b : LocallyDiscrete (SingleObj H)}
    (f : a ⟶ b) (X : F.obj ⟨p⟩) :
    ((F.restrictFiberFst H p).naturality f).hom.toNatTrans.app X =
      (F.mapId ⟨p⟩).hom.toNatTrans.app X :=
  Cat.rightUnitor_trans_leftUnitor_symm_hom_app _ _

@[simp]
lemma restrictFiberFst_naturality_inv_app (p : Γ) {a b : LocallyDiscrete (SingleObj H)}
    (f : a ⟶ b) (X : F.obj ⟨p⟩) :
    ((F.restrictFiberFst H p).naturality f).inv.toNatTrans.app X =
      (F.mapId ⟨p⟩).inv.toNatTrans.app X :=
  Cat.rightUnitor_trans_leftUnitor_symm_inv_app _ _

/-- The lift of the trivial actions of `H` on the categories `F p` attached to a pseudofunctor
`F : LocallyDiscrete Γ ⥤ᵖ Cat`. Its joint pseudofunctor is the composite of `F` with the
projection `Γ × SingleObj H ⥤ Γ`, and its fiber comparison at `p` is `F.restrictFiberFst H p`,
whose component is the identity of `F p`. -/
-- The body is exposed so that the joint fibers and joint functors of the lift are definitionally
-- the categories `F p` and the functors `F g`, as the formulas below state.
@[expose] noncomputable def toEquivariantGroupoidLift :
    EquivariantGroupoidLift Γ (fun p ↦ trivialAction H (F.obj ⟨p⟩)) where
  joint := (CategoryTheory.Prod.fst Γ (SingleObj H)).toPseudofunctor.comp F
  comparison p := F.restrictFiberFst H p
  isEquivalence_comparison _ := inferInstanceAs (𝟭 _).IsEquivalence

lemma toEquivariantGroupoidLift_joint :
    (F.toEquivariantGroupoidLift H).joint =
      (CategoryTheory.Prod.fst Γ (SingleObj H)).toPseudofunctor.comp F :=
  rfl

lemma toEquivariantGroupoidLift_comparison (p : Γ) :
    (F.toEquivariantGroupoidLift H).comparison p = F.restrictFiberFst H p :=
  rfl

/-- The fiber comparisons of `F.toEquivariantGroupoidLift H` are identity functors. -/
@[simp]
lemma toEquivariantGroupoidLift_fiberEquivalence_functor (p : Γ) :
    ((F.toEquivariantGroupoidLift H).fiberEquivalence p).functor = 𝟭 (F.obj ⟨p⟩) :=
  rfl

/-- The joint functor of `F.toEquivariantGroupoidLift H` along `g` is `F g`. -/
@[simp]
lemma toEquivariantGroupoidLift_jointMap {p q : Γ} (g : p ⟶ q) :
    (F.toEquivariantGroupoidLift H).jointMap g = (F.map ⟨g⟩).toFunctor :=
  rfl

/-- The unit comparison of the joint pseudofunctor of `F.toEquivariantGroupoidLift H` is that
of `F`. -/
lemma toEquivariantGroupoidLift_jointMapId_hom_app (p : Γ)
    (Y : (F.toEquivariantGroupoidLift H).jointFiber p) :
    ((F.toEquivariantGroupoidLift H).jointMapId p).hom.app Y =
      (F.mapId ⟨p⟩).hom.toNatTrans.app Y := by
  rw [jointMapId_hom_app]
  have key {o : LocallyDiscrete Γ} (η₁ η₂ : 𝟙 o ⟶ 𝟙 o) (Y : F.obj o) :
      (F.map₂ η₁ ≫ F.map₂ η₂ ≫ (F.mapId o).hom).toNatTrans.app Y =
        (F.mapId o).hom.toNatTrans.app Y := by
    simp [Subsingleton.elim η₁ (𝟙 _), Subsingleton.elim η₂ (𝟙 _)]
  exact key _ _ _

/-- The composition comparison of the joint pseudofunctor of `F.toEquivariantGroupoidLift H` is
that of `F`. -/
lemma toEquivariantGroupoidLift_jointMapComp_hom_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (Y : (F.toEquivariantGroupoidLift H).jointFiber p) :
    ((F.toEquivariantGroupoidLift H).jointMapComp g h (g ≫ h) rfl).hom.app Y =
      (F.mapComp ⟨g⟩ ⟨h⟩).hom.toNatTrans.app Y := by
  rw [jointMapComp_hom_app]
  have key {o₀ o₁ o₂ : LocallyDiscrete Γ} (f₁ : o₀ ⟶ o₁) (f₂ : o₁ ⟶ o₂)
      (η₁ η₂ : f₁ ≫ f₂ ⟶ f₁ ≫ f₂) (Y : F.obj o₀) :
      (F.map₂ η₁ ≫ F.map₂ η₂ ≫ (F.mapComp f₁ f₂).hom).toNatTrans.app Y =
        (F.mapComp f₁ f₂).hom.toNatTrans.app Y := by
    simp [Subsingleton.elim η₁ (𝟙 _), Subsingleton.elim η₂ (𝟙 _)]
  exact key _ _ _ _ _

/-! ### Transport recovers the pseudofunctor -/

/-- The transport functor of `F.toEquivariantGroupoidLift H` along `g` is isomorphic to `F g`,
by the counit of the fiber comparison at the source. -/
noncomputable def toEquivariantGroupoidLiftTransportIso {p q : Γ} (g : p ⟶ q) :
    (F.toEquivariantGroupoidLift H).transport g ≅ (F.map ⟨g⟩).toFunctor :=
  Functor.isoWhiskerRight ((Functor.rightUnitor _).symm ≪≫
    ((F.toEquivariantGroupoidLift H).fiberEquivalence p).counitIso) _

@[simp]
lemma toEquivariantGroupoidLiftTransportIso_hom_app {p q : Γ} (g : p ⟶ q)
    (X : fiber (fun p : Γ ↦ trivialAction H (F.obj ⟨p⟩)) p) :
    (F.toEquivariantGroupoidLiftTransportIso H g).hom.app X =
      (F.map ⟨g⟩).toFunctor.map
        (((F.toEquivariantGroupoidLift H).fiberEquivalence p).counit.app X) :=
  -- The component is `F g` applied to `𝟙 _ ≫ ε_X`, coming from the right unitor.
  congrArg (F.map ⟨g⟩).toFunctor.map (Category.id_comp _)

@[simp]
lemma toEquivariantGroupoidLiftTransportIso_inv_app {p q : Γ} (g : p ⟶ q)
    (X : fiber (fun p : Γ ↦ trivialAction H (F.obj ⟨p⟩)) p) :
    (F.toEquivariantGroupoidLiftTransportIso H g).inv.app X =
      (F.map ⟨g⟩).toFunctor.map
        (((F.toEquivariantGroupoidLift H).fiberEquivalence p).counitInv.app X) :=
  -- The component is `F g` applied to `ε⁻¹_X ≫ 𝟙 _`, coming from the right unitor.
  congrArg (F.map ⟨g⟩).toFunctor.map (Category.comp_id _)

/-- Under `toEquivariantGroupoidLiftTransportIso`, the unit isomorphism of transport of
`F.toEquivariantGroupoidLift H` is the unit comparison of `F`. -/
lemma toEquivariantGroupoidLift_transportId_hom_app (p : Γ)
    (X : fiber (fun p : Γ ↦ trivialAction H (F.obj ⟨p⟩)) p) :
    ((F.toEquivariantGroupoidLift H).transportId p).hom.app X =
      (F.toEquivariantGroupoidLiftTransportIso H (𝟙 p)).hom.app X ≫
        (F.mapId ⟨p⟩).hom.toNatTrans.app X := by
  rw [transportId_hom_app, toEquivariantGroupoidLift_jointMapId_hom_app,
    toEquivariantGroupoidLiftTransportIso_hom_app]
  exact ((F.mapId ⟨p⟩).hom.toNatTrans.naturality _).symm

/-- Under `toEquivariantGroupoidLiftTransportIso`, the composition isomorphisms of transport of
`F.toEquivariantGroupoidLift H` are the composition comparisons of `F`. -/
lemma toEquivariantGroupoidLiftTransportIso_hom_app_comp_mapComp {p q r : Γ} (g : p ⟶ q)
    (h : q ⟶ r) (X : fiber (fun p : Γ ↦ trivialAction H (F.obj ⟨p⟩)) p) :
    (F.toEquivariantGroupoidLiftTransportIso H (g ≫ h)).hom.app X ≫
        (F.mapComp ⟨g⟩ ⟨h⟩).hom.toNatTrans.app X =
      ((F.toEquivariantGroupoidLift H).transportComp g h (g ≫ h) rfl).inv.app X ≫
        (F.toEquivariantGroupoidLiftTransportIso H h).hom.app
          (((F.toEquivariantGroupoidLift H).transport g).obj X) ≫
        (F.map ⟨h⟩).toFunctor.map ((F.toEquivariantGroupoidLiftTransportIso H g).hom.app X) := by
  rw [transportComp_inv_app, toEquivariantGroupoidLift_jointMapComp_hom_app,
    toEquivariantGroupoidLiftTransportIso_hom_app, toEquivariantGroupoidLiftTransportIso_hom_app,
    toEquivariantGroupoidLiftTransportIso_hom_app]
  set e := (F.toEquivariantGroupoidLift H).fiberEquivalence
  set Y := (F.map ⟨g⟩).toFunctor.obj ((e p).inverse.obj X)
  -- Since the fiber comparison at `q` is the identity functor, its unit and counit at `Y` are
  -- inverse to each other.
  have hu : (F.map ⟨h⟩).toFunctor.map ((e q).unit.app Y) ≫
      (F.map ⟨h⟩).toFunctor.map ((e q).counit.app Y) = 𝟙 _ :=
    ((F.map ⟨h⟩).toFunctor.map_comp _ _).symm.trans
      ((congrArg (F.map ⟨h⟩).toFunctor.map ((e q).functor_unit_comp Y)).trans
        ((F.map ⟨h⟩).toFunctor.map_id _))
  calc _ = (F.mapComp ⟨g⟩ ⟨h⟩).hom.toNatTrans.app ((e p).inverse.obj X) ≫
        (F.map ⟨h⟩).toFunctor.map ((F.map ⟨g⟩).toFunctor.map ((e p).counit.app X)) :=
          (F.mapComp ⟨g⟩ ⟨h⟩).hom.toNatTrans.naturality _
    _ = ((F.mapComp ⟨g⟩ ⟨h⟩).hom.toNatTrans.app ((e p).inverse.obj X) ≫
        (F.map ⟨h⟩).toFunctor.map ((e q).unit.app Y)) ≫
          (F.map ⟨h⟩).toFunctor.map ((e q).counit.app Y) ≫
            (F.map ⟨h⟩).toFunctor.map ((F.map ⟨g⟩).toFunctor.map ((e p).counit.app X)) := by
      rw [Category.assoc, reassoc_of% hu]
    -- The fiber comparison at `r` is the identity functor, and the joint functors are the
    -- functors `F g`, definitionally.
    _ = _ := rfl

/-- The inverse form of `toEquivariantGroupoidLiftTransportIso_hom_app_comp_mapComp`. -/
lemma toEquivariantGroupoidLiftTransportIso_inv_app_comp_transportComp_inv_app {p q r : Γ}
    (g : p ⟶ q) (h : q ⟶ r) (X : fiber (fun p : Γ ↦ trivialAction H (F.obj ⟨p⟩)) p) :
    (F.toEquivariantGroupoidLiftTransportIso H (g ≫ h)).inv.app X ≫
        ((F.toEquivariantGroupoidLift H).transportComp g h (g ≫ h) rfl).inv.app X =
      (F.mapComp ⟨g⟩ ⟨h⟩).hom.toNatTrans.app X ≫
        (F.toEquivariantGroupoidLiftTransportIso H h).inv.app ((F.map ⟨g⟩).toFunctor.obj X) ≫
        ((F.toEquivariantGroupoidLift H).transport h).map
          ((F.toEquivariantGroupoidLiftTransportIso H g).inv.app X) := by
  rw [← cancel_epi ((F.toEquivariantGroupoidLiftTransportIso H (g ≫ h)).hom.app X),
    Iso.hom_inv_id_app_assoc, ← Category.assoc,
    toEquivariantGroupoidLiftTransportIso_hom_app_comp_mapComp]
  -- By naturality of the transport isomorphism along `h`, the right side cancels to the
  -- composition isomorphism.
  simp only [Category.assoc]
  rw [← (F.toEquivariantGroupoidLiftTransportIso H h).hom.naturality_assoc,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
  exact (Category.comp_id _).symm

/-- The transport pseudofunctor of `F.toEquivariantGroupoidLift H` maps to `F` by a strong
transformation whose components are identities and whose naturality isomorphism at `g` is
`toEquivariantGroupoidLiftTransportIso`. -/
-- The body is exposed so that the naturality isomorphisms can be stated in terms of the
-- identity components, as in `toEquivariantGroupoidLiftTransportHom_naturality_hom_app`.
@[expose] noncomputable def toEquivariantGroupoidLiftTransportHom :
    StrongTrans (F.toEquivariantGroupoidLift H).transportPseudofunctor F where
  app _ := 𝟙 _
  naturality g := ρ_ _ ≪≫ Cat.Hom.isoMk (F.toEquivariantGroupoidLiftTransportIso H g.as) ≪≫
    (λ_ _).symm
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    exact Bicategory.id_whiskerRight_comp_eq_comp_whiskerLeft_id _ _ _ _ _
  naturality_id b := by
    exact Cat.rightUnitor_trans_leftUnitor_symm_naturality_id _ _ _ fun X ↦
      (F.toEquivariantGroupoidLift_transportId_hom_app H b.as X).symm
  naturality_comp g h := by
    exact Cat.rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _ _
      (F.toEquivariantGroupoidLiftTransportIso_hom_app_comp_mapComp H g.as h.as)

@[simp]
lemma toEquivariantGroupoidLiftTransportHom_app (b : LocallyDiscrete Γ) :
    (F.toEquivariantGroupoidLiftTransportHom H).app b = 𝟙 _ :=
  (rfl)

@[simp]
lemma toEquivariantGroupoidLiftTransportHom_naturality_hom_app {b b' : LocallyDiscrete Γ}
    (g : b ⟶ b') (X : F.obj b) :
    ((F.toEquivariantGroupoidLiftTransportHom H).naturality g).hom.toNatTrans.app X =
      (F.toEquivariantGroupoidLiftTransportIso H g.as).hom.app X :=
  Cat.rightUnitor_trans_leftUnitor_symm_hom_app _ _

@[simp]
lemma toEquivariantGroupoidLiftTransportHom_naturality_inv_app {b b' : LocallyDiscrete Γ}
    (g : b ⟶ b') (X : F.obj b) :
    ((F.toEquivariantGroupoidLiftTransportHom H).naturality g).inv.toNatTrans.app X =
      (F.toEquivariantGroupoidLiftTransportIso H g.as).inv.app X :=
  Cat.rightUnitor_trans_leftUnitor_symm_inv_app _ _

/-- `F` maps to the transport pseudofunctor of `F.toEquivariantGroupoidLift H` by a strong
transformation whose components are identities and whose naturality isomorphism at `g` is the
inverse of `toEquivariantGroupoidLiftTransportIso`. -/
-- The body is exposed so that the naturality isomorphisms can be stated in terms of the
-- identity components, as in `toEquivariantGroupoidLiftTransportInv_naturality_hom_app`.
@[expose] noncomputable def toEquivariantGroupoidLiftTransportInv :
    StrongTrans F (F.toEquivariantGroupoidLift H).transportPseudofunctor where
  app _ := 𝟙 _
  naturality g := ρ_ _ ≪≫ Cat.Hom.isoMk (F.toEquivariantGroupoidLiftTransportIso H g.as).symm ≪≫
    (λ_ _).symm
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    exact Bicategory.id_whiskerRight_comp_eq_comp_whiskerLeft_id _ _ _ _ _
  naturality_id b := by
    exact Cat.rightUnitor_trans_leftUnitor_symm_naturality_id _ _ _ fun X ↦
      (Iso.inv_comp_eq ((F.toEquivariantGroupoidLiftTransportIso H (𝟙 b.as)).app X)).2
        (F.toEquivariantGroupoidLift_transportId_hom_app H b.as X)
  naturality_comp g h := by
    exact Cat.rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _ _
      (F.toEquivariantGroupoidLiftTransportIso_inv_app_comp_transportComp_inv_app H g.as h.as)

@[simp]
lemma toEquivariantGroupoidLiftTransportInv_app (b : LocallyDiscrete Γ) :
    (F.toEquivariantGroupoidLiftTransportInv H).app b = 𝟙 _ :=
  (rfl)

@[simp]
lemma toEquivariantGroupoidLiftTransportInv_naturality_hom_app {b b' : LocallyDiscrete Γ}
    (g : b ⟶ b') (X : F.obj b) :
    ((F.toEquivariantGroupoidLiftTransportInv H).naturality g).hom.toNatTrans.app X =
      (F.toEquivariantGroupoidLiftTransportIso H g.as).inv.app X :=
  Cat.rightUnitor_trans_leftUnitor_symm_hom_app _ _

@[simp]
lemma toEquivariantGroupoidLiftTransportInv_naturality_inv_app {b b' : LocallyDiscrete Γ}
    (g : b ⟶ b') (X : F.obj b) :
    ((F.toEquivariantGroupoidLiftTransportInv H).naturality g).inv.toNatTrans.app X =
      (F.toEquivariantGroupoidLiftTransportIso H g.as).hom.app X :=
  Cat.rightUnitor_trans_leftUnitor_symm_inv_app _ _

section Inverse

open StrongTrans

/-- The composite of `toEquivariantGroupoidLiftTransportHom` with
`toEquivariantGroupoidLiftTransportInv` is the identity of the transport pseudofunctor, by the
invertible modification whose components are left unitors. -/
noncomputable def toEquivariantGroupoidLiftTransportHomInvIso :
    F.toEquivariantGroupoidLiftTransportHom H ≫ F.toEquivariantGroupoidLiftTransportInv H ≅
      𝟙 (F.toEquivariantGroupoidLift H).transportPseudofunctor :=
  isoMk (fun _ ↦ λ_ _) fun f ↦ by
    simp only [categoryStruct_comp_naturality_hom, categoryStruct_id_naturality_hom]
    exact Cat.rightUnitor_trans_leftUnitor_symm_comp_modification _ _ fun X ↦
      Iso.hom_inv_id_app _ X

@[simp]
lemma toEquivariantGroupoidLiftTransportHomInvIso_hom_as_app (b : LocallyDiscrete Γ) :
    (F.toEquivariantGroupoidLiftTransportHomInvIso H).hom.as.app b =
      (λ_ (𝟙 ((F.toEquivariantGroupoidLift H).transportPseudofunctor.obj b))).hom :=
  (rfl)

@[simp]
lemma toEquivariantGroupoidLiftTransportHomInvIso_inv_as_app (b : LocallyDiscrete Γ) :
    (F.toEquivariantGroupoidLiftTransportHomInvIso H).inv.as.app b =
      (λ_ (𝟙 ((F.toEquivariantGroupoidLift H).transportPseudofunctor.obj b))).inv :=
  (rfl)

/-- The composite of `toEquivariantGroupoidLiftTransportInv` with
`toEquivariantGroupoidLiftTransportHom` is the identity of `F`, by the invertible modification
whose components are left unitors. -/
noncomputable def toEquivariantGroupoidLiftTransportInvHomIso :
    F.toEquivariantGroupoidLiftTransportInv H ≫ F.toEquivariantGroupoidLiftTransportHom H ≅ 𝟙 F :=
  isoMk (fun _ ↦ λ_ _) fun f ↦ by
    simp only [categoryStruct_comp_naturality_hom, categoryStruct_id_naturality_hom]
    exact Cat.rightUnitor_trans_leftUnitor_symm_comp_modification _ _ fun X ↦
      Iso.inv_hom_id_app _ X

@[simp]
lemma toEquivariantGroupoidLiftTransportInvHomIso_hom_as_app (b : LocallyDiscrete Γ) :
    (F.toEquivariantGroupoidLiftTransportInvHomIso H).hom.as.app b = (λ_ (𝟙 (F.obj b))).hom :=
  (rfl)

@[simp]
lemma toEquivariantGroupoidLiftTransportInvHomIso_inv_as_app (b : LocallyDiscrete Γ) :
    (F.toEquivariantGroupoidLiftTransportInvHomIso H).inv.as.app b = (λ_ (𝟙 (F.obj b))).inv :=
  (rfl)

end Inverse

end CategoryTheory.Pseudofunctor
