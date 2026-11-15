/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Pullback.Basic
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Equivariant transport of an equivariant groupoid lift

Let `L : EquivariantGroupoidLift Γ actions` be a coherent equivariant lift of a family of
categorical actions `actions p : LocallyDiscrete (SingleObj H) ⥤ᵖ Cat` of a monoid `H` along a
category `Γ`. Its transport functors `E_g : C p ⥤ C q` commute with the prescribed actions by the
isomorphisms `T_a ⋙ E_g ≅ E_g ⋙ T_a` of `EquivariantGroupoidLift.transportCommIso`. This file
packages these data in the bicategory of categorical actions of `H`, the
bicategory of pseudofunctors `LocallyDiscrete (SingleObj H) ⥤ᵖ Cat` with strong transformations
and modifications.

* `TauCeti.EquivariantGroupoidLift.transportStrongTrans L g : actions p ⟶ actions q` is the
  strong transformation with component `E_g` and naturality isomorphisms `transportCommIso g`:
  an equivariant functor between the prescribed actions. Its unit and composition conditions are
  the mixed coherence conditions `transportCommIso_actId` and `transportCommIso_actComp`.
* `TauCeti.EquivariantGroupoidLift.transportStrongTransId` and
  `TauCeti.EquivariantGroupoidLift.transportStrongTransComp` are the unit and composition
  isomorphisms of transport, as invertible modifications. That they are modifications is the
  mixed coherence `transportCommIso_id` and `transportCommIso_comp`.
* `TauCeti.EquivariantGroupoidLift.equivariantTransport L` is the pseudofunctor
  `LocallyDiscrete Γ ⥤ᵖ (LocallyDiscrete (SingleObj H) ⥤ᵖ Cat)` with value `actions p` at `p`,
  assembled from these. Its coherence is the associativity and unitality of `transportComp`.
* `TauCeti.EquivariantGroupoidLift.transportActionEquivalence L g`: for an isomorphism
  `g : p ≅ q`, the equivariant transports along `g` and `g⁻¹` form an equivalence
  `actions p ≌ actions q` of categorical actions of `H`.
* `TauCeti.EquivariantGroupoidLift.equivariantEndAction L p`: the endomorphism monoid of `p`, and
  so for a groupoid `Γ` the isotropy group of `p`, acts on the categorical action `actions p` by
  equivariant transport.

Thus the transport of a lift is equivariant as a whole: the coherence data of transport along
`Γ` are compatible with the actions of `H`, not just its individual functors. Since
`equivariantTransport` is a pseudofunctor out of `LocallyDiscrete Γ`, reindexing it along
naturally isomorphic functors `ψ₁ ≅ ψ₂ : Λ ⥤ Γ` gives equivalent families by
`CategoryTheory.Pseudofunctor.mapNatIso`, whose components are the equivariant transports along
the components of the natural isomorphism; `pullback_transportStrongTrans` identifies the
equivariant transport of `L.pullback ψ` with that of `L` along `ψ`.

## References

* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): families of local categories over the
  groupoid of local Langlands parameters, compatible with the loop group actions.
* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 4: pseudofunctors, strong
  transformations and modifications.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  (L : EquivariantGroupoidLift Γ actions)

/-- The transport functor `E_g` along `g : p ⟶ q`, with the isomorphisms
`T_a ⋙ E_g ≅ E_g ⋙ T_a` commuting it with the prescribed actions, as a strong transformation
`actions p ⟶ actions q`: an equivariant functor between the prescribed categorical actions. -/
-- The body is exposed so that the components and naturality cells are definitionally the
-- transport functors and `transportCommIso`, as stated in the component lemmas below.
@[expose] noncomputable def transportStrongTrans {p q : Γ} (g : p ⟶ q) :
    actions p ⟶ actions q where
  app _ := (L.transport g).toCatHom
  naturality f := Cat.Hom.isoMk (L.transportCommIso g f.as)
  naturality_naturality η :=
    Pseudofunctor.naturality_naturality_of_locallyDiscrete (actions p) (actions q)
      (fun _ ↦ (L.transport g).toCatHom) (fun f ↦ Cat.Hom.isoMk (L.transportCommIso g f.as)) η
  -- In the coherence conditions here and below, the unitors and associators of `Cat` contribute
  -- identities at objects that agree with those of the goal only after unfolding. Each condition
  -- is therefore stated componentwise as `key`, with these identities written out, and then
  -- closed by unification with the goal.
  naturality_id a := by
    have h (X : fiber actions p) := L.transportCommIso_actId g X
    simp only [actId_hom_app, Quiver.Hom.id_toLoc, Pseudofunctor.mapId'_eq_mapId] at h
    have key (X : fiber actions p) :
        (L.transportCommIso g (𝟙 a.as)).hom.app X ≫
            ((actions q).mapId a).hom.toNatTrans.app ((L.transport g).obj X) =
          (L.transport g).map (((actions p).mapId a).hom.toNatTrans.app X) ≫ 𝟙 _ ≫ 𝟙 _ := by
      simp only [Category.comp_id]
      exact h X
    ext X
    exact key X
  naturality_comp f h := by
    have h' (X : fiber actions p) := L.transportCommIso_actComp g f.as h.as (f ≫ h).as rfl X
    simp only [actComp_hom_app_eq_mapComp] at h'
    have key (X : fiber actions p) :
        (L.transportCommIso g (f ≫ h).as).hom.app X ≫
            ((actions q).mapComp f h).hom.toNatTrans.app ((L.transport g).obj X) =
          (L.transport g).map (((actions p).mapComp f h).hom.toNatTrans.app X) ≫ 𝟙 _ ≫
            (L.transportCommIso g h.as).hom.app ((act actions p f.as).obj X) ≫ 𝟙 _ ≫
              (act actions q h.as).map ((L.transportCommIso g f.as).hom.app X) ≫ 𝟙 _ := by
      simp only [Category.id_comp, Category.comp_id]
      exact (h' X).symm
    ext X
    exact key X

@[simp]
lemma transportStrongTrans_app {p q : Γ} (g : p ⟶ q) (a : LocallyDiscrete (SingleObj H)) :
    ((L.transportStrongTrans g).app a).toFunctor = L.transport g :=
  rfl

@[simp]
lemma transportStrongTrans_naturality_hom_app {p q : Γ} (g : p ⟶ q)
    {a b : LocallyDiscrete (SingleObj H)} (f : a ⟶ b) (X : fiber actions p) :
    ((L.transportStrongTrans g).naturality f).hom.toNatTrans.app X =
      (L.transportCommIso g f.as).hom.app X :=
  rfl

@[simp]
lemma transportStrongTrans_naturality_inv_app {p q : Γ} (g : p ⟶ q)
    {a b : LocallyDiscrete (SingleObj H)} (f : a ⟶ b) (X : fiber actions p) :
    ((L.transportStrongTrans g).naturality f).inv.toNatTrans.app X =
      (L.transportCommIso g f.as).inv.app X :=
  rfl

/-- The unit isomorphism `E_(𝟙 p) ≅ 𝟭` of transport, as an invertible modification from the
equivariant transport along `𝟙 p` to the identity strong transformation of `actions p`. -/
@[expose] noncomputable def transportStrongTransId (p : Γ) :
    L.transportStrongTrans (𝟙 p) ≅ 𝟙 (actions p) :=
  isoMk (fun _ ↦ Cat.Hom.isoMk (L.transportId p)) (fun f ↦ by
    have key (X : fiber actions p) :
        (L.transportId p).hom.app ((act actions p f.as).obj X) ≫ 𝟙 _ ≫ 𝟙 _ =
          (L.transportCommIso (𝟙 p) f.as).hom.app X ≫
            (act actions p f.as).map ((L.transportId p).hom.app X) := by
      rw [Category.comp_id, Category.comp_id, L.transportCommIso_id]
    ext X
    exact key X)

@[simp]
lemma transportStrongTransId_hom_as_app (p : Γ) (a : LocallyDiscrete (SingleObj H))
    (X : fiber actions p) :
    ((L.transportStrongTransId p).hom.as.app a).toNatTrans.app X =
      (L.transportId p).hom.app X :=
  rfl

@[simp]
lemma transportStrongTransId_inv_as_app (p : Γ) (a : LocallyDiscrete (SingleObj H))
    (X : fiber actions p) :
    ((L.transportStrongTransId p).inv.as.app a).toNatTrans.app X =
      (L.transportId p).inv.app X :=
  rfl

/-- The composition isomorphism `E_(gh) ≅ E_g ⋙ E_h` of transport, for `g ≫ h = gh`, as an
invertible modification from the equivariant transport along `gh` to the composite of the
equivariant transports along `g` and `h`. -/
@[expose] noncomputable def transportStrongTransComp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh := by cat_disch) :
    L.transportStrongTrans gh ≅ L.transportStrongTrans g ≫ L.transportStrongTrans h :=
  isoMk (fun _ ↦ Cat.Hom.isoMk (L.transportComp g h gh hgh).symm) (fun f ↦ by
    have key (X : fiber actions p) :
        (L.transportComp g h gh hgh).inv.app ((act actions p f.as).obj X) ≫
            (L.transport h).map ((L.transportCommIso g f.as).hom.app X) ≫
              (L.transportCommIso h f.as).hom.app ((L.transport g).obj X) =
          (L.transportCommIso gh f.as).hom.app X ≫
            (act actions r f.as).map ((L.transportComp g h gh hgh).inv.app X) := by
      rw [← cancel_epi ((L.transportComp g h gh hgh).hom.app ((act actions p f.as).obj X)),
        Iso.hom_inv_id_app_assoc,
        ← cancel_mono ((act actions r f.as).map ((L.transportComp g h gh hgh).hom.app X))]
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
      rw [CategoryTheory.Functor.map_id]
      -- The identity is on an object of the fiber seen through `Cat`, so it is removed by
      -- unification rather than by `rw`.
      exact (L.transportCommIso_comp g h gh hgh f.as X).trans
        (congrArg (_ ≫ ·) (Category.comp_id _).symm)
    ext X
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, comp_naturality_hom_app]
    exact key X)

@[simp]
lemma transportStrongTransComp_hom_as_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r)
    (hgh : g ≫ h = gh) (a : LocallyDiscrete (SingleObj H)) (X : fiber actions p) :
    ((L.transportStrongTransComp g h gh hgh).hom.as.app a).toNatTrans.app X =
      (L.transportComp g h gh hgh).inv.app X :=
  rfl

@[simp]
lemma transportStrongTransComp_inv_as_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r)
    (hgh : g ≫ h = gh) (a : LocallyDiscrete (SingleObj H)) (X : fiber actions p) :
    ((L.transportStrongTransComp g h gh hgh).inv.as.app a).toNatTrans.app X =
      (L.transportComp g h gh hgh).hom.app X :=
  rfl

/-! ### The equivariant transport pseudofunctor

In the coherence conditions below, composite arrows of `Γ` appear in two forms that agree only
propositionally (for instance `(f ≫ g) ≫ h` and `f ≫ g ≫ h`). They are therefore first proved
for arbitrary composites, related by `eqToHom`. -/

private lemma transportStrongTransComp_associativity_eqToHom {p q r s : Γ} (f : p ⟶ q)
    (g : q ⟶ r) (h : r ⟶ s) (fg : p ⟶ r) (gh : q ⟶ s) (fgh fgh' : p ⟶ s) (hfg : f ≫ g = fg)
    (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh')
    (e : L.transportStrongTrans fgh = L.transportStrongTrans fgh') :
    (L.transportStrongTransComp fg h fgh hfgh).hom ≫
        (L.transportStrongTransComp f g fg hfg).hom ▷ L.transportStrongTrans h ≫
          (α_ _ _ _).hom ≫ L.transportStrongTrans f ◁ (L.transportStrongTransComp g h gh hgh).inv ≫
            (L.transportStrongTransComp f gh fgh' hfgh').inv = eqToHom e := by
  obtain rfl : fgh' = fgh := by rw [← hfgh', ← hfgh, ← hfg, ← hgh, Category.assoc]
  have key (X : fiber actions p) :
      (L.transportComp fg h fgh' hfgh).inv.app X ≫
          (L.transport h).map ((L.transportComp f g fg hfg).inv.app X) ≫ 𝟙 _ ≫
            (L.transportComp g h gh hgh).hom.app ((L.transport f).obj X) ≫
              (L.transportComp f gh fgh' hfgh').hom.app X = 𝟙 _ := by
    rw [Category.id_comp, ← L.transportComp_associativity f g h fg gh fgh' hfg hgh hfgh,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app]
  rw [eqToHom_refl]
  ext a X
  exact key X

private lemma transportStrongTransComp_left_unitality_eqToHom {p q : Γ} (f k : p ⟶ q)
    (hk : 𝟙 p ≫ f = k) (e : L.transportStrongTrans k = L.transportStrongTrans f) :
    (L.transportStrongTransComp (𝟙 p) f k hk).hom ≫
        (L.transportStrongTransId p).hom ▷ L.transportStrongTrans f ≫ (λ_ _).hom = eqToHom e := by
  obtain rfl : k = f := hk.symm.trans (Category.id_comp f)
  have key (X : fiber actions p) :
      (L.transportComp (𝟙 p) k k hk).inv.app X ≫
          (L.transport k).map ((L.transportId p).hom.app X) ≫ 𝟙 _ = 𝟙 _ := by
    rw [Category.comp_id, ← L.transportComp_left_unitality k hk X, Iso.inv_hom_id_app]
  rw [eqToHom_refl]
  ext a X
  exact key X

private lemma transportStrongTransComp_right_unitality_eqToHom {p q : Γ} (f k : p ⟶ q)
    (hk : f ≫ 𝟙 q = k) (e : L.transportStrongTrans k = L.transportStrongTrans f) :
    (L.transportStrongTransComp f (𝟙 q) k hk).hom ≫
        L.transportStrongTrans f ◁ (L.transportStrongTransId q).hom ≫ (ρ_ _).hom = eqToHom e := by
  obtain rfl : k = f := hk.symm.trans (Category.comp_id f)
  have key (X : fiber actions p) :
      (L.transportComp k (𝟙 q) k hk).inv.app X ≫
          (L.transportId q).hom.app ((L.transport k).obj X) ≫ 𝟙 _ = 𝟙 _ := by
    rw [Category.comp_id, ← L.transportComp_right_unitality k hk X, Iso.inv_hom_id_app]
  rw [eqToHom_refl]
  ext a X
  exact key X

/-- The equivariant transport of a lift: the pseudofunctor from `Γ` to the bicategory of
categorical actions of `H` (pseudofunctors `LocallyDiscrete (SingleObj H) ⥤ᵖ Cat`, strong
transformations and modifications) sending `p` to the prescribed action `actions p` and
`g` to the equivariant transport `transportStrongTrans g`. -/
@[expose] noncomputable def equivariantTransport :
    LocallyDiscrete Γ ⥤ᵖ (LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) :=
  LocallyDiscrete.mkPseudofunctor actions L.transportStrongTrans L.transportStrongTransId
    (fun f g ↦ L.transportStrongTransComp f g (f ≫ g) rfl)
    (fun f g h ↦ by
      exact transportStrongTransComp_associativity_eqToHom L f g h _ _ _ _ rfl rfl rfl rfl _)
    (fun f ↦ by exact transportStrongTransComp_left_unitality_eqToHom L f _ rfl _)
    (fun f ↦ by exact transportStrongTransComp_right_unitality_eqToHom L f _ rfl _)

@[simp]
lemma equivariantTransport_obj (b : LocallyDiscrete Γ) :
    L.equivariantTransport.obj b = actions b.as :=
  rfl

@[simp]
lemma equivariantTransport_map {b b' : LocallyDiscrete Γ} (g : b ⟶ b') :
    L.equivariantTransport.map g = L.transportStrongTrans g.as :=
  rfl

@[simp]
lemma equivariantTransport_mapId (b : LocallyDiscrete Γ) :
    L.equivariantTransport.mapId b = L.transportStrongTransId b.as :=
  rfl

@[simp]
lemma equivariantTransport_mapComp {b₀ b₁ b₂ : LocallyDiscrete Γ} (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂) :
    L.equivariantTransport.mapComp g h =
      L.transportStrongTransComp g.as h.as (g.as ≫ h.as) rfl :=
  rfl

/-- For an isomorphism `g : p ≅ q` of `Γ`, the equivariant transport along `g` is an equivalence
`actions p ≌ actions q` in the bicategory of categorical actions of `H`, with inverse the
equivariant transport along `g⁻¹`. Its unit `𝟙 ≅ E_g ≫ E_(g⁻¹)` is built from the unit and
composition isomorphisms of transport; its counit is obtained from the corresponding isomorphism
`E_(g⁻¹) ≫ E_g ≅ 𝟙` by `Bicategory.Equivalence.mkOfAdjointifyCounit`. -/
-- The body is exposed so that the unit can be stated against `transportStrongTrans`, as in
-- `transportActionEquivalence_unit`.
@[expose] noncomputable def transportActionEquivalence {p q : Γ} (g : p ≅ q) :
    Bicategory.Equivalence (actions p) (actions q) :=
  Equivalence.mkOfAdjointifyCounit
    ((L.transportStrongTransId p).symm ≪≫ L.transportStrongTransComp g.hom g.inv (𝟙 p))
    ((L.transportStrongTransComp g.inv g.hom (𝟙 q)).symm ≪≫ L.transportStrongTransId q)

@[simp]
lemma transportActionEquivalence_hom {p q : Γ} (g : p ≅ q) :
    (L.transportActionEquivalence g).hom = L.transportStrongTrans g.hom :=
  rfl

@[simp]
lemma transportActionEquivalence_inv {p q : Γ} (g : p ≅ q) :
    (L.transportActionEquivalence g).inv = L.transportStrongTrans g.inv :=
  rfl

lemma transportActionEquivalence_unit {p q : Γ} (g : p ≅ q) :
    (L.transportActionEquivalence g).unit =
      (L.transportStrongTransId p).symm ≪≫ L.transportStrongTransComp g.hom g.inv (𝟙 p) :=
  rfl

/-- The action of the endomorphism monoid `End p` on the prescribed categorical action
`actions p` by equivariant transport: the restriction of `equivariantTransport` along the
inclusion `SingleObj (End p) ⥤ Γ`. It sends `g` to the strong transformation
`transportStrongTrans g`, so `End p` acts on `C p` by functors commuting coherently with the
action of `H`. Its component functors are the transport functors `E_g` of `endAction p`. -/
@[expose] noncomputable def equivariantEndAction (p : Γ) :
    LocallyDiscrete (SingleObj (End p)) ⥤ᵖ (LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) :=
  (SingleObj.functor (MonoidHom.id (End p))).toPseudofunctor.comp L.equivariantTransport

@[simp]
lemma equivariantEndAction_obj (p : Γ) (b : LocallyDiscrete (SingleObj (End p))) :
    (L.equivariantEndAction p).obj b = actions p :=
  rfl

@[simp]
lemma equivariantEndAction_map (p : Γ) {b b' : LocallyDiscrete (SingleObj (End p))}
    (g : b ⟶ b') : (L.equivariantEndAction p).map g = L.transportStrongTrans g.as.asHom :=
  rfl

/-- The equivariant transport of the pullback of `L` along `ψ : Λ ⥤ Γ` is the equivariant
transport of `L` along the image of `ψ`. -/
@[simp]
lemma pullback_transportStrongTrans {Λ : Type*} [Category Λ] (ψ : Λ ⥤ Γ) {l l' : Λ}
    (g : l ⟶ l') : (L.pullback ψ).transportStrongTrans g = L.transportStrongTrans (ψ.map g) := by
  simp only [transportStrongTrans, pullback_transportCommIso, pullback_transport]

end TauCeti.EquivariantGroupoidLift
