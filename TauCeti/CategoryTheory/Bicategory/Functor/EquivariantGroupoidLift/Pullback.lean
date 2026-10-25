/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Basic

/-!
# Pulling back equivariant groupoid lifts along functors

Let `L : EquivariantGroupoidLift Γ actions` be a coherent equivariant lift of a family of
categorical actions of a monoid `H` along a category `Γ`, and let `ψ : Λ ⥤ Γ` be a functor. This
file constructs the pulled-back lift `L.pullback ψ`, a lift along `Λ` of the actions
`actions (ψ l)`. Its joint pseudofunctor is the composite of `L.joint` with
`ψ × 𝟭 : Λ × SingleObj H ⥤ Γ × SingleObj H`, and its fiber comparison at `l` is the fiber
comparison of `L` at `ψ l`. So the pulled-back lift has the prescribed fibers and actions of `L`
at the points of the image of `ψ`, with the same fiber comparisons.

The restriction of the composite pseudofunctor to the fiber `{l} × SingleObj H` sends `a : H` to
the value of `L.joint` at `(ψ.map (𝟙 l), a)`. This is equal, but not definitionally equal, to the
value at `(𝟙 (ψ l), a)` of the restriction of `L.joint` to the fiber `{ψ l} × SingleObj H`. The
strong transformation `Pseudofunctor.restrictFiberPullback` compares the two restrictions; its
components are identities and its naturality isomorphisms are the identities given by
`ψ.map_id`.

The normalized transport data of `L.pullback ψ` on the prescribed fibers are those of `L` along
the image of `ψ`: the transport functor along `g` is `L.transport (ψ.map g)`, the composition
isomorphisms and the isomorphisms commuting transport with the actions are those of `L`, and the
unit isomorphism is that of `L` after identifying `ψ.map (𝟙 l)` with `𝟙 (ψ l)`.

Applied to a quasi-inverse `Λ ⥤ Γ` of an equivalence of parameter groupoids, this transports a
lift along the equivalence, as in the descent of the families of local categories from the
groupoid of opers to the groupoid of local systems.

## Main declarations

* `CategoryTheory.Pseudofunctor.restrictFiberPullback`: the comparison of the fiber restrictions
  of the composite of `F` with `ψ × 𝟭` and of `F`;
* `TauCeti.EquivariantGroupoidLift.pullback`: the pullback of a lift along a functor;
* `TauCeti.EquivariantGroupoidLift.pullback_fiberEquivalence`,
  `TauCeti.EquivariantGroupoidLift.pullback_transport`: the pullback has the same fiber
  comparisons, and its transport functors are those of `L` along `ψ`;
* `TauCeti.EquivariantGroupoidLift.pullback_transportComp`,
  `TauCeti.EquivariantGroupoidLift.pullback_transportId_hom_app`,
  `TauCeti.EquivariantGroupoidLift.pullback_transportCommIso`: its composition and unit
  isomorphisms of transport, and its isomorphisms commuting transport with the actions, are those
  of `L`.

## References

* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): the families of local categories over
  the groupoid of local Langlands parameters, and their descent to local systems.
-/

public section

universe w v u₃ v₃ u₂ v₁ u₁

namespace CategoryTheory.Pseudofunctor

open Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {Λ : Type u₃} [Category.{v₃} Λ]

/-! ### Comparing fiber restrictions -/

/-- The restriction to the fiber `{l} × SingleObj H` of the composite of `F` with `ψ × 𝟭` has the
same values on objects as the restriction of `F` to the fiber `{ψ l} × SingleObj H`. -/
-- The two sides agree only after unfolding `Pseudofunctor.comp`. Naming the equality gives
-- `eqToHom` of it the expected type at reducible transparency, as `simp` and `rw` require.
lemma restrictFiber_comp_prod_obj (F : LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ Cat.{v, w})
    (ψ : Λ ⥤ Γ) (l : Λ) (a : LocallyDiscrete (SingleObj H)) :
    (((ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.comp F).restrictFiber l).obj a =
      (F.restrictFiber (ψ.obj l)).obj a :=
  rfl

/-- The comparison of the restriction to the fiber `{l} × SingleObj H` of the composite of `F`
with `ψ × 𝟭 : Λ × SingleObj H ⥤ Γ × SingleObj H` with the restriction of `F` to the fiber
`{ψ l} × SingleObj H`. The two restrictions have the same value `F (ψ l, ⋆)` at the unique
object, and their values `F (ψ.map (𝟙 l), a)` and `F (𝟙 (ψ l), a)` at `a : H` are equal by
`ψ.map_id`. The component is the identity, and the naturality isomorphisms are the identities
given by these equalities. -/
-- The body is exposed so that the component of a composite with this transformation is
-- definitionally the component of the other factor, as used by `EquivariantGroupoidLift.pullback`.
@[expose] noncomputable def restrictFiberPullback
    (F : LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ Cat.{v, w}) (ψ : Λ ⥤ Γ) (l : Λ) :
    StrongTrans (((ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.comp F).restrictFiber l)
      (F.restrictFiber (ψ.obj l)) :=
  -- `hmap` identifies the arrows of `LocallyDiscrete (Γ × SingleObj H)` underlying the values of
  -- the two restrictions at `f`.
  have hmap {a b : LocallyDiscrete (SingleObj H)} (f : a ⟶ b) :
      (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.map
          ((Prod.sectR l (SingleObj H)).toPseudofunctor.map f) =
        (Prod.sectR (ψ.obj l) (SingleObj H)).toPseudofunctor.map f := by
    obtain ⟨f⟩ := f
    exact congrArg Quiver.Hom.toLoc (Prod.hom_ext (ψ.map_id l) rfl)
  { app a := eqToHom (restrictFiber_comp_prod_obj F ψ l a)
    naturality {a b} f := eqToIso (by
      have h : (((ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.comp F).restrictFiber l).map f ≫
            eqToHom (restrictFiber_comp_prod_obj F ψ l b) =
          eqToHom (restrictFiber_comp_prod_obj F ψ l a) ≫ (F.restrictFiber (ψ.obj l)).map f :=
        (Category.comp_id _).trans ((congrArg F.map (hmap f)).trans (Category.id_comp _).symm)
      exact h)
    naturality_naturality η := by
      obtain rfl := LocallyDiscrete.eq_of_hom η
      rw [Subsingleton.elim η (𝟙 _)]
      simp
    -- The unit and composition conditions are first proved for arbitrary arrows of
    -- `LocallyDiscrete (Γ × SingleObj H)` and `2`-cells between them, and for a component `t`
    -- equal to the identity; in the goal these arrows are equal but not definitionally equal.
    -- The arrows and `2`-cells are then found by unification with the unfolded goal.
    naturality_id _ := by
      have h {o : LocallyDiscrete (Γ × SingleObj H)} {u₁ u₂ u₃ : o ⟶ o}
          (t : F.obj o ⟶ F.obj o) (ht : t = 𝟙 _) (e : F.map u₁ ≫ t = t ≫ F.map u₂)
          (η₁ : u₂ ⟶ 𝟙 o) (η₂ : u₁ ⟶ u₃) (η₃ : u₃ ⟶ 𝟙 o) :
          (eqToIso e).hom ≫ t ◁ (F.map₂ η₁ ≫ (F.mapId o).hom) =
            (F.map₂ η₂ ≫ F.map₂ η₃ ≫ (F.mapId o).hom) ▷ t ≫ (λ_ t).hom ≫ (ρ_ t).inv := by
        subst ht
        obtain rfl := obj_ext_of_isDiscrete η₂
        obtain rfl := obj_ext_of_isDiscrete η₃
        obtain rfl := obj_ext_of_isDiscrete η₁
        obtain rfl := Subsingleton.elim η₂ (𝟙 _)
        obtain rfl := Subsingleton.elim η₃ η₁
        ext X
        simp
      exact h _ rfl _ _ _ _
    naturality_comp f g := by
      have h {o : LocallyDiscrete (Γ × SingleObj H)} {u₁ u₂ u₃ f₁ f₂ g₁ g₂ : o ⟶ o}
          (t : F.obj o ⟶ F.obj o) (ht : t = 𝟙 _)
          (e₁ : F.map u₁ ≫ t = t ≫ F.map u₂) (e₂ : F.map f₁ ≫ t = t ≫ F.map f₂)
          (e₃ : F.map g₁ ≫ t = t ≫ F.map g₂) (η₁ : u₂ ⟶ f₂ ≫ g₂) (η₂ : u₁ ⟶ u₃)
          (η₃ : u₃ ⟶ f₁ ≫ g₁) (hf : f₁ = f₂) (hg : g₁ = g₂) :
          (eqToIso e₁).hom ≫ t ◁ (F.map₂ η₁ ≫ (F.mapComp f₂ g₂).hom) =
            (F.map₂ η₂ ≫ F.map₂ η₃ ≫ (F.mapComp f₁ g₁).hom) ▷ t ≫ (α_ _ _ _).hom ≫
              F.map f₁ ◁ (eqToIso e₃).hom ≫ (α_ _ _ _).inv ≫ (eqToIso e₂).hom ▷ F.map g₂ ≫
                (α_ _ _ _).hom := by
        subst ht hf hg
        obtain rfl := obj_ext_of_isDiscrete η₂
        obtain rfl := obj_ext_of_isDiscrete η₃
        obtain rfl := obj_ext_of_isDiscrete η₁
        obtain rfl := Subsingleton.elim η₂ (𝟙 _)
        obtain rfl := Subsingleton.elim η₃ η₁
        ext X
        simp
      exact h _ rfl _ _ _ _ _ _ (hmap f) (hmap g) }

end CategoryTheory.Pseudofunctor

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {Λ : Type u₃} [Category.{v₃} Λ]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  (L : EquivariantGroupoidLift Γ actions) (ψ : Λ ⥤ Γ)

/-- The pullback of a coherent equivariant lift `L` along a functor `ψ : Λ ⥤ Γ`: a lift along `Λ`
of the actions `actions (ψ l)`. Its joint pseudofunctor is the composite of `L.joint` with
`ψ × 𝟭 : Λ × SingleObj H ⥤ Γ × SingleObj H`, and its fiber comparison at `l` is the fiber
comparison of `L` at `ψ l`, precomposed with `Pseudofunctor.restrictFiberPullback`. -/
-- The body is exposed so that the fiber comparisons and transport functors of the pullback are
-- definitionally those of `L`, as stated by `pullback_fiberEquivalence` and `pullback_transport`.
@[expose] noncomputable def pullback : EquivariantGroupoidLift Λ (fun l ↦ actions (ψ.obj l)) where
  joint := (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.comp L.joint
  comparison l :=
    (Pseudofunctor.restrictFiberPullback L.joint ψ l).vcomp (L.comparison (ψ.obj l))
  isEquivalence_comparison l := L.isEquivalence_comparison (ψ.obj l)

/-- The fiber comparisons of the pullback along `ψ` are those of `L` at the image of `ψ`. -/
@[simp]
lemma pullback_fiberEquivalence (l : Λ) :
    (L.pullback ψ).fiberEquivalence l = L.fiberEquivalence (ψ.obj l) :=
  rfl

/-- The joint functors `F (g, 1)` of the pullback along `ψ` are those of `L` at `ψ.map g`. -/
@[simp]
lemma pullback_jointMap {l l' : Λ} (g : l ⟶ l') :
    (L.pullback ψ).jointMap g = L.jointMap (ψ.map g) :=
  rfl

/-- The joint functors `F (𝟙 l, a)` of the pullback along `ψ` are those of `L` at `ψ l`; they are
equal, but not definitionally equal, since `ψ.map (𝟙 l)` is not definitionally `𝟙 (ψ l)`. -/
lemma pullback_jointAct (l : Λ) (a : SingleObj.star H ⟶ SingleObj.star H) :
    (L.pullback ψ).jointAct l a = L.jointAct (ψ.obj l) a :=
  congrArg (fun u ↦ (L.joint.map u).toFunctor)
    (congrArg Quiver.Hom.toLoc (Prod.hom_ext (ψ.map_id l) rfl) :
      (ψ.map (𝟙 l) ×ₘ a).toLoc = (𝟙 (ψ.obj l) ×ₘ a).toLoc)

/-- The transport functors of the pullback along `ψ` are those of `L` along the image of `ψ`. -/
@[simp]
lemma pullback_transport {l l' : Λ} (g : l ⟶ l') :
    (L.pullback ψ).transport g = L.transport (ψ.map g) :=
  rfl

/-! ### The unit and composition isomorphisms of transport -/

-- The comparisons of the composite with `ψ × 𝟭` contribute `map₂` of `2`-cells of a locally
-- discrete bicategory, so two composites of them with the same source and target agree.

private lemma map₂_comp_map₂_comp {J : Type*} [Category J] {C : Type*} [Bicategory C]
    (F : LocallyDiscrete J ⥤ᵖ C) {a b : LocallyDiscrete J} {u₁ u₂ u₃ : a ⟶ b}
    {c : F.obj a ⟶ F.obj b} (η₁ : u₁ ⟶ u₂) (η₂ : u₂ ⟶ u₃) (η₃ : u₁ ⟶ u₃) (θ : F.map u₃ ⟶ c) :
    F.map₂ η₁ ≫ F.map₂ η₂ ≫ θ = F.map₂ η₃ ≫ θ := by
  rw [← F.map₂_comp_assoc, Subsingleton.elim (η₁ ≫ η₂) η₃]

private lemma comp_map₂_comp_map₂ {J : Type*} [Category J] {C : Type*} [Bicategory C]
    (F : LocallyDiscrete J ⥤ᵖ C) {a b : LocallyDiscrete J} {u₁ u₂ u₃ : a ⟶ b}
    {c : F.obj a ⟶ F.obj b} (θ : c ⟶ F.map u₁) (η₁ : u₁ ⟶ u₂) (η₂ : u₂ ⟶ u₃) (η₃ : u₁ ⟶ u₃) :
    (θ ≫ F.map₂ η₁) ≫ F.map₂ η₂ = θ ≫ F.map₂ η₃ := by
  rw [Category.assoc, ← F.map₂_comp, Subsingleton.elim (η₁ ≫ η₂) η₃]

/-- The unit comparison of the joint functors of the pullback along `ψ` is the unit comparison
`mapId'` of `L.joint` at `ψ.map (𝟙 l)`. -/
@[simp]
lemma pullback_jointMapId (l : Λ) :
    (L.pullback ψ).jointMapId l = Cat.Hom.toNatIso
      (L.joint.mapId' (ψ.map (𝟙 l) ×ₘ 𝟙 (SingleObj.star H)).toLoc (by rw [ψ.map_id]; rfl)) := by
  ext Y
  exact ((L.pullback ψ).jointMapId_hom_app l Y).trans
    (congrArg (fun α ↦ Cat.Hom₂.toNatTrans α |>.app Y) (map₂_comp_map₂_comp L.joint _ _ _ _))

/-- The composition comparisons of the joint functors of the pullback along `ψ` are those of `L`
along the image of `ψ`. -/
@[simp]
lemma pullback_jointMapComp {l l' l'' : Λ} (g : l ⟶ l') (h : l' ⟶ l'') (gh : l ⟶ l'')
    (hgh : g ≫ h = gh) :
    (L.pullback ψ).jointMapComp g h gh hgh =
      L.jointMapComp (ψ.map g) (ψ.map h) (ψ.map gh) (by rw [← hgh, ψ.map_comp]) := by
  ext Y
  exact ((L.pullback ψ).jointMapComp_hom_app g h gh hgh Y).trans
    ((congrArg (fun α ↦ Cat.Hom₂.toNatTrans α |>.app Y)
      (map₂_comp_map₂_comp L.joint _ _ _ _)).trans (L.jointMapComp_hom_app _ _ _ _ Y).symm)

/-- The composition isomorphisms of transport for the pullback along `ψ` are those of `L`
along the image of `ψ`. -/
@[simp]
lemma pullback_transportComp {l l' l'' : Λ} (g : l ⟶ l') (h : l' ⟶ l'') (gh : l ⟶ l'')
    (hgh : g ≫ h = gh) :
    (L.pullback ψ).transportComp g h gh hgh =
      L.transportComp (ψ.map g) (ψ.map h) (ψ.map gh) (by rw [← hgh, ψ.map_comp]) := by
  ext X
  simp only [transportComp_hom_app, pullback_fiberEquivalence, pullback_jointMapComp]
  -- The two sides differ only in the joint functors `F (ψ.map g, 1)` of the pullback, which are
  -- definitionally the joint functors of `L`.
  rfl

-- The unit isomorphism of transport along an arrow `x` equal to an identity, stated through the
-- unit comparison `mapId'` of the joint pseudofunctor at `x`.
private lemma map_mapId'_comp_counit {p : Γ} (x : p ⟶ p) (hx : x = 𝟙 p) (X : fiber actions p) :
    (L.fiberEquivalence p).functor.map
        ((L.joint.mapId' (x ×ₘ 𝟙 (SingleObj.star H)).toLoc (by rw [hx]; rfl)).hom.toNatTrans.app
          ((L.fiberEquivalence p).inverse.obj X)) ≫ (L.fiberEquivalence p).counit.app X =
      eqToHom (by rw [hx] : (L.transport x).obj X = (L.transport (𝟙 p)).obj X) ≫
        (L.transportId p).hom.app X := by
  subst hx
  rw [eqToHom_refl, Category.id_comp, transportId_hom_app, jointMapId_hom_app]

/-- The unit isomorphism of transport for the pullback along `ψ` is the unit isomorphism of `L`
at `ψ l`, after identifying `ψ.map (𝟙 l)` with `𝟙 (ψ l)`. -/
lemma pullback_transportId_hom_app (l : Λ) (X : fiber actions (ψ.obj l)) :
    ((L.pullback ψ).transportId l).hom.app X =
      eqToHom (by rw [pullback_transport, ψ.map_id]) ≫ (L.transportId (ψ.obj l)).hom.app X := by
  refine ((L.pullback ψ).transportId_hom_app l X).trans ?_
  simp only [pullback_fiberEquivalence, pullback_jointMapId]
  exact L.map_mapId'_comp_counit (ψ.map (𝟙 l)) (ψ.map_id l) X

/-! ### Commuting transport with the actions -/

-- The components of the naturality isomorphisms of a composite of strong transformations into
-- `Cat` whose first factor has identity component and naturality isomorphisms `eqToIso e`.

private lemma vcomp_eqToIso_naturality_hom_app {A B : Cat.{v, w}} {F₁ F₂ : A ⟶ A} {T : B ⟶ B}
    (e : F₁ ≫ 𝟙 A = 𝟙 A ≫ F₂) (s : A ⟶ B) (ν : F₂ ≫ s ⟶ s ≫ T) (Y : A)
    (h : F₁.toFunctor.obj Y = F₂.toFunctor.obj Y) :
    ((α_ F₁ (𝟙 A) s).inv ≫ (eqToIso e).hom ▷ s ≫ (α_ (𝟙 A) F₂ s).hom ≫ 𝟙 A ◁ ν ≫
        (α_ (𝟙 A) s T).inv).toNatTrans.app Y =
      s.toFunctor.map (eqToHom h) ≫ ν.toNatTrans.app Y := by
  simp [eqToHom_map]

private lemma vcomp_eqToIso_naturality_inv_app {A B : Cat.{v, w}} {F₁ F₂ : A ⟶ A} {T : B ⟶ B}
    (e : F₁ ≫ 𝟙 A = 𝟙 A ≫ F₂) (s : A ⟶ B) (ν : s ≫ T ⟶ F₂ ≫ s) (Y : A)
    (h : F₂.toFunctor.obj Y = F₁.toFunctor.obj Y) :
    (((((α_ (𝟙 A) s T).hom ≫ 𝟙 A ◁ ν) ≫ (α_ (𝟙 A) F₂ s).inv) ≫ (eqToIso e).inv ▷ s) ≫
        (α_ F₁ (𝟙 A) s).hom).toNatTrans.app Y =
      ν.toNatTrans.app Y ≫ s.toFunctor.map (eqToHom h) := by
  simp [eqToHom_map]

/-- The naturality isomorphisms of the fiber comparisons of the pullback along `ψ` are those of
`L` at `ψ l`, after identifying `ψ.map (𝟙 l)` with `𝟙 (ψ l)`. -/
lemma pullback_comparisonNaturality_hom_app (l : Λ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber (ψ.obj l)) :
    ((L.pullback ψ).comparisonNaturality l a).hom.app Y =
      (L.fiberEquivalence (ψ.obj l)).functor.map (eqToHom (by rw [ψ.map_id] :
          (L.joint.map (ψ.map (𝟙 l) ×ₘ a).toLoc).toFunctor.obj Y =
            (L.jointAct (ψ.obj l) a).obj Y)) ≫
        (L.comparisonNaturality (ψ.obj l) a).hom.app Y := by
  refine ((L.pullback ψ).comparisonNaturality_hom_app l a Y).trans
    ((vcomp_eqToIso_naturality_hom_app (F₁ := L.joint.map (ψ.map (𝟙 l) ×ₘ a).toLoc)
      (F₂ := L.joint.map (𝟙 (ψ.obj l) ×ₘ a).toLoc) (by simp)
      ((L.comparison (ψ.obj l)).app ⟨SingleObj.star H⟩)
      ((L.comparison (ψ.obj l)).naturality a.toLoc).hom Y (by rw [ψ.map_id])).trans ?_)
  rw [comparisonNaturality_hom_app]
  -- `(L.fiberEquivalence _).functor` is definitionally the component of the fiber comparison.
  rfl

/-- The inverses of the naturality isomorphisms of the fiber comparisons of the pullback along
`ψ` are those of `L` at `ψ l`, after identifying `ψ.map (𝟙 l)` with `𝟙 (ψ l)`. -/
lemma pullback_comparisonNaturality_inv_app (l : Λ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber (ψ.obj l)) :
    ((L.pullback ψ).comparisonNaturality l a).inv.app Y =
      (L.comparisonNaturality (ψ.obj l) a).inv.app Y ≫
        (L.fiberEquivalence (ψ.obj l)).functor.map (eqToHom (by rw [ψ.map_id] :
          (L.jointAct (ψ.obj l) a).obj Y =
            (L.joint.map (ψ.map (𝟙 l) ×ₘ a).toLoc).toFunctor.obj Y)) := by
  refine ((L.pullback ψ).comparisonNaturality_inv_app l a Y).trans
    ((vcomp_eqToIso_naturality_inv_app (F₁ := L.joint.map (ψ.map (𝟙 l) ×ₘ a).toLoc)
      (F₂ := L.joint.map (𝟙 (ψ.obj l) ×ₘ a).toLoc) (by simp)
      ((L.comparison (ψ.obj l)).app ⟨SingleObj.star H⟩)
      ((L.comparison (ψ.obj l)).naturality a.toLoc).inv Y (by rw [ψ.map_id])).trans ?_)
  rw [comparisonNaturality_inv_app]
  -- As in `pullback_comparisonNaturality_hom_app`.
  rfl

-- The commuting isomorphism of the joint functors, stated through the composition comparisons
-- `mapComp'` of the joint pseudofunctor at arrows `x` and `x'` equal to identities.
private lemma mapComp'_inv_comp_mapComp'_hom_app {p q : Γ} (g : p ⟶ q) (x : p ⟶ p)
    (x' : q ⟶ q) (hx : x = 𝟙 p) (hx' : x' = 𝟙 q) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber p) :
    (L.joint.mapComp' (x ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
          (by subst hx; simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app Y ≫
        (L.joint.mapComp' (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (x' ×ₘ a).toLoc (g ×ₘ a).toLoc
          (by subst hx'; simp [← Quiver.Hom.comp_toLoc])).hom.toNatTrans.app Y =
      (L.jointMap g).map (eqToHom (by subst hx; rfl :
          (L.joint.map (x ×ₘ a).toLoc).toFunctor.obj Y = (L.jointAct p a).obj Y)) ≫
        (L.jointActCommIso g a).hom.app Y ≫ eqToHom (by subst hx'; rfl :
          (L.jointAct q a).obj ((L.jointMap g).obj Y) =
            (L.joint.map (x' ×ₘ a).toLoc).toFunctor.obj ((L.jointMap g).obj Y)) := by
  subst hx hx'
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact (L.jointActCommIso_hom_app g a Y).symm

/-- The commuting isomorphisms of the joint functors of the pullback along `ψ` are those of `L`
along the image of `ψ`, after identifying `ψ.map (𝟙 l)` with `𝟙 (ψ l)`. -/
lemma pullback_jointActCommIso_hom_app {l l' : Λ} (g : l ⟶ l')
    (a : SingleObj.star H ⟶ SingleObj.star H) (Y : L.jointFiber (ψ.obj l)) :
    ((L.pullback ψ).jointActCommIso g a).hom.app Y =
      (L.jointMap (ψ.map g)).map (eqToHom (by rw [ψ.map_id] :
          (L.joint.map (ψ.map (𝟙 l) ×ₘ a).toLoc).toFunctor.obj Y =
            (L.jointAct (ψ.obj l) a).obj Y)) ≫
        (L.jointActCommIso (ψ.map g) a).hom.app Y ≫ eqToHom (by rw [ψ.map_id] :
          (L.jointAct (ψ.obj l') a).obj ((L.jointMap (ψ.map g)).obj Y) =
            (L.joint.map (ψ.map (𝟙 l') ×ₘ a).toLoc).toFunctor.obj
              ((L.jointMap (ψ.map g)).obj Y)) :=
  ((L.pullback ψ).jointActCommIso_hom_app g a Y).trans
    ((congrArg₂ (· ≫ ·) (congrArg (fun α ↦ Cat.Hom₂.toNatTrans α |>.app Y)
      (comp_map₂_comp_map₂ L.joint _ _ _ _))
      (congrArg (fun α ↦ Cat.Hom₂.toNatTrans α |>.app Y)
        (map₂_comp_map₂_comp L.joint _ _ _ _))).trans
      (L.mapComp'_inv_comp_mapComp'_hom_app (ψ.map g) _ _ (ψ.map_id l) (ψ.map_id l') a Y))

-- The correction terms `eqToHom` of `pullback_comparisonNaturality_inv_app` and
-- `pullback_jointActCommIso_hom_app` cancel across the unit of the fiber comparison.
private lemma map_map_unitInv_eqToHom {C D C' D' : Type*} [Category C] [Category D]
    [Category C'] [Category D'] (e : C ≌ D) (G : C ⥤ C') (e' : C' ⥤ D') {A B : C} (h : A = B)
    {P₁ P₂ : D} (u₁ : P₁ ⟶ P₂) (u₂ : P₂ ⟶ e.functor.obj A) {Q R : C'} (k : G.obj A ⟶ Q)
    (h' : Q = R) {S : D'} (m : e'.obj Q ⟶ S) :
    e'.map (G.map (e.inverse.map (u₁ ≫ u₂ ≫ e.functor.map (eqToHom h)) ≫ e.unitInv.app B) ≫
        G.map (eqToHom h.symm) ≫ k ≫ eqToHom h') ≫ e'.map (eqToHom h'.symm) ≫ m =
      e'.map (G.map (e.inverse.map (u₁ ≫ u₂) ≫ e.unitInv.app A) ≫ k) ≫ m := by
  subst h h'
  simp

/-- The isomorphisms commuting transport with the actions for the pullback along `ψ` are those
of `L` along the image of `ψ`. -/
@[simp]
lemma pullback_transportCommIso {l l' : Λ} (g : l ⟶ l')
    (a : SingleObj.star H ⟶ SingleObj.star H) :
    (L.pullback ψ).transportCommIso g a = L.transportCommIso (ψ.map g) a := by
  ext X
  simp only [transportCommIso_hom_app, actInverseIso_hom_app, pullback_fiberEquivalence,
    pullback_jointMap, pullback_comparisonNaturality_hom_app]
  -- `simp` does not use the next two lemmas, whose objects match those of the goal only up to
  -- unfolding the pullback, so they are rewritten at the objects of the goal.
  rw [L.pullback_comparisonNaturality_inv_app ψ l a ((L.fiberEquivalence (ψ.obj l)).inverse.obj X),
    L.pullback_jointActCommIso_hom_app ψ g a ((L.fiberEquivalence (ψ.obj l)).inverse.obj X)]
  exact map_map_unitInv_eqToHom _ _ _ _ _ _ _ _ _

end TauCeti.EquivariantGroupoidLift
