/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Prelax functors and locally discrete bicategories

In a locally discrete bicategory every `2`-morphism `η : f ⟶ g` forces `f = g`, so a prelax
functor (in particular a pseudofunctor) sends `η` to an `eqToHom`. This lets the coherence
data of a pseudofunctor out of `LocallyDiscrete B₀`, such as `F.map₂ (α_ f g h).hom`, be
computed componentwise.

Dually, the unit and composition comparisons of a pseudofunctor `P` into a locally discrete
bicategory are determined by equalities of `1`-morphisms. So the comparisons of a composite
`P.comp F` are the flexible comparisons `F.mapId'` and `F.mapComp'` of `F` at the images of
`P`, for instance for `P = Functor.toPseudofunctor ψ` induced by a functor of categories.
Consequently, pulling `F : LocallyDiscrete Λ ⥤ᵖ C` back along the identity functor, or along a
composite `f ⋙ g` instead of first along `g` and then along `f`, does not change its unit and
composition comparisons.

Finally, `CategoryTheory.LocallyDiscrete.mkCatPseudofunctor` builds a pseudofunctor
`LocallyDiscrete B₀ ⥤ᵖ Cat` from functors, unit isomorphisms and composition isomorphisms
`map fg ≅ map f ⋙ map g` given at arbitrary factorizations `f ≫ g = fg`, from componentwise
associativity and unit laws.
-/

@[expose] public section

namespace CategoryTheory.PrelaxFunctor

open Bicategory

/-- A prelax functor out of a locally discrete bicategory sends every `2`-morphism to an
`eqToHom`. -/
lemma map₂_eq_eqToHom {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (F : PrelaxFunctor B C) {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    F.map₂ η = eqToHom (by rw [obj_ext_of_isDiscrete η]) := by
  obtain rfl := obj_ext_of_isDiscrete η
  rw [Subsingleton.elim η (𝟙 f)]
  simp

/-- A prelax functor out of a locally discrete bicategory sends a composite of two `2`-morphisms
to the image of any `2`-morphism with the same source and target. -/
@[reassoc]
lemma map₂_comp_map₂ {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (F : PrelaxFunctor B C) {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (ι : f ⟶ h) :
    F.map₂ η ≫ F.map₂ θ = F.map₂ ι := by
  simp [map₂_eq_eqToHom]

end CategoryTheory.PrelaxFunctor

namespace CategoryTheory.Pseudofunctor

open Bicategory

variable {B₀ : Type*} [Bicategory B₀] {B₁ : Type*} [Bicategory B₁] [IsLocallyDiscrete B₁]
  {C : Type*} [Bicategory C] (P : B₀ ⥤ᵖ B₁) (F : B₁ ⥤ᵖ C)

/-- The unit comparison of the composite of a pseudofunctor `P` into a locally discrete
bicategory with `F` is the unit comparison of `F` at the `1`-morphism `P.map (𝟙 a)`, which
equals `𝟙 (P.obj a)`. -/
lemma comp_mapId_eq_mapId' (a : B₀) :
    (P.comp F).mapId a = F.mapId' (P.map (𝟙 a)) (obj_ext_of_isDiscrete (P.mapId a).hom) := by
  have h : P.mapId a = eqToIso (obj_ext_of_isDiscrete (P.mapId a).hom) :=
    Iso.ext (Subsingleton.elim _ _)
  rw [comp_mapId, h]
  -- `F.mapId' u hu` is by definition `F.map₂Iso (eqToIso _) ≪≫ F.mapId _`.
  rfl

/-- The composition comparison of the composite of a pseudofunctor `P` into a locally discrete
bicategory with `F` is the composition comparison of `F` at the factorization
`P.map f ≫ P.map g = P.map (f ≫ g)`. -/
lemma comp_mapComp_eq_mapComp' {a b c : B₀} (f : a ⟶ b) (g : b ⟶ c) :
    (P.comp F).mapComp f g = F.mapComp' (P.map f) (P.map g) (P.map (f ≫ g))
      (obj_ext_of_isDiscrete (P.mapComp f g).hom).symm := by
  have h : P.mapComp f g = eqToIso (obj_ext_of_isDiscrete (P.mapComp f g).hom) :=
    Iso.ext (Subsingleton.elim _ _)
  rw [comp_mapComp, h]
  -- `F.mapComp' u v w huv` is by definition `F.map₂Iso (eqToIso _) ≪≫ F.mapComp u v`.
  rfl

/-- The flexible unit comparison of the composite of a pseudofunctor `P` into a locally discrete
bicategory with `F`, at a `1`-morphism `u` equal to an identity, is the flexible unit comparison
of `F` at `P.map u`. -/
lemma comp_mapId'_eq_mapId' {a : B₀} (u : a ⟶ a) (hu : u = 𝟙 a) :
    (P.comp F).mapId' u hu =
      F.mapId' (P.map u) (by subst hu; exact obj_ext_of_isDiscrete (P.mapId a).hom) := by
  subst hu
  rw [mapId'_eq_mapId, comp_mapId_eq_mapId']

/-- The flexible composition comparison of the composite of a pseudofunctor `P` into a locally
discrete bicategory with `F` is the flexible composition comparison of `F` at the images under
`P`. -/
lemma comp_mapComp'_eq_mapComp' {a b c : B₀} (u : a ⟶ b) (v : b ⟶ c) (uv : a ⟶ c)
    (huv : u ≫ v = uv) :
    (P.comp F).mapComp' u v uv huv = F.mapComp' (P.map u) (P.map v) (P.map uv)
      (by subst huv; exact (obj_ext_of_isDiscrete (P.mapComp u v).hom).symm) := by
  subst huv
  rw [mapComp'_eq_mapComp, comp_mapComp_eq_mapComp']

/-! ### Pulling back along identities and composites of functors -/

section ToPseudofunctor

variable {Γ : Type*} [Category Γ] {Λ : Type*} [Category Λ] {Λ' : Type*} [Category Λ']
  {C : Type*} [Bicategory C]

-- The two sides of the following four lemmas have definitionally equal, but not syntactically
-- equal, types: `((𝟭 Γ).toPseudofunctor.comp F).obj x` unfolds to `F.obj x`, and similarly for
-- the composite functor.

/-- Pulling back along the identity functor does not change the unit comparisons. -/
lemma toPseudofunctor_id_comp_mapId (F : LocallyDiscrete Γ ⥤ᵖ C) (x : LocallyDiscrete Γ) :
    ((𝟭 Γ).toPseudofunctor.comp F).mapId x = F.mapId x := by
  rw [comp_mapId_eq_mapId']
  exact F.mapId'_eq_mapId x

/-- Pulling back along the identity functor does not change the composition comparisons. -/
lemma toPseudofunctor_id_comp_mapComp (F : LocallyDiscrete Γ ⥤ᵖ C) {x y z : LocallyDiscrete Γ}
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    ((𝟭 Γ).toPseudofunctor.comp F).mapComp φ ψ = F.mapComp φ ψ := by
  rw [comp_mapComp_eq_mapComp']
  exact F.mapComp'_eq_mapComp φ ψ

/-- Pulling back along a composite functor `f ⋙ g` has the same unit comparisons as pulling back
along `g` and then along `f`. -/
lemma toPseudofunctor_comp_comp_mapId (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') (F : LocallyDiscrete Λ' ⥤ᵖ C)
    (x : LocallyDiscrete Γ) :
    ((f ⋙ g).toPseudofunctor.comp F).mapId x =
      (f.toPseudofunctor.comp (g.toPseudofunctor.comp F)).mapId x := by
  rw [comp_mapId_eq_mapId', comp_mapId_eq_mapId', comp_mapId'_eq_mapId']
  -- Both sides are `F.mapId'` at the same arrow `(g.map (f.map (𝟙 x.as))).toLoc`.
  rfl

/-- Pulling back along a composite functor `f ⋙ g` has the same composition comparisons as
pulling back along `g` and then along `f`. -/
lemma toPseudofunctor_comp_comp_mapComp (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') (F : LocallyDiscrete Λ' ⥤ᵖ C)
    {x y z : LocallyDiscrete Γ} (φ : x ⟶ y) (ψ : y ⟶ z) :
    ((f ⋙ g).toPseudofunctor.comp F).mapComp φ ψ =
      (f.toPseudofunctor.comp (g.toPseudofunctor.comp F)).mapComp φ ψ := by
  rw [comp_mapComp_eq_mapComp', comp_mapComp_eq_mapComp', comp_mapComp'_eq_mapComp']
  -- Both sides are `F.mapComp'` at the same arrows of `LocallyDiscrete Λ'`.
  rfl

end ToPseudofunctor

end CategoryTheory.Pseudofunctor

namespace CategoryTheory.LocallyDiscrete

open Bicategory

universe v u

variable {B₀ : Type*} [Category B₀] {obj : B₀ → Cat.{v, u}}
  {map : ∀ {b b' : B₀}, (b ⟶ b') → (obj b ⥤ obj b')}

/-- Associativity of composition isomorphisms `map f ⋙ map g ≅ map fg` of a family of functors,
given at arbitrary factorizations, implies the associativity of their inverses. -/
@[reassoc]
lemma inv_associativity_of_hom_associativity
    (mapComp : ∀ {b₀ b₁ b₂ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂), f ≫ g = fg →
      (map f ⋙ map g ≅ map fg))
    (associativity : ∀ {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃)
      (fg : b₀ ⟶ b₂) (gh : b₁ ⟶ b₃) (fgh : b₀ ⟶ b₃) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
      (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh) (x : obj b₀),
      (map h).map ((mapComp f g fg hfg).hom.app x) ≫ (mapComp fg h fgh hfgh).hom.app x =
        (mapComp g h gh hgh).hom.app ((map f).obj x) ≫ (mapComp f gh fgh hfgh').hom.app x)
    {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃)
    (fg : b₀ ⟶ b₂) (gh : b₁ ⟶ b₃) (fgh : b₀ ⟶ b₃) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh) (x : obj b₀) :
    (mapComp fg h fgh hfgh).inv.app x ≫ (map h).map ((mapComp f g fg hfg).inv.app x) =
      (mapComp f gh fgh hfgh').inv.app x ≫ (mapComp g h gh hgh).inv.app ((map f).obj x) := by
  have := congrArg Iso.inv (Iso.ext (associativity f g h fg gh fgh hfg hgh hfgh hfgh' x) :
    (map h).mapIso ((mapComp f g fg hfg).app x) ≪≫ (mapComp fg h fgh hfgh).app x =
      (mapComp g h gh hgh).app ((map f).obj x) ≪≫ (mapComp f gh fgh hfgh').app x)
  simpa using this

variable (map) (mapId : ∀ b : B₀, map (𝟙 b) ≅ 𝟭 (obj b))
  (mapComp : ∀ {b₀ b₁ b₂ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂), f ≫ g = fg →
    (map fg ≅ map f ⋙ map g))

-- The three lemmas below are the coherence conditions of `mkCatPseudofunctor`. In them the
-- composite arrows of `B₀` appear in two forms that agree only propositionally (for instance
-- `(f ≫ g) ≫ h` and `f ≫ g ≫ h`), so they are stated for arbitrary composites, related by
-- `eqToHom`.

private lemma mapComp_associativity_eqToHom
    (associativity : ∀ {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃)
      (fg : b₀ ⟶ b₂) (gh : b₁ ⟶ b₃) (fgh : b₀ ⟶ b₃) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
      (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh) (x : obj b₀),
      (mapComp fg h fgh hfgh).hom.app x ≫ (map h).map ((mapComp f g fg hfg).hom.app x) =
        (mapComp f gh fgh hfgh').hom.app x ≫ (mapComp g h gh hgh).hom.app ((map f).obj x))
    {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃) (fg : b₀ ⟶ b₂)
    (gh : b₁ ⟶ b₃) (fgh fgh' : b₀ ⟶ b₃) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh') (x : obj b₀)
    (hx : (map fgh).obj x = (map fgh').obj x) :
    (mapComp fg h fgh hfgh).hom.app x ≫ (map h).map ((mapComp f g fg hfg).hom.app x) ≫
        (mapComp g h gh hgh).inv.app ((map f).obj x) ≫ (mapComp f gh fgh' hfgh').inv.app x =
      eqToHom hx := by
  obtain rfl : fgh' = fgh := by rw [← hfgh', ← hfgh, ← hfg, ← hgh, Category.assoc]
  rw [← Category.assoc, associativity f g h fg gh fgh' hfg hgh hfgh hfgh' x]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, eqToHom_refl]

private lemma mapComp_left_unitality_eqToHom
    (left_unitality : ∀ {b₀ b₁ : B₀} (f : b₀ ⟶ b₁) (hf : 𝟙 b₀ ≫ f = f) (x : obj b₀),
      (mapComp (𝟙 b₀) f f hf).hom.app x ≫ (map f).map ((mapId b₀).hom.app x) = 𝟙 _)
    {b₀ b₁ : B₀} (f k : b₀ ⟶ b₁) (hk : 𝟙 b₀ ≫ f = k) (x : obj b₀)
    (hx : (map k).obj x = (map f).obj x) :
    (mapComp (𝟙 b₀) f k hk).hom.app x ≫ (map f).map ((mapId b₀).hom.app x) = eqToHom hx := by
  obtain rfl : k = f := hk.symm.trans (Category.id_comp f)
  rw [left_unitality, eqToHom_refl]

private lemma mapComp_right_unitality_eqToHom
    (right_unitality : ∀ {b₀ b₁ : B₀} (f : b₀ ⟶ b₁) (hf : f ≫ 𝟙 b₁ = f) (x : obj b₀),
      (mapComp f (𝟙 b₁) f hf).hom.app x ≫ (mapId b₁).hom.app ((map f).obj x) = 𝟙 _)
    {b₀ b₁ : B₀} (f k : b₀ ⟶ b₁) (hk : f ≫ 𝟙 b₁ = k) (x : obj b₀)
    (hx : (map k).obj x = (map f).obj x) :
    (mapComp f (𝟙 b₁) k hk).hom.app x ≫ (mapId b₁).hom.app ((map f).obj x) = eqToHom hx := by
  obtain rfl : k = f := hk.symm.trans (Category.comp_id f)
  rw [right_unitality, eqToHom_refl]

/-- Constructor for pseudofunctors `LocallyDiscrete B₀ ⥤ᵖ Cat` with value `obj b` at `b`, from
functors `map f`, unit isomorphisms `map (𝟙 b) ≅ 𝟭` and composition isomorphisms
`map fg ≅ map f ⋙ map g` at arbitrary factorizations `f ≫ g = fg`. Since the coherence
conditions are required at arbitrary factorizations, they are stated componentwise without the
`eqToHom` relating `(f ≫ g) ≫ h` and `f ≫ g ≫ h`. -/
def mkCatPseudofunctor
    (associativity : ∀ {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃)
      (fg : b₀ ⟶ b₂) (gh : b₁ ⟶ b₃) (fgh : b₀ ⟶ b₃) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
      (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh) (x : obj b₀),
      (mapComp fg h fgh hfgh).hom.app x ≫ (map h).map ((mapComp f g fg hfg).hom.app x) =
        (mapComp f gh fgh hfgh').hom.app x ≫ (mapComp g h gh hgh).hom.app ((map f).obj x))
    (left_unitality : ∀ {b₀ b₁ : B₀} (f : b₀ ⟶ b₁) (hf : 𝟙 b₀ ≫ f = f) (x : obj b₀),
      (mapComp (𝟙 b₀) f f hf).hom.app x ≫ (map f).map ((mapId b₀).hom.app x) = 𝟙 _)
    (right_unitality : ∀ {b₀ b₁ : B₀} (f : b₀ ⟶ b₁) (hf : f ≫ 𝟙 b₁ = f) (x : obj b₀),
      (mapComp f (𝟙 b₁) f hf).hom.app x ≫ (mapId b₁).hom.app ((map f).obj x) = 𝟙 _) :
    LocallyDiscrete B₀ ⥤ᵖ Cat.{v, u} :=
  mkPseudofunctor obj (fun f ↦ (map f).toCatHom) (fun b ↦ Cat.Hom.isoMk (mapId b))
    (fun f g ↦ Cat.Hom.isoMk (mapComp f g (f ≫ g) rfl))
    (fun f g h ↦ by
      ext x
      simp only [Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv,
        Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans, Cat.associator_hom_toNatTrans,
        Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
        Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, NatTrans.toCatHom₂_toNatTrans,
        Functor.toCatHom_toFunctor, Cat.Hom.comp_toFunctor, Functor.comp_obj]
      exact mapComp_associativity_eqToHom map mapComp associativity _ _ _ _ _ _ _ _ _ _ _ _ _)
    (fun f ↦ by
      ext x
      simp only [Cat.Hom.isoMk_hom, Cat.Hom.toNatTrans_comp,
        Cat.whiskerRight_toNatTrans, Cat.leftUnitor_hom_toNatTrans, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Cat.Hom₂.eqToHom_toNatTrans,
        eqToHom_app, NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor, Functor.comp_obj, Cat.Hom.id_toFunctor]
      -- The left unitor of `Cat` contributes an identity whose object is only definitionally
      -- that of the goal, so it is removed through `congrArg` rather than by `rw`.
      exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
        (mapComp_left_unitality_eqToHom map mapId mapComp left_unitality _ _ _ _ _))
    (fun f ↦ by
      ext x
      simp only [Cat.Hom.isoMk_hom, Cat.Hom.toNatTrans_comp,
        Cat.whiskerLeft_toNatTrans, Cat.rightUnitor_hom_toNatTrans, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Cat.Hom₂.eqToHom_toNatTrans,
        eqToHom_app, NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor, Functor.comp_obj, Cat.Hom.id_toFunctor]
      -- As for the left unitor.
      exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
        (mapComp_right_unitality_eqToHom map mapId mapComp right_unitality _ _ _ _ _))

section

variable {mapId mapComp}
  {associativity : ∀ {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃)
    (fg : b₀ ⟶ b₂) (gh : b₁ ⟶ b₃) (fgh : b₀ ⟶ b₃) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh) (x : obj b₀),
    (mapComp fg h fgh hfgh).hom.app x ≫ (map h).map ((mapComp f g fg hfg).hom.app x) =
      (mapComp f gh fgh hfgh').hom.app x ≫ (mapComp g h gh hgh).hom.app ((map f).obj x)}
  {left_unitality : ∀ {b₀ b₁ : B₀} (f : b₀ ⟶ b₁) (hf : 𝟙 b₀ ≫ f = f) (x : obj b₀),
    (mapComp (𝟙 b₀) f f hf).hom.app x ≫ (map f).map ((mapId b₀).hom.app x) = 𝟙 _}
  {right_unitality : ∀ {b₀ b₁ : B₀} (f : b₀ ⟶ b₁) (hf : f ≫ 𝟙 b₁ = f) (x : obj b₀),
    (mapComp f (𝟙 b₁) f hf).hom.app x ≫ (mapId b₁).hom.app ((map f).obj x) = 𝟙 _}

@[simp]
lemma mkCatPseudofunctor_obj (b : LocallyDiscrete B₀) :
    (mkCatPseudofunctor map mapId mapComp associativity left_unitality right_unitality).obj b =
      obj b.as :=
  rfl

@[simp]
lemma mkCatPseudofunctor_map_toFunctor {b b' : LocallyDiscrete B₀} (f : b ⟶ b') :
    ((mkCatPseudofunctor map mapId mapComp associativity left_unitality right_unitality).map
      f).toFunctor = map f.as :=
  rfl

@[simp]
lemma mkCatPseudofunctor_mapId_hom_toNatTrans_app (b : LocallyDiscrete B₀) (x : obj b.as) :
    ((mkCatPseudofunctor map mapId mapComp associativity left_unitality right_unitality).mapId
      b).hom.toNatTrans.app x = (mapId b.as).hom.app x :=
  rfl

@[simp]
lemma mkCatPseudofunctor_mapId_inv_toNatTrans_app (b : LocallyDiscrete B₀) (x : obj b.as) :
    ((mkCatPseudofunctor map mapId mapComp associativity left_unitality right_unitality).mapId
      b).inv.toNatTrans.app x = (mapId b.as).inv.app x :=
  rfl

@[simp]
lemma mkCatPseudofunctor_mapComp_hom_toNatTrans_app {b₀ b₁ b₂ : LocallyDiscrete B₀}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (x : obj b₀.as) :
    ((mkCatPseudofunctor map mapId mapComp associativity left_unitality right_unitality).mapComp
      f g).hom.toNatTrans.app x = (mapComp f.as g.as (f.as ≫ g.as) rfl).hom.app x :=
  rfl

@[simp]
lemma mkCatPseudofunctor_mapComp_inv_toNatTrans_app {b₀ b₁ b₂ : LocallyDiscrete B₀}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (x : obj b₀.as) :
    ((mkCatPseudofunctor map mapId mapComp associativity left_unitality right_unitality).mapComp
      f g).inv.toNatTrans.app x = (mapComp f.as g.as (f.as ≫ g.as) rfl).inv.app x :=
  rfl

end

end CategoryTheory.LocallyDiscrete
