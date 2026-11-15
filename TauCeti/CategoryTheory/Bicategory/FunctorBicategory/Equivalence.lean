/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Pointwise equivalences in the bicategory of pseudofunctors

Let `B` and `C` be bicategories and let `η : F ⟶ G` be a strong transformation between
pseudofunctors `F G : B ⥤ᵖ C`. If each component `η.app a : F.obj a ⟶ G.obj a` is equipped with
an inverse `1`-morphism `inv a : G.obj a ⟶ F.obj a` and unit and counit `2`-isomorphisms
`𝟙 (F.obj a) ≅ η.app a ≫ inv a` and `inv a ≫ η.app a ≅ 𝟙 (G.obj a)`, then `η` extends to an
adjoint equivalence `F ≌ G` in the bicategory of pseudofunctors, strong transformations and
modifications.

For a `1`-morphism `f : a ⟶ b`, the naturality `2`-isomorphism
`G.map f ≫ inv b ≅ inv a ≫ F.map f` of the inverse strong transformation is the inverse of the
mate `mateEquiv (adj a) (adj b) (η.naturality f).hom` across the component adjunctions
`adj a : η.app a ⊣ inv a`. Because the component units and counits are invertible, this mate is
an isomorphism (`Bicategory.isIso_mateEquiv`, `Bicategory.Equivalence.mateIso`). Compatibility of
mates with whiskering, identity cells and vertical pasting then yields the strong-transformation
axioms for the inverse and the modification axioms for the unit and counit.

## Main declarations

* `CategoryTheory.Bicategory.isIso_mateEquiv`: the mate of an invertible `2`-cell across two
  adjunctions with invertible unit and counit is invertible;
* `CategoryTheory.Bicategory.mateEquiv_whiskerRight_comp`,
  `CategoryTheory.Bicategory.mateEquiv_comp_whiskerLeft`: naturality of `mateEquiv` in the
  vertical `1`-morphisms;
* `CategoryTheory.Bicategory.Equivalence.mateIso`: the mate isomorphism
  `e₁.inv ≫ g ≅ h ≫ e₂.inv` induced by `g ≫ e₂.hom ≅ e₁.hom ≫ h` across adjoint equivalences;
* `CategoryTheory.Pseudofunctor.StrongTrans.equivalenceOfComponents`: an adjoint equivalence
  `F ≌ G` built from component equivalence data satisfying the left triangle identity, preserving
  both the component `1`-morphisms and the component unit and counit `2`-isomorphisms;
* `CategoryTheory.Pseudofunctor.StrongTrans.mkEquivalence`: the variant that adjointifies
  arbitrary component unit and counit `2`-isomorphisms before assembling `F ≌ G`.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapters 4 and 6: strong transformations,
  modifications, mates and pointwise equivalences.
-/

public section

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

/-- The mate of an invertible `2`-morphism across adjunctions `l₁ ⊣ r₁` and `l₂ ⊣ r₂` is
invertible whenever the unit of the second adjunction and the counit of the first are invertible. -/
instance isIso_mateEquiv {c d e f : B} {g : c ⟶ e} {h : d ⟶ f}
    {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e}
    (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) [IsIso adj₂.unit] [IsIso adj₁.counit]
    (α : g ≫ l₂ ⟶ l₁ ≫ h) [IsIso α] :
    IsIso (mateEquiv adj₁ adj₂ α) := by
  rw [mateEquiv_apply, Adjunction.homEquiv₂_apply, Adjunction.homEquiv₁_apply]
  infer_instance

/-- Taking mates commutes with pre-whiskering the top vertical `1`-morphism by a `2`-cell. -/
@[reassoc]
lemma mateEquiv_whiskerRight_comp {c d e f : B} {g g' : c ⟶ e} {h : d ⟶ f}
    {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e}
    (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (ξ : g ⟶ g') (α : g' ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv adj₁ adj₂ (ξ ▷ l₂ ≫ α) = r₁ ◁ ξ ≫ mateEquiv adj₁ adj₂ α := by
  simp only [mateEquiv_apply']
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ (g ◁ adj₂.unit ≫ ξ ▷ (l₂ ≫ r₂)) ⊗≫ r₁ ◁ α ▷ r₂ ⊗≫
          adj₁.counit ▷ h ▷ r₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

/-- Taking mates commutes with post-whiskering the bottom vertical `1`-morphism by a `2`-cell. -/
@[reassoc]
lemma mateEquiv_comp_whiskerLeft {c d e f : B} {g : c ⟶ e} {h h' : d ⟶ f}
    {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e}
    (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (α : g ≫ l₂ ⟶ l₁ ≫ h) (ζ : h ⟶ h') :
    mateEquiv adj₁ adj₂ (α ≫ l₁ ◁ ζ) = mateEquiv adj₁ adj₂ α ≫ ζ ▷ r₂ := by
  simp only [mateEquiv_apply']
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ⊗≫ r₁ ◁ α ▷ r₂ ⊗≫
          ((r₁ ≫ l₁) ◁ ζ ≫ adj₁.counit ▷ h') ▷ r₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

namespace Equivalence

/-- The mate of a `2`-isomorphism `g ≫ e₂.hom ≅ e₁.hom ≫ h` across adjoint equivalences
`e₁ : c ≌ d` and `e₂ : e ≌ f` is a `2`-isomorphism `e₁.inv ≫ g ≅ h ≫ e₂.inv`. -/
@[expose] noncomputable def mateIso {c d e f : B} {g : c ⟶ e} {h : d ⟶ f}
    (e₁ : c ≌ d) (e₂ : e ≌ f) (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    e₁.inv ≫ g ≅ h ≫ e₂.inv :=
  haveI : IsIso e₂.adj.unit := inferInstanceAs (IsIso e₂.unit.hom)
  haveI : IsIso e₁.adj.counit := inferInstanceAs (IsIso e₁.counit.hom)
  asIso (mateEquiv e₁.adj e₂.adj α.hom)

@[simp]
lemma mateIso_hom {c d e f : B} {g : c ⟶ e} {h : d ⟶ f}
    (e₁ : c ≌ d) (e₂ : e ≌ f) (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    (mateIso e₁ e₂ α).hom = mateEquiv e₁.adj e₂.adj α.hom :=
  (rfl)

end Equivalence

end CategoryTheory.Bicategory

namespace CategoryTheory.Pseudofunctor.StrongTrans

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {F G : B ⥤ᵖ C}

section Helper

variable (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
  (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
  (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
  (left_triangle : ∀ a : B,
    leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)

private abbrev compEquiv (a : B) : F.obj a ≌ G.obj a :=
  { hom := η.app a
    inv := inv a
    unit := unit a
    counit := counit a
    left_triangle := left_triangle a }

private noncomputable def invNaturality {a b : B} (f : a ⟶ b) :
    G.map f ≫ inv b ≅ inv a ≫ F.map f :=
  (Equivalence.mateIso (compEquiv η inv unit counit left_triangle a)
    (compEquiv η inv unit counit left_triangle b) (η.naturality f)).symm

private lemma invNaturality_naturality {a b : B} {f g : a ⟶ b} (ξ : f ⟶ g) :
    G.map₂ ξ ▷ inv b ≫ (invNaturality η inv unit counit left_triangle g).hom =
      (invNaturality η inv unit counit left_triangle f).hom ≫ inv a ◁ F.map₂ ξ := by
  set nf := invNaturality η inv unit counit left_triangle f
  set ng := invNaturality η inv unit counit left_triangle g
  have hm : inv a ◁ F.map₂ ξ ≫ ng.inv = nf.inv ≫ G.map₂ ξ ▷ inv b := by
    simp only [ng, nf, invNaturality, Iso.symm_inv, Equivalence.mateIso_hom]
    rw [← mateEquiv_whiskerRight_comp, ← mateEquiv_comp_whiskerLeft, η.naturality_naturality ξ]
  rw [← cancel_epi nf.inv, ← Category.assoc, Iso.inv_hom_id_assoc,
    ← cancel_mono ng.inv, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact hm.symm

private lemma invNaturality_id (a : B) :
    (invNaturality η inv unit counit left_triangle (𝟙 a)).hom ≫ inv a ◁ (F.mapId a).hom =
      (G.mapId a).hom ▷ inv a ≫ (λ_ (inv a)).hom ≫ (ρ_ (inv a)).inv := by
  set n := invNaturality η inv unit counit left_triangle (𝟙 a)
  have hm : n.inv ≫ (G.mapId a).hom ▷ inv a =
      inv a ◁ (F.mapId a).hom ≫ ((ρ_ (inv a)).hom ≫ (λ_ (inv a)).inv) := by
    simp only [n, invNaturality, Iso.symm_inv, Equivalence.mateIso_hom]
    rw [← mateEquiv_comp_whiskerLeft, η.naturality_id a,
      mateEquiv_whiskerRight_comp, mateEquiv_leftUnitor_hom_rightUnitor_inv]
  rw [← cancel_epi n.inv, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  calc
    inv a ◁ (F.mapId a).hom =
        (inv a ◁ (F.mapId a).hom ≫ ((ρ_ (inv a)).hom ≫ (λ_ (inv a)).inv)) ≫
          ((λ_ (inv a)).hom ≫ (ρ_ (inv a)).inv) := by
      bicategory
    _ = n.inv ≫ (G.mapId a).hom ▷ inv a ≫ (λ_ (inv a)).hom ≫ (ρ_ (inv a)).inv := by
      rw [← hm]
      bicategory

private lemma invNaturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (invNaturality η inv unit counit left_triangle (f ≫ g)).hom ≫ inv a ◁ (F.mapComp f g).hom =
      (G.mapComp f g).hom ▷ inv c ≫ (α_ (G.map f) (G.map g) (inv c)).hom ≫
        G.map f ◁ (invNaturality η inv unit counit left_triangle g).hom ≫
        (α_ (G.map f) (inv b) (F.map g)).inv ≫
        (invNaturality η inv unit counit left_triangle f).hom ▷ F.map g ≫
        (α_ (inv a) (F.map f) (F.map g)).hom := by
  set nf := invNaturality η inv unit counit left_triangle f
  set ng := invNaturality η inv unit counit left_triangle g
  set nfg := invNaturality η inv unit counit left_triangle (f ≫ g)
  -- Express the mate of `η.naturality (f ≫ g)` as the vertical composite of the mates at `f`
  -- and `g`, then invert both right-adjoint squares.
  have hm : nfg.inv ≫ (G.mapComp f g).hom ▷ inv c =
      inv a ◁ (F.mapComp f g).hom ≫ rightAdjointSquare.vcomp nf.inv ng.inv := by
    simp only [nfg, nf, ng, invNaturality, Iso.symm_inv, Equivalence.mateIso_hom]
    rw [← mateEquiv_comp_whiskerLeft, η.naturality_comp f g, ← mateEquiv_vcomp,
      ← mateEquiv_whiskerRight_comp]
    rfl
  rw [← cancel_epi nfg.inv, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hcancel : rightAdjointSquare.vcomp nf.inv ng.inv ≫
      ((α_ (G.map f) (G.map g) (inv c)).hom ≫ G.map f ◁ ng.hom ≫
        (α_ (G.map f) (inv b) (F.map g)).inv ≫ nf.hom ▷ F.map g ≫
        (α_ (inv a) (F.map f) (F.map g)).hom) = 𝟙 _ := by
    dsimp only [rightAdjointSquare.vcomp]
    calc
      _ = 𝟙 _ ⊗≫ nf.inv ▷ F.map g ⊗≫ G.map f ◁ (ng.inv ≫ ng.hom) ⊗≫
            nf.hom ▷ F.map g ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ (nf.inv ≫ nf.hom) ▷ F.map g ⊗≫ 𝟙 _ := by
        rw [Iso.inv_hom_id]
        bicategory
      _ = 𝟙 _ := by
        rw [Iso.inv_hom_id]
        bicategory
  calc
    inv a ◁ (F.mapComp f g).hom =
        (inv a ◁ (F.mapComp f g).hom ≫ rightAdjointSquare.vcomp nf.inv ng.inv) ≫
          ((α_ (G.map f) (G.map g) (inv c)).hom ≫ G.map f ◁ ng.hom ≫
            (α_ (G.map f) (inv b) (F.map g)).inv ≫ nf.hom ▷ F.map g ≫
            (α_ (inv a) (F.map f) (F.map g)).hom) := by
      rw [Category.assoc, hcancel, Category.comp_id]
    _ = _ := by
      rw [← hm]
      simp only [Category.assoc]

private lemma unit_modification_naturality {a b : B} (f : a ⟶ b) :
    F.map f ◁ (unit b).hom ≫
        ((α_ (F.map f) (η.app b) (inv b)).inv ≫ (η.naturality f).hom ▷ inv b ≫
          (α_ (η.app a) (G.map f) (inv b)).hom ≫
          η.app a ◁ (invNaturality η inv unit counit left_triangle f).hom ≫
          (α_ (η.app a) (inv a) (F.map f)).inv) =
      ((ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv) ≫ (unit a).hom ▷ F.map f := by
  let e := compEquiv η inv unit counit left_triangle
  set nf := invNaturality η inv unit counit left_triangle f
  -- Unpack `mateEquiv_eq_iff` into equality of the adjuncts under `homEquiv₁` and `homEquiv₂`.
  have hmate : (e a).adj.homEquiv₁.symm nf.inv =
      (e b).adj.homEquiv₂ (η.naturality f).hom ≫ (α_ (η.app a) (G.map f) (inv b)).hom := by
    refine (mateEquiv_eq_iff (e a).adj (e b).adj (η.naturality f).hom nf.inv).mp ?_
    simp only [nf, invNaturality, Iso.symm_inv, Equivalence.mateIso_hom, e]
  rw [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply] at hmate
  dsimp only [e, compEquiv, Equivalence.adj_unit] at hmate
  rw [← cancel_mono ((α_ (η.app a) (inv a) (F.map f)).hom ≫ η.app a ◁ nf.inv),
    ← cancel_epi (ρ_ (F.map f)).inv]
  calc
    _ = ((ρ_ (F.map f)).inv ≫ F.map f ◁ (unit b).hom ≫ (α_ (F.map f) (η.app b) (inv b)).inv ≫
          (η.naturality f).hom ▷ inv b) ≫ (α_ (η.app a) (G.map f) (inv b)).hom ≫
          η.app a ◁ (nf.hom ≫ nf.inv) := by
      bicategory
    _ = (λ_ (F.map f)).inv ≫ (unit a).hom ▷ F.map f ≫ (α_ (η.app a) (inv a) (F.map f)).hom ≫
          η.app a ◁ nf.inv := by
      rw [Iso.hom_inv_id, Bicategory.whiskerLeft_id, Category.comp_id, ← hmate]
    _ = _ := by
      bicategory

private lemma counit_modification_naturality {a b : B} (f : a ⟶ b) :
    G.map f ◁ (counit b).hom ≫ ((ρ_ (G.map f)).hom ≫ (λ_ (G.map f)).inv) =
      ((α_ (G.map f) (inv b) (η.app b)).inv ≫
        (invNaturality η inv unit counit left_triangle f).hom ▷ η.app b ≫
        (α_ (inv a) (F.map f) (η.app b)).hom ≫ inv a ◁ (η.naturality f).hom ≫
        (α_ (inv a) (η.app a) (G.map f)).inv) ≫ (counit a).hom ▷ G.map f := by
  let e := compEquiv η inv unit counit left_triangle
  set nf := invNaturality η inv unit counit left_triangle f
  -- Cancel `nf.hom` against `nf.inv = mateEquiv ...`, then exchange `counit b` past
  -- `η.naturality f` to form the left zigzag at `b`.
  rw [← cancel_epi (nf.inv ▷ η.app b ≫ (α_ (G.map f) (inv b) (η.app b)).hom)]
  have hrhs : (nf.inv ▷ η.app b ≫ (α_ (G.map f) (inv b) (η.app b)).hom) ≫
      (((α_ (G.map f) (inv b) (η.app b)).inv ≫ nf.hom ▷ η.app b ≫
          (α_ (inv a) (F.map f) (η.app b)).hom ≫ inv a ◁ (η.naturality f).hom ≫
          (α_ (inv a) (η.app a) (G.map f)).inv) ≫ (counit a).hom ▷ G.map f) =
      (α_ (inv a) (F.map f) (η.app b)).hom ≫ inv a ◁ (η.naturality f).hom ≫
        (α_ (inv a) (η.app a) (G.map f)).inv ≫ (counit a).hom ▷ G.map f := by
    calc
      _ = (nf.inv ≫ nf.hom) ▷ η.app b ⊗≫ inv a ◁ (η.naturality f).hom ⊗≫
            (counit a).hom ▷ G.map f := by
        bicategory
      _ = _ := by
        rw [Iso.inv_hom_id]
        bicategory
  rw [hrhs]
  simp only [nf, invNaturality, Iso.symm_inv, Equivalence.mateIso_hom]
  rw [mateEquiv_apply']
  dsimp only [compEquiv, Equivalence.adj_unit, Equivalence.adj_counit]
  calc
    _ = 𝟙 _ ⊗≫ inv a ◁ F.map f ◁ (unit b).hom ▷ η.app b ⊗≫
          inv a ◁ (η.naturality f).hom ▷ inv b ▷ η.app b ⊗≫
          (((counit a).hom ▷ G.map f) ▷ (inv b ≫ η.app b) ≫
            (𝟙 (G.obj a) ≫ G.map f) ◁ (counit b).hom) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ inv a ◁ F.map f ◁ (unit b).hom ▷ η.app b ⊗≫
          (inv a ◁ ((η.naturality f).hom ▷ (inv b ≫ η.app b) ≫
            (η.app a ≫ G.map f) ◁ (counit b).hom)) ⊗≫
          (counit a).hom ▷ G.map f ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ ⊗≫ inv a ◁ F.map f ◁ leftZigzag (unit b).hom (counit b).hom ⊗≫
          inv a ◁ (η.naturality f).hom ⊗≫ (counit a).hom ▷ G.map f ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = _ := by
      rw [(e b).left_triangle_hom]
      bicategory

end Helper

/-- Extend a strong transformation `η : F ⟶ G` between pseudofunctors `F G : B ⥤ᵖ C` to an
adjoint equivalence `F ≌ G` from component inverse `1`-morphisms and component unit and counit
`2`-isomorphisms satisfying the left triangle identity. -/
-- Expose the record projections so the dependent unit, counit and naturality equations retain
-- their literal component types in importing modules.
@[expose] noncomputable def equivalenceOfComponents (η : F ⟶ G)
    (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (left_triangle : ∀ a : B,
      leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm := by cat_disch) :
    F ≌ G where
  hom := η
  inv := {
    app := inv
    naturality {a b} f :=
      (Equivalence.mateIso
        { hom := η.app a, inv := inv a, unit := unit a, counit := counit a,
          left_triangle := left_triangle a }
        { hom := η.app b, inv := inv b, unit := unit b, counit := counit b,
          left_triangle := left_triangle b }
        (η.naturality f)).symm
    naturality_naturality ξ := by
      exact invNaturality_naturality η inv unit counit left_triangle ξ
    naturality_id a := by
      exact invNaturality_id η inv unit counit left_triangle a
    naturality_comp f g := by
      exact invNaturality_comp η inv unit counit left_triangle f g }
  unit := isoMk unit (fun f ↦ by
    exact unit_modification_naturality η inv unit counit left_triangle f)
  counit := isoMk counit (fun f ↦ by
    exact counit_modification_naturality η inv unit counit left_triangle f)
  left_triangle := by
    apply Iso.ext
    have reduce {X Y : B ⥤ᵖ C} (f : X ⟶ Y) (g : Y ⟶ X) (ι : 𝟙 X ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 Y) :
        leftZigzag ι ε = ι ▷ f ≫ (α_ f g f).hom ≫ f ◁ ε := by
      simp [leftZigzag, bicategoricalComp]
    simp only [leftZigzagIso_hom, Iso.trans_hom, Iso.symm_hom]
    refine (reduce η _ _ _).trans ?_
    apply homCategory.ext
    intro a
    simp only [homCategory_comp_as_app, whiskerRight_as_app, whiskerLeft_as_app,
      associator_hom_as_app, leftUnitor_hom_as_app, rightUnitor_inv_as_app]
    dsimp only [isoMk]
    simpa [leftZigzag, bicategoricalComp] using! congrArg Iso.hom (left_triangle a)

@[simp]
lemma equivalenceOfComponents_hom (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (left_triangle : ∀ a : B,
      leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm) :
    (η.equivalenceOfComponents inv unit counit left_triangle).hom = η :=
  (rfl)

@[simp]
lemma equivalenceOfComponents_inv_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (left_triangle : ∀ a : B,
      leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    (a : B) :
    (η.equivalenceOfComponents inv unit counit left_triangle).inv.app a = inv a :=
  (rfl)

/-- The inverse of the naturality `2`-isomorphism of the inverse strong transformation is the mate
of the original naturality cell across the component adjunctions. -/
lemma equivalenceOfComponents_inv_naturality_inv (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (left_triangle : ∀ a : B,
      leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    {a b : B} (f : a ⟶ b) :
    ((η.equivalenceOfComponents inv unit counit left_triangle).inv.naturality f).inv =
      mateEquiv
        (Bicategory.Equivalence.mk (η.app a) (inv a) (unit a) (counit a) (left_triangle a)).adj
        (Bicategory.Equivalence.mk (η.app b) (inv b) (unit b) (counit b) (left_triangle b)).adj
        (η.naturality f).hom :=
  (rfl)

-- Keep the unit and counit component equations named: their dependent modification carriers do
-- not reduce to a common simp normal form across importing modules.
lemma equivalenceOfComponents_unit_hom_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (left_triangle : ∀ a : B,
      leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    (a : B) :
    (η.equivalenceOfComponents inv unit counit left_triangle).unit.hom.as.app a = (unit a).hom :=
  (rfl)

lemma equivalenceOfComponents_unit_inv_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (left_triangle : ∀ a : B,
      leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    (a : B) :
    (η.equivalenceOfComponents inv unit counit left_triangle).unit.inv.as.app a = (unit a).inv :=
  (rfl)

lemma equivalenceOfComponents_counit_hom_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (left_triangle : ∀ a : B,
      leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    (a : B) :
    (η.equivalenceOfComponents inv unit counit left_triangle).counit.hom.as.app a =
      (counit a).hom :=
  (rfl)

lemma equivalenceOfComponents_counit_inv_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a))
    (left_triangle : ∀ a : B,
      leftZigzagIso (unit a) (counit a) = λ_ (η.app a) ≪≫ (ρ_ (η.app a)).symm)
    (a : B) :
    (η.equivalenceOfComponents inv unit counit left_triangle).counit.inv.as.app a =
      (counit a).inv :=
  (rfl)

/-- Extend a strong transformation `η : F ⟶ G` between pseudofunctors `F G : B ⥤ᵖ C` to an
adjoint equivalence `F ≌ G` from arbitrary component inverse `1`-morphisms and component unit and
counit `2`-isomorphisms, adjointifying each component counit. -/
@[expose] noncomputable def mkEquivalence (η : F ⟶ G)
    (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a)) :
    F ≌ G :=
  η.equivalenceOfComponents inv unit
    (fun a ↦ adjointifyCounit (unit a) (counit a))
    (fun a ↦ adjointifyCounit_left_triangle (unit a) (counit a))

@[simp]
lemma mkEquivalence_hom (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a)) :
    (η.mkEquivalence inv unit counit).hom = η :=
  (rfl)

@[simp]
lemma mkEquivalence_inv_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a)) (a : B) :
    (η.mkEquivalence inv unit counit).inv.app a = inv a :=
  (rfl)

lemma mkEquivalence_unit_hom_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a)) (a : B) :
    (η.mkEquivalence inv unit counit).unit.hom.as.app a = (unit a).hom :=
  (rfl)

lemma mkEquivalence_unit_inv_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a)) (a : B) :
    (η.mkEquivalence inv unit counit).unit.inv.as.app a = (unit a).inv :=
  (rfl)

lemma mkEquivalence_counit_hom_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a)) (a : B) :
    (η.mkEquivalence inv unit counit).counit.hom.as.app a =
      (adjointifyCounit (unit a) (counit a)).hom :=
  (rfl)

lemma mkEquivalence_counit_inv_as_app (η : F ⟶ G) (inv : ∀ a : B, G.obj a ⟶ F.obj a)
    (unit : ∀ a : B, 𝟙 (F.obj a) ≅ η.app a ≫ inv a)
    (counit : ∀ a : B, inv a ≫ η.app a ≅ 𝟙 (G.obj a)) (a : B) :
    (η.mkEquivalence inv unit counit).counit.inv.as.app a =
      (adjointifyCounit (unit a) (counit a)).inv :=
  (rfl)

end CategoryTheory.Pseudofunctor.StrongTrans
