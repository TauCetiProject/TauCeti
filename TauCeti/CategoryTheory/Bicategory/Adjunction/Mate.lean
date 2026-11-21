/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
public import TauCeti.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Naturality and isomorphism preservation for mates in bicategories

For adjunctions `adj₁ : l₁ ⊣ r₁` and `adj₂ : l₂ ⊣ r₂` in a bicategory, `mateEquiv adj₁ adj₂`
relates `2`-cells `g ≫ l₂ ⟶ l₁ ≫ h` and `r₁ ≫ g ⟶ h ≫ r₂`. This file records its naturality in the
vertical `1`-morphisms `g` and `h`, its compatibility equations with the unit of `adj₁` and the
counit of `adj₂` (the bicategorical counterparts of `CategoryTheory.unit_mateEquiv` and
`CategoryTheory.mateEquiv_counit`), and the induced equivalence on `2`-isomorphisms when `l₁ ⊣ r₁`
and `l₂ ⊣ r₂` come from adjoint equivalences `e₁` and `e₂`.

For general adjunctions a mate of an isomorphism need not be invertible, because `mateEquiv`
whiskers by the unit of `adj₂` and the counit of `adj₁`. When `e₁ : a ≌ b` and `e₂ : c ≌ d` are
adjoint equivalences, the inverse equivalences `e₁.symm` and `e₂.symm` supply the inverse
adjunctions `e₁.symm.adj : e₁.inv ⊣ e₁.hom` and `e₂.symm.adj : e₂.inv ⊣ e₂.hom` acting by the
inverse unit and inverse counit, giving `Equivalence.mateIsoEquiv`.

## Main definitions and results

* `CategoryTheory.Bicategory.Adjunction.mateEquiv_whiskerRight_comp`,
  `CategoryTheory.Bicategory.Adjunction.mateEquiv_comp_whiskerLeft`,
  `CategoryTheory.Bicategory.Adjunction.mateEquiv_symm_whiskerLeft_comp`,
  `CategoryTheory.Bicategory.Adjunction.mateEquiv_symm_comp_whiskerRight`,
  `CategoryTheory.Bicategory.Adjunction.whiskerLeft_comp_mateEquiv_eq_iff`: naturality of
  `mateEquiv` and its inverse with respect to `2`-morphisms between the vertical `1`-morphisms;
* `CategoryTheory.Bicategory.Adjunction.unit_mateEquiv`,
  `CategoryTheory.Bicategory.Adjunction.unit_mateEquiv_symm`,
  `CategoryTheory.Bicategory.Adjunction.mateEquiv_counit`,
  `CategoryTheory.Bicategory.Adjunction.mateEquiv_counit_symm`: the unit and counit pasting
  identities characterizing `mateEquiv` and its inverse;
* `CategoryTheory.Bicategory.Equivalence.mateIsoEquiv`: for adjoint equivalences `e₁ : a ≌ b` and
  `e₂ : c ≌ d`, the bijection `(g ≫ e₂.hom ≅ e₁.hom ≫ h) ≃ (e₁.inv ≫ g ≅ h ≫ e₂.inv)`.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055): mates and adjoint equivalences in
  bicategories.
-/

public section

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

namespace Adjunction

section Naturality

variable {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
  (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/-- `mateEquiv` commutes with pre-whiskering along a `2`-morphism `γ : g₁ ⟶ g₂` between the left
vertical `1`-morphisms. -/
lemma mateEquiv_whiskerRight_comp {g₁ g₂ : a ⟶ c} {h : b ⟶ d}
    (γ : g₁ ⟶ g₂) (β : g₂ ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv adj₁ adj₂ (γ ▷ l₂ ≫ β) = r₁ ◁ γ ≫ mateEquiv adj₁ adj₂ β := by
  simp only [mateEquiv_apply']
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ (g₁ ◁ adj₂.unit ≫ γ ▷ (l₂ ≫ r₂)) ⊗≫
          r₁ ◁ β ▷ r₂ ⊗≫ adj₁.counit ▷ h ▷ r₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ (γ ▷ 𝟙 c ≫ g₂ ◁ adj₂.unit) ⊗≫
          r₁ ◁ β ▷ r₂ ⊗≫ adj₁.counit ▷ h ▷ r₂ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by
      bicategory

/-- `mateEquiv` commutes with post-whiskering along a `2`-morphism `δ : h₁ ⟶ h₂` between the right
vertical `1`-morphisms. -/
lemma mateEquiv_comp_whiskerLeft {g : a ⟶ c} {h₁ h₂ : b ⟶ d}
    (α : g ≫ l₂ ⟶ l₁ ≫ h₁) (δ : h₁ ⟶ h₂) :
    mateEquiv adj₁ adj₂ (α ≫ l₁ ◁ δ) = mateEquiv adj₁ adj₂ α ≫ δ ▷ r₂ := by
  simp only [mateEquiv_apply']
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ⊗≫ r₁ ◁ α ▷ r₂ ⊗≫
          ((r₁ ≫ l₁) ◁ δ ≫ adj₁.counit ▷ h₂) ▷ r₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ⊗≫ r₁ ◁ α ▷ r₂ ⊗≫
          (adj₁.counit ▷ h₁ ≫ 𝟙 b ◁ δ) ▷ r₂ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
    _ = _ := by
      bicategory

/-- `(mateEquiv adj₁ adj₂).symm` commutes with pre-whiskering along a `2`-morphism `γ : g₁ ⟶ g₂`
between the left vertical `1`-morphisms. -/
lemma mateEquiv_symm_whiskerLeft_comp {g₁ g₂ : a ⟶ c} {h : b ⟶ d}
    (γ : g₁ ⟶ g₂) (β : r₁ ≫ g₂ ⟶ h ≫ r₂) :
    (mateEquiv adj₁ adj₂).symm (r₁ ◁ γ ≫ β) = γ ▷ l₂ ≫ (mateEquiv adj₁ adj₂).symm β := by
  rw [Equiv.symm_apply_eq, adj₁.mateEquiv_whiskerRight_comp adj₂, Equiv.apply_symm_apply]

/-- `(mateEquiv adj₁ adj₂).symm` commutes with post-whiskering along a `2`-morphism `δ : h₁ ⟶ h₂`
between the right vertical `1`-morphisms. -/
lemma mateEquiv_symm_comp_whiskerRight {g : a ⟶ c} {h₁ h₂ : b ⟶ d}
    (α : r₁ ≫ g ⟶ h₁ ≫ r₂) (δ : h₁ ⟶ h₂) :
    (mateEquiv adj₁ adj₂).symm (α ≫ δ ▷ r₂) = (mateEquiv adj₁ adj₂).symm α ≫ l₁ ◁ δ := by
  rw [Equiv.symm_apply_eq, adj₁.mateEquiv_comp_whiskerLeft adj₂, Equiv.apply_symm_apply]

/-- Naturality of `mateEquiv` in both vertical `1`-morphisms: `2`-morphisms `γ : g₁ ⟶ g₂` and
`δ : h₁ ⟶ h₂` intertwine two squares between the left adjoints if and only if they intertwine their
mates between the right adjoints. -/
lemma whiskerLeft_comp_mateEquiv_eq_iff {g₁ g₂ : a ⟶ c} {h₁ h₂ : b ⟶ d}
    {α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁} {β : g₂ ≫ l₂ ⟶ l₁ ≫ h₂} {γ : g₁ ⟶ g₂} {δ : h₁ ⟶ h₂} :
    r₁ ◁ γ ≫ mateEquiv adj₁ adj₂ β = mateEquiv adj₁ adj₂ α ≫ δ ▷ r₂ ↔
      γ ▷ l₂ ≫ β = α ≫ l₁ ◁ δ := by
  rw [← adj₁.mateEquiv_whiskerRight_comp adj₂, ← adj₁.mateEquiv_comp_whiskerLeft adj₂,
    (mateEquiv adj₁ adj₂).apply_eq_iff_eq]

/-- Whiskering the mate of `α : g ≫ l₂ ⟶ l₁ ≫ h` on the left by `l₁` and pasting with `adj₁.unit`
recovers `α` whiskered on the right by `r₂` and pasted with `adj₂.unit`. -/
lemma unit_mateEquiv {g : a ⟶ c} {h : b ⟶ d} (α : g ≫ l₂ ⟶ l₁ ≫ h) :
    adj₁.unit ▷ g ≫ (α_ l₁ r₁ g).hom ≫ l₁ ◁ mateEquiv adj₁ adj₂ α =
      (λ_ g).hom ≫ (ρ_ g).inv ≫ g ◁ adj₂.unit ≫ (α_ g l₂ r₂).inv ≫
        α ▷ r₂ ≫ (α_ l₁ h r₂).hom := by
  have h := (mateEquiv_eq_iff adj₁ adj₂ α (mateEquiv adj₁ adj₂ α)).mp rfl
  simp only [homEquiv₁_symm_apply, homEquiv₂_apply] at h
  rw [← cancel_epi (λ_ g).inv]
  simpa only [Iso.inv_hom_id_assoc, Category.assoc] using h

/-- Pasting `β : r₁ ≫ g ⟶ h ≫ r₂` whiskered on the left by `l₁` with `adj₁.unit` recovers the
inverse mate `(mateEquiv adj₁ adj₂).symm β` whiskered on the right by `r₂` and pasted with
`adj₂.unit`. -/
lemma unit_mateEquiv_symm {g : a ⟶ c} {h : b ⟶ d} (β : r₁ ≫ g ⟶ h ≫ r₂) :
    adj₁.unit ▷ g ≫ (α_ l₁ r₁ g).hom ≫ l₁ ◁ β =
      (λ_ g).hom ≫ (ρ_ g).inv ≫ g ◁ adj₂.unit ≫ (α_ g l₂ r₂).inv ≫
        (mateEquiv adj₁ adj₂).symm β ▷ r₂ ≫ (α_ l₁ h r₂).hom := by
  simpa only [Equiv.apply_symm_apply] using adj₁.unit_mateEquiv adj₂ ((mateEquiv adj₁ adj₂).symm β)

/-- Whiskering the mate of `α : g ≫ l₂ ⟶ l₁ ≫ h` on the right by `l₂` and pasting with
`adj₂.counit` recovers `α` whiskered on the left by `r₁` and pasted with `adj₁.counit`. -/
lemma mateEquiv_counit {g : a ⟶ c} {h : b ⟶ d} (α : g ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv adj₁ adj₂ α ▷ l₂ ≫ (α_ h r₂ l₂).hom ≫ h ◁ adj₂.counit =
      (α_ r₁ g l₂).hom ≫ r₁ ◁ α ≫ (α_ r₁ l₁ h).inv ≫ adj₁.counit ▷ h ≫
        (λ_ h).hom ≫ (ρ_ h).inv := by
  simp only [mateEquiv_apply']
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ▷ l₂ ⊗≫ r₁ ◁ α ▷ (r₂ ≫ l₂) ⊗≫
          (adj₁.counit ▷ (h ≫ r₂ ≫ l₂) ≫ 𝟙 b ◁ h ◁ adj₂.counit) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ▷ l₂ ⊗≫
          r₁ ◁ (α ▷ (r₂ ≫ l₂) ≫ (l₁ ≫ h) ◁ adj₂.counit) ⊗≫
            adj₁.counit ▷ (h ≫ 𝟙 d) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ leftZigzag adj₂.unit adj₂.counit ⊗≫
          r₁ ◁ α ⊗≫ adj₁.counit ▷ h ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = _ := by
      rw [adj₂.left_triangle]
      bicategory

/-- Pasting `β : r₁ ≫ g ⟶ h ≫ r₂` whiskered on the right by `l₂` with `adj₂.counit` recovers the
inverse mate `(mateEquiv adj₁ adj₂).symm β` whiskered on the left by `r₁` and pasted with
`adj₁.counit`. -/
lemma mateEquiv_counit_symm {g : a ⟶ c} {h : b ⟶ d} (β : r₁ ≫ g ⟶ h ≫ r₂) :
    β ▷ l₂ ≫ (α_ h r₂ l₂).hom ≫ h ◁ adj₂.counit =
      (α_ r₁ g l₂).hom ≫ r₁ ◁ (mateEquiv adj₁ adj₂).symm β ≫ (α_ r₁ l₁ h).inv ≫
        adj₁.counit ▷ h ≫ (λ_ h).hom ≫ (ρ_ h).inv := by
  simpa only [Equiv.apply_symm_apply] using
    adj₁.mateEquiv_counit adj₂ ((mateEquiv adj₁ adj₂).symm β)

end Naturality

end Adjunction

namespace Equivalence

variable {a b c d : B} (e₁ : a ≌ b) (e₂ : c ≌ d) {g : a ⟶ c} {h : b ⟶ d}

private lemma mateEquiv_hom_comp_symm_adj_symm_inv (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    mateEquiv e₁.adj e₂.adj α.hom ≫
        (mateEquiv e₁.symm.adj e₂.symm.adj).symm α.inv = 𝟙 (e₁.inv ≫ g) := by
  rw [mateEquiv_apply', mateEquiv_symm_apply']
  simp only [adj_unit, adj_counit, symm_unit, symm_counit, Iso.symm_hom]
  calc
    _ = 𝟙 _ ⊗≫ e₁.inv ◁ g ◁ e₂.unit.hom ⊗≫ e₁.inv ◁ α.hom ▷ e₂.inv ⊗≫
          (e₁.counit.hom ≫ e₁.counit.inv) ▷ h ▷ e₂.inv ⊗≫
            e₁.inv ◁ α.inv ▷ e₂.inv ⊗≫ e₁.inv ◁ g ◁ e₂.unit.inv ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ e₁.inv ◁ g ◁ e₂.unit.hom ⊗≫
          e₁.inv ◁ (α.hom ≫ α.inv) ▷ e₂.inv ⊗≫ e₁.inv ◁ g ◁ e₂.unit.inv ⊗≫ 𝟙 _ := by
      rw [Iso.hom_inv_id]
      bicategory
    _ = 𝟙 _ ⊗≫ e₁.inv ◁ g ◁ (e₂.unit.hom ≫ e₂.unit.inv) ⊗≫ 𝟙 _ := by
      rw [Iso.hom_inv_id]
      bicategory
    _ = 𝟙 (e₁.inv ≫ g) := by
      rw [Iso.hom_inv_id]
      bicategory

private lemma mateEquiv_symm_adj_symm_inv_comp_hom (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    (mateEquiv e₁.symm.adj e₂.symm.adj).symm α.inv ≫
        mateEquiv e₁.adj e₂.adj α.hom = 𝟙 (h ≫ e₂.inv) := by
  rw [mateEquiv_apply', mateEquiv_symm_apply']
  simp only [adj_unit, adj_counit, symm_unit, symm_counit, Iso.symm_hom]
  calc
    _ = 𝟙 _ ⊗≫ e₁.counit.inv ▷ h ▷ e₂.inv ⊗≫ e₁.inv ◁ α.inv ▷ e₂.inv ⊗≫
          e₁.inv ◁ g ◁ (e₂.unit.inv ≫ e₂.unit.hom) ⊗≫
            e₁.inv ◁ α.hom ▷ e₂.inv ⊗≫ e₁.counit.hom ▷ h ▷ e₂.inv ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ e₁.counit.inv ▷ h ▷ e₂.inv ⊗≫
          e₁.inv ◁ (α.inv ≫ α.hom) ▷ e₂.inv ⊗≫ e₁.counit.hom ▷ h ▷ e₂.inv ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id]
      bicategory
    _ = 𝟙 _ ⊗≫ (e₁.counit.inv ≫ e₁.counit.hom) ▷ h ▷ e₂.inv ⊗≫ 𝟙 _ := by
      rw [Iso.inv_hom_id]
      bicategory
    _ = 𝟙 (h ≫ e₂.inv) := by
      rw [Iso.inv_hom_id]
      bicategory

private lemma mateEquiv_symm_hom_comp_symm_adj_inv (β : e₁.inv ≫ g ≅ h ≫ e₂.inv) :
    (mateEquiv e₁.adj e₂.adj).symm β.hom ≫
        mateEquiv e₁.symm.adj e₂.symm.adj β.inv = 𝟙 (g ≫ e₂.hom) :=
  mateEquiv_symm_adj_symm_inv_comp_hom e₁.symm e₂.symm β.symm

private lemma mateEquiv_symm_adj_inv_comp_symm_hom (β : e₁.inv ≫ g ≅ h ≫ e₂.inv) :
    mateEquiv e₁.symm.adj e₂.symm.adj β.inv ≫
        (mateEquiv e₁.adj e₂.adj).symm β.hom = 𝟙 (e₁.hom ≫ h) :=
  mateEquiv_hom_comp_symm_adj_symm_inv e₁.symm e₂.symm β.symm

/-- When the horizontal `1`-morphisms of a square are adjoint equivalences `e₁ : a ≌ b` and
`e₂ : c ≌ d`, taking mates under `e₁.adj` and `e₂.adj` preserves and reflects `2`-isomorphisms,
inducing a bijection `(g ≫ e₂.hom ≅ e₁.hom ≫ h) ≃ (e₁.inv ≫ g ≅ h ≫ e₂.inv)`. -/
def mateIsoEquiv : (g ≫ e₂.hom ≅ e₁.hom ≫ h) ≃ (e₁.inv ≫ g ≅ h ≫ e₂.inv) where
  toFun α :=
    { hom := mateEquiv e₁.adj e₂.adj α.hom
      inv := (mateEquiv e₁.symm.adj e₂.symm.adj).symm α.inv
      hom_inv_id := mateEquiv_hom_comp_symm_adj_symm_inv e₁ e₂ α
      inv_hom_id := mateEquiv_symm_adj_symm_inv_comp_hom e₁ e₂ α }
  invFun β :=
    { hom := (mateEquiv e₁.adj e₂.adj).symm β.hom
      inv := mateEquiv e₁.symm.adj e₂.symm.adj β.inv
      hom_inv_id := mateEquiv_symm_hom_comp_symm_adj_inv e₁ e₂ β
      inv_hom_id := mateEquiv_symm_adj_inv_comp_symm_hom e₁ e₂ β }
  left_inv _ := Iso.ext (Equiv.symm_apply_apply _ _)
  right_inv _ := Iso.ext (Equiv.apply_symm_apply _ _)

@[simp]
lemma mateIsoEquiv_apply_hom (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    (e₁.mateIsoEquiv e₂ α).hom = mateEquiv e₁.adj e₂.adj α.hom :=
  (rfl)

@[simp]
lemma mateIsoEquiv_apply_inv (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    (e₁.mateIsoEquiv e₂ α).inv = (mateEquiv e₁.symm.adj e₂.symm.adj).symm α.inv :=
  (rfl)

@[simp]
lemma mateIsoEquiv_symm_apply_hom (β : e₁.inv ≫ g ≅ h ≫ e₂.inv) :
    ((e₁.mateIsoEquiv e₂).symm β).hom = (mateEquiv e₁.adj e₂.adj).symm β.hom :=
  (rfl)

@[simp]
lemma mateIsoEquiv_symm_apply_inv (β : e₁.inv ≫ g ≅ h ≫ e₂.inv) :
    ((e₁.mateIsoEquiv e₂).symm β).inv = mateEquiv e₁.symm.adj e₂.symm.adj β.inv :=
  (rfl)

@[simp]
lemma mateIsoEquiv_leftUnitor_trans_rightUnitor_symm (e : a ≌ b) :
    e.mateIsoEquiv e (λ_ e.hom ≪≫ (ρ_ e.hom).symm) = ρ_ e.inv ≪≫ (λ_ e.inv).symm := by
  ext
  simp

/-- Pasting `(e₁.mateIsoEquiv e₂ α).inv` with `α.hom` and `e₂.unit.hom` recovers `e₁.unit.hom`. -/
lemma unit_mateIsoEquiv_inv (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    g ◁ e₂.unit.hom ≫
        ((α_ g e₂.hom e₂.inv).inv ≫ α.hom ▷ e₂.inv ≫ (α_ e₁.hom h e₂.inv).hom ≫
          e₁.hom ◁ (e₁.mateIsoEquiv e₂ α).inv ≫ (α_ e₁.hom e₁.inv g).inv) =
      ((ρ_ g).hom ≫ (λ_ g).inv) ≫ e₁.unit.hom ▷ g := by
  have hu : e₁.unit.hom ▷ g ≫ (α_ e₁.hom e₁.inv g).hom ≫ e₁.hom ◁ (e₁.mateIsoEquiv e₂ α).hom =
      (λ_ g).hom ≫ (ρ_ g).inv ≫ g ◁ e₂.unit.hom ≫ (α_ g e₂.hom e₂.inv).inv ≫
        α.hom ▷ e₂.inv ≫ (α_ e₁.hom h e₂.inv).hom := by
    simpa only [mateIsoEquiv_apply_hom, adj_unit] using e₁.adj.unit_mateEquiv e₂.adj α.hom
  generalize e₁.mateIsoEquiv e₂ α = β at hu ⊢
  calc
    _ = 𝟙 _ ⊗≫ ((λ_ g).hom ≫ (ρ_ g).inv ≫ g ◁ e₂.unit.hom ≫ (α_ g e₂.hom e₂.inv).inv ≫
          α.hom ▷ e₂.inv ≫ (α_ e₁.hom h e₂.inv).hom) ⊗≫ e₁.hom ◁ β.inv ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ (e₁.unit.hom ▷ g ≫ (α_ e₁.hom e₁.inv g).hom ≫ e₁.hom ◁ β.hom) ⊗≫
          e₁.hom ◁ β.inv ⊗≫ 𝟙 _ := by
      rw [← hu]
    _ = 𝟙 _ ⊗≫ e₁.unit.hom ▷ g ⊗≫ e₁.hom ◁ (β.hom ≫ β.inv) ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [Iso.hom_inv_id]
      bicategory

/-- Pasting `(e₁.mateIsoEquiv e₂ α).inv` with `α.hom` and `e₁.counit.hom` recovers
`e₂.counit.hom`. -/
lemma mateIsoEquiv_inv_counit (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    ((α_ h e₂.inv e₂.hom).inv ≫ (e₁.mateIsoEquiv e₂ α).inv ▷ e₂.hom ≫
        (α_ e₁.inv g e₂.hom).hom ≫ e₁.inv ◁ α.hom ≫ (α_ e₁.inv e₁.hom h).inv) ≫
        e₁.counit.hom ▷ h =
      h ◁ e₂.counit.hom ≫ ((ρ_ h).hom ≫ (λ_ h).inv) := by
  have hc : (e₁.mateIsoEquiv e₂ α).hom ▷ e₂.hom ≫ (α_ h e₂.inv e₂.hom).hom ≫
        h ◁ e₂.counit.hom =
      (α_ e₁.inv g e₂.hom).hom ≫ e₁.inv ◁ α.hom ≫ (α_ e₁.inv e₁.hom h).inv ≫
        e₁.counit.hom ▷ h ≫ (λ_ h).hom ≫ (ρ_ h).inv := by
    simpa only [mateIsoEquiv_apply_hom, adj_counit] using e₁.adj.mateEquiv_counit e₂.adj α.hom
  generalize e₁.mateIsoEquiv e₂ α = β at hc ⊢
  calc
    _ = 𝟙 _ ⊗≫ β.inv ▷ e₂.hom ⊗≫
          ((α_ e₁.inv g e₂.hom).hom ≫ e₁.inv ◁ α.hom ≫ (α_ e₁.inv e₁.hom h).inv ≫
            e₁.counit.hom ▷ h ≫ (λ_ h).hom ≫ (ρ_ h).inv) ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ β.inv ▷ e₂.hom ⊗≫
          (β.hom ▷ e₂.hom ≫ (α_ h e₂.inv e₂.hom).hom ≫ h ◁ e₂.counit.hom) ⊗≫ 𝟙 _ := by
      rw [← hc]
    _ = 𝟙 _ ⊗≫ (β.inv ≫ β.hom) ▷ e₂.hom ⊗≫ h ◁ e₂.counit.hom ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]
      bicategory

end Equivalence

end CategoryTheory.Bicategory
