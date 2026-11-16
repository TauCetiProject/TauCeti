/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-!
# Isomorphisms and horizontal whiskering of mates in bicategories

Given adjunctions `adj₁ : l₁ ⊣ r₁` and `adj₂ : l₂ ⊣ r₂` in a bicategory `B`, `mateEquiv adj₁ adj₂`
maps `2`-morphisms `g ≫ l₂ ⟶ l₁ ≫ h` to `2`-morphisms `r₁ ≫ g ⟶ h ≫ r₂`. When `adj₂.unit` and
`adj₁.counit` are isomorphisms, `mateEquiv adj₁ adj₂` preserves invertibility; in particular,
adjoint equivalences `e₁ : c ≌ d` and `e₂ : e ≌ f` send any `2`-isomorphism
`g ≫ e₂.hom ≅ e₁.hom ≫ h` to a mate `2`-isomorphism `e₁.inv ≫ g ≅ h ≫ e₂.inv`. Taking mates also
commutes with whiskering the vertical `1`-morphisms `g` and `h` by `2`-morphisms.

## Main declarations

* `CategoryTheory.Bicategory.isIso_mateEquiv`: the mate of an invertible `2`-morphism across two
  adjunctions with invertible unit and counit is invertible;
* `CategoryTheory.Bicategory.mateEquiv_whiskerRight_comp`,
  `CategoryTheory.Bicategory.mateEquiv_comp_whiskerLeft`: naturality of `mateEquiv` in the
  vertical `1`-morphisms;
* `CategoryTheory.Bicategory.Equivalence.mateIso`: the mate isomorphism
  `e₁.inv ≫ g ≅ h ≫ e₂.inv` induced by `g ≫ e₂.hom ≅ e₁.hom ≫ h` across adjoint equivalences.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 6: mates and adjoint equivalences
  in bicategories.
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
