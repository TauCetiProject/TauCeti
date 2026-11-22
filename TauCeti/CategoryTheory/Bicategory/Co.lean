/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# The 2-cell dual of a bicategory

For a bicategory `B`, its *2-cell dual* `TauCeti.Bicategory.Co B`, written `Bᶜᵒ` in the
literature, has the objects and the `1`-morphisms of `B`, and the `2`-morphisms of `B` reversed:
each hom-category `a ⟶ b` is replaced by its opposite category. Horizontal composition and
whiskering are those of `B`, while vertical composition of `2`-morphisms is reversed, and the
associators and unitors are the inverses of those of `B`. Mathlib's
`Mathlib/CategoryTheory/Bicategory/Opposites.lean` constructs the `1`-cell dual `Bᵒᵖ`, which
reverses the `1`-morphisms and keeps the direction of the `2`-morphisms; the 2-cell dual is the
other basic duality of bicategories.

An object of `Co B` is a wrapped object `Co.co a` of `B`, with inverse `Co.unco`. A `1`-morphism
`a ⟶ b` of `Co B` is, by definition, an element of the opposite `(a.unco ⟶ b.unco)ᵒᵖ` of the
hom-category of `B`, and the hom-categories of `Co B` are Mathlib's opposite categories. So
`1`-morphisms are converted with `Opposite.op` and `Opposite.unop` (write `unop f`: the dot
notation `f.unop` refers to `Quiver.Hom.unop`), and `2`-morphisms with `Quiver.Hom.op` and
`Quiver.Hom.unop`: a `2`-morphism `θ : g ⟶ f` of `B` gives `θ.op : op f ⟶ op g`, and an invertible
`2`-morphism `e : g ≅ f` gives `e.op`. Mathlib's lemmas on opposite categories, such as
`CategoryTheory.op_comp` for the reversal of vertical composition, apply to the hom-categories of
`Co B`. Those that `simp` should use on `2`-morphisms of `Co B` are restated here, because `simp`
does not recognise these hom-categories as opposite categories (see `Co.unop_comp₂`).

The construction parallels Mathlib's `1`-cell dual `Bicategory.Opposite.bicategory`: each
bicategory axiom of `Co B` is the corresponding axiom of `B` read through `Quiver.Hom.unop`.

A typical use of the 2-cell dual is to compare a bicategory in which `2`-morphisms point the
other way with an existing one: for instance, a `2`-morphism between specified adjunctions
`F ⟶ F'` in `CategoryTheory.Bicategory.Adj B` has components `F.l ⟶ F'.l` and `F'.r ⟶ F.r`, so a
`2`-morphism in the opposite direction on left adjoints is a `2`-morphism of `Co (Adj B)`.

## Main definitions and results

* `TauCeti.Bicategory.Co`: the type of objects of the 2-cell dual of a bicategory.
* `TauCeti.Bicategory.Co.instBicategory`: its bicategory structure.
* `TauCeti.Bicategory.Co.unop_whiskerLeft`, `TauCeti.Bicategory.Co.op_whiskerLeft` and their
  right-hand versions: whiskering in `Co B` is whiskering in `B`.
* `TauCeti.Bicategory.Co.associator_hom_unop`, `TauCeti.Bicategory.Co.op_associator_hom` and
  their analogues for the unitors and the inverse `2`-morphisms: the coherence isomorphisms of
  `Co B` are the inverses of those of `B`, read as reversed `2`-morphisms.
* `TauCeti.Bicategory.Co.instStrict`: the 2-cell dual of a strict bicategory is strict.

## References

* G. M. Kelly and Ross Street, *Review of the elements of 2-categories*, Category Seminar,
  Lecture Notes in Mathematics **420** (1974), 75–103: the duals of a 2-category.
* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 2: bicategories.
-/

@[expose] public section

universe w v u

namespace TauCeti.Bicategory

open CategoryTheory Bicategory Opposite

/-- The type of objects of the 2-cell dual `Bᶜᵒ` of a bicategory `B`: the bicategory with the
objects and `1`-morphisms of `B` whose hom-categories are the opposites of those of `B`. -/
structure Co (B : Type u) where
  /-- The object of the 2-cell dual corresponding to an object of `B`. -/
  co ::
  /-- The object of `B` underlying an object of its 2-cell dual. -/
  unco : B

namespace Co

variable {B : Type u}

@[simp]
lemma unco_co (a : B) : (co a).unco = a :=
  rfl

@[simp]
lemma co_unco (a : Co B) : co a.unco = a :=
  rfl

variable [Bicategory.{w, v} B]

/-- The 2-cell dual of a bicategory `B`. A `1`-morphism `a ⟶ b` is an element of
`(a.unco ⟶ b.unco)ᵒᵖ` and the hom-categories are Mathlib's opposite categories, so that a
`2`-morphism `f ⟶ g` of `Co B` is a reversed `2`-morphism `unop g ⟶ unop f` of `B`.
Composition of `1`-morphisms and whiskering are those of `B`, and the associators and unitors
are the opposites of the inverse associators and unitors of `B`. -/
instance instBicategory : Bicategory.{w, v} (Co B) where
  Hom a b := (a.unco ⟶ b.unco)ᵒᵖ
  id a := op (𝟙 a.unco)
  comp f g := op (unop f ≫ unop g)
  homCategory _ _ := Category.opposite
  whiskerLeft f _ _ η := (unop f ◁ η.unop).op
  whiskerRight η h := (η.unop ▷ unop h).op
  associator f g h := Iso.op (α_ (unop f) (unop g) (unop h)).symm
  leftUnitor f := Iso.op (λ_ (unop f)).symm
  rightUnitor f := Iso.op (ρ_ (unop f)).symm
  whiskerLeft_id _ _ := Quiver.Hom.unop_inj (by simp)
  whiskerLeft_comp _ _ _ _ _ _ := Quiver.Hom.unop_inj (by simp)
  id_whiskerLeft _ := Quiver.Hom.unop_inj (by simp)
  comp_whiskerLeft _ _ _ _ _ := Quiver.Hom.unop_inj (by simp)
  id_whiskerRight _ _ := Quiver.Hom.unop_inj (by simp)
  comp_whiskerRight _ _ _ := Quiver.Hom.unop_inj (by simp)
  whiskerRight_id _ := Quiver.Hom.unop_inj (by simp)
  whiskerRight_comp _ _ _ := Quiver.Hom.unop_inj (by simp)
  whisker_assoc _ _ _ _ _ := Quiver.Hom.unop_inj (by simp)
  whisker_exchange _ _ := Quiver.Hom.unop_inj (by simp [whisker_exchange])
  pentagon _ _ _ _ := Quiver.Hom.unop_inj (by simp)
  triangle _ _ := Quiver.Hom.unop_inj (by simp)

/-! ### `1`-morphisms -/

section Hom

variable {a b c : Co B}

@[simp]
lemma unop_id (a : Co B) : unop (𝟙 a) = 𝟙 a.unco :=
  rfl

@[simp]
lemma unop_comp (f : a ⟶ b) (g : b ⟶ c) : unop (f ≫ g) = unop f ≫ unop g :=
  rfl

@[simp]
lemma op_id (a : B) : (op (𝟙 a) : co a ⟶ co a) = 𝟙 (co a) :=
  rfl

@[simp]
lemma op_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (op (f ≫ g) : co a ⟶ co c) = CategoryStruct.comp (obj := Co B) (op f) (op g) :=
  rfl

/-- Two `1`-morphisms of the 2-cell dual are equal when the underlying `1`-morphisms of `B`
are. -/
lemma hom_ext {f g : a ⟶ b} (h : unop f = unop g) : f = g :=
  unop_injective h

end Hom

/-! ### `2`-morphisms and whiskering -/

section Hom₂

variable {a b c : Co B}

/-- Two `2`-morphisms of the 2-cell dual are equal when the reversed `2`-morphisms of `B` are. -/
@[ext]
lemma hom₂_ext {f g : a ⟶ b} {η θ : f ⟶ g} (h : η.unop = θ.unop) : η = θ :=
  Quiver.Hom.unop_inj h

@[simp]
lemma unop_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (f ◁ η).unop = unop f ◁ η.unop :=
  rfl

@[simp]
lemma unop_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (η ▷ h).unop = η.unop ▷ unop h :=
  rfl

@[simp]
lemma op_whiskerLeft {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (θ : g ⟶ h) :
    (f ◁ θ).op = whiskerLeft (B := Co B) (op f) θ.op :=
  rfl

@[simp]
lemma op_whiskerRight {a b c : B} {f g : a ⟶ b} (θ : f ⟶ g) (h : b ⟶ c) :
    (θ ▷ h).op = whiskerRight (B := Co B) θ.op (op h) :=
  rfl

/-! Mathlib's lemmas `CategoryTheory.unop_id`, `CategoryTheory.unop_comp` and
`CategoryTheory.eqToHom_unop` apply to the hom-categories of `Co B` by unification, but `simp` does
not find them there: they are indexed by a category whose type of objects is an opposite `Cᵒᵖ`,
while the type of objects of a hom-category of `Co B` is `a ⟶ b` with `a b : Co B`, which is an
opposite only after unfolding the bicategory structure. The following lemmas restate them for
`Co B`, so that `simp` can convert `2`-morphisms of `Co B` back to `B`. -/

@[simp]
lemma unop_id₂ (f : a ⟶ b) : (𝟙 f).unop = 𝟙 (unop f) :=
  rfl

@[simp]
lemma unop_comp₂ {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) : (η ≫ θ).unop = θ.unop ≫ η.unop :=
  rfl

@[simp]
lemma eqToHom_unop {f g : a ⟶ b} (h : f = g) :
    (eqToHom h).unop = eqToHom (congrArg unop h.symm) :=
  CategoryTheory.eqToHom_unop h

end Hom₂

/-! ### Associators and unitors -/

section Coherence

variable {a b c d : Co B}

@[simp]
lemma unop_associator (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    Iso.unop (α_ f g h) = (α_ (unop f) (unop g) (unop h)).symm :=
  rfl

@[simp]
lemma unop_leftUnitor (f : a ⟶ b) : Iso.unop (λ_ f) = (λ_ (unop f)).symm :=
  rfl

@[simp]
lemma unop_rightUnitor (f : a ⟶ b) : Iso.unop (ρ_ f) = (ρ_ (unop f)).symm :=
  rfl

@[simp]
lemma associator_hom_unop (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).hom.unop = (α_ (unop f) (unop g) (unop h)).inv :=
  rfl

@[simp]
lemma associator_inv_unop (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).inv.unop = (α_ (unop f) (unop g) (unop h)).hom :=
  rfl

@[simp]
lemma leftUnitor_hom_unop (f : a ⟶ b) : (λ_ f).hom.unop = (λ_ (unop f)).inv :=
  rfl

@[simp]
lemma leftUnitor_inv_unop (f : a ⟶ b) : (λ_ f).inv.unop = (λ_ (unop f)).hom :=
  rfl

@[simp]
lemma rightUnitor_hom_unop (f : a ⟶ b) : (ρ_ f).hom.unop = (ρ_ (unop f)).inv :=
  rfl

@[simp]
lemma rightUnitor_inv_unop (f : a ⟶ b) : (ρ_ f).inv.unop = (ρ_ (unop f)).hom :=
  rfl

end Coherence

section CoherenceOp

variable {a b c d : B}

@[simp]
lemma op_associator (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    Iso.op (α_ f g h) =
      (associator (B := Co B) (op f) (op g) (op h)).symm :=
  rfl

@[simp]
lemma op_associator_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).hom.op = (associator (B := Co B) (op f) (op g) (op h)).inv :=
  rfl

@[simp]
lemma op_associator_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).inv.op = (associator (B := Co B) (op f) (op g) (op h)).hom :=
  rfl

@[simp]
lemma op_leftUnitor (f : a ⟶ b) : Iso.op (λ_ f) = (leftUnitor (B := Co B) (op f)).symm :=
  rfl

@[simp]
lemma op_leftUnitor_hom (f : a ⟶ b) : (λ_ f).hom.op = (leftUnitor (B := Co B) (op f)).inv :=
  rfl

@[simp]
lemma op_leftUnitor_inv (f : a ⟶ b) : (λ_ f).inv.op = (leftUnitor (B := Co B) (op f)).hom :=
  rfl

@[simp]
lemma op_rightUnitor (f : a ⟶ b) : Iso.op (ρ_ f) = (rightUnitor (B := Co B) (op f)).symm :=
  rfl

@[simp]
lemma op_rightUnitor_hom (f : a ⟶ b) : (ρ_ f).hom.op = (rightUnitor (B := Co B) (op f)).inv :=
  rfl

@[simp]
lemma op_rightUnitor_inv (f : a ⟶ b) : (ρ_ f).inv.op = (rightUnitor (B := Co B) (op f)).hom :=
  rfl

end CoherenceOp

/-! ### Strictness -/

/-- The 2-cell dual of a strict bicategory is strict: its `1`-morphisms compose as in `B`, and
its associators and unitors are the opposites of the inverses of `eqToIso`s. -/
instance instStrict [Bicategory.Strict B] : Bicategory.Strict (Co B) where
  id_comp f := congrArg op (Bicategory.Strict.id_comp (unop f))
  comp_id f := congrArg op (Bicategory.Strict.comp_id (unop f))
  assoc f g h := congrArg op (Bicategory.Strict.assoc (unop f) (unop g) (unop h))
  leftUnitor_eqToIso f := by
    ext
    simp [Bicategory.Strict.leftUnitor_eqToIso]
  rightUnitor_eqToIso f := by
    ext
    simp [Bicategory.Strict.rightUnitor_eqToIso]
  associator_eqToIso f g h := by
    ext
    simp [Bicategory.Strict.associator_eqToIso]

end Co

end TauCeti.Bicategory
