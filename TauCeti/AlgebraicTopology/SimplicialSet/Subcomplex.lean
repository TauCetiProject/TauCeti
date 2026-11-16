/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Subcomplexes transported along isomorphisms and monomorphisms

An isomorphism `e : X ≅ Y` of simplicial sets carries a subcomplex `A` of `X` to the subcomplex
`A.preimage e.inv` of `Y`, and the inclusions of the two subcomplexes are isomorphic arrows. Hence
any class of morphisms that respects isomorphisms, such as the (inner) anodyne extensions, contains
one inclusion exactly when it contains the other.

More generally, a monomorphism `g : X ⟶ Y` identifies `X` with `range g`, and the preimage of a
subcomplex `B` of `Y` with `B ⊓ range g`. So the inclusion of `B.preimage g` into `X` is
isomorphic, as an arrow, to the inclusion of `B ⊓ range g` into `range g`. This lets a statement
about a subcomplex of `X` be read inside `Y`, for instance for the singular simplicial set of an
open subspace inside that of the ambient space.

Intersecting a bicartesian square of subcomplexes, such as the square of two subcomplexes, their
intersection and their union, with a further subcomplex gives a bicartesian square again. This
compares the Mayer–Vietoris sequences of the two squares.

## Main results

* `SSet.Subcomplex.isoOfPreimageEq`: for `A.preimage e.inv = B`, the restriction of `e` to an
  isomorphism `(A : SSet) ≅ B`, compatible with the inclusions.
* `SSet.Subcomplex.morphismProperty_ι_iff_of_preimage_eq`: for `A.preimage e.inv = B` and a class
  `W` of morphisms respecting isomorphisms, `W A.ι ↔ W B.ι`.
* `SSet.Subcomplex.BicartSq.inf_left`: intersecting a bicartesian square of subcomplexes with a
  further subcomplex gives a bicartesian square.
* `SSet.Subcomplex.preimageToInfRange`: the map from the preimage of a subcomplex `B` of `Y` along
  `g : X ⟶ Y` to `B ⊓ range g`, an isomorphism when `g` is a monomorphism.
* `SSet.Subcomplex.morphismProperty_ι_preimage_iff`: for a monomorphism `g` and a class `W` of
  morphisms respecting isomorphisms, `W` contains the inclusion of `B.preimage g` exactly when it
  contains the inclusion of `B ⊓ range g` into `range g`.
-/

public section

open CategoryTheory

universe u

namespace SSet.Subcomplex

variable {X Y : SSet.{u}}

/-- If an isomorphism `e : X ≅ Y` carries a subcomplex `A` of `X` to a subcomplex `B` of `Y`, it
restricts to an isomorphism between `A` and `B`. -/
def isoOfPreimageEq (e : X ≅ Y) {A : X.Subcomplex} {B : Y.Subcomplex} (h : A.preimage e.inv = B) :
    (A : SSet) ≅ B where
  hom := homOfLE (by rw [← h, ← preimage_comp, e.hom_inv_id, preimage_id]) ≫ fromPreimage _ e.hom
  inv := homOfLE h.ge ≫ fromPreimage _ e.inv
  hom_inv_id := by
    rw [← cancel_mono A.ι]
    simp
  inv_hom_id := by
    rw [← cancel_mono B.ι]
    simp

section

variable (e : X ≅ Y) {A : X.Subcomplex} {B : Y.Subcomplex} (h : A.preimage e.inv = B)

/-- The restriction of `e` to `A ≅ B` commutes with the inclusions and `e.hom`. -/
@[reassoc (attr := simp)]
lemma isoOfPreimageEq_hom_ι : (isoOfPreimageEq e h).hom ≫ B.ι = A.ι ≫ e.hom := by
  simp [isoOfPreimageEq]

/-- The restriction of `e` to `A ≅ B` commutes with the inclusions and `e.inv`. -/
@[reassoc (attr := simp)]
lemma isoOfPreimageEq_inv_ι : (isoOfPreimageEq e h).inv ≫ A.ι = B.ι ≫ e.inv := by
  simp [isoOfPreimageEq]

end

/-- If an isomorphism `e : X ≅ Y` carries a subcomplex `A` of `X` to a subcomplex `B` of `Y`, then a
class of morphisms respecting isomorphisms contains the inclusion of `A` exactly when it contains
the inclusion of `B`. -/
lemma morphismProperty_ι_iff_of_preimage_eq (W : MorphismProperty SSet.{u}) [W.RespectsIso]
    (e : X ≅ Y) {A : X.Subcomplex} {B : Y.Subcomplex} (h : A.preimage e.inv = B) :
    W A.ι ↔ W B.ι :=
  W.arrow_mk_iso_iff (Arrow.isoMk (isoOfPreimageEq e h) e (isoOfPreimageEq_hom_ι e h))

/-- Intersecting a bicartesian square of subcomplexes with a further subcomplex `S` gives a
bicartesian square. -/
lemma BicartSq.inf_left {S A₁ A₂ A₃ A₄ : X.Subcomplex} (hsq : BicartSq A₁ A₂ A₃ A₄) :
    BicartSq (S ⊓ A₁) (S ⊓ A₂) (S ⊓ A₃) (S ⊓ A₄) where
  sup_eq := by
    rw [← hsq.sup_eq]
    ext n σ
    simp [and_or_left]
  inf_eq := by
    rw [← hsq.inf_eq]
    exact (inf_inf_distrib_left S A₂ A₃).symm

section Mono

variable (g : X ⟶ Y) (B : Y.Subcomplex)

/-- The map from the preimage of a subcomplex `B` of `Y` along `g : X ⟶ Y` to `B ⊓ range g`
induced by `g`. It is an isomorphism when `g` is a monomorphism. -/
def preimageToInfRange : (B.preimage g : SSet) ⟶ ((B ⊓ range g : Y.Subcomplex) : SSet) :=
  lift ((B.preimage g).ι ≫ g) (by
    rintro n _ ⟨x, rfl⟩
    exact ⟨x.2, x.1, rfl⟩)

@[reassoc (attr := simp)]
lemma preimageToInfRange_ι : preimageToInfRange g B ≫ (B ⊓ range g).ι = (B.preimage g).ι ≫ g :=
  lift_ι _ _

instance [Mono g] : IsIso (preimageToInfRange g B) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  have hg : Function.Injective (g.app n) := (mono_iff_injective _).1 inferInstance
  refine ⟨fun x y h ↦ Subtype.ext (hg (congrArg Subtype.val h)), fun y ↦ ?_⟩
  obtain ⟨hyB, x, hx⟩ := y.2
  exact ⟨⟨x, by simpa [hx] using hyB⟩, Subtype.ext hx⟩

/-- Along a monomorphism `g : X ⟶ Y`, a class of morphisms respecting isomorphisms contains the
inclusion of the preimage of a subcomplex `B` of `Y` exactly when it contains the inclusion of
`B ⊓ range g` into `range g`. -/
lemma morphismProperty_ι_preimage_iff (W : MorphismProperty SSet.{u}) [W.RespectsIso] [Mono g] :
    W (B.preimage g).ι ↔ W (homOfLE (inf_le_right : B ⊓ range g ≤ range g)) :=
  W.arrow_mk_iso_iff (Arrow.isoMk (asIso (preimageToInfRange g B)) (asIso (toRange g)) (by
    rw [← cancel_mono (range g).ι]
    simp))

end Mono

end SSet.Subcomplex
