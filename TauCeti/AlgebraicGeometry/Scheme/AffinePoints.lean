/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Morphisms of schemes from their affine points

A scheme `X` is covered by affine schemes `Spec A`, so it is determined by its functor of affine
points `A ↦ (Spec A ⟶ X)`, a Yoneda principle for the dense subcategory of affine schemes. This
file records the three forms of this principle used to construct and compare schemes defined by a
universal property on affine schemes, such as the Grassmannian.

* Two morphisms `X ⟶ Y` agreeing on every affine point `Spec A ⟶ X` are equal
  (`AlgebraicGeometry.Scheme.hom_ext_of_forall_spec`).
* A family of maps `(Spec A ⟶ X) → (Spec A ⟶ Y)`, natural in `Spec A`, is composition with a
  unique morphism `X ⟶ Y` (`AlgebraicGeometry.Scheme.homOfAffinePoints`), glued over the affine
  cover of `X`.
* A commutative square of schemes is a pullback square as soon as it is one on affine points
  (`AlgebraicGeometry.Scheme.isPullback_of_forall_spec`).

## Main definitions

* `AlgebraicGeometry.Scheme.homOfAffinePoints F hF`: the morphism `X ⟶ Y` inducing a natural map
  `F` on affine points.

## Main results

* `AlgebraicGeometry.Scheme.comp_homOfAffinePoints`: composing an affine point with
  `homOfAffinePoints F hF` applies `F`.
* `AlgebraicGeometry.Scheme.isPullback_of_forall_spec`: a square is a pullback square if every
  compatible pair of affine points has a unique lift.

## References

* [The Stacks Project, Tag 01JF](https://stacks.math.columbia.edu/tag/01JF), for schemes as
  functors on rings.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- **Morphisms are determined by their affine points.** Two morphisms `X ⟶ Y` which agree after
composition with every morphism `Spec A ⟶ X` are equal. -/
theorem hom_ext_of_forall_spec {f g : X ⟶ Y}
    (h : ∀ (A : CommRingCat.{u}) (a : Spec A ⟶ X), a ≫ f = a ≫ g) : f = g :=
  X.affineOpenCover.openCover.hom_ext _ _ fun _ ↦ h _ _

/-- **The morphism inducing a natural map on affine points.** A map `F` sending each morphism
`Spec A ⟶ X` to a morphism `Spec A ⟶ Y`, compatibly with precomposition by morphisms of affine
schemes, is composition with this morphism `X ⟶ Y` (`comp_homOfAffinePoints`). It is glued from
the images under `F` of the members of the affine cover of `X`. -/
noncomputable def homOfAffinePoints
    (F : ∀ {A : CommRingCat.{u}}, (Spec A ⟶ X) → (Spec A ⟶ Y))
    (hF : ∀ {A B : CommRingCat.{u}} (φ : Spec B ⟶ Spec A) (a : Spec A ⟶ X),
      F (φ ≫ a) = φ ≫ F a) : X ⟶ Y :=
  have h (i j : X.affineOpenCover.I₀) :
      pullback.fst (X.affineOpenCover.f i) (X.affineOpenCover.f j) ≫ F (X.affineOpenCover.f i) =
        pullback.snd _ _ ≫ F (X.affineOpenCover.f j) :=
    hom_ext_of_forall_spec fun _ c ↦ by
      simp only [← Category.assoc, ← hF]
      simp [pullback.condition]
  X.affineOpenCover.openCover.glueMorphisms (fun i ↦ F (X.affineOpenCover.f i)) h

/-- Composing an affine point `a : Spec A ⟶ X` with `homOfAffinePoints F hF` gives `F a`. -/
@[reassoc (attr := simp)]
theorem comp_homOfAffinePoints
    (F : ∀ {A : CommRingCat.{u}}, (Spec A ⟶ X) → (Spec A ⟶ Y))
    (hF : ∀ {A B : CommRingCat.{u}} (φ : Spec B ⟶ Spec A) (a : Spec A ⟶ X),
      F (φ ≫ a) = φ ≫ F a) {A : CommRingCat.{u}} (a : Spec A ⟶ X) :
    a ≫ homOfAffinePoints F hF = F a := by
  -- on the members of the affine cover of `X`, `homOfAffinePoints F hF` is `F`
  have hι (i : X.affineOpenCover.I₀) :
      X.affineOpenCover.f i ≫ homOfAffinePoints F hF = F (X.affineOpenCover.f i) := by
    rw [homOfAffinePoints]
    exact X.affineOpenCover.openCover.ι_glueMorphisms _ _ i
  -- so the claim holds on the affine points of the pullbacks of these members along `a`
  have key (i : X.affineOpenCover.I₀) {B : CommRingCat.{u}}
      (c : Spec B ⟶ pullback a (X.affineOpenCover.f i)) :
      c ≫ pullback.fst _ _ ≫ a ≫ homOfAffinePoints F hF = c ≫ pullback.fst _ _ ≫ F a := by
    rw [pullback.condition_assoc, hι]
    simp only [← Category.assoc, ← hF]
    simp [pullback.condition]
  -- and these pullbacks cover `Spec A`
  exact Cover.hom_ext (X.affineOpenCover.openCover.pullback₁ a) _ _ fun i ↦
    hom_ext_of_forall_spec fun _ c ↦ key i c

/-- **A pullback square on affine points is a pullback square.** A commutative square of schemes
is a pullback square when every pair of affine points `Spec A ⟶ X`, `Spec A ⟶ Y` with the same
image in `Z` lifts uniquely to `P`. -/
theorem isPullback_of_forall_spec {P Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : ∀ (A : CommRingCat.{u}) (a : Spec A ⟶ X) (b : Spec A ⟶ Y), a ≫ f = b ≫ g →
      ∃! c : Spec A ⟶ P, c ≫ fst = a ∧ c ≫ snd = b) :
    IsPullback fst snd f g := by
  -- the lift of an affine point of the pullback, chosen by `h`
  have h' {A : CommRingCat.{u}} (a : Spec A ⟶ pullback f g) :=
    h A (a ≫ pullback.fst f g) (a ≫ pullback.snd f g) (by simp [pullback.condition])
  let L {A : CommRingCat.{u}} (a : Spec A ⟶ pullback f g) : Spec A ⟶ P := (h' a).exists.choose
  have hL {A : CommRingCat.{u}} (a : Spec A ⟶ pullback f g) :
      L a ≫ fst = a ≫ pullback.fst f g ∧ L a ≫ snd = a ≫ pullback.snd f g :=
    (h' a).exists.choose_spec
  have hL_unique {A : CommRingCat.{u}} (a : Spec A ⟶ pullback f g) (c : Spec A ⟶ P)
      (hc₁ : c ≫ fst = a ≫ pullback.fst f g) (hc₂ : c ≫ snd = a ≫ pullback.snd f g) :
      c = L a :=
    (h' a).unique ⟨hc₁, hc₂⟩ (hL a)
  let inv : pullback f g ⟶ P := homOfAffinePoints L fun φ a ↦
    (hL_unique _ _ (by rw [Category.assoc, (hL a).1, Category.assoc])
      (by rw [Category.assoc, (hL a).2, Category.assoc])).symm
  have hinv {A : CommRingCat.{u}} (a : Spec A ⟶ pullback f g) : a ≫ inv = L a :=
    comp_homOfAffinePoints _ _ a
  let e : P ≅ pullback f g :=
    { hom := pullback.lift fst snd w
      inv := inv
      hom_inv_id := hom_ext_of_forall_spec fun A c ↦ by
        rw [← Category.assoc, hinv, Category.comp_id]
        exact (hL_unique _ c (by simp) (by simp)).symm
      inv_hom_id := hom_ext_of_forall_spec fun A c ↦ by
        rw [← Category.assoc, hinv, Category.comp_id]
        exact pullback.hom_ext (by simp [(hL c).1]) (by simp [(hL c).2]) }
  exact .of_iso_pullback ⟨w⟩ e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end AlgebraicGeometry.Scheme
