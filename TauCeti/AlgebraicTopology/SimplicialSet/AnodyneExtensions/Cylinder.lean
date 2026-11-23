/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.PushoutProduct
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Lifting homotopies along left and right fibrations

The ends `Z ⊗ {0}` and `Z ⊗ {1}` of the cylinder `Z ⊗ Δ[1]` are anodyne extensions
(`SSet.anodyneExtensions_ι₀`, `SSet.anodyneExtensions_ι₁`): they are the images of
`Z ⊗ Λ[1, 0]` and `Z ⊗ Λ[1, 1]`, and the product of `Z` with a horn inclusion is anodyne. So a
homotopy into the base of a Kan fibration lifts, starting from a lift of either of its ends.
More precisely, the start is left anodyne (`SSet.leftAnodyneExtensions_ι₀`) and the end is right
anodyne (`SSet.rightAnodyneExtensions_ι₁`).

More generally, a left (resp. right) fibration has the covering homotopy extension property at
the start (resp. end) with respect to every monomorphism `i : A ⟶ B`
(`SSet.exists_lift_cylinder_ι₀_of_mono`,
`SSet.exists_lift_cylinder_ι₁_of_mono`): a homotopy `B ⊗ Δ[1] ⟶ Y` lifts, extending a lift of
one of its ends `B ⊗ {k}` and a compatible lift of its restriction to `A ⊗ Δ[1]`. This is lifting
against the pushout-product of `i` with `Λ[1, k] ⟶ Δ[1]`, the inclusion of
`B ⊗ {k} ∪ A ⊗ Δ[1]` into `B ⊗ Δ[1]`. It is left anodyne for `k = 0` and right anodyne for
`k = 1` (`SSet.leftAnodyneExtensions_pushoutObjObjι`, `SSet.rightAnodyneExtensions_pushoutObjObjι`
in Tau Ceti), following the proof by Joël Riou and Jack McKoen in Mathlib that it is anodyne
(`SSet.anodyneExtensions_pushoutObjObjι`).

## References

* P. Gabriel and M. Zisman, *Calculus of fractions and homotopy theory*, Ergebnisse der
  Mathematik 35, Springer, 1967, Chapter IV, Section 2.
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter I, Section 4.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty MonoidalCategory CartesianMonoidalCategory
  HomotopicalAlgebra Simplicial

namespace SSet

open modelCategoryQuillen

/-- The end `Z ⊗ {k}` of the cylinder `Z ⊗ Δ[1]`; it is `ι₀` for `k = 0` and `ι₁` for `k = 1`. -/
private noncomputable def cylinderEnd (Z : SSet.{u}) (k : Fin 2) : Z ⟶ Z ⊗ Δ[1] :=
  lift (𝟙 Z) (const (stdSimplex.obj₀Equiv.symm k))

private lemma cylinderEnd_zero (Z : SSet.{u}) : cylinderEnd Z 0 = ι₀ :=
  CartesianMonoidalCategory.hom_ext _ _ (by simp [cylinderEnd]) (by simp [cylinderEnd])

private lemma cylinderEnd_one (Z : SSet.{u}) : cylinderEnd Z 1 = ι₁ :=
  CartesianMonoidalCategory.hom_ext _ _ (by simp [cylinderEnd]) (by simp [cylinderEnd])

/-- The product of `Z` with the inclusion of the horn `Λ[1, k]`, which is the vertex `k`, factors
through the end `Z ⊗ {k}` of the cylinder. -/
private lemma whiskerLeft_horn_one_ι (Z : SSet.{u}) (k : Fin 2) :
    Z ◁ Λ[1, k].ι = fst _ _ ≫ cylinderEnd Z k :=
  CartesianMonoidalCategory.hom_ext _ _ (by simp [cylinderEnd])
    (by simp [cylinderEnd, horn_one_ι_eq_const, comp_const])

/-- The end `Z ⊗ {k}` of the cylinder factors through `Z ⊗ Λ[1, k]` by a section of the
projection to `Z`. -/
private lemma exists_section_whiskerLeft_horn_one_ι (Z : SSet.{u}) (k : Fin 2) :
    ∃ s : Z ⟶ Z ⊗ (Λ[1, k] : SSet.{u}), s ≫ fst _ _ = 𝟙 Z ∧
      s ≫ Z ◁ Λ[1, k].ι = cylinderEnd Z k :=
  -- Any map to the horn `Λ[1, k]` composes with its inclusion to the constant map at `k`.
  ⟨lift (𝟙 Z) (stdSimplex.isTerminalObj₀.from Z ≫ horn.ι k (k + 1) (by fin_cases k <;> decide)),
    by simp,
    by simp only [cylinderEnd, lift_whiskerLeft, Category.assoc, horn_one_ι_eq_const, comp_const]⟩

/-- Lifting against the product with the one-dimensional horn suffices to lift against the
corresponding end of the cylinder. -/
private lemma hasLiftingProperty_cylinderEnd (Z : SSet.{u}) (k : Fin 2)
    {E B : SSet.{u}} (p : E ⟶ B) [HasLiftingProperty (Z ◁ Λ[1, k].ι) p] :
    HasLiftingProperty (cylinderEnd Z k) p := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_whiskerLeft_horn_one_ι Z k
  refine ⟨fun {f g} sq ↦ ?_⟩
  -- Lift against `Z ⊗ Λ[1, k] ⟶ Z ⊗ Δ[1]` and restrict along the section `s`.
  have sq' : CommSq (fst _ _ ≫ f) (Z ◁ Λ[1, k].ι) p g :=
    ⟨by rw [whiskerLeft_horn_one_ι, Category.assoc, sq.w, Category.assoc]⟩
  exact ⟨⟨{ l := sq'.lift
            fac_left := by rw [← hs₂, Category.assoc, sq'.fac_left, reassoc_of% hs₁] }⟩⟩

/-- The start `Z ⊗ {0}` of the cylinder `Z ⊗ Δ[1]` is a left anodyne extension. -/
lemma leftAnodyneExtensions_ι₀ (Z : SSet.{u}) :
    leftAnodyneExtensions (ι₀ : Z ⟶ Z ⊗ Δ[1]) := by
  rw [← cylinderEnd_zero, leftAnodyneExtensions_eq_llp]
  intro E B p hp
  have : LeftFibration p := ⟨hp⟩
  have := leftAnodyneExtensions.hasLiftingProperty
    ((leftAnodyneExtensions.horn_ι (n := 1) (i := 0) (by decide)).whiskerLeft Z) p
  exact hasLiftingProperty_cylinderEnd Z 0 p

/-- The end `Z ⊗ {1}` of the cylinder `Z ⊗ Δ[1]` is a right anodyne extension. -/
lemma rightAnodyneExtensions_ι₁ (Z : SSet.{u}) :
    rightAnodyneExtensions (ι₁ : Z ⟶ Z ⊗ Δ[1]) := by
  rw [← cylinderEnd_one, rightAnodyneExtensions_eq_llp]
  intro E B p hp
  have : RightFibration p := ⟨hp⟩
  have := rightAnodyneExtensions.hasLiftingProperty
    ((rightAnodyneExtensions.horn_ι (n := 1) (i := 1) (by decide)).whiskerLeft Z) p
  exact hasLiftingProperty_cylinderEnd Z 1 p

/-- The end `Z ⊗ {0}` of the cylinder `Z ⊗ Δ[1]` is an anodyne extension. -/
lemma anodyneExtensions_ι₀ (Z : SSet.{u}) : anodyneExtensions (ι₀ : Z ⟶ Z ⊗ Δ[1]) :=
  leftAnodyneExtensions_le_anodyneExtensions _ (leftAnodyneExtensions_ι₀ Z)

/-- The end `Z ⊗ {1}` of the cylinder `Z ⊗ Δ[1]` is an anodyne extension. -/
lemma anodyneExtensions_ι₁ (Z : SSet.{u}) : anodyneExtensions (ι₁ : Z ⟶ Z ⊗ Δ[1]) :=
  rightAnodyneExtensions_le_anodyneExtensions _ (rightAnodyneExtensions_ι₁ Z)

/-- The covering homotopy extension property of `p : X ⟶ Y` when it lifts against the
pushout-product of `i : A ⟶ B` with the horn `Λ[1, k]`: a homotopy `H : B ⊗ Δ[1] ⟶ Y` lifts
along `p`, extending a lift `g` of its restriction to `B ⊗ {k}` and a lift `L` of its restriction
to `A ⊗ Δ[1]` which agree on `A ⊗ {k}`. -/
private lemma exists_lift_cylinderEnd {A B X Y : SSet.{u}} (k : Fin 2) (i : A ⟶ B)
    (p : X ⟶ Y)
    [HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (curriedTensor SSet.{u}) i Λ[1, k].ι).ι p] (H : B ⊗ Δ[1] ⟶ Y) (g : B ⟶ X) (L : A ⊗ Δ[1] ⟶ X)
    (hg : g ≫ p = cylinderEnd B k ≫ H) (hL : L ≫ p = i ▷ Δ[1] ≫ H)
    (hgL : i ≫ g = cylinderEnd A k ≫ L) :
    ∃ L' : B ⊗ Δ[1] ⟶ X, cylinderEnd B k ≫ L' = g ∧ i ▷ Δ[1] ≫ L' = L ∧ L' ≫ p = H := by
  -- Lift against the pushout-product of `i` with the vertex `k` of `Δ[1]`, the
  -- inclusion of `B ⊗ {k} ∪ A ⊗ Δ[1]`, on which `g` and `L` define a map.
  let P := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i Λ[1, k].ι
  let φ : P.pt ⟶ X := P.isPushout.desc (fst _ _ ≫ g) L (by
    dsimp
    rw [whiskerLeft_horn_one_ι, Category.assoc, ← hgL, whiskerRight_fst_assoc])
  have sq : CommSq φ P.ι p H := ⟨P.hom_ext
    (by simp only [φ, IsPushout.inl_desc_assoc, P.inl_ι_assoc, curriedTensor_obj_map,
      whiskerLeft_horn_one_ι, Category.assoc, hg])
    (by simp [φ, hL])⟩
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_whiskerLeft_horn_one_ι B k
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · have e : B ◁ Λ[1, k].ι = P.inl ≫ P.ι := P.inl_ι.symm
    -- The end is the composite of the section `s` with `B ⊗ Λ[1, k] ⟶ B ⊗ Δ[1]`.
    rw [← hs₂, e, Category.assoc, Category.assoc, sq.fac_left]
    simp [φ, reassoc_of% hs₁]
  · have e : i ▷ Δ[1] = P.inr ≫ P.ι := P.inr_ι.symm
    rw [e, Category.assoc, sq.fac_left]
    simp [φ]

/-- The covering homotopy extension property of a left fibration `p : X ⟶ Y` with respect to a
monomorphism `i : A ⟶ B`: a homotopy `H : B ⊗ Δ[1] ⟶ Y` lifts along `p`, extending a lift `g` of
its start and a lift `L` of its restriction to `A ⊗ Δ[1]` which agree on `A ⊗ {0}`. -/
theorem exists_lift_cylinder_ι₀_of_mono {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i] (p : X ⟶ Y)
    [LeftFibration p] (H : B ⊗ Δ[1] ⟶ Y) (g : B ⟶ X) (L : A ⊗ Δ[1] ⟶ X) (hg : g ≫ p = ι₀ ≫ H)
    (hL : L ≫ p = i ▷ Δ[1] ≫ H) (hgL : i ≫ g = ι₀ ≫ L) :
    ∃ L' : B ⊗ Δ[1] ⟶ X, ι₀ ≫ L' = g ∧ i ▷ Δ[1] ≫ L' = L ∧ L' ≫ p = H := by
  have := (leftAnodyneExtensions_pushoutObjObjι
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i Λ[1, 0].ι)
    (.horn_ι (by decide))).hasLiftingProperty p
  simp only [← cylinderEnd_zero] at hg hgL ⊢
  exact exists_lift_cylinderEnd 0 i p H g L hg hL hgL

/-- The covering homotopy extension property of a right fibration `p : X ⟶ Y` with respect to a
monomorphism `i : A ⟶ B`, backwards in time: a homotopy `H : B ⊗ Δ[1] ⟶ Y` lifts along `p`,
extending a lift `g` of its end and a lift `L` of its restriction to `A ⊗ Δ[1]` which agree on
`A ⊗ {1}`. -/
theorem exists_lift_cylinder_ι₁_of_mono {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i] (p : X ⟶ Y)
    [RightFibration p] (H : B ⊗ Δ[1] ⟶ Y) (g : B ⟶ X) (L : A ⊗ Δ[1] ⟶ X) (hg : g ≫ p = ι₁ ≫ H)
    (hL : L ≫ p = i ▷ Δ[1] ≫ H) (hgL : i ≫ g = ι₁ ≫ L) :
    ∃ L' : B ⊗ Δ[1] ⟶ X, ι₁ ≫ L' = g ∧ i ▷ Δ[1] ≫ L' = L ∧ L' ≫ p = H := by
  have := (rightAnodyneExtensions_pushoutObjObjι
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i Λ[1, 1].ι)
    (.horn_ι (by decide))).hasLiftingProperty p
  simp only [← cylinderEnd_one] at hg hgL ⊢
  exact exists_lift_cylinderEnd 1 i p H g L hg hL hgL

end SSet
