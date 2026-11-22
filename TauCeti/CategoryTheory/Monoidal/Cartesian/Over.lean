/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Products and base-change factorizations in a slice category

The pullback of two sections over the same base has equal projections to that base.
Consequently a product chart followed by multiplication in a monoid object evaluates as the
product of its two sections. This is useful for restricting group operations to a subscheme
covered by sections.

This file also records `CategoryTheory.Over.exists_pullback_snd_comp_eq_of_pullback`: if
the base change of `f : X ⊗ Y ⟶ Z` in `Over S` along `y ≫ Y.hom` factors through the second
projection in `Over R`, then the restriction of `f.left` to the fibre of
`pullback.snd X.hom Y.hom` over `y : R ⟶ Y.left` factors through the projection to `R`.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace TauCeti.CategoryTheory.Over

variable {C : Type*} [Category* C] [HasPullbacks C] {S : C}

/-- On a product of two section charts, multiplication after a map to a monoid object is the
product of the resulting sections, pulled back from the base. -/
@[reassoc]
theorem pullback_map_comp_mul_left {D G : Over S} [MonObj G] (i : D ⟶ G)
    (a b : 𝟙_ (Over S) ⟶ D) :
    pullback.map (a.left ≫ D.hom) (b.left ≫ D.hom) D.hom D.hom a.left b.left (𝟙 S)
      (Category.comp_id _) (Category.comp_id _) ≫ ((i ⊗ₘ i) ≫ μ[G]).left =
      pullback.fst (a.left ≫ D.hom) (b.left ≫ D.hom) ≫ ((a ≫ i) * (b ≫ i)).left := by
  have hsb (a : 𝟙_ (Over S) ⟶ D) : a.left ≫ D.hom = 𝟙 S := Over.w a
  have hab : pullback.fst (a.left ≫ D.hom) (b.left ≫ D.hom) =
      pullback.snd (a.left ≫ D.hom) (b.left ≫ D.hom) := by
    have h := pullback.condition (f := a.left ≫ D.hom) (g := b.left ≫ D.hom)
    simp only [hsb] at h
    exact (Category.comp_id _).symm.trans (h.trans (Category.comp_id _))
  rw [Hom.mul_def]
  simp only [Over.comp_left, Over.lift_left, Over.tensorHom_left]
  refine (Category.assoc _ _ _).symm.trans ?_
  conv_rhs => rw [← Category.assoc]
  apply congrArg (fun k ↦ k ≫ (μ[G]).left)
  apply pullback.hom_ext
  · simp [pullback.map, Category.assoc]
  · simp [pullback.map, Category.assoc, hab]

end TauCeti.CategoryTheory.Over

namespace CategoryTheory.Over

variable {C : Type*} [Category* C] [HasPullbacks C] {S : C}

/-- If the base change of `f : X ⊗ Y ⟶ Z` in `Over S` along `y ≫ Y.hom` factors through the second
projection in `Over R`, then the restriction of `f.left` to the pullback of
`pullback.snd X.hom Y.hom` along `y : R ⟶ Y.left` factors through the projection to `R`. -/
theorem exists_pullback_snd_comp_eq_of_pullback {R : C} {X Y Z : Over S} (f : X ⊗ Y ⟶ Z)
    (y : R ⟶ Y.left)
    {gR : (Over.pullback (y ≫ Y.hom)).obj Y ⟶ (Over.pullback (y ≫ Y.hom)).obj Z}
    (hgR : Functor.LaxMonoidal.μ (Over.pullback (y ≫ Y.hom)) X Y ≫
      (Over.pullback (y ≫ Y.hom)).map f = snd _ _ ≫ gR) :
    ∃ h : R ⟶ Z.left,
      pullback.fst (pullback.snd X.hom Y.hom) y ≫ f.left =
        pullback.snd (pullback.snd X.hom Y.hom) y ≫ h := by
  let c := pullback.snd X.hom Y.hom
  let s := y ≫ Y.hom
  let F : Over S ⥤ Over R := Over.pullback s
  let wX : Limits.pullback c y ⟶ (F.obj X).left :=
    pullback.lift (pullback.fst c y ≫ pullback.fst X.hom Y.hom) (pullback.snd c y)
      (by rw [Category.assoc, pullback.condition, pullback.condition_assoc])
  let yR : R ⟶ (F.obj Y).left := pullback.lift y (𝟙 R) (by simp [s])
  let φ : Limits.pullback c y ⟶ Limits.pullback (F.obj X).hom (F.obj Y).hom :=
    pullback.lift wX (pullback.snd c y ≫ yR) (by simp [F, wX, yR])
  have hμ : φ ≫ (Functor.LaxMonoidal.μ F X Y).left ≫ pullback.fst (X ⊗ Y).hom s =
      pullback.fst c y := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, μ_pullback_left_fst_fst X Y]
      simp [φ, F, wX]
    · rw [Category.assoc, Category.assoc, μ_pullback_left_fst_snd X Y]
      simp [φ, F, yR, c, pullback.condition]
  have hmap : (F.map f).left ≫ pullback.fst Z.hom s = pullback.fst (X ⊗ Y).hom s ≫ f.left := by
    simp [F]
  refine ⟨yR ≫ gR.left ≫ pullback.fst Z.hom s, ?_⟩
  calc pullback.fst c y ≫ f.left
    _ = φ ≫ (Functor.LaxMonoidal.μ F X Y ≫ F.map f).left ≫ pullback.fst Z.hom s := by
      rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc _ _ f.left, ← Category.assoc φ, hμ]
    _ = pullback.snd c y ≫ yR ≫ gR.left ≫ pullback.fst Z.hom s := by
      rw [hgR, Over.comp_left]
      simp [φ, F, s, Category.assoc]

end CategoryTheory.Over
