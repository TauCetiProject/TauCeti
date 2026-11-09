/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Base change of a fibre product

Let `X ⟶ S` and `Y ⟶ S` be two objects over `S`, and let `X' ⟶ S'` and `Y' ⟶ S'` be their base
changes along `f : S' ⟶ S`. Then the fibre product `X' ×_{S'} Y'` is the base change of
`X ×_S Y` along `f`, through the morphism `pullback.map` induced by `X' ⟶ X` and `Y' ⟶ Y`
(`CategoryTheory.IsPullback.pullback_map`). In other words, base change preserves fibre
products over the base. The canonical comparison isomorphism
`CategoryTheory.Limits.pullbackBaseChangeIso` has explicit projection formulas and is natural
in both objects over the base.

Fibre products over a common base also commute with each other: if `T` is the fibre product of
`T₁` and `T₂` over `S`, and `X` that of `X₁` and `X₂`, then `T ×_S X` is the fibre product of
`T₁ ×_S X₁` and `T₂ ×_S X₂` over `S`, through the morphisms `pullback.map` induced by the
projections (`CategoryTheory.IsPullback.pullback_map_pullback_map`). This is the
middle-four interchange of fibre products,
`(T₁ ×_S T₂) ×_S (X₁ ×_S X₂) ≅ (T₁ ×_S X₁) ×_S (T₂ ×_S X₂)`.

The canonical identification of an iterated fibre product with a direct fibre product commutes
with maps in the first factor
(`CategoryTheory.Limits.pullbackLeftPullbackSndIso_inv_naturality`).
-/

public section

namespace CategoryTheory.IsPullback

open Limits

variable {C : Type*} [Category* C] {S S' X Y X' Y' : C} {f : S' ⟶ S} {pX : X ⟶ S} {pY : Y ⟶ S}
  {pX' : X' ⟶ S'} {pY' : Y' ⟶ S'} {iX : X' ⟶ X} {iY : Y' ⟶ Y}

/-- **Base change preserves fibre products.** If `X' ⟶ S'` and `Y' ⟶ S'` are the base changes of
`X ⟶ S` and `Y ⟶ S` along `f : S' ⟶ S`, then `X' ×_{S'} Y'`, as an object over `S'`, is the base
change of `X ×_S Y` along `f`. -/
theorem pullback_map [HasPullback pX pY] [HasPullback pX' pY']
    (hX : IsPullback pX' iX f pX) (hY : IsPullback pY' iY f pY) :
    IsPullback (pullback.fst pX' pY' ≫ pX')
      (pullback.map pX' pY' pX pY iX iY f hX.w hY.w) f (pullback.fst pX pY ≫ pX) := by
  -- `X' ×_{S'} Y'` is the base change of `X ×_S Y ⟶ X` along `X' ⟶ X`
  have top : IsPullback (pullback.map pX' pY' pX pY iX iY f hX.w hY.w)
      (pullback.fst pX' pY') (pullback.fst pX pY) iX := by
    refine .of_right (h₁₂ := pullback.snd pX pY) ?_ (by simp)
      (IsPullback.of_hasPullback pX pY).flip
    simpa [hX.w] using (IsPullback.of_hasPullback pX' pY').flip.paste_horiz hY.flip
  exact (top.paste_vert hX.flip).flip

section Interchange

variable {T T₁ T₂ X₁ X₂ : C} {t : T ⟶ S} {t₁ : T₁ ⟶ S} {t₂ : T₂ ⟶ S} {x : X ⟶ S} {x₁ : X₁ ⟶ S}
  {x₂ : X₂ ⟶ S} {p₁ : T ⟶ T₁} {p₂ : T ⟶ T₂} {q₁ : X ⟶ X₁} {q₂ : X ⟶ X₂}

/-- **Fibre products commute with fibre products.** If `T` is the fibre product of `T₁` and `T₂`
over `S`, and `X` is the fibre product of `X₁` and `X₂` over `S`, then `T ×_S X` is the fibre
product of `T₁ ×_S X₁` and `T₂ ×_S X₂` over `S`, with the projections induced by those of `T` and
`X`. -/
theorem pullback_map_pullback_map [HasPullback t x] [HasPullback t₁ x₁] [HasPullback t₂ x₂]
    (hT : IsPullback p₁ p₂ t₁ t₂) (hX : IsPullback q₁ q₂ x₁ x₂)
    (ht₁ : p₁ ≫ t₁ = t) (ht₂ : p₂ ≫ t₂ = t) (hx₁ : q₁ ≫ x₁ = x) (hx₂ : q₂ ≫ x₂ = x) :
    IsPullback (pullback.map t x t₁ x₁ p₁ q₁ (𝟙 S) (by simp [ht₁]) (by simp [hx₁]))
      (pullback.map t x t₂ x₂ p₂ q₂ (𝟙 S) (by simp [ht₂]) (by simp [hx₂]))
      (pullback.snd t₁ x₁ ≫ x₁) (pullback.snd t₂ x₂ ≫ x₂) := by
  have hc₁ {W : C} (a : W ⟶ pullback t₁ x₁) :
      a ≫ pullback.fst t₁ x₁ ≫ t₁ = a ≫ pullback.snd t₁ x₁ ≫ x₁ := by
    rw [pullback.condition]
  have hc₂ {W : C} (b : W ⟶ pullback t₂ x₂) :
      b ≫ pullback.fst t₂ x₂ ≫ t₂ = b ≫ pullback.snd t₂ x₂ ≫ x₂ := by
    rw [pullback.condition]
  -- A cone over the two factor fibre products gives compatible maps to `T` and to `X`.
  let lT (c : PullbackCone (pullback.snd t₁ x₁ ≫ x₁) (pullback.snd t₂ x₂ ≫ x₂)) : c.pt ⟶ T :=
    hT.lift (c.fst ≫ pullback.fst _ _) (c.snd ≫ pullback.fst _ _) <| by
      simpa only [Category.assoc, hc₁, hc₂] using c.condition
  let lX (c : PullbackCone (pullback.snd t₁ x₁ ≫ x₁) (pullback.snd t₂ x₂ ≫ x₂)) : c.pt ⟶ X :=
    hX.lift (c.fst ≫ pullback.snd _ _) (c.snd ≫ pullback.snd _ _) <| by
      simpa only [Category.assoc] using c.condition
  refine ⟨⟨by simp [hx₁, hx₂]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ pullback.lift (lT c) (lX c) ?_) (fun c ↦ ?_) (fun c ↦ ?_) (fun c m h₁ h₂ ↦ ?_)⟩⟩
  · rw [← ht₁, ← hx₁, hT.lift_fst_assoc, hX.lift_fst_assoc, Category.assoc, Category.assoc,
      pullback.condition]
  · apply pullback.hom_ext <;> simp [lT, lX]
  · apply pullback.hom_ext <;> simp [lT, lX]
  · apply pullback.hom_ext
    · apply hT.hom_ext
      · simpa [lT] using congrArg (· ≫ pullback.fst t₁ x₁) h₁
      · simpa [lT] using congrArg (· ≫ pullback.fst t₂ x₂) h₂
    · apply hX.hom_ext
      · simpa [lX] using congrArg (· ≫ pullback.snd t₁ x₁) h₁
      · simpa [lX] using congrArg (· ≫ pullback.snd t₂ x₂) h₂

end Interchange

end CategoryTheory.IsPullback

namespace CategoryTheory.Limits

section BaseChange

variable {C : Type*} [Category* C] [HasPullbacks C] {X Y S S' : C}
  (f : X ⟶ S) (g : Y ⟶ S) (φ : S' ⟶ S)

/-- Base change of a fibre product is the fibre product of the base changes, with both
base-changed factors regarded as objects over `S'` through their second projections. -/
noncomputable def pullbackBaseChangeIso :
    pullback (pullback.fst f g ≫ f) φ ≅
      pullback (pullback.snd f φ) (pullback.snd g φ) :=
  (((IsPullback.of_hasPullback f φ).flip.pullback_map
    (IsPullback.of_hasPullback g φ).flip).flip.isoPullback).symm

/-- The first projection of the base-change comparison is the base change of the first
projection. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeIso_hom_fst :
    (pullbackBaseChangeIso f g φ).hom ≫ pullback.fst _ _ =
      pullback.map (pullback.fst f g ≫ f) φ f φ (pullback.fst f g) (𝟙 S') (𝟙 S)
        (by simp) (by simp) := by
  apply (cancel_epi (pullbackBaseChangeIso f g φ).inv).mp
  apply pullback.hom_ext <;> simp [pullbackBaseChangeIso]

/-- The second projection of the base-change comparison is the base change of the second
projection. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeIso_hom_snd :
    (pullbackBaseChangeIso f g φ).hom ≫ pullback.snd _ _ =
      pullback.map (pullback.fst f g ≫ f) φ g φ (pullback.snd f g) (𝟙 S') (𝟙 S)
        (by simp [pullback.condition]) (by simp) := by
  apply (cancel_epi (pullbackBaseChangeIso f g φ).inv).mp
  apply pullback.hom_ext <;> simp [pullbackBaseChangeIso, pullback.condition]

/-- The inverse base-change comparison projects to the original fibre product by the
projections from both base changes. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeIso_inv_fst :
    (pullbackBaseChangeIso f g φ).inv ≫ pullback.fst _ _ =
      pullback.map _ _ f g (pullback.fst f φ) (pullback.fst g φ)
        φ pullback.condition.symm pullback.condition.symm := by
  simp [pullbackBaseChangeIso]

/-- The base-change comparison is an isomorphism over the new base. -/
@[reassoc (attr := simp)]
theorem pullbackBaseChangeIso_inv_snd :
    (pullbackBaseChangeIso f g φ).inv ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.snd f φ := by
  simp [pullbackBaseChangeIso]

/-- The base-change comparison is natural in both objects over the base. -/
@[reassoc]
theorem pullbackBaseChangeIso_naturality {X' Y' : C}
    (f' : X' ⟶ S) (g' : Y' ⟶ S) (a : X ⟶ X') (b : Y ⟶ Y')
    (ha : a ≫ f' = f) (hb : b ≫ g' = g) :
    pullback.map (pullback.fst f g ≫ f) φ (pullback.fst f' g' ≫ f') φ
        (pullback.map f g f' g' a b (𝟙 S) (by simp [ha]) (by simp [hb]))
        (𝟙 S') (𝟙 S) (by simp [ha]) (by simp) ≫
        (pullbackBaseChangeIso f' g' φ).hom =
      (pullbackBaseChangeIso f g φ).hom ≫
        pullback.map (pullback.snd f φ) (pullback.snd g φ)
          (pullback.snd f' φ) (pullback.snd g' φ)
          (pullback.map f φ f' φ a (𝟙 S') (𝟙 S) (by simp [ha]) (by simp))
          (pullback.map g φ g' φ b (𝟙 S') (𝟙 S) (by simp [hb]) (by simp))
          (𝟙 S') (by simp) (by simp) := by
  ext <;> simp

end BaseChange

/-- The inverse canonical isomorphism between a direct and an iterated pullback is natural in
morphisms of the first factor over the common base. -/
@[reassoc]
theorem pullbackLeftPullbackSndIso_inv_naturality
    {C : Type*} [Category* C] {S T U X Y : C}
    (a : X ⟶ S) (b : Y ⟶ S) (g : T ⟶ S) (h : U ⟶ T)
    [HasPullback a g] [HasPullback b g]
    [HasPullback (pullback.snd a g) h] [HasPullback (pullback.snd b g) h]
    (φ : X ⟶ Y) (hφ : φ ≫ b = a) :
    pullback.map a (h ≫ g) b (h ≫ g) φ (𝟙 U) (𝟙 S) (by simp [hφ]) (by simp) ≫
        (pullbackLeftPullbackSndIso b g h).inv =
      (pullbackLeftPullbackSndIso a g h).inv ≫
        pullback.map (pullback.snd a g) h (pullback.snd b g) h
          (pullback.map a g b g φ (𝟙 T) (𝟙 S) (by simp [hφ]) (by simp)) (𝟙 U) (𝟙 T)
          (by simp) (by simp) := by
  ext <;> simp

end CategoryTheory.Limits
