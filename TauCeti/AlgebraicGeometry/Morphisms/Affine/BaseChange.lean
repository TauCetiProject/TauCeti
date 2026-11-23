/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine morphisms and base-changed projection composites

Affineness of an over-morphism after base change is compared with affineness of its
composite with the projection to the original target.
-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- If a base change of an over-morphism is affine and the base map is affine,
its composite with the projection to the original target is affine. -/
theorem snd_comp_of_overPullbackMap
    {S T : Scheme.{u}} (a : T ⟶ S) [IsAffineHom a]
    (X Y : Over S) (f : X ⟶ Y)
    (hf : IsAffineHom (((Over.pullback a).map f).left)) :
    IsAffineHom (pullback.snd a X.hom ≫ f.left) := by
  have : IsAffineHom (pullback.fst Y.hom a) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback Y.hom a).flip inferInstance
  have : IsAffineHom (((Over.pullback a).map f).left) := hf
  have hcomp : IsAffineHom (pullback.fst X.hom a ≫ f.left) := by
    have eq : ((Over.pullback a).map f).left ≫ pullback.fst Y.hom a =
        pullback.fst X.hom a ≫ f.left := by simp [Over.pullback_map_left]
    rw [← eq]
    infer_instance
  have eq : pullback.snd a X.hom ≫ f.left =
      (pullbackSymmetry a X.hom).hom ≫ (pullback.fst X.hom a ≫ f.left) := by simp
  rw [eq]
  infer_instance

/-- A base-changed over-morphism is affine if its composite with the projection
to the original target is affine. No separatedness assumption on the base map is needed. -/
theorem overPullbackMap_of_snd_comp
    {S T : Scheme.{u}} (a : T ⟶ S) (X Y : Over S) (f : X ⟶ Y)
    (hf : IsAffineHom (pullback.snd a X.hom ≫ f.left)) :
    IsAffineHom (((Over.pullback a).map f).left) := by
  have : IsAffineHom (pullback.snd a X.hom ≫ f.left) := hf
  have : IsAffineHom (pullback.fst X.hom a ≫ f.left) := by
    have eq : pullback.fst X.hom a ≫ f.left =
        (pullbackSymmetry X.hom a).hom ≫ (pullback.snd a X.hom ≫ f.left) := by simp
    rw [eq]
    infer_instance
  let g := pullback.fst X.hom a ≫ f.left
  let b := pullback.fst Y.hom a
  let f' := ((Over.pullback a).map f).left
  let r : pullback g b ⟶ pullback X.hom a :=
    pullback.lift (pullback.fst g b ≫ pullback.fst X.hom a)
      (pullback.snd g b ≫ pullback.snd Y.hom a) (by
        simp only [Category.assoc, ← Over.w f]
        rw [← pullback.condition]
        simpa only [g, b, Category.assoc] using
          congrArg (fun k ↦ k ≫ Y.hom) (pullback.condition (f := g) (g := b)))
  let s : pullback X.hom a ⟶ pullback g b :=
    pullback.lift (𝟙 _) f' (by simp [g, b, f', Over.pullback_map_left])
  have hrs : s ≫ r = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [s, r, f', Over.pullback_map_left]
  have hr : r ≫ f' = pullback.snd g b := by
    apply pullback.hom_ext
    · simpa [r, f', Over.pullback_map_left, g, b] using
        (pullback.condition (f := g) (g := b))
    · simp [r, f', Over.pullback_map_left]
  have : IsAffineHom g := inferInstanceAs
    (IsAffineHom (pullback.fst X.hom a ≫ f.left))
  have : IsAffineHom (pullback.snd g b) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback g b) inferInstance
  have : IsSeparated (r ≫ f') := by rw [hr]; infer_instance
  have : IsSeparated r := IsSeparated.of_comp r f'
  have : IsClosedImmersion (s ≫ r) := by rw [hrs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s r
  have eq : f' = s ≫ pullback.snd g b := by simp [s]
  have : IsAffineHom f' := by rw [eq]; infer_instance
  exact this

end AlgebraicGeometry.Scheme.Hom
