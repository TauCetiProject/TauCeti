/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Functoriality of the relative normalization

For quasi-compact quasi-separated morphisms `f : Y ⟶ J` and `g : Y' ⟶ J`, a morphism
`φ : Y ⟶ Y'` over `J` induces a morphism
`f.normalizationMap g φ hφ : f.normalization ⟶ g.normalization` of relative normalizations over
`J`, compatible with the canonical morphisms from `Y` and `Y'`.

When `f` is an open immersion, the normalization of `J` in `Y` does not change `Y`: since
normalization commutes with smooth base change (Mathlib's `Scheme.Hom.normalizationPullback`), the
part of `f.normalization` over the open image of `f` is the normalization of `Y` in itself, which is
`Y`. This is how normalizing a scheme in a dense open subscheme leaves that open alone.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.normalizationMap`: the morphism of relative normalizations
  induced by a morphism of sources over a common target.
* `AlgebraicGeometry.Scheme.Hom.normalizationLift`: the lift into `f.normalization` along a
  commuting square whose source relative normalization is an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.normalizationMap_fromNormalization`: the induced morphism lies
  over `J`.
* `AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationMap`: the induced morphism is
  compatible with the canonical morphisms from the sources.
* `AlgebraicGeometry.Scheme.Hom.normalizationMap_id` and
  `AlgebraicGeometry.Scheme.Hom.normalizationMap_comp`: the construction preserves identities and
  composition.
* `AlgebraicGeometry.Scheme.Hom.normalizationLift_fromNormalization`,
  `AlgebraicGeometry.Scheme.Hom.comp_normalizationLift`, and
  `AlgebraicGeometry.Scheme.Hom.eq_normalizationLift`: the triangle laws and uniqueness of the
  lift into a relative normalization.
* `AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticallyDominant_fromNormalization`: relative
  normalization of a scheme-theoretically dominant morphism is scheme-theoretically dominant.
* `AlgebraicGeometry.Scheme.Hom.isPullback_toNormalization`: over the image of an open immersion
  `f : Y ⟶ J`, the normalization of `J` in `Y` is `Y`.
* `AlgebraicGeometry.Scheme.Hom.canonicallyOverNormalization`: the relative normalization of
  `f : Y ⟶ J` lies canonically over `J` through `f.fromNormalization`.
* `AlgebraicGeometry.Scheme.Hom.isDominant_fromNormalization`: relative normalization of a dominant
  morphism is dominant, hence surjective.

## References

* The Stacks Project, Tag 035H (relative normalization) and Lemma 29.53.5 (03GV) (normalization
  commutes with smooth base change).
-/

public section

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory Limits

universe u

variable {Y Y' J : Scheme.{u}} (f : Y ⟶ J) [QuasiCompact f] [QuasiSeparated f]
  (g : Y' ⟶ J) [QuasiCompact g] [QuasiSeparated g]

/-- A morphism `φ : Y ⟶ Y'` over `J` induces a morphism `f.normalization ⟶ g.normalization` of
relative normalizations over `J`. -/
@[stacks 035J "existence, over a common base"]
noncomputable def normalizationMap (φ : Y ⟶ Y') (hφ : φ ≫ g = f) :
    f.normalization ⟶ g.normalization :=
  f.normalizationDesc (φ ≫ g.toNormalization) g.fromNormalization (by simp [hφ])
  deriving IsIntegralHom

/-- The morphism of relative normalizations induced by `φ` lies over `J`. -/
@[reassoc (attr := simp)]
theorem normalizationMap_fromNormalization (φ : Y ⟶ Y') (hφ : φ ≫ g = f) :
    f.normalizationMap g φ hφ ≫ g.fromNormalization = f.fromNormalization := by
  simp [normalizationMap]

/-- The morphism of relative normalizations induced by `φ` is compatible with the canonical
morphisms from `Y` and `Y'`. -/
@[reassoc (attr := simp)]
theorem toNormalization_normalizationMap (φ : Y ⟶ Y') (hφ : φ ≫ g = f) :
    f.toNormalization ≫ f.normalizationMap g φ hφ = φ ≫ g.toNormalization := by
  simp [normalizationMap]

/-- The identity of `Y` induces the identity of `f.normalization`. -/
@[simp]
theorem normalizationMap_id : f.normalizationMap f (𝟙 Y) (Category.id_comp f) = 𝟙 _ :=
  normalization.hom_ext f _ _ f.fromNormalization (by simp) (by simp) (by simp)

/-- The morphisms of relative normalizations induced by `φ` and then `ψ` compose to the one
induced by `φ ≫ ψ`. -/
@[reassoc (attr := simp)]
theorem normalizationMap_comp {Y'' : Scheme.{u}} (h : Y'' ⟶ J) [QuasiCompact h] [QuasiSeparated h]
    (φ : Y ⟶ Y') (hφ : φ ≫ g = f) (ψ : Y' ⟶ Y'') (hψ : ψ ≫ h = g) :
    f.normalizationMap g φ hφ ≫ g.normalizationMap h ψ hψ =
      f.normalizationMap h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) :=
  normalization.hom_ext f _ _ h.fromNormalization (by simp) (by simp) (by simp)

/-- The relative normalization of `f : Y ⟶ J` lies canonically over `J` through
`f.fromNormalization`, hence over every `S` that `J` lies over. -/
@[simps! over]
noncomputable instance canonicallyOverNormalization : f.normalization.CanonicallyOver J where
  hom := f.fromNormalization

/-- The normalization morphism lies over the target. -/
instance isOver_fromNormalization : f.fromNormalization.IsOver J where
  comp_over := Category.comp_id _

/-- The morphism of relative normalizations induced by `φ` lies over `J`. -/
instance isOver_normalizationMap (φ : Y ⟶ Y') (hφ : φ ≫ g = f) :
    (f.normalizationMap g φ hφ).IsOver J where
  comp_over := f.normalizationMap_fromNormalization g φ hφ

/-- The canonical morphism from `Y` to its relative normalization is scheme-theoretically
dominant. -/
instance isSchemeTheoreticallyDominant_toNormalization :
    IsSchemeTheoreticallyDominant f.toNormalization :=
  ⟨f.ker_toNormalization⟩

/-- Over the image of an open immersion `f : Y ⟶ J`, the relative normalization of `J` in `Y` is
`Y` itself: the square formed by `f.toNormalization`, `f.fromNormalization` and `f` is a pullback.
This is normalization commuting with the smooth base change along `f`, together with the fact that
the normalization of `Y` in itself, along the isomorphism `pullback.snd f f`, is trivial. -/
theorem isPullback_toNormalization [IsOpenImmersion f] :
    IsPullback f.toNormalization (𝟙 Y) f.fromNormalization f := by
  -- `f.normalizationPullback f` identifies `pullback f.fromNormalization f` with the normalization
  -- of `Y` along the isomorphism `pullback.snd f f`, which is an isomorphism onto `Y`.
  have : IsIso ((pullback.snd f f).toNormalization ≫ (pullback.snd f f).fromNormalization) := by
    rw [toNormalization_fromNormalization]
    infer_instance
  have := IsIso.of_isIso_comp_left (pullback.snd f f).toNormalization
    (pullback.snd f f).fromNormalization
  have : IsIso (f.normalizationPullback f ≫ pullback.snd f.fromNormalization f) := by
    rw [normalizationPullback_snd]
    infer_instance
  have := IsIso.of_isIso_comp_left (f.normalizationPullback f) (pullback.snd f.fromNormalization f)
  have h : inv (pullback.snd f.fromNormalization f) =
      pullback.lift f.toNormalization (𝟙 Y) (by simp) :=
    IsIso.inv_eq_of_inv_hom_id (pullback.lift_snd _ _ _)
  refine (IsPullback.of_hasPullback f.fromNormalization f).of_iso
    (asIso (pullback.snd f.fromNormalization f)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ (by simp) (by simp) (by simp)
  rw [asIso_hom, Iso.refl_hom, Category.comp_id, ← cancel_epi (inv (pullback.snd _ _)),
    IsIso.inv_hom_id_assoc, h, pullback.lift_fst]

section Lift

/-- **Lift into a relative normalization along a commuting square.** Given a commuting square
`u ≫ f = g ≫ v` whose source relative normalization `g.fromNormalization` is an isomorphism, `Y`
lifts to `f.normalization`. -/
noncomputable def normalizationLift {U U' Y Y' : Scheme.{u}}
    (g : U ⟶ Y) [QuasiCompact g] [QuasiSeparated g] [IsIso g.fromNormalization]
    (f : U' ⟶ Y') [QuasiCompact f] [QuasiSeparated f]
    (u : U ⟶ U') (v : Y ⟶ Y') (h : u ≫ f = g ≫ v) :
    Y ⟶ f.normalization :=
  inv g.fromNormalization ≫
    g.normalizationMap (pullback.snd f v) (pullback.lift u g h) (pullback.lift_snd _ _ _) ≫
    f.normalizationPullback v ≫ pullback.fst f.fromNormalization v

/-- The lift into `f.normalization` lies over `v : Y ⟶ Y'`. -/
@[reassoc (attr := simp)]
theorem normalizationLift_fromNormalization {U U' Y Y' : Scheme.{u}}
    (g : U ⟶ Y) [QuasiCompact g] [QuasiSeparated g] [IsIso g.fromNormalization]
    (f : U' ⟶ Y') [QuasiCompact f] [QuasiSeparated f]
    (u : U ⟶ U') (v : Y ⟶ Y') (h : u ≫ f = g ≫ v) :
    g.normalizationLift f u v h ≫ f.fromNormalization = v := by
  simp only [normalizationLift, Category.assoc, pullback.condition,
    normalizationPullback_snd_assoc, normalizationMap_fromNormalization_assoc,
    IsIso.inv_hom_id_assoc]

/-- Precomposing the lift into `f.normalization` with `g` factors `u ≫ f.toNormalization`. -/
@[reassoc (attr := simp)]
theorem comp_normalizationLift {U U' Y Y' : Scheme.{u}}
    (g : U ⟶ Y) [QuasiCompact g] [QuasiSeparated g] [IsIso g.fromNormalization]
    (f : U' ⟶ Y') [QuasiCompact f] [QuasiSeparated f]
    (u : U ⟶ U') (v : Y ⟶ Y') (h : u ≫ f = g ≫ v) :
    g ≫ g.normalizationLift f u v h = u ≫ f.toNormalization := by
  have hg : g ≫ inv g.fromNormalization = g.toNormalization := by
    rw [IsIso.comp_inv_eq, toNormalization_fromNormalization]
  rw [normalizationLift, ← Category.assoc, ← Category.assoc, ← Category.assoc, hg,
    toNormalization_normalizationMap, Category.assoc, Category.assoc,
    toNormalization_normalizationPullback_fst, pullback.lift_fst_assoc]

/-- **Uniqueness of the lift into a relative normalization.** If `g : U ⟶ Y` is
scheme-theoretically dominant with `g.fromNormalization` an isomorphism, then any morphism
`k : Y ⟶ f.normalization` making both triangles commute agrees with
`g.normalizationLift f u v h`. -/
theorem eq_normalizationLift {U U' Y Y' : Scheme.{u}}
    (g : U ⟶ Y) [QuasiCompact g] [QuasiSeparated g] [IsIso g.fromNormalization]
    [IsSchemeTheoreticallyDominant g]
    (f : U' ⟶ Y') [QuasiCompact f] [QuasiSeparated f]
    {u : U ⟶ U'} {v : Y ⟶ Y'} (h : u ≫ f = g ≫ v)
    {k : Y ⟶ f.normalization}
    (hk₁ : g ≫ k = u ≫ f.toNormalization)
    (hk₂ : k ≫ f.fromNormalization = v) :
    k = g.normalizationLift f u v h :=
  TauCeti.ext_of_isSchemeTheoreticallyDominant g f.fromNormalization
    (by simp [hk₂]) (by simp [hk₁])

end Lift

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti

open CategoryTheory AlgebraicGeometry

universe u

/-- Relative normalization of a scheme-theoretically dominant morphism is
scheme-theoretically dominant over the target. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticallyDominant_fromNormalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsSchemeTheoreticallyDominant f] : IsSchemeTheoreticallyDominant f.fromNormalization := by
  have : IsSchemeTheoreticallyDominant (f.toNormalization ≫ f.fromNormalization) := by
    rw [f.toNormalization_fromNormalization]
    infer_instance
  exact IsSchemeTheoreticallyDominant.of_comp f.toNormalization f.fromNormalization

/-- Relative normalization of a dominant morphism is dominant over the target. Being integral,
hence universally closed, the normalization morphism is then surjective. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isDominant_fromNormalization {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [IsDominant f] :
    IsDominant f.fromNormalization := by
  have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
    rw [f.toNormalization_fromNormalization]
    infer_instance
  exact IsDominant.of_comp f.toNormalization f.fromNormalization

end TauCeti
