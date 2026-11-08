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

## Main results

* `AlgebraicGeometry.Scheme.Hom.normalizationMap_fromNormalization`: the induced morphism lies
  over `J`.
* `AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationMap`: the induced morphism is
  compatible with the canonical morphisms from the sources.
* `AlgebraicGeometry.Scheme.Hom.normalizationMap_id` and
  `AlgebraicGeometry.Scheme.Hom.normalizationMap_comp`: the construction preserves identities and
  composition.
* `AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticallyDominant_fromNormalization`: relative
  normalization of a scheme-theoretically dominant morphism is scheme-theoretically dominant.
* `AlgebraicGeometry.Scheme.Hom.isPullback_toNormalization`: over the image of an open immersion
  `f : Y ⟶ J`, the normalization of `J` in `Y` is `Y`.

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

end TauCeti
