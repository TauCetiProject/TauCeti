/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Coproducts of morphisms of schemes

For a family of morphisms `f i : X i ⟶ Y i` of schemes, indexed by a possibly infinite type, the
square formed by `f i`, the coprojections `X i ⟶ ∐ X` and `Y i ⟶ ∐ Y`, and `∐ f : ∐ X ⟶ ∐ Y` is a
pullback: the preimage of the component `Y i` is the component `X i`
(`AlgebraicGeometry.isPullback_sigmaι_sigmaι_sigmaMap`). Since the components `Y i` form an open
cover of `∐ Y`, a property of morphisms that is local on the target holds for `∐ f` exactly when it
holds for every `f i` (`AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap_iff`). For instance a
coproduct of quasi-compact quasi-separated morphisms is quasi-compact and quasi-separated, even over
an infinite index type, where `∐ Y` is not quasi-compact.

## Main results

* `AlgebraicGeometry.sigmaMap_preimage_opensRange_sigmaι`,
  `AlgebraicGeometry.isPullback_sigmaι_sigmaι_sigmaMap`: the components of `∐ f` are pullbacks.
* `AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap_iff`: a property local on the target holds
  for `∐ f` iff it holds for every `f i`.

These generalize and adapt, from binary to arbitrary coproducts, Mathlib's
`AlgebraicGeometry.isPullback_inl_inl_coprodMap` (in `Mathlib.AlgebraicGeometry.Limits`) and
`AlgebraicGeometry.IsZariskiLocalAtTarget.coprodMap` (in
`Mathlib.AlgebraicGeometry.Morphisms.Basic`).
-/

public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {σ : Type v} [Small.{u} σ] {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i)

/-- The preimage under `∐ f` of the component `Y i` of `∐ Y` is the component `X i` of `∐ X`. -/
@[simp]
lemma sigmaMap_preimage_opensRange_sigmaι (i : σ) :
    Limits.Sigma.map f ⁻¹ᵁ (Sigma.ι Y i).opensRange = (Sigma.ι X i).opensRange := by
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨j, x, rfl⟩ : ∃ (j : σ) (x' : X j), Sigma.ι X j x' = x :=
      (sigmaOpenCover X).exists_eq x
    rw [← Scheme.Hom.comp_apply, Sigma.ι_map, Scheme.Hom.comp_apply] at hxy
    obtain ⟨rfl, -⟩ := Sigma.mk.inj ((sigmaι_eq_iff Y i j y _).mp hxy)
    exact ⟨x, by simp⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨f i x, by simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]⟩

/-- **The components of a coproduct of morphisms are pullbacks.** For `f i : X i ⟶ Y i`, the
square formed by `f i`, `∐ f` and the coprojections of `X i` and `Y i` is a pullback. -/
lemma isPullback_sigmaι_sigmaι_sigmaMap (i : σ) :
    IsPullback (f i) (Sigma.ι X i) (Sigma.ι Y i) (Limits.Sigma.map f) :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp) (sigmaMap_preimage_opensRange_sigmaι f i)

/-- **Properties local on the target and coproducts.** A property of morphisms of schemes that is
local on the target holds for the coproduct `∐ f` of a family of morphisms exactly when it holds
for each of them. -/
lemma IsZariskiLocalAtTarget.sigmaMap_iff (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] : P (Limits.Sigma.map f) ↔ ∀ i, P (f i) := by
  refine ⟨fun h i ↦
      IsZariskiLocalAtTarget.of_isPullback (isPullback_sigmaι_sigmaι_sigmaMap f i).flip h,
    fun h ↦ IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover Y) fun i ↦ ?_⟩
  have hi := (isPullback_sigmaι_sigmaι_sigmaMap f i).flip
  refine (P.arrow_mk_iso_iff (Arrow.isoMk hi.isoPullback (Iso.refl _) ?_)).mp (h i)
  exact hi.isoPullback_hom_snd

end AlgebraicGeometry
