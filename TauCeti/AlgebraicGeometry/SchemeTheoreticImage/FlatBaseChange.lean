/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Flat base change of scheme-theoretic images

The scheme-theoretic image of a quasi-compact morphism commutes with flat base change.
We prove this first as an equality of ideal sheaves, then construct the canonical
isomorphism between the image after base change and the base change of the image.
The isomorphism respects both the closed immersion and the map from the source.

In particular, schematic closures can be compared after localization or completion
without discarding nilpotents. No reducedness or Noetherian hypothesis is needed.

## References

* The Stacks Project, Tag 081I (flat base change of scheme-theoretic images).
-/

public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y X' Y' : Scheme.{u}}

/-- The ideal sheaf defining a scheme-theoretic image pulls back under flat base change
of a quasi-compact morphism. -/
theorem ker_eq_comap_of_isPullback_of_flat (f : X ⟶ Y) {g : Y' ⟶ Y}
    {p : X' ⟶ X} {f' : X' ⟶ Y'} (H : IsPullback p f' f g)
    [QuasiCompact f] [Flat g] : f'.ker = f.ker.comap g := by
  let a : X' ⟶ pullback f.imageι g :=
    pullback.lift (p ≫ f.toImage) f' (by simpa using H.w)
  have ha : IsPullback p a f.toImage (pullback.fst f.imageι g) := by
    have h : IsPullback p (a ≫ pullback.snd f.imageι g)
        (f.toImage ≫ f.imageι) g := by simpa [a] using H
    exact h.of_bot (by simp [a]) (.of_hasPullback _ _)
  have : IsSchemeTheoreticallyDominant a :=
    IsSchemeTheoreticallyDominant.of_isPullback ha
  calc
    f'.ker = (a ≫ pullback.snd f.imageι g).ker := by simp [a]
    _ = (pullback.snd f.imageι g).ker := a.ker_comp_of_isSchemeTheoreticallyDominant _
    _ = f.ker.comap g := by
      simpa only [Scheme.IdealSheafData.ker_subschemeι] using
        Scheme.IdealSheafData.ker_eq_comap_of_isPullback f.imageι
          (IsPullback.of_hasPullback f.imageι g).flip

variable (f : X ⟶ Y) (g : Y' ⟶ Y) [QuasiCompact f] [Flat g]

/-- The scheme-theoretic image after flat base change is canonically the base change
of the scheme-theoretic image. -/
def imagePullbackIso : (pullback.snd f g).image ≅ pullback f.imageι g := by
  have h : (pullback.snd f g).imageι.ker = (pullback.snd f.imageι g).ker := by
    have h₁ := f.ker_eq_comap_of_isPullback_of_flat (IsPullback.of_hasPullback f g)
    have h₂ : (pullback.snd f.imageι g).ker = f.ker.comap g := by
      simpa only [Scheme.IdealSheafData.ker_subschemeι] using
        Scheme.IdealSheafData.ker_eq_comap_of_isPullback f.imageι
          (IsPullback.of_hasPullback f.imageι g).flip
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using h₁.trans h₂.symm
  let l := IsClosedImmersion.lift (pullback.snd f.imageι g)
    (pullback.snd f g).imageι h.symm.le
  have : IsIso l := IsClosedImmersion.isIso_lift _ _ h.symm
  exact asIso l

/-- The comparison of images respects the closed immersions into the new target. -/
@[reassoc (attr := simp)]
theorem imagePullbackIso_hom_snd :
    (f.imagePullbackIso g).hom ≫ pullback.snd f.imageι g = (pullback.snd f g).imageι := by
  dsimp only [imagePullbackIso, asIso]
  exact IsClosedImmersion.lift_fac _ _ _

/-- The inverse comparison respects the closed immersions into the new target. -/
@[reassoc (attr := simp)]
theorem imagePullbackIso_inv_imageι :
    (f.imagePullbackIso g).inv ≫ (pullback.snd f g).imageι = pullback.snd f.imageι g := by
  rw [Iso.inv_comp_eq, imagePullbackIso_hom_snd]

/-- The comparison of images also respects the factorization of the base-changed morphism. -/
@[reassoc (attr := simp)]
theorem toImage_imagePullbackIso_hom :
    (pullback.snd f g).toImage ≫ (f.imagePullbackIso g).hom =
      pullback.lift (pullback.fst f g ≫ f.toImage) (pullback.snd f g)
        (by simp [pullback.condition]) := by
  apply (cancel_mono (pullback.snd f.imageι g)).mp
  simp

end AlgebraicGeometry.Scheme.Hom
