/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Basic
public import TauCeti.AlgebraicGeometry.Sites.ZariskiCoproduct

/-!
# Algebraic spaces from étale covers

An fppf sheaf `F` on schemes with representable diagonal, together with a family of étale
morphisms `a i : h_{U i} ⟶ F` that is jointly surjective after every base change to a scheme, is
an algebraic space: the morphisms glue to an étale atlas `h_{∐ U i} ⟶ F` (Stacks, Lemma 65.8.4
(02WQ)). The gluing uses `TauCeti.AlgebraicGeometry.exists_yoneda_sigma_desc`, since an fppf sheaf
is a Zariski sheaf.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.of_sigma`: a representable morphism
  `h_{∐ U i} ⟶ F` whose restrictions to the `h_{U i}` are étale and jointly surjective after every
  base change to a scheme is an étale atlas.
* `TauCeti.AlgebraicGeometry.Spaces.isAlgebraicSpace_of_etale_cover`: an fppf sheaf with
  representable diagonal and a jointly surjective family of étale morphisms from schemes is an
  algebraic space.

## References

* [Stacks Project, Lemma 65.8.4](https://stacks.math.columbia.edu/tag/02WQ)
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

variable {F : SchemePresheaf.{u}} {ι : Type u} {U : ι → Scheme.{u}}

/-- A morphism `b : h_{∐ U i} ⟶ F` that is representable by schemes is an étale atlas if its
restrictions `a i : h_{U i} ⟶ F` are representable by étale morphisms and are jointly surjective
after every base change to a scheme. -/
theorem EtaleAtlas.of_sigma {b : yoneda.obj (∐ U) ⟶ F} (hb : yoneda.relativelyRepresentable b)
    {a : ∀ i, yoneda.obj (U i) ⟶ F} (hab : ∀ i, yoneda.map (Sigma.ι U i) ≫ b = a i)
    (ha : ∀ i, MorphismProperty.presheaf @Etale (a i))
    (hs : ∀ ⦃T : Scheme.{u}⦄ (g : yoneda.obj T ⟶ F) (t : T),
      ∃ i, t ∈ Set.range ((ha i).rep.snd g)) :
    EtaleAtlas b := by
  refine .of_snd hb (fun T g ↦ ?_) (fun T g ↦ ⟨fun t ↦ ?_⟩)
  · -- Instance search does not derive the locality of étale morphisms from their ring-hom
    -- description.
    have : IsZariskiLocalAtSource @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtSource
    let 𝒱 := (sigmaOpenCover U).pullback₁ (hb.fst' g)
    refine IsZariskiLocalAtSource.of_openCover 𝒱 fun (i : ι) ↦ ?_
    have sq := ((IsPullback.of_hasPullback (hb.fst' g) (Sigma.ι U i)).flip.map yoneda).paste_vert
      (hb.isPullback' g)
    rw [← Functor.map_comp, hab] at sq
    exact (ha i).property g _ _ sq
  · obtain ⟨i, w, rfl⟩ := hs g t
    let k := hb.lift (yoneda.map ((ha i).rep.fst' g ≫ Sigma.ι U i)) ((ha i).rep.snd g)
      (by simpa [hab, Functor.relativelyRepresentable.map_fst'] using (ha i).rep.w g)
    exact ⟨k w, by rw [← Scheme.Hom.comp_apply, hb.lift_snd]⟩

/-- **Algebraic spaces from étale covers.** A sheaf `F` for the fppf topology with representable
diagonal is an algebraic space as soon as it admits a family of morphisms `h_{U i} ⟶ F` from
schemes, indexed by a type in the universe of the site, that are representable by étale morphisms
and jointly surjective after every base change to a scheme (Stacks, Lemma 65.8.4 (02WQ)). The
étale atlas is the induced morphism `h_{∐ U i} ⟶ F`. -/
theorem isAlgebraicSpace_of_etale_cover (hF : Presheaf.IsSheaf Scheme.fppfTopology F)
    (hΔ : RepresentableDiagonal F) (a : ∀ i, yoneda.obj (U i) ⟶ F)
    (ha : ∀ i, MorphismProperty.presheaf @Etale (a i))
    (hs : ∀ ⦃T : Scheme.{u}⦄ (g : yoneda.obj T ⟶ F) (t : T),
      ∃ i, t ∈ Set.range ((ha i).rep.snd g)) :
    IsAlgebraicSpace F := by
  have hZ : Presieve.IsSheaf Scheme.zariskiTopology F :=
    Presieve.isSheaf_of_le _ (Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage)
      ((isSheaf_iff_isSheaf_of_type _ _).1 hF)
  obtain ⟨b, hab⟩ := exists_yoneda_sigma_desc hZ a
  exact ⟨hF, hΔ, _, b, .of_sigma (hΔ.relativelyRepresentable b) hab ha hs⟩

end TauCeti.AlgebraicGeometry.Spaces
