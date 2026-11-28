/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Hilbert.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank

/-!
# Finite locally free closed subschemes on affine schemes

The finite locally free degree condition is equivalent to the corresponding condition on
the quotient of the coordinate ring by the ideal of global sections.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Over affine schemes, a closed subscheme is finite locally free of degree `d` exactly
when its quotient coordinate algebra is finite, flat and of rank `d`. -/
theorem Scheme.IdealSheafData.isFiniteLocallyFreeOfDegree_iff_of_isAffine
    [IsAffine X] [IsAffine S] (I : X.IdealSheafData) (f : X ⟶ S) (d : ℕ) :
    I.IsFiniteLocallyFreeOfDegree f d ↔
      RingHom.IsFiniteLocallyFreeOfRank d
        ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp f.appTop.hom) := by
  set ψ := (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp
    f.appTop.hom
  have hZ : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have hp : (I.subschemeι ≫ f).appTop.hom =
      (I.subschemeObjIso ⟨⊤, isAffineOpen_top _⟩).inv.hom.comp ψ := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rw [Scheme.Hom.appTop, I.subschemeι_app ⟨⊤, isAffineOpen_top _⟩]
    -- The subscheme coordinate isomorphism identifies its inclusion with the quotient map.
    rfl
  have hfin : IsFinite (I.subschemeι ≫ f) ↔ ψ.Finite := by
    rw [MorphismProperty.arrow_mk_iso_iff @IsFinite
      (arrowIsoSpecΓOfIsAffine (I.subschemeι ≫ f)), IsFinite.SpecMap_iff, hp]
    exact RingHom.finite_respectsIso.cancel_right_isIso (CommRingCat.ofHom ψ) _
  have hflat : Flat (I.subschemeι ≫ f) ↔ ψ.Flat := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Flat), hp]
    exact RingHom.Flat.respectsIso.cancel_right_isIso (CommRingCat.ofHom ψ) _
  rw [Scheme.IdealSheafData.isFiniteLocallyFreeOfDegree_iff,
    RingHom.isFiniteLocallyFreeOfRank_iff, hfin, hflat]
  refine and_congr_right fun h₁ ↦ and_congr_right fun h₂ ↦ ?_
  have := hfin.2 h₁
  have := hflat.2 h₂
  have hrank (t : S) : (I.subschemeι ≫ f).finrank t =
      ψ.finrank (S.isoSpec.hom t) := by
    rw [Scheme.Hom.finrank_eq_finrank_appTop, hp]
    exact RingHom.finrank_comp_left_of_bijective ψ (I.subschemeObjIso _).inv.hom
      (ConcreteCategory.bijective_of_isIso (I.subschemeObjIso _).inv) h₁ h₂ _
  rw [funext_iff]
  refine (forall_congr' fun t ↦ by rw [hrank]).trans ?_
  exact ((Scheme.homeoOfIso S.isoSpec).surjective.forall
    (p := fun P : PrimeSpectrum Γ(S, ⊤) ↦ ψ.finrank P = d)).symm

end AlgebraicGeometry
