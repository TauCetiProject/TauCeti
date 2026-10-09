/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.GlobalCoordinates
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Equality

/-!
# Equality of projective morphisms on a degree-one chart

On a standard chart whose denominator has degree one, two systems of homogeneous
coordinates define the same scheme morphism exactly when their degree-`n` coordinates
are related by the `n`th power of one unit. This detects equality on nonreduced value
rings as well as on fields, and supplies the chart criterion for fibers of projective
orbit morphisms.

The chart morphisms use `HomogeneousLocalization.Away.lift` and `Proj.awayι`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace AlgebraicGeometry.Proj

universe u

variable {A B σ : Type u} [CommRing A] [CommRing B] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]

variable {X : Scheme.{u}}

/-- If one homogeneous coordinate is a unit, the projective morphism factors through
its standard affine chart via the degree-zero coordinate map. -/
theorem fromOfGlobalSections_eq_toSpecΓ_awayLift (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) (hu : IsUnit (f t)) :
    fromOfGlobalSections 𝒜 f hf =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Away.lift 𝒜 f hu)) ≫ awayι 𝒜 t ht hd := by
  let U := X.basicOpen (f t)
  have hU : U = ⊤ := X.basicOpen_of_isUnit hu
  have : IsIso U.ι := by rw [hU, ← Scheme.topIso_hom]; infer_instance
  rw [← cancel_epi U.ι]
  have hchart := congrArg (fun e ↦ e ≫ (basicOpen 𝒜 t).ι)
    (fromOfGlobalSections_resLE 𝒜 f hf hd ht)
  rw [Scheme.Hom.resLE_comp_ι,
    TauCeti.ProjectiveSpectrum.toBasicOpenOfGlobalSections_eq] at hchart
  rw [hchart]
  simp only [Category.assoc, basicOpenIsoSpec_inv_ι]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc]
  simp only [← Spec.map_comp_assoc]
  congr 2
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    RingHom.comp_homogeneousLocalizationAwayLift]

/-- Homogeneous coordinates in a ring with an invertible chart denominator give the
corresponding projective morphism from its spectrum. -/
theorem fromOfGlobalSections_Spec_eq_awayLift (f : A →+* B)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    {t : A} {d : ℕ} (hd : 0 < d) (ht : t ∈ 𝒜 d) (hu : IsUnit (f t)) :
    fromOfGlobalSections 𝒜 ((Scheme.ΓSpecIso (.of B)).inv.hom.comp f)
        (by rw [← Ideal.map_map, hf, Ideal.map_top]) =
      Spec.map (CommRingCat.ofHom (Away.lift 𝒜 f hu)) ≫ awayι 𝒜 t ht hd := by
  rw [fromOfGlobalSections_eq_toSpecΓ_awayLift _ _ hd ht
    (hu.map (Scheme.ΓSpecIso (.of B)).inv.hom),
    ← RingHom.comp_homogeneousLocalizationAwayLift (Scheme.ΓSpecIso (.of B)).inv.hom f hu,
    CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc, CommRingCat.ofHom_hom]
  rw [← Scheme.isoSpec_Spec_inv, Scheme.toSpecΓ_isoSpec_inv_assoc]

/-- Two morphisms read on the same degree-one projective chart agree exactly when all
homogeneous coordinates differ by powers of a common unit in the value ring. -/
theorem SpecMap_awayLift_awayι_eq_iff (f g : A →+* B) {t : A} (ht : t ∈ 𝒜 1)
    (hf : IsUnit (f t)) (hg : IsUnit (g t)) :
    Spec.map (CommRingCat.ofHom (Away.lift 𝒜 f hf)) ≫ awayι 𝒜 t ht one_pos =
        Spec.map (CommRingCat.ofHom (Away.lift 𝒜 g hg)) ≫ awayι 𝒜 t ht one_pos ↔
      ∃ c : Bˣ, ∀ n, ∀ a ∈ 𝒜 n, g a = c ^ n * f a := by
  rw [cancel_mono]
  rw [← Away.lift_eq_iff_exists_unit f g ht hf hg]
  constructor
  · intro h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  · intro h
    rw [h]

end AlgebraicGeometry.Proj
