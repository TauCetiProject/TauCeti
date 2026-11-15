/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Naturality

/-!
# Local unit rescaling and equality of projective morphisms

Two systems of global homogeneous coordinates on an affine scheme define the same
projective morphism precisely when, on an affine open cover, their degree-`n`
coordinates differ by the `n`th power of a unit. The degree-one coordinates of the
first system must generate the unit ideal. The units may vary between opens.

This criterion compares scheme morphisms, including their structure-sheaf maps. It
therefore detects infinitesimal fibers and applies to nonreduced schemes. It combines
the degree-one chart criterion `Proj.SpecMap_awayLift_awayι_eq_iff` with descent of
equality along an open cover.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Proj

universe u v

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}}

/-- Locally unit-proportional homogeneous coordinates define the same projective
morphism. The source scheme and the members of the cover need not be affine. -/
theorem fromOfGlobalSections_eq_of_openCover_unit_rescaling
    (f g : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤)
    (𝒰 : X.OpenCover.{v}) (h : ∀ i, ∃ c : Γ(𝒰.X i, ⊤)ˣ,
      ∀ n, ∀ a ∈ 𝒜 n, (𝒰.f i).appTop (g a) = c ^ n * (𝒰.f i).appTop (f a)) :
    fromOfGlobalSections 𝒜 f hf = fromOfGlobalSections 𝒜 g hg := by
  refine 𝒰.hom_ext _ _ fun i ↦ ?_
  rw [fromOfGlobalSections_naturality, fromOfGlobalSections_naturality]
  obtain ⟨c, hc⟩ := h i
  exact (TauCeti.ProjectiveSpectrum.fromOfGlobalSections_eq_of_unit_rescaling
    𝒜 _ _ c hc (by rw [← Ideal.map_map, hf, Ideal.map_top])).symm

/-- On an affine source covered by its degree-one coordinates, equality of projective
morphisms is equivalent to unit rescaling of homogeneous coordinates on an affine
open cover. No reducedness assumption is made. -/
theorem fromOfGlobalSections_eq_iff_exists_affineOpenCover_unit_rescaling [IsAffine X]
    (f g : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤)
    (hspan : Ideal.span (f '' (𝒜 1 : Set A)) = ⊤) :
    fromOfGlobalSections 𝒜 f hf = fromOfGlobalSections 𝒜 g hg ↔
      ∃ 𝒰 : X.OpenCover.{u}, (∀ i, IsAffine (𝒰.X i)) ∧
        ∀ i, ∃ c : Γ(𝒰.X i, ⊤)ˣ, ∀ n, ∀ a ∈ 𝒜 n,
          (𝒰.f i).appTop (g a) = c ^ n * (𝒰.f i).appTop (f a) := by
  classical
  constructor
  · intro heq
    let U (t : 𝒜 1) := X.basicOpen (f t)
    have hcover : TopologicalSpace.IsOpenCover U := by
      refine TopologicalSpace.IsOpenCover.mk ?_
      have h := iSup_basicOpen_of_span_eq_top (X := X) ⊤ _ hspan
      simpa only [iSup_image, iSup_subtype, SetLike.mem_coe, U] using h
    let 𝒰 := X.openCoverOfIsOpenCover U hcover
    refine ⟨𝒰, ?_, ?_⟩
    · dsimp only [𝒰, Scheme.openCoverOfIsOpenCover]
      exact fun t ↦ inferInstanceAs (IsAffine (X.basicOpen (f t)))
    dsimp only [𝒰, Scheme.openCoverOfIsOpenCover]
    intro t
    have hU : X.basicOpen (f t) = X.basicOpen (g t) := by
      rw [← fromOfGlobalSections_preimage_basicOpen 𝒜 f hf one_pos t.property,
        ← fromOfGlobalSections_preimage_basicOpen 𝒜 g hg one_pos t.property, heq]
    have hfu : IsUnit ((U t).ι.appTop (f t)) :=
      IsLocalization.Away.algebraMap_isUnit (f t)
    have hgu : IsUnit ((U t).ι.appTop (g t)) := by
      have hu (V : X.Opens) (hV : V = X.basicOpen (g t)) :
          IsUnit (V.ι.appTop (g t)) := by
        subst V
        exact IsLocalization.Away.algebraMap_isUnit (g t)
      exact hu (U t) hU
    have hlocal := congrArg (fun e ↦ (U t).ι ≫ e) heq
    rw [fromOfGlobalSections_naturality, fromOfGlobalSections_naturality,
      fromOfGlobalSections_eq_toSpecΓ_awayLift (𝒜 := 𝒜) _ _ one_pos t.property hfu,
      fromOfGlobalSections_eq_toSpecΓ_awayLift (𝒜 := 𝒜) _ _ one_pos t.property hgu,
      cancel_epi] at hlocal
    exact (SpecMap_awayLift_awayι_eq_iff (𝒜 := 𝒜) _ _ t.property hfu hgu).mp hlocal
  · rintro ⟨𝒰, _, h⟩
    exact fromOfGlobalSections_eq_of_openCover_unit_rescaling 𝒜 f g hf hg 𝒰 h

end AlgebraicGeometry.Proj
