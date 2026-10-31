/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FiniteCover
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Cohomological bounds from finite homogeneous covers of Proj

If `r` positive-degree homogeneous basic opens cover `Proj 𝒜`, every scheme affine over
`Proj 𝒜` has vanishing quasi-coherent cohomology in degrees at least `r`. The same bound
holds for higher direct images along the composite with any morphism from `Proj 𝒜` to an
affine scheme, in particular `Proj.toSpecZero 𝒜`.

These are the finite affine-cover bounds used for the high-degree part of projective-space
cohomology. No generation-in-degree-one or Noetherian hypothesis on the graded ring is needed.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.4.8.
* The Stacks Project, Lemma 30.4.2 (tag 01XD).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {ι : Type*}

/-- If `r` positive-degree homogeneous basic opens cover `Proj 𝒜`, quasi-coherent cohomology
on any scheme affine over it vanishes in degrees at least `r`. -/
theorem subsingleton_cohomology_of_card_le_of_isAffineHom_to_proj
    {X : Scheme.{u}} (f : X ⟶ Proj 𝒜) [IsAffineHom f]
    {s : Finset ι} (hs : s.Nonempty) (a : ι → A)
    (ha : ∀ i ∈ s, ∃ m, 0 < m ∧ a i ∈ 𝒜 m)
    (hcov : ⨆ i ∈ s, Proj.basicOpen 𝒜 (a i) = ⊤)
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) (hq : s.card ≤ q) :
    Subsingleton (Cohomology F q) := by
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated f
  refine Modules.subsingleton_cohomology_of_isAffineOpen_of_card_le F hs
    (fun i ↦ f ⁻¹ᵁ Proj.basicOpen 𝒜 (a i)) (fun i hi ↦ ?_) ?_ q hq
  · obtain ⟨m, hm, hai⟩ := ha i hi
    exact (Proj.isAffineOpen_basicOpen 𝒜 _ hai hm).preimage f
  · simpa only [Finset.sup_eq_iSup, ← Scheme.Hom.preimage_iSup] using
      f.iSup_preimage_eq_top hcov

/-- For a scheme affine over a projective spectrum covered by `r` positive-degree homogeneous
basic opens, higher direct images to any affine base vanish in degrees at least `r`.
Taking `g = Proj.toSpecZero 𝒜` gives the bound over the degree-zero coefficient ring. -/
theorem isZero_higherDirectImage_of_card_le_of_isAffineHom_to_proj
    {X Y : Scheme.{u}} (f : X ⟶ Proj 𝒜) [IsAffineHom f]
    (g : Proj 𝒜 ⟶ Y) [IsAffine Y]
    {s : Finset ι} (hs : s.Nonempty) (a : ι → A)
    (ha : ∀ i ∈ s, ∃ m, 0 < m ∧ a i ∈ 𝒜 m)
    (hcov : ⨆ i ∈ s, Proj.basicOpen 𝒜 (a i) = ⊤)
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) (hq : s.card ≤ q) :
    IsZero (((f ≫ g).higherDirectImage q).obj F) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by have := hs.card_pos; omega⟩
  let h := f ≫ g
  refine h.isZero_higherDirectImage_succ_of_isBasis F p Y.isBasis_affineOpens (fun V hV ↦ ?_)
  have : IsAffine V := hV
  have : IsAffineHom (h ⁻¹ᵁ V).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict h V) inferInstance
  have := Modules.isQuasicoherent_restrictFunctor (h ⁻¹ᵁ V).ι F
  -- Over an affine base, the inclusion of an affine open and its base change are affine.
  -- Thus the restricted source is still affine over the same projective spectrum.
  have := subsingleton_cohomology_of_card_le_of_isAffineHom_to_proj
    ((h ⁻¹ᵁ V).ι ≫ f) hs a ha hcov (F.restrict (h ⁻¹ᵁ V).ι) (p + 1) hq
  let e := Modules.cohomologyOnOpensRangeIso (h ⁻¹ᵁ V).ι F (p + 1)
  simpa only [Scheme.Opens.opensRange_ι] using
    e.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end AlgebraicGeometry.Scheme.Hom
