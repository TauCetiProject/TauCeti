/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import TauCeti.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Affine covers from locally constant labels

The fibres of a locally constant function on an affine scheme are affine clopen subschemes.
Any finite injective family of labels containing its image gives a coproduct of fibre spectra
isomorphic to the original affine scheme. Labels with empty fibres give empty summands.
This construction applies
before choosing modules or quotients on the components.

## References

* The Stacks Project, Tag 00EE, for clopen decompositions and idempotents.
-/

public section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry PrimeSpectrum

namespace LocallyConstant

variable {A : Type u} [CommRing A] {α : Type v}
  (f : LocallyConstant (PrimeSpectrum A) α)

/-- The canonical inclusion of a labelled fibre spectrum is an open immersion. -/
noncomputable instance isOpenImmersion_specMap_fiberRing (a : α) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (f.fiberRing a)))) :=
  IsOpenImmersion.of_isLocalization (fiberIdempotent f.isLocallyConstant a)

/-- The open range of the labelled fibre inclusion is its fibre-idempotent basic open. -/
@[simp]
theorem opensRange_specMap_fiberRing (a : α) :
    -- Give the immersion instance explicitly for the quotient-map simp normal form.
    @Scheme.Hom.opensRange _ _
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {1 - fiberIdempotent f.isLocallyConstant a}))))
      (f.isOpenImmersion_specMap_fiberRing a) =
        basicOpen (fiberIdempotent f.isLocallyConstant a) := by
  apply TopologicalSpace.Opens.ext
  -- Spec.map acts on points by comap of the coefficient homomorphism.
  exact localization_away_comap_range (f.fiberRing a) _

variable {ι : Type w} [Finite ι] (e : ι ↪ α)

/-- The canonical morphism from the coproduct of fibre spectra to the original spectrum. -/
noncomputable def specCover :
    (∐ fun i : ι ↦ Spec (.of (f.fiberRing (e i)))) ⟶ Spec (.of A) :=
  Sigma.desc fun i : ι ↦ Spec.map (CommRingCat.ofHom (algebraMap A (f.fiberRing (e i))))

/-- Restricting the fibre cover to a summand gives its coefficient map. -/
@[reassoc (attr := simp)]
theorem ι_specCover (i : ι) :
    Sigma.ι _ i ≫ f.specCover e =
      Spec.map (CommRingCat.ofHom (algebraMap A (f.fiberRing (e i)))) :=
  Sigma.ι_comp_desc _ _

/-- A finite injective family containing every label gives an isomorphism from the coproduct
of fibre spectra onto the original spectrum. -/
theorem isIso_specCover (hs : Set.range f ⊆ Set.range e) : IsIso (f.specCover e) := by
  classical
  let := Fintype.ofFinite ι
  let F := fun i : ι ↦ Spec (.of (f.fiberRing (e i)))
  let k := (equivShrink.{u} ι).symm
  let := Fintype.ofEquiv ι k.symm
  let g := RingHom.pi fun i : Shrink.{u} ι ↦ algebraMap A (f.fiberRing (e (k i)))
  have hg : Function.Bijective g := by
    apply f.bijective_pi_fiberRing (k.toEmbedding.trans e)
    rintro _ ⟨p, rfl⟩
    obtain ⟨i, hi⟩ := hs ⟨p, rfl⟩
    exact ⟨k.symm i, by simpa using hi⟩
  have : IsIso (Spec.map (CommRingCat.ofHom g)) := isIso_SpecMap_iff.mpr hg
  have heq : (Sigma.reindex k F).hom ≫ f.specCover e =
      sigmaSpec.{u, u} (fun i : Shrink.{u} ι ↦ .of (f.fiberRing (e (k i)))) ≫
        Spec.map (CommRingCat.ofHom g) := by
    apply Sigma.hom_ext
    intro i
    dsimp only [F]
    rw [Sigma.ι_reindex_hom_assoc, ι_specCover]
    dsimp only [Function.comp_def]
    rw [ι_sigmaSpec_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun h ↦ Spec.map (CommRingCat.ofHom h))
    ext x
    simp only [g, RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.pi_apply]
  have : IsIso ((Sigma.reindex k F).hom ≫ f.specCover e) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (Sigma.reindex k F).hom _

end LocallyConstant
