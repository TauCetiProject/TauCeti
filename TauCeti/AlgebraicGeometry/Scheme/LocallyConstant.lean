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
Any finite set containing its image gives a coproduct of fibre spectra isomorphic to the
original affine scheme. Labels with empty fibres give empty summands. This construction applies
before choosing modules or quotients on the components.

## References

* The Stacks Project, Tag 00EE, for clopen decompositions and idempotents.
-/

public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry PrimeSpectrum

namespace LocallyConstant

variable {A : Type u} [CommRing A] {α : Type v}
  (f : LocallyConstant (PrimeSpectrum A) α) (s : Finset α)

/-- The canonical morphism from the coproduct of fibre spectra to the original spectrum. -/
noncomputable def specCover :
    (∐ fun a : s ↦ Spec (.of (f.fiberRing a))) ⟶ Spec (.of A) :=
  Sigma.desc fun a : s ↦ Spec.map (CommRingCat.ofHom (algebraMap A (f.fiberRing a)))

/-- Restricting the fibre cover to a summand gives its coefficient map. -/
@[reassoc (attr := simp)]
theorem ι_specCover (a : s) :
    Sigma.ι _ a ≫ f.specCover s =
      Spec.map (CommRingCat.ofHom (algebraMap A (f.fiberRing a))) :=
  Sigma.ι_comp_desc _ _

/-- A finite set containing every label gives an isomorphism from the coproduct of fibre spectra
onto the original spectrum. -/
theorem isIso_specCover (hs : Set.range f ⊆ s) : IsIso (f.specCover s) := by
  classical
  let F := fun a : s ↦ Spec (.of (f.fiberRing a))
  let e := (equivShrink.{u} s).symm
  let := Fintype.ofEquiv s e.symm
  let g := RingHom.pi fun a : Shrink.{u} s ↦ algebraMap A (f.fiberRing (e a))
  have hc := completeOrthogonalIdempotents_fiberIdempotent f.isLocallyConstant hs
  have hf : Function.Bijective (RingHom.pi fun a : s ↦ algebraMap A (f.fiberRing a)) := by
    simpa only [Ideal.Quotient.algebraMap_eq] using hc.bijective_pi
  have hg : Function.Bijective g := by
    have h := (Equiv.piCongrLeft (fun a : s ↦ f.fiberRing a) e).symm.bijective.comp hf
    have heq : ⇑g = (Equiv.piCongrLeft (fun a : s ↦ f.fiberRing a) e).symm ∘
        (RingHom.pi fun a : s ↦ algebraMap A (f.fiberRing a)) := by
      funext x a
      simp only [g, Function.comp_apply, Equiv.piCongrLeft_symm_apply, RingHom.pi_apply]
    rwa [heq]
  have : IsIso (Spec.map (CommRingCat.ofHom g)) := isIso_SpecMap_iff.mpr hg
  have heq : (Sigma.reindex e F).hom ≫ f.specCover s =
      sigmaSpec.{u, u} (fun a : Shrink.{u} s ↦ .of (f.fiberRing (e a))) ≫
        Spec.map (CommRingCat.ofHom g) := by
    apply Sigma.hom_ext
    intro a
    dsimp only [F]
    rw [Sigma.ι_reindex_hom_assoc, ι_specCover]
    dsimp only [Function.comp_def]
    rw [ι_sigmaSpec_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun h ↦ Spec.map (CommRingCat.ofHom h))
    ext x
    simp only [g, RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.pi_apply]
  have : IsIso ((Sigma.reindex e F).hom ≫ f.specCover s) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (Sigma.reindex e F).hom _

end LocallyConstant
