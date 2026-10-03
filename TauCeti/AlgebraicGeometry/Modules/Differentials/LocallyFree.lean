/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Quasicoherent
public import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Finite local freeness of smooth relative differentials

For a smooth scheme over an affine base, its sheaf of relative differentials is finite locally
free. On an affine chart the differential sheaf is the sheaf associated with the Kähler
module, which is finite projective for a smooth algebra. The open-cover criterion for finite
local freeness then gives the result on the whole scheme.

This produces the cotangent bundle of a smooth scheme without any Noetherian or field
hypothesis. For a smooth curve, identifying its rank as one is the further step needed to
regard the differential sheaf as the canonical line bundle.

## References

* The Stacks Project, *Morphisms of Schemes*, Lemma 29.34.12 (Tag 02G1).
* R. Hartshorne, *Algebraic Geometry*, Section II.8.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- The differential sheaf of the spectrum of a smooth algebra is finite locally free. -/
theorem isFiniteLocallyFree_relativeDifferentials_spec (A : Type u) [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] :
    Scheme.Modules.isFiniteLocallyFree (Spec (.of A)) ((Spec (.of A)).relativeDifferentials R) := by
  have h := isFiniteLocallyFree_tilde (R := .of A) (ModuleCat.of A Ω[A⁄R])
  exact (Scheme.Modules.isFiniteLocallyFree (Spec (.of A))).prop_of_iso
    (relativeDifferentialsSpecIso R (.of A)).symm h

variable (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- Relative differentials of a scheme smooth over `Spec R` are finite locally free. -/
theorem isFiniteLocallyFree_relativeDifferentials [Smooth (X ↘ Spec (.of R))] :
    Scheme.Modules.isFiniteLocallyFree X (X.relativeDifferentials R) := by
  -- Use all canonical affine charts so that their algebra structures are exactly the base-ring
  -- maps used by the restriction comparison for relative differentials.
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X.affineOpens
    (fun U : X.affineOpens ↦ Spec Γ(X, U))
    (fun U ↦ U.property.fromSpec)
    (fun x ↦ by
      obtain ⟨U, hx⟩ := (Opens.mem_iSup.mp
        ((iSup_affineOpens_eq_top X).symm ▸ (Opens.mem_top x)))
      have h := U.property.opensRange_fromSpec
      rw [← h] at hx
      obtain ⟨p, hp⟩ := hx
      exact ⟨U, p, hp⟩)
    (fun U ↦ IsAffineOpen.isOpenImmersion_fromSpec U.property)
  refine (Scheme.Modules.isFiniteLocallyFree_iff_forall_pullback 𝒰
    (X.relativeDifferentials R)).mpr fun (U : X.affineOpens) ↦ ?_
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  let : U.property.fromSpec.IsOver (Spec (.of R)) := isOver_fromSpec R X U
  have : IsOpenImmersion U.property.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.property
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) := by
    have hc : Smooth (U.property.fromSpec ≫ X ↘ Spec (.of R)) := inferInstance
    rw [HomIsOver.comp_over (f := U.property.fromSpec) (S := Spec (.of R))] at hc
    exact hc
  have : Algebra.Smooth R Γ(X, U) :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hs)
  let e := ((Scheme.Modules.restrictFunctorIsoPullback U.property.fromSpec).app
    (X.relativeDifferentials R)).symm ≪≫
      relativeDifferentialsRestrictIso R U.property.fromSpec
  exact (Scheme.Modules.isFiniteLocallyFree (Spec Γ(X, U))).prop_of_iso e.symm
    (isFiniteLocallyFree_relativeDifferentials_spec R Γ(X, U))

/-- The sheaf of relative differentials of a smooth scheme is locally free. -/
instance isLocallyFree_relativeDifferentials [Smooth (X ↘ Spec (.of R))] :
    (X.relativeDifferentials R).IsLocallyFree :=
  (isFiniteLocallyFree_relativeDifferentials R X).1

end

end TauCeti.AlgebraicGeometry
