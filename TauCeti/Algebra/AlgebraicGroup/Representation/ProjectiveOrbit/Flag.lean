/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Points
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Translation
public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Exterior
public import TauCeti.LinearAlgebra.ExteriorPower.Flag.Cone
import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Flag

/-!
# The exterior flag locus under projective orbits

Rational projective translations (`Comodule.projectivePointTranslation`) preserve the closed
subvariety of `ℙ(FlagSpace k M d)` cut out by `TauCeti.exteriorPower.exteriorFlagForms k M d`,
and the counit image of `w` lies in this locus iff `w ∈ exteriorFlagCone k M d`.

## Main results

* `TauCeti.Comodule.mapsTo_projectivePointTranslation_exteriorFlagZeroLocus`: rational
  projective translations preserve the zero locus of `exteriorFlagForms`.
* `TauCeti.Comodule.projectiveOrbitMap_counit_mem_exteriorFlagZeroLocus_iff`: the counit image
  of `w` lies in the flag zero locus iff `w ∈ exteriorFlagCone k M d`.
-/

public section

open AlgebraicGeometry WithConv

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M]

/-- Rational projective translations on `ℙ(FlagSpace k M d)` preserve the closed subvariety cut
out by `exteriorPower.exteriorFlagForms k M d`. -/
theorem mapsTo_projectivePointTranslation_exteriorFlagZeroLocus (d : ℕ)
    (g : WithConv (H →ₐ[k] k)) :
    letI : AddCommGroup (exteriorPower.FlagSpace k M d) := Module.addCommMonoidToAddCommGroup k
    letI : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
    Set.MapsTo
      (projectivePointTranslation (M := exteriorPower.FlagSpace k M d) g).hom
      (ProjectiveSpectrum.zeroLocus _ (exteriorPower.exteriorFlagForms k M d) :
        Set (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k
          (Module.Dual k (exteriorPower.FlagSpace k M d)))))
      (ProjectiveSpectrum.zeroLocus _ (exteriorPower.exteriorFlagForms k M d)) := by
  let _ : AddCommGroup (exteriorPower.FlagSpace k M d) := Module.addCommMonoidToAddCommGroup k
  let _ : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
  intro x hx s hs
  by_contra hmem
  have hb : (projectivePointTranslation (M := exteriorPower.FlagSpace k M d) g).hom x ∈
      Proj.basicOpen _ s := (Proj.mem_basicOpen _ s _).mpr hmem
  rw [← Scheme.Hom.mem_preimage, projectivePointTranslation_hom,
    Proj.map_preimage_basicOpen, Proj.mem_basicOpen, SymmetricAlgebra.gradedMap_apply] at hb
  refine hb (hx ?_)
  rw [basePointsRepresentation_exteriorFlag]
  exact exteriorPower.map_dualMap_mem_exteriorFlagForms
    (fun _ hw ↦ exteriorPower.exteriorFlagMap_mem_exteriorFlagCone _ hw) hs

/-- The counit image of `w : FlagSpace k M d` under `projectiveOrbitMap` lies in the zero locus of
`exteriorFlagForms k M d` if and only if `w ∈ exteriorFlagCone k M d`. -/
theorem projectiveOrbitMap_counit_mem_exteriorFlagZeroLocus_iff [Module.Finite k M]
    (d : ℕ) (w : exteriorPower.FlagSpace k M d) (hw : Module.IsUnimodular k w) :
    (letI : AddCommGroup (exteriorPower.FlagSpace k M d) := Module.addCommMonoidToAddCommGroup k
     letI : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
     projectiveOrbitMap (H := H) w hw
       (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
         ProjectiveSpectrum.zeroLocus _ (exteriorPower.exteriorFlagForms k M d)) ↔
      w ∈ exteriorPower.exteriorFlagCone k M d := by
  let _ : AddCommGroup (exteriorPower.FlagSpace k M d) := Module.addCommMonoidToAddCommGroup k
  let _ : Comodule k H (exteriorPower.FlagSpace k M d) := exteriorFlag k H M d
  have : FiniteDimensional k M := inferInstance
  refine (ProjectiveSpectrum.mem_zeroLocus _ _ _).trans ?_
  rw [exteriorPower.mem_exteriorFlagCone_iff]
  refine forall₂_congr fun s hs ↦ ?_
  have h := mem_projectiveOrbitMap_kernelPoint_iff (H := H) w hw 1
    (exteriorPower.mem_homogeneousSubmodule_of_mem_exteriorFlagForms hs)
  simp only [map_one, one_apply_eq_self] at h
  simp only [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp] at h
  exact h

end TauCeti.Comodule
