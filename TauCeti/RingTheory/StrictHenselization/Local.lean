/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Algebra
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Units and local-ring structure of the strict-henselization colimit

Let `R` and `Ω` be commutative rings with `Ω` an `R`-algebra, let `algebra R Ω` be the
colimit of the pointed étale neighbourhoods of `(R, Ω)`, and let
`toTarget : algebra R Ω →ₐ[R] Ω` be the map induced by their pointings. This file relates
the ring-theoretic properties of `algebra R Ω` to those of its base ring `R` and its target
`Ω` along `toTarget`:

* `isUnit_stage_of_isUnit_point`: a stage element whose image at the point is a unit is a
  unit of `algebra R Ω`;
* `isUnit_iff_isUnit_toTarget`: an element of `algebra R Ω` is a unit exactly when its
  image in `Ω` is a unit;
* `isLocalHom_toTarget`, an instance: `toTarget` is a local homomorphism;
* `isLocalRing`: hence `algebra R Ω` is a local ring as soon as `Ω` is;
* `ker_toTarget_eq_maximalIdeal`: when `Ω` is a field, the kernel of `toTarget` is the
  maximal ideal of `algebra R Ω`;
* `isLocalHom_algebraMap`, an instance: the structure map `R → algebra R Ω` is local as soon
  as `R → Ω` is. An algebra map between local rings need not be local, so localness of
  `R → Ω` is an explicit hypothesis, not a consequence of `[IsLocalRing R]` and
  `[IsLocalRing Ω]`.

## References

* Stacks Project, Tags 04GP, 04GQ, and 04GW.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`
  (Apache 2.0): the point-locality statements of `StrictHenselizationConstruction.lean`.
* Tau Ceti, `TauCeti.RingTheory.Henselization.Jacobson`, whose
  `isUnit_stage_of_isUnit_quotient` inverts a stage element by localizing at that
  element, the method used here for the point of a neighbourhood.
-/

public section

open CategoryTheory

universe u

namespace TauCeti.StrictHenselization

variable (R Ω : Type u) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- A stage element whose image at the point of its pointed étale neighbourhood is a unit is a
unit of the colimit: localizing that neighbourhood at the element is a further pointed
neighbourhood in which the element is a unit. -/
theorem isUnit_stage_of_isUnit_point (B : Neighbourhood R Ω) (b : B.obj.left)
    (hpoint : IsUnit (B.obj.hom.hom b)) : IsUnit (stage R Ω B b) := by
  obtain ⟨target, refinement, hunit⟩ := Neighbourhood.exists_refinement_isUnit R Ω B b hpoint
  rw [← stage_hom_apply R Ω refinement b]
  exact hunit.map (stage R Ω target).toRingHom

/-- An element of the colimit of pointed étale neighbourhoods is a unit exactly when its image
under the induced map `toTarget` is a unit. -/
theorem isUnit_iff_isUnit_toTarget (x : algebra R Ω) : IsUnit x ↔ IsUnit (toTarget R Ω x) := by
  refine ⟨fun h ↦ h.map (toTarget R Ω).toRingHom, fun h ↦ ?_⟩
  obtain ⟨B, b, rfl⟩ := exists_stage_eq R Ω x
  have hdown : IsUnit ((B.obj.hom.hom b).down) := by
    rwa [toTarget_stage_apply] at h
  have hpoint : IsUnit (B.obj.hom.hom b) :=
    (MulEquiv.isUnit_map (ULift.ringEquiv (R := Ω))).mp hdown
  exact isUnit_stage_of_isUnit_point R Ω B b hpoint

/-- The map induced by the pointings of the pointed étale neighbourhoods is a local
homomorphism. -/
instance isLocalHom_toTarget : IsLocalHom (toTarget R Ω) where
  map_nonunit x hx := (isUnit_iff_isUnit_toTarget R Ω x).mpr hx

/-- The colimit of pointed étale neighbourhoods is a local ring when the target is local. -/
@[stacks 04GP "(2), local"]
instance isLocalRing [IsLocalRing Ω] : IsLocalRing (algebra R Ω) :=
  RingHom.domain_isLocalRing ((toTarget R Ω) : algebra R Ω →+* Ω)

/-- The structure map from the base ring to the colimit of pointed étale neighbourhoods is local
whenever the structure map to the target is. As an instance, it is found by typeclass inference
from `IsLocalHom (algebraMap R Ω)`. -/
@[stacks 04GQ "local ring map"]
instance isLocalHom_algebraMap [h : IsLocalHom (algebraMap R Ω)] :
    IsLocalHom (algebraMap R (algebra R Ω)) := by
  have hcomp : (toTarget R Ω).toRingHom.comp (algebraMap R (algebra R Ω)) = algebraMap R Ω := by
    ext x
    exact AlgHom.commutes (toTarget R Ω) x
  have : IsLocalHom ((toTarget R Ω).toRingHom.comp (algebraMap R (algebra R Ω))) := hcomp ▸ h
  exact isLocalHom_of_comp (algebraMap R (algebra R Ω)) (toTarget R Ω).toRingHom

section TargetField

variable (R : Type u) [CommRing R]
variable (Ω : Type u) [Field Ω] [Algebra R Ω]

/-- When the target is a field, the kernel of the induced map `toTarget` is the maximal ideal of
the colimit of pointed étale neighbourhoods. -/
@[stacks 04GP "(5), kernel"]
theorem ker_toTarget_eq_maximalIdeal :
    RingHom.ker (toTarget R Ω).toRingHom = IsLocalRing.maximalIdeal (algebra R Ω) := by
  have : IsLocalHom (toTarget R Ω).toRingHom := isLocalHom_toRingHom (f := toTarget R Ω)
  simpa only [RingHom.ker_eq_comap_bot, IsLocalRing.maximalIdeal_eq_bot] using
    IsLocalRing.maximalIdeal_comap (toTarget R Ω).toRingHom

end TargetField

end TauCeti.StrictHenselization
