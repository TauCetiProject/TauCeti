/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ULift
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Congr

/-!
# Finite Galois levels under universe lifting

A subextension of the separable closure of `K` has a corresponding subextension of the
chosen separable closure of `ULift K`. The latter is the image of the actual lifted field,
not a new choice of a splitting field. Finiteness, degree and the Galois property are
preserved. Conjugating automorphisms through this identification commutes with restriction
from the absolute Galois groups.

These finite-level identifications supply the field and group data for comparing inflated
cocycles across universes. They use the same chosen separable-closure identification as
`RingEquiv.absoluteGaloisGroupCongr`; thus the restriction square compares actual maps,
independently of any Brauer or cohomology comparison.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X, §5.
-/

public noncomputable section

universe u w

namespace IntermediateField

variable {K : Type u} [Field K] (E : IntermediateField K (SeparableClosure K))

/-- The simultaneous lifted algebra action on the source of the field identification.
It is local to avoid enabling the generic lifted-scalar instance on intermediate fields
or their separable closures. -/
local instance uliftSeparableClosureAlgebra : Algebra (ULift.{w} K) (ULift.{w} E) :=
  ULift.algebra' K (ULift.{w} E)

/-- Embed the lifted subextension in the separable closure of the lifted base field,
using the chosen identification of separable closures. -/
def uliftSeparableClosureEmbedding :
    ULift.{w} E →ₐ[ULift.{w} K] SeparableClosure (ULift.{w} K) where
  toRingHom := (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm.toRingHom.comp
    (E.val.toRingHom.comp (ULift.ringEquiv : ULift.{w} E ≃+* E).toRingHom)
  commutes' r := by
    -- The local lifted algebra action sends r to the lift of algebraMap K E r.down;
    -- coercing that element to the separable closure is definitionally the base algebraMap.
    change (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm
      (algebraMap K (SeparableClosure K) r.down) = _
    exact (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr_symm_algebraMap
      r.down

@[simp]
theorem uliftSeparableClosureEmbedding_apply (x : ULift.{w} E) :
    uliftSeparableClosureEmbedding.{u, w} E x =
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm
        (x.down : SeparableClosure K) := (rfl)

/-- The image of the lifted subextension inside the chosen separable closure of `ULift K`. -/
abbrev uliftSeparableClosure : IntermediateField (ULift.{w} K) (SeparableClosure (ULift.{w} K)) :=
  E.separableClosureCongr (ULift.ringEquiv.symm : K ≃+* ULift.{w} K)

/-- The lifted field is isomorphic, over the lifted base, to its image in the separable closure.
For operations requiring synthesis of the source algebra action, such as taking the inverse,
enable Mathlib's `ULift.algebra'` locally. -/
def uliftSeparableClosureEquiv :
    ULift.{w} E ≃ₐ[ULift.{w} K] uliftSeparableClosure.{u, w} E where
  toRingEquiv := ULift.ringEquiv.trans
    (E.separableClosureCongrEquiv (ULift.ringEquiv.symm : K ≃+* ULift.{w} K))
  commutes' r := by
    -- The simultaneous lifted algebraMap has underlying value algebraMap K E r.down.
    change E.separableClosureCongrEquiv _ (algebraMap K E r.down) = _
    exact E.separableClosureCongrEquiv_algebraMap _ r.down

@[simp]
theorem coe_uliftSeparableClosureEquiv (x : ULift.{w} E) :
    (uliftSeparableClosureEquiv.{u, w} E x : SeparableClosure (ULift.{w} K)) =
      uliftSeparableClosureEmbedding.{u, w} E x := by
  exact E.coe_separableClosureCongrEquiv _ x.down

/-- The inverse field identification is the chosen separable-closure map on underlying elements. -/
@[simp]
theorem coe_uliftSeparableClosureEquiv_symm (x : uliftSeparableClosure.{u, w} E) :
    ((uliftSeparableClosureEquiv.{u, w} E).symm x).down.val =
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr x := by
  apply (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).separableClosureCongr.symm.injective
  simp [← uliftSeparableClosureEmbedding_apply, ← coe_uliftSeparableClosureEquiv]

/-- Refining a subextension refines its transported image. -/
theorem uliftSeparableClosure_mono {E F : IntermediateField K (SeparableClosure K)}
    (h : E ≤ F) : uliftSeparableClosure.{u, w} E ≤ uliftSeparableClosure.{u, w} F :=
  separableClosureCongr_mono _ h

/-- The degree is unchanged when both the base and subextension are lifted. -/
@[simp]
theorem finrank_uliftSeparableClosure :
    Module.finrank (ULift.{w} K) (uliftSeparableClosure.{u, w} E) =
      Module.finrank K E :=
  E.finrank_separableClosureCongr _

/-- A finite subextension remains finite in the larger universe. -/
instance [FiniteDimensional K E] :
    FiniteDimensional (ULift.{w} K) (uliftSeparableClosure.{u, w} E) :=
  E.instFiniteDimensionalSeparableClosureCongr
    (ULift.ringEquiv.symm : K ≃+* ULift.{w} K)

/-- Normality is preserved when the base and subextension are lifted. -/
instance [Normal K E] : Normal (ULift.{w} K) (uliftSeparableClosure.{u, w} E) :=
  inferInstanceAs (Normal (ULift.{w} K)
    (E.separableClosureCongr (ULift.ringEquiv.symm : K ≃+* ULift.{w} K)))

/-- The transported normal subextension is Galois: its separability is inherited from
the separable closure. -/
instance [Normal K E] : IsGalois (ULift.{w} K) (uliftSeparableClosure.{u, w} E) where

/-- Identify automorphisms by conjugating through the chosen field transport.
No finiteness or normality is needed. -/
def uliftSeparableClosureAutEquiv :
    (E ≃ₐ[K] E) ≃* ((uliftSeparableClosure.{u, w} E) ≃ₐ[ULift.{w} K]
      uliftSeparableClosure.{u, w} E) :=
  E.separableClosureCongrAutEquiv (ULift.ringEquiv.symm : K ≃+* ULift.{w} K)

@[simp]
theorem uliftSeparableClosureAutEquiv_apply (g : E ≃ₐ[K] E) (x : ULift.{w} E) :
    uliftSeparableClosureAutEquiv.{u, w} E g (uliftSeparableClosureEquiv.{u, w} E x) =
      uliftSeparableClosureEquiv.{u, w} E (ULift.up (g x.down)) := by
  let e : K ≃+* ULift.{w} K := ULift.ringEquiv.symm
  -- The lifted identification is the restricted ring equivalence applied to x.down.
  change E.separableClosureCongrAutEquiv e g
    (E.separableClosureCongrEquiv e x.down) = E.separableClosureCongrEquiv e (g x.down)
  rw [separableClosureCongrAutEquiv_apply, RingEquiv.symm_apply_apply]

/-- Pulling an automorphism back acts by the inverse lifted field identification. -/
@[simp]
theorem uliftSeparableClosureAutEquiv_symm_apply
    (g : uliftSeparableClosure.{u, w} E ≃ₐ[ULift.{w} K] uliftSeparableClosure.{u, w} E)
    (x : E) :
    (uliftSeparableClosureAutEquiv.{u, w} E).symm g x =
      ((uliftSeparableClosureEquiv.{u, w} E).symm
        (g (uliftSeparableClosureEquiv.{u, w} E (ULift.up x)))).down := by
  -- Unwrap the ULift specialization to use the general inverse formula.
  change (E.separableClosureCongrAutEquiv
    (ULift.ringEquiv.symm : K ≃+* ULift.{w} K)).symm g x = _
  rw [separableClosureCongrAutEquiv_symm_apply]
  -- The inverse of ULift.ringEquiv.trans f lifts f.symm, and .down cancels that lift.
  rfl

/-- Restriction from the absolute Galois group commutes with simultaneous lifting of the
base and a normal subextension. This is an equality of the actual finite-level maps. -/
theorem uliftSeparableClosureAutEquiv_restrictNormalHom [Normal K E]
    (g : TauCeti.AbsoluteGaloisGroup (ULift.{w} K)) :
    uliftSeparableClosureAutEquiv.{u, w} E
        (AlgEquiv.restrictNormalHom E
          ((ULift.ringEquiv.symm : K ≃+* ULift.{w} K).absoluteGaloisGroupCongr g)) =
      AlgEquiv.restrictNormalHom (uliftSeparableClosure.{u, w} E) g :=
  E.separableClosureCongrAutEquiv_restrictNormalHom _ g

/-- The open normal subgroup attached to a finite Galois level is transported by the
same absolute-Galois-group equivalence. The equality also holds for infinite normal levels. -/
theorem fixingSubgroup_uliftSeparableClosure [Normal K E] :
    (uliftSeparableClosure.{u, w} E).fixingSubgroup = E.fixingSubgroup.comap
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K).absoluteGaloisGroupCongr.toMonoidHom :=
  E.fixingSubgroup_separableClosureCongr _

end IntermediateField
