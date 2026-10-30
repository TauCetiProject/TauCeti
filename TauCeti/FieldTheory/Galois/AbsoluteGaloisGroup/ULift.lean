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

-- Public signatures insert the canonical action explicitly: private instances are unavailable
-- there, while enabling the generic instance would also affect intermediate fields and closures.
private local instance uliftSeparableClosureAlgebra : Algebra (ULift.{w} K) (ULift.{w} E) :=
  ULift.algebra' K (ULift.{w} E)

/-- The image of the lifted subextension inside the chosen separable closure of `ULift K`. -/
abbrev uliftSeparableClosure : IntermediateField (ULift.{w} K) (SeparableClosure (ULift.{w} K)) :=
  E.separableClosureCongr (ULift.ringEquiv.symm : K ≃+* ULift.{w} K)

/-- The lifted field is isomorphic, over the lifted base, to its image in the separable closure.
For operations requiring synthesis of the source algebra action, such as taking the inverse,
use `letI := ULift.algebra' K (ULift E)` locally. -/
def uliftSeparableClosureEquiv :
    letI := ULift.algebra' K (ULift.{w} E)
    ULift.{w} E ≃ₐ[ULift.{w} K] uliftSeparableClosure.{u, w} E where
  toRingEquiv := ULift.ringEquiv.trans
    (E.separableClosureCongrEquiv (ULift.ringEquiv.symm : K ≃+* ULift.{w} K))
  commutes' r := by
    simp only [ULift.algebraMap_apply', ULift.algebraMap_eq]
    exact
      E.separableClosureCongrEquiv_algebraMap
        (ULift.ringEquiv.symm : K ≃+* ULift.{w} K) r.down

/-- The lifted field identification applies the restricted identification
to the underlying element. -/
@[simp]
theorem uliftSeparableClosureEquiv_apply (x : ULift.{w} E) :
    uliftSeparableClosureEquiv.{u, w} E x =
      E.separableClosureCongrEquiv (ULift.ringEquiv.symm : K ≃+* ULift.{w} K) x.down := (rfl)

/-- The inverse field identification lifts the inverse restricted identification. -/
@[simp]
theorem uliftSeparableClosureEquiv_symm_apply (x : uliftSeparableClosure.{u, w} E) :
    letI := ULift.algebra' K (ULift.{w} E)
    (uliftSeparableClosureEquiv.{u, w} E).symm x =
      ULift.up ((E.separableClosureCongrEquiv
        (ULift.ringEquiv.symm : K ≃+* ULift.{w} K)).symm x) := (rfl)

-- These two specializations are needed for the inferred ULift.module action: reducible
-- matching does not identify it with the general transport's intermediate-field action.
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

end IntermediateField
