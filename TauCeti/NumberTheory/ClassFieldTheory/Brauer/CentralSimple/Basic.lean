/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Comparison
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Basic

/-!
# The cohomological Brauer group is the Brauer group of central simple algebras

Class field theory works with the cohomological Brauer group
`TauCeti.ClassFieldTheory.Br F = H²(G_F, (Fˢ)ˣ)`, on the coefficient object `unitsRep F` over
`Field.absoluteGaloisGroup F`. The crossed-product comparison
`TauCeti.brauerCohomologyEquiv F` identifies Mathlib's `BrauerGroup F` of central simple algebras
with continuous cohomology of the separable-closure model `AbsoluteGaloisGroup F` with coefficients
`UnitsCoeff F`. Passing through the explicit inhomogeneous model, where
`TauCeti.ClassFieldTheory.unitsRepH2Equiv F` changes the model of the Galois group and of the
coefficients, gives

```text
brauerGroupEquivBr F : Additive (BrauerGroup F) ≃+ Br F.
```

This is the bridge along which the local invariant `TauCeti.ClassFieldTheory.invMap` and the other
invariants of class field theory evaluate Brauer classes of central simple algebras, such as the
classes of quaternion algebras.

## Main definitions

* `TauCeti.ClassFieldTheory.brauerGroupEquivBr F`: the identification
  `Additive (BrauerGroup F) ≃+ Br F`.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, Chapter X, §5.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable (F : Type) [Field F]

/-- The absolute Galois group is locally compact, being compact and Hausdorff. Instance search
does not find this within its default budget under the imports of this file, so it is assembled
here from the Krull topology being Hausdorff. -/
local instance locallyCompactSpace_absoluteGaloisGroup :
    LocallyCompactSpace (AbsoluteGaloisGroup F) :=
  have : R1Space (AbsoluteGaloisGroup F) := @T2Space.r1Space _ _ krullTopology_t2
  have : WeaklyLocallyCompactSpace (AbsoluteGaloisGroup F) :=
    ⟨fun _ ↦ ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
  WeaklyLocallyCompactSpace.locallyCompactSpace

/-- **The Brauer group of central simple algebras is the cohomological Brauer group.** The
crossed-product comparison `TauCeti.brauerCohomologyEquiv F`, read in the explicit model of
`H²(G_F, (Fˢ)ˣ)` and transported to the carrier `Br F` of class field theory. Multiplication of
Brauer classes goes to addition of cohomology classes. -/
def brauerGroupEquivBr : Additive (BrauerGroup F) ≃+ Br F :=
  (brauerCohomologyEquiv F).trans <|
    (explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (UnitsCoeff F)).symm.trans
      (unitsRepH2Equiv F)

/-- `brauerGroupEquivBr` is the crossed-product comparison followed by the change of model to
`Br F`. -/
theorem brauerGroupEquivBr_apply (x : Additive (BrauerGroup F)) :
    brauerGroupEquivBr F x =
      unitsRepH2Equiv F
        ((explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (UnitsCoeff F)).symm
          (brauerCohomologyEquiv F x)) := by
  simp only [brauerGroupEquivBr, AddEquiv.trans_apply]

end TauCeti.ClassFieldTheory
