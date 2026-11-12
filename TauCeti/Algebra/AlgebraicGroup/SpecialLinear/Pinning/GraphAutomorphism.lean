/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Pinning.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.GraphAutomorphism

/-!
# The type-A graph involution on the standard pinning's generators

Over every nontrivial commutative base ring with connected spectrum, the
differential of the signed reverse inverse transpose automorphism of `SL_{r+1}`
sends the standard pinning's simple-root trivialization at `i` and scalar `c`
to the trivialization at `i.rev` with the same scalar `c`.

The root-subgroup and normalized root-vector equations are proved in
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.GraphAutomorphism`.

Use `rw` with these equations: the simplifier does not match their left-hand
sides through the indexed coordinate-ring presentations.

The normalization follows `SpecialLinear.typeAGraphCoordinateIso` and
`SpecialLinear.cotangentLinearEquiv_symm_derivationComp_rootSubgroup`.

## References

* R. W. Carter, *Finite Groups of Lie Type*, §1.15.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

namespace TauCeti.SpecialLinear

universe u

variable {R : Type u} [CommRing R] {r : ℕ}

variable [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]

/-- The graph differential sends the standard pinning's simple-root trivialization
at `i` and scalar `c` to the trivialization at `i.rev` with the same scalar `c`. -/
theorem derivationComp_typeAGraphCoordinateIso_standardPinning_rootSpaceEquiv
    (i : Fin r) (c : R) :
    derivationComp (B := R) (typeAGraphCoordinateIso R r).hom.hom
        (Derivation.cotangentLinearEquiv (B := R)
          ((standardPinning R r).rootSpaceEquiv (standardPinningSimpleRootEquiv (R := R) i) c)) =
      Derivation.cotangentLinearEquiv (B := R)
        ((standardPinning R r).rootSpaceEquiv
          (standardPinningSimpleRootEquiv (R := R) i.rev) c) := by
  -- The pinning's root spaces use the quotient-indexed cotangent presentation.
  erw [standardPinning_rootSpaceEquiv_apply_coe, standardPinning_rootSpaceEquiv_apply_coe]
  rw [map_smul, map_smul, map_smul]
  exact congrArg (c • ·) (derivationComp_typeAGraphCoordinateIso_rootVector i)

end TauCeti.SpecialLinear
