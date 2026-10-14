/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Pinning.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.GraphAutomorphism

/-!
# The type-A graph involution on the standard pinning's generators

The signed reverse inverse transpose automorphism of `SL_{r+1}` sends the chosen
simple root vector numbered `i` to the one numbered `i.rev`, with no sign or scalar
factor. Together with its torus and Borel preservation equations, this identifies
its action on the standard integral pinning, rather than just on matrix points.

The differential equation holds over every commutative coefficient algebra,
including nonreduced algebras. The pinning equations require a nontrivial base
with connected spectrum, as does the standard pinning itself.

Use `rw` with these equations: the simplifier does not match their left-hand
sides through the indexed coordinate-ring presentations.

The normalization follows `SpecialLinear.typeAGraphCoordinateIso` and
`SpecialLinear.cotangentLinearEquiv_symm_derivationComp_rootSubgroup`.

## References

* R. W. Carter, *Finite Groups of Lie Type*, §1.15.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

open CategoryTheory

namespace TauCeti.SpecialLinear

universe u v

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The differential of the graph involution reverses the positive simple-root
subgroup differentials, preserving the additive tangent parameter over every
commutative coefficient algebra. -/
theorem derivationComp_typeAGraphCoordinateIso_rootSubgroup
    {B : Type v} [CommRing B] [Algebra R B] (i : Fin r)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    derivationComp (B := B) (typeAGraphCoordinateIso R r).hom.hom
        (derivationComp (B := B)
          (rootSubgroupCoordinateMap (R := R) (Fin.castSucc_lt_succ (i := i)).ne).hom d) =
      derivationComp (B := B)
        (rootSubgroupCoordinateMap (R := R) (Fin.castSucc_lt_succ (i := i.rev)).ne).hom d := by
  have h := congrArg CommHopfAlgCat.Hom.hom
    (typeAGraphCoordinateIso_hom_comp_rootSubgroupCoordinateMap R r i)
  simp only [CommHopfAlgCat.hom_comp] at h
  rw [← LinearMap.comp_apply, ← derivationComp_comp, h]

/-- On the cotangent-dual model of the Lie algebra, the graph differential sends
normalized consecutive matrix-unit root vectors to the reversed generators.
This equation holds over arbitrary commutative base rings. -/
theorem derivationComp_typeAGraphCoordinateIso_rootVector (i : Fin r) :
    derivationComp (B := R) (typeAGraphCoordinateIso R r).hom.hom
        (Derivation.cotangentLinearEquiv (B := R)
          (rootVector (R := R) (diagonalSimpleRootIndex r i))) =
      Derivation.cotangentLinearEquiv (B := R)
        (rootVector (R := R) (diagonalSimpleRootIndex r i.rev)) := by
  let d := (AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).symm 1
  have hroot (j : Fin r) :
      Derivation.cotangentLinearEquiv (B := R)
          (rootVector (R := R) (diagonalSimpleRootIndex r j)) =
        derivationComp (B := R)
          (rootSubgroupCoordinateMap (R := R) (Fin.castSucc_lt_succ (i := j)).ne).hom d := by
    apply (Derivation.cotangentLinearEquiv (B := R)).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    have h := cotangentLinearEquiv_symm_derivationComp_rootSubgroup
      (R := R) (diagonalSimpleRootIndex r j) d
    simp only [diagonalSimpleRootIndex_fst, diagonalSimpleRootIndex_snd,
      d, LinearEquiv.apply_symm_apply, one_smul] at h
    exact h.symm
  rw [hroot, hroot, derivationComp_typeAGraphCoordinateIso_rootSubgroup]

variable [Nontrivial R] [ConnectedSpace (PrimeSpectrum R)]

/-- The graph differential preserves the scalar coordinates of every chosen
simple-root trivialization of the standard pinning. -/
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
