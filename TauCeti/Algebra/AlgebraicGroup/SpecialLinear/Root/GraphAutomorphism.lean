/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Base
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.GraphAutomorphism
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.Adjoint

/-!
# The type-A graph involution on root-subgroup differentials

The signed reverse inverse transpose automorphism of `SL_{r+1}` reverses the
positive simple-root subgroup differentials, preserving their additive tangent
parameters over every commutative coefficient algebra. Over every commutative
base ring, it sends the normalized simple root vector numbered `i` to the one
numbered `i.rev`, with no sign or scalar factor.

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
  rw [cotangentLinearEquiv_rootVector, cotangentLinearEquiv_rootVector]
  simp only [diagonalSimpleRootIndex_fst, diagonalSimpleRootIndex_snd]
  rw [derivationComp_typeAGraphCoordinateIso_rootSubgroup]

end TauCeti.SpecialLinear
