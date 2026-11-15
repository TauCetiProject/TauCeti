/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Positive
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Borel

/-!
# The standard pinning of the general linear group

The diagonal torus, upper-triangular Borel, and consecutive matrix units give a pinning
of `GL_(r+1)` over every nontrivial commutative ring with connected spectrum. Its torus
has rank `r+1`, whereas its simple roots are indexed by `Fin r`. In particular, this
constructs the integral general-linear pinning without restricting the characteristic
or requiring the base ring to be reduced.

The simple-root trivializations are normalized by the elementary root subgroups:
the differential of `x_(i,i+1)` sends the unit additive tangent vector to the chosen
root vector. The matrix-unit computation rules below, together with
`GeneralLinear.cotangentDual_rootSubgroup_unit`, identify this differential without
unfolding the assembled pinning.

This assembles `GeneralLinear.splitMaximalTorus`, the upper-triangular Borel,
`GeneralLinear.diagonalSimpleRootEquiv`, and `GeneralLinear.rootSpaceEquiv`.
The construction follows `SpecialLinear.Pinning.Basic`, keeping the full rank of the
general-linear torus rather than imposing determinant one.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1 and Example 21.2.
-/

public section

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {R : Type u} [CommRing R] [Nontrivial R]
  [ConnectedSpace (PrimeSpectrum R)] {r : ℕ}

/-- The standard pinning of `GL_(r+1)` over a connected base: diagonal torus,
upper-triangular Borel, and normalized consecutive matrix-unit root vectors. -/
def standardPinning (R : Type u) [CommRing R] [Nontrivial R]
    [ConnectedSpace (PrimeSpectrum R)] (r : ℕ) :
    Pinning R (coordinateHopfAlgebra R (r + 1)) (r + 1) where
  reductive := by
    have h : finiteTypeCoordinateHopfAlgebra R (r + 1) =
        FiniteTypeCommHopfAlgCat.of R (coordinateHopfAlgebra R (r + 1)) := by
      apply CategoryTheory.ObjectProperty.FullSubcategory.ext
      exact finiteTypeCoordinateHopfAlgebra_obj R (r + 1)
    exact h ▸ reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra R (r + 1)
  torus := splitMaximalTorus R (r + 1)
  borel := UpperTriangular.definingHopfIdeal R (r + 1)
  isBorel := UpperTriangular.isBorelOver_definingHopfIdeal R (r + 1)
  borel_le_torus := UpperTriangular.definingHopfIdeal_le_splitMaximalTorus_definingIdeal R (r + 1)
  rootSpaceEquiv α :=
    (rootSpaceEquiv (diagonalSimpleRootIndex r ((diagonalSimpleRootEquiv (R := R)).symm α))).trans
      (LinearEquiv.ofEq _ _ (by
        have h := congrArg Subtype.val ((diagonalSimpleRootEquiv (R := R)).apply_symm_apply α)
        rw [diagonalSimpleRootEquiv_apply] at h
        rw [splitMaximalTorus_coordinateMap, h]
        rfl))

/-- The standard pinning uses the parametrized diagonal maximal torus. -/
@[simp]
theorem standardPinning_torus :
    (standardPinning R r).torus = splitMaximalTorus R (r + 1) := (rfl)

/-- The standard pinning uses the upper-triangular Borel. -/
@[simp]
theorem standardPinning_borel :
    (standardPinning R r).borel = UpperTriangular.definingHopfIdeal R (r + 1) := (rfl)

/-- Consecutive numbering of the intrinsic simple roots of the standard pinning. -/
def standardPinningSimpleRootEquiv :
    Fin r ≃ {α // (standardPinning R r).torus.IsSimpleRoot (standardPinning R r).borel α} :=
  diagonalSimpleRootEquiv (R := R)

/-- The numbered simple root is the consecutive coordinate difference. -/
@[simp]
theorem standardPinningSimpleRootEquiv_apply (i : Fin r) :
    (standardPinningSimpleRootEquiv (R := R) i).val =
      (diagonalRootDatum.{u} (r + 1)).root (diagonalSimpleRootIndex r i) :=
  diagonalSimpleRootEquiv_apply i

/-- The chosen simple-root trivialization sends a scalar to the corresponding
multiple of the consecutive matrix-unit tangent vector. -/
@[simp↓ 1100]
theorem standardPinning_rootSpaceEquiv_apply_coe (i : Fin r) (c : R) :
    ((standardPinning R r).rootSpaceEquiv (standardPinningSimpleRootEquiv (R := R) i) c :
      Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R (r + 1)))) =
        c • matrixUnitTangent (k := R) i.castSucc i.succ := by
  simp only [standardPinning, standardPinningSimpleRootEquiv]
  -- The root-space transports use indexed cotangent and character presentations.
  erw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Equiv.symm_apply_apply, rootSpaceEquiv_apply_coe]
  simp only [diagonalSimpleRootIndex_fst, diagonalSimpleRootIndex_snd, ULift.down_up]

/-- The standard pinning chooses the consecutive matrix units as root vectors. -/
@[simp↓ 1100]
theorem standardPinning_rootVector (i : Fin r) :
    (standardPinning R r).rootVector (standardPinningSimpleRootEquiv (R := R) i) =
      matrixUnitTangent (k := R) i.castSucc i.succ := by
  rw [Pinning.rootVector_def, standardPinning_rootSpaceEquiv_apply_coe, one_smul]

end

end TauCeti.GeneralLinear
