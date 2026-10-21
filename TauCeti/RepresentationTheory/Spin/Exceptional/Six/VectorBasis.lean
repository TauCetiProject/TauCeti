/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Exceptional.Six.Hyperbolic
public import TauCeti.RepresentationTheory.Spin.Exceptional.Six.SpecialIsometry
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.SpecialLinear

/-!
# Coordinate transport for the six-dimensional vector comparison

The exterior-square model and the Clifford Fock model use different canonical coordinates. The
wedge basis identifies the six-dimensional exterior square with the split quadratic space, while
the Spin-to-`SL₄` equivalence is recorded in the finite-dimensional basis chosen by the matrix
model. This file keeps those changes of coordinates explicit.

The half-spin action of each canonical Spin lift is an elementary transvection in the monomial
basis. The two basis-change results below transport that calculation to the fixed `SL₄`
coordinates. They are the generator boundary for comparing the Spin vector action with the
exterior-square standard action.
-/

public section

namespace TauCeti

open Module

universe u

variable (K : Type u) [CommRing K] [Nontrivial K] [Invertible (2 : K)]

/-- The wedge basis transported to the split six-dimensional quadratic space. -/
noncomputable def spinSixWedgeBasisInSplit :
    Basis (Fin 3 ⊕ Fin 3) K (SplitEvenSpace K 3) :=
  (spinSixWedgeBasis K).map (spinSixWedgeQuadraticIsometryEquivSplit K).toLinearEquiv

@[simp]
theorem spinSixWedgeBasisInSplit_inl (i : Fin 3) :
    spinSixWedgeBasisInSplit K (Sum.inl i) =
      ((Pi.basisFun K (Fin 3)).coord i, 0) := by
  rw [spinSixWedgeBasisInSplit, Basis.map_apply]
  change (spinSixWedgeQuadraticIsometryEquivSplit K)
      (spinSixWedgeBasis K (Sum.inl i)) = _
  rw [spinSixWedgeQuadraticIsometryEquivSplit_apply,
    spinSixWedgeIsometryEquivPolarSplit_apply_inl]

@[simp]
theorem spinSixWedgeBasisInSplit_inr (i : Fin 3) :
    spinSixWedgeBasisInSplit K (Sum.inr i) =
      (0, Pi.single i 1) := by
  rw [spinSixWedgeBasisInSplit, Basis.map_apply]
  change (spinSixWedgeQuadraticIsometryEquivSplit K)
      (spinSixWedgeBasis K (Sum.inr i)) = _
  rw [spinSixWedgeQuadraticIsometryEquivSplit_apply,
    spinSixWedgeIsometryEquivPolarSplit_apply_inr]

end TauCeti

namespace TauCeti

open _root_.CliffordAlgebra Module

universe u

variable (K : Type u) [Field K] [NeZero (2 : K)]

/-- The characteristic-not-two witness used by the split Clifford and half-spin APIs. -/
local instance spinSixBasisInvertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (NeZero.ne (2 : K))

/-- The even half-spin basis made from the canonical exterior monomials. -/
noncomputable abbrev spinSixHalfSpinMonomialBasis :
    Basis (Fin 4) K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) :=
  (splitEvenBasis K 3).spinSixEvenMonomialBasis (spinPlus_def _)

/-- The finite-dimensional basis used by the split Spin-to-`SL₄` matrix equivalence. -/
noncomputable abbrev spinSixHalfSpinStandardBasis :
    Basis (Fin 4) K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) :=
  Module.finBasisOfFinrankEq K _ (finrank_hyperbolicSixSpinPlus K)

/-- Conjugating the fixed `SL₄` coordinates by the canonical basis change gives the
monomial-basis matrix of the Spin half-spin action. -/
theorem spinSixBasisChange_conjugate_spinPlusAction
    (s : spinGroup (splitEvenForm K 3)) :
    (spinSixHalfSpinMonomialBasis K).toMatrix (spinSixHalfSpinStandardBasis K) *
        (hyperbolicSixSpinEquivSpecialLinear K s : Matrix (Fin 4) (Fin 4) K) *
        (spinSixHalfSpinStandardBasis K).toMatrix (spinSixHalfSpinMonomialBasis K) =
      LinearMap.toMatrix (spinSixHalfSpinMonomialBasis K) (spinSixHalfSpinMonomialBasis K)
        (spinPlusAction (splitEvenForm K 3) (splitEvenPolarization K 3)
          (splitEvenPolarization_line K 3) (spinGroupToEven _ s)) := by
  let P := splitEvenPolarization K 3
  let hline := splitEvenPolarization_line K 3
  let hW := splitEvenPolarization_W_ne_bot K (by norm_num : (3 : ℕ) ≠ 0)
  let hplus := finrank_hyperbolicSixSpinPlus K
  let hV := finrank_splitEvenSpace K 3
  let F := spinSixHalfSpinStandardBasis K
  have hmatrix : (hyperbolicSixSpinEquivSpecialLinear K s : Matrix (Fin 4) (Fin 4) K) =
      LinearMap.toMatrix F F
        (spinPlusAction (splitEvenForm K 3) P hline (spinGroupToEven _ s)) := by
    exact coe_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_apply P hline
      (by simp [P]) hW hplus hV F rfl s
  rw [hmatrix]
  exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (b := spinSixHalfSpinMonomialBasis K) (b' := spinSixHalfSpinStandardBasis K)
    (c := spinSixHalfSpinMonomialBasis K) (c' := spinSixHalfSpinStandardBasis K)
    (f := spinPlusAction (splitEvenForm K 3) (splitEvenPolarization K 3)
      (splitEvenPolarization_line K 3) (spinGroupToEven _ s))

/-- The conjugated fixed-coordinate matrix of a canonical Spin lift is the elementary
transvection it lifts. -/
theorem spinSixBasisChange_transvection {i j : Fin 4} (hij : i ≠ j) (c : K) :
    (spinSixHalfSpinMonomialBasis K).toMatrix (spinSixHalfSpinStandardBasis K) *
        (hyperbolicSixSpinEquivSpecialLinear K
          (spinSixTransvectionLift (splitEvenPolarization K 3)
            (splitEvenPolarization_line K 3) (splitEvenBasis K 3) hij c) :
          Matrix (Fin 4) (Fin 4) K) *
        (spinSixHalfSpinStandardBasis K).toMatrix (spinSixHalfSpinMonomialBasis K) =
      Matrix.transvection i j c := by
  rw [spinSixBasisChange_conjugate_spinPlusAction]
  exact toMatrix_spinPlusAction_spinSixTransvectionLift
    (P := splitEvenPolarization K 3) (hline := splitEvenPolarization_line K 3)
    (b := splitEvenBasis K 3) hij c

end TauCeti

end
