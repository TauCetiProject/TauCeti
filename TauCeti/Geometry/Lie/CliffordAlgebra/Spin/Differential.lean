/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Lie.Adjoint.Units.Basic
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Projection
public import TauCeti.LinearAlgebra.CliffordAlgebra.StandardBivector

/-!
# The differential of the real Spin projection

The differential of the compact real Spin projection acts on the defining real quadratic space
by the Clifford commutator. Consequently, after identifying quadratic Clifford elements with
exterior bivectors, it is the standard bivector-to-skew-matrix Lie equivalence, with no additional
sign or scalar factor.

The proof compares the source and target exponential curves of the concrete projection. In
Clifford coordinates this is conjugation by `exp (t x)`, while in matrix coordinates it is the
action of `exp (t A)`. Differentiating at zero gives `A v = [x, v]`.

## Main results

* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalCoordinateLieHom_lie_ι`:
  the coordinate differential acts by the Clifford commutator.
* `TauCeti.CliffordAlgebra.realCliffordSpinToSpecialOrthogonalCoordinateLieHom_eq_bivectorEquivSo`:
  the coordinate differential is the normalized bivector/skew-matrix equivalence.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras* (2008), Chapter 3.
-/

public section

open Manifold
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

attribute [local instance] Matrix.linftyOpTopologicalSpace

local notation "SpinUnitsRange(" n ")" =>
  MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))

local notation "SpecialOrthogonalUnitsRange(" n ")" =>
  MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
    (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))

local notation "SpinLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := modelWithCornersSelf ℝ (CliffordAlgebra (realCliffordForm n 0)))
    (SpinUnitsRange(n)))

local notation "SpecialOrthogonalLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := modelWithCornersSelf ℝ (Matrix (Fin n) (Fin n) ℝ))
    (SpecialOrthogonalUnitsRange(n)))

private theorem coordinate_exp_mulVec_eq_conjugation (n : ℕ)
    (x : quadraticLieSubalgebra (realCliffordForm n 0)) (v : Fin n → ℝ) (t : ℝ) :
    let Q := realCliffordForm n 0
    let A := ((realCliffordSpinToSpecialOrthogonalCoordinateLieHom n x :
      LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
    ι Q (NormedSpace.exp (t • A) *ᵥ v) =
      NormedSpace.exp (t • (x : CliffordAlgebra Q)) * ι Q v *
        NormedSpace.exp (t • (-(x : CliffordAlgebra Q))) := by
  let Q := realCliffordForm n 0
  let X := (realCliffordSpinLieEquivQuadratic n).symm x
  let Y := lieMap (realCliffordSpinToSpecialOrthogonalSmoothRange n) X
  let A := ((realCliffordSpinToSpecialOrthogonalCoordinateLieHom n x :
    LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
  let s := (realCliffordSpinContinuousMulEquivUnitsRange n).symm (lieExp (t • X))
  have hY : Y = realCliffordSpinToSpecialOrthogonalRangeLieMap n X := by
    exact DFunLike.congr_fun
      (realCliffordSpinToSpecialOrthogonalRangeLieMap_eq_lieMap n).symm X
  have hmap : realCliffordSpinToSpecialOrthogonalSmoothRange n (lieExp (t • X)) =
      lieExp (t • Y) := by
    calc
      realCliffordSpinToSpecialOrthogonalSmoothRange n (lieExp (t • X)) =
          lieExp (lieMap (realCliffordSpinToSpecialOrthogonalSmoothRange n) (t • X)) :=
        map_lieExp (realCliffordSpinToSpecialOrthogonalSmoothRange n) (t • X)
      _ = lieExp (t • Y) := by
        congr 1
        exact (lieMap (realCliffordSpinToSpecialOrthogonalSmoothRange n)).map_smul t X
  have htarget :
      (((realCliffordSpinToSpecialOrthogonalSmoothRange n (lieExp (t • X))).1 :
          (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ) =
        NormedSpace.exp (t • A) := by
    calc
      _ = (((realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n).subtypeVal
          (lieExp (t • Y)) : (Matrix (Fin n) (Fin n) ℝ)ˣ) :
            Matrix (Fin n) (Fin n) ℝ) := by
        simpa only [TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply] using congrArg
          (fun z : SpecialOrthogonalUnitsRange(n) ↦
            ((z.1 : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ)) hmap
      _ = NormedSpace.exp (t • unitsLieAlgebraEquiv
          ((realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n).lieMapSubtypeVal Y)) :=
        (realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n).coe_lieExp_smul Y t
      _ = NormedSpace.exp (t • A) := by
        congr 2
        calc
          unitsLieAlgebraEquiv
              ((realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n).lieMapSubtypeVal Y) =
              TauCeti.Lie.unitsLieAlgebraLieEquiv
                ((realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n).lieMapSubtypeVal Y) :=
            (TauCeti.Lie.unitsLieAlgebraLieEquiv_apply _).symm
          _ =
              ((realCliffordSpecialOrthogonalLieEquivSo n Y :
                LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) :=
            (coe_realCliffordSpecialOrthogonalLieEquivSo_apply n Y).symm
          _ = ((realCliffordSpecialOrthogonalLieEquivSo n
                (realCliffordSpinToSpecialOrthogonalRangeLieMap n X) :
              LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
            exact congrArg
              (fun z ↦ ((realCliffordSpecialOrthogonalLieEquivSo n z :
                  LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) hY
          _ = A := by
            simpa only [A, X] using congrArg
              (fun z : LieAlgebra.Orthogonal.so (Fin n) ℝ ↦
                (z : Matrix (Fin n) (Fin n) ℝ))
              (realCliffordSpinToSpecialOrthogonalCoordinateLieHom_apply n x).symm
  have hsource : (s : CliffordAlgebra Q) =
      NormedSpace.exp (t • (x : CliffordAlgebra Q)) := by
    have hequiv := (realCliffordSpinContinuousMulEquivUnitsRange n).apply_symm_apply
      (lieExp (t • X))
    have hsval : (s : CliffordAlgebra Q) =
        ((((realCliffordSpinContinuousMulEquivUnitsRange n s).1 :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
      rw [realCliffordSpinContinuousMulEquivUnitsRange_apply]
      rfl
    calc
      (s : CliffordAlgebra Q) =
          ((((realCliffordSpinContinuousMulEquivUnitsRange n s).1 :
            (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := hsval
      _ =
          ((((lieExp (t • X) : SpinUnitsRange(n)).1 :
            (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
        exact congrArg
          (fun z : SpinUnitsRange(n) ↦
            ((z.1 : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) hequiv
      _ = NormedSpace.exp (t • unitsLieAlgebraEquiv
          ((realCliffordSpinEmbeddedLieSubgroupData n).lieMapSubtypeVal X)) :=
        by simpa only [TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply] using
          (realCliffordSpinEmbeddedLieSubgroupData n).coe_lieExp_smul X t
      _ = NormedSpace.exp (t • (x : CliffordAlgebra Q)) := by
        congr 2
        calc
          unitsLieAlgebraEquiv
              ((realCliffordSpinEmbeddedLieSubgroupData n).lieMapSubtypeVal X) =
              TauCeti.Lie.unitsLieAlgebraLieEquiv
                ((realCliffordSpinEmbeddedLieSubgroupData n).lieMapSubtypeVal X) :=
            (TauCeti.Lie.unitsLieAlgebraLieEquiv_apply _).symm
          _ =
              ((realCliffordSpinLieEquivQuadratic n X :
                quadraticLieSubalgebra Q) : CliffordAlgebra Q) :=
            (coe_realCliffordSpinLieEquivQuadratic_apply n X).symm
          _ = (x : CliffordAlgebra Q) := by
            simp only [X, LieEquiv.apply_symm_apply]
  have hmatrix : NormedSpace.exp (t • A) *ᵥ v = spinVectorAction Q s v := by
    rw [← htarget]
    rw [realCliffordSpinToSpecialOrthogonalSmoothRange_apply,
      realCliffordSpinToSpecialOrthogonalRange_apply]
    -- Expose the underlying general-linear matrix so the canonical coordinate-action theorem
    -- can rewrite it to the special-orthogonal linear action.
    change (((QuadraticMap.specialOrthogonalToGeneralLinear Q
      (spinToSpecialOrthogonal Q s) : Matrix.GeneralLinearGroup (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ) *ᵥ v) = _
    rw [TauCeti.QuadraticMap.specialOrthogonalToGeneralLinear_mulVec,
      coe_spinToSpecialOrthogonal_apply]
  have hstar : star (x : CliffordAlgebra Q) = -(x : CliffordAlgebra Q) := by
    have hreverse := reverse_eq_neg_of_mem_quadraticLieSubalgebra Q x.property
    rw [reverse_eq_star_of_mem_even
      ⟨(x : CliffordAlgebra Q), quadraticLieSubalgebra_le_even Q x.property⟩] at hreverse
    exact hreverse
  dsimp only
  rw [hmatrix, ι_spinVectorAction_apply, hsource, NormedSpace.star_exp,
    CliffordAlgebra.star_smul, hstar]

private theorem hasDerivAt_ι_exp_mulVec (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ ι (realCliffordForm n 0) (NormedSpace.exp (t • A) *ᵥ v))
      (ι (realCliffordForm n 0) (A *ᵥ v)) 0 := by
  let mulVecCLM : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.mk ((Matrix.mulVecBilin ℝ ℝ).flip v)
      ((Matrix.mulVecBilin ℝ ℝ).flip v).continuous_of_finiteDimensional
  let ιCLM : (Fin n → ℝ) →L[ℝ] CliffordAlgebra (realCliffordForm n 0) :=
    ContinuousLinearMap.mk (ι (realCliffordForm n 0))
      (ι (realCliffordForm n 0)).continuous_of_finiteDimensional
  have hmatrix := mulVecCLM.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const A (0 : ℝ))
  have hι := ιCLM.hasFDerivAt.comp_hasDerivAt 0 hmatrix
  -- Expose the continuous-linear-map composition used by the derivative chain rule.
  change HasDerivAt (ιCLM ∘ mulVecCLM ∘ fun t : ℝ ↦ NormedSpace.exp (t • A))
    (ιCLM (mulVecCLM A)) 0
  simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using hι

/-- The differential of the real Spin projection acts on an embedded vector by the Clifford
commutator with its quadratic source coordinate. In particular, the convention has positive sign
and no additional scalar factor. -/
private theorem realCliffordSpinToSpecialOrthogonalCoordinateLieHom_commutator (n : ℕ)
    (x : quadraticLieSubalgebra (realCliffordForm n 0)) (v : Fin n → ℝ) :
    let Q := realCliffordForm n 0
    ι Q ((((realCliffordSpinToSpecialOrthogonalCoordinateLieHom n x :
      LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)) =
      (x : CliffordAlgebra Q) * ι Q v - ι Q v * (x : CliffordAlgebra Q) := by
  let Q := realCliffordForm n 0
  let A := ((realCliffordSpinToSpecialOrthogonalCoordinateLieHom n x :
    LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
  have hleft := hasDerivAt_ι_exp_mulVec n A v
  have hright := TauCeti.Lie.hasDerivAt_exp_mul_const_mul_exp_neg
    (x : CliffordAlgebra Q) (ι Q v)
  have hright' : HasDerivAt
      (fun t : ℝ ↦ ι Q (NormedSpace.exp (t • A) *ᵥ v))
      ((x : CliffordAlgebra Q) * ι Q v - ι Q v * (x : CliffordAlgebra Q)) 0 :=
    hright.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦
      coordinate_exp_mulVec_eq_conjugation n x v t)
  have hderiv := hleft.unique hright'
  simpa only [Q, A] using hderiv

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The differential action is the Lie bracket with its quadratic Clifford coordinate. -/
theorem realCliffordSpinToSpecialOrthogonalCoordinateLieHom_lie_ι (n : ℕ)
    (x : quadraticLieSubalgebra (realCliffordForm n 0)) (v : Fin n → ℝ) :
    let Q := realCliffordForm n 0
    ι Q ((((realCliffordSpinToSpecialOrthogonalCoordinateLieHom n x :
      LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)) =
      ⁅(x : CliffordAlgebra Q), ι Q v⁆ := by
  dsimp only
  rw [Ring.lie_def]
  exact realCliffordSpinToSpecialOrthogonalCoordinateLieHom_commutator n x v

/-- After the exterior-bivector identification, the differential of the real Spin projection is
the standard bivector-to-skew-matrix Lie equivalence. Thus its convention has positive sign and
the polar-form factor of two already built into `bivectorEquivSo`, with no further scalar. -/
theorem realCliffordSpinToSpecialOrthogonalCoordinateLieHom_eq_bivectorEquivSo (n : ℕ)
    (z : ⋀[ℝ]^2 (Fin n → ℝ)) :
    realCliffordSpinToSpecialOrthogonalCoordinateLieHom n
        (bivectorExteriorEquivQuadraticLieSubalgebra (realCliffordForm n 0) z) =
      bivectorEquivSo n ℝ z := by
  let Q := realCliffordForm n 0
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext y
  apply ι_injective Q
  rw [realCliffordSpinToSpecialOrthogonalCoordinateLieHom_lie_ι]
  symm
  apply ι_bivectorEquivSo_mulVec_of_polar
  intro a b
  -- Rewrite the compact real form to the standard quadratic form whose polar pairing is known.
  change QuadraticMap.polar (realCliffordForm n 0) a b = _
  rw [realCliffordForm_zero_eq_weightedSumSquares_one,
    ← QuadraticMap.polarBilin_apply_apply,
    TauCeti.QuadraticForm.polarBilin_weightedSumSquares_one]
  simp [Matrix.toLinearMap₂'_apply, Matrix.one_apply]

end TauCeti.CliffordAlgebra
