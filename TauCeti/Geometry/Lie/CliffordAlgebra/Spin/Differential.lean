/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.UnitsDifferential
public import TauCeti.Geometry.Lie.CliffordAlgebra.Spin.Projection
public import TauCeti.LinearAlgebra.CliffordAlgebra.StandardBivector
import TauCeti.LinearAlgebra.QuadraticForm.Standard

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
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The differential action is the Lie bracket with its quadratic Clifford coordinate. -/
theorem realCliffordSpinToSpecialOrthogonalCoordinateLieHom_lie_ι (n : ℕ)
    (x : quadraticLieSubalgebra (realCliffordForm n 0)) (v : Fin n → ℝ) :
    let Q := realCliffordForm n 0
    ι Q ((((realCliffordSpinToSpecialOrthogonalCoordinateLieHom n x :
      LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)) =
      ⁅(x : CliffordAlgebra Q), ι Q v⁆ := by
  let Q := realCliffordForm n 0
  let X := (realCliffordSpinLieEquivQuadratic n).symm x
  let A := ((realCliffordSpinToSpecialOrthogonalCoordinateLieHom n x :
    LieAlgebra.Orthogonal.so (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
  refine ι_mulVec_eq_lie_of_spinToSpecialOrthogonal_exp_curve (Q := realCliffordFormZero n)
    (AlgEquiv.refl : CliffordAlgebra Q ≃ₐ[ℝ] CliffordAlgebra Q) (x : CliffordAlgebra Q) A
    (fun t : ℝ ↦ lieExp (t • X)) ?_ ?_ v
  · intro t
    rw [← TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply
        (d := realCliffordSpinEmbeddedLieSubgroupData n),
      (realCliffordSpinEmbeddedLieSubgroupData n).coe_lieExp_smul X t,
      ← TauCeti.Lie.unitsLieAlgebraLieEquiv_apply,
      unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_realCliffordSpinLieEquivQuadratic]
    simp only [X, LieEquiv.apply_symm_apply, AlgEquiv.coe_refl, id_eq]
  · intro t
    rw [← realCliffordSpinToSpecialOrthogonalSmoothRange_apply,
      ← TauCeti.Lie.EmbeddedLieSubgroupData.subtypeVal_apply
        (d := realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n),
      (realCliffordSpinEmbeddedLieSubgroupData n).coe_map_lieExp_smul
        (realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n)
        (realCliffordSpinToSpecialOrthogonalSmoothRange n) X t,
      ← TauCeti.Lie.unitsLieAlgebraLieEquiv_apply,
      unitsLieAlgebraLieEquiv_lieMapSubtypeVal_eq_coe_realCliffordSpecialOrthogonalLieEquivSo,
      ← realCliffordSpinToSpecialOrthogonalCoordinateLieHom_apply]

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
