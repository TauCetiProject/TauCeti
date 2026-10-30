/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Two
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.Basic
-- Non-public: the path-connectedness of `ℂˣ`, the non-simple-connectedness of `ℂˣ`, and the
-- normalization of complex quadratic forms are used only in proofs.
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.LinearAlgebra.QuadraticForm.SepClosed

/-!
# The two-dimensional Spin group as a multiplicative group

Over a field `K` in which `2` is invertible and which contains a square root `i` of `-1`, the Spin
group of the sum of two squares on `K²` is the multiplicative group `Kˣ`: writing
`J = ι e₀ * ι e₁`, so that `J * J = -1`, a Spin element is `u + v J` with `u² + v² = 1`, and
`u + v J ↦ u + i v` is an isomorphism `CliffordAlgebra.spinGroupEquivUnitsWeightedSumSquaresOne`.
This file shows that over a topological field both this isomorphism and its inverse `z ↦ u + v J`,
with `u = (z + z⁻¹) / 2` and `v = i (z⁻¹ - z) / 2`, are continuous, so that it is an isomorphism
of topological groups.

Over `ℂ` every nondegenerate quadratic form on a two-dimensional space is isometric to the sum of
two squares. Its Spin group, with the subtype topology from the Clifford algebra, is therefore
isomorphic to `ℂˣ` as a topological group. Consequently it is path-connected but not simply
connected: `ℂˣ` deformation retracts onto the unit circle. Two is the exceptional dimension here,
as the complex Spin groups of dimension at least three are simply connected.

## Main definitions

* `CliffordAlgebra.spinGroupContinuousMulEquivUnitsWeightedSumSquaresOne`: the isomorphism of
  topological groups `Spin(x₀² + x₁²) ≃ₜ* Kˣ` over a topological field containing `√-1`, in
  which `2` is invertible.

## Main results

* `CliffordAlgebra.nonempty_spinGroup_continuousMulEquiv_units_of_finrank_eq_two`: the Spin group
  of a nondegenerate quadratic form on a two-dimensional complex space is isomorphic to `ℂˣ` as a
  topological group.
* `CliffordAlgebra.pathConnectedSpace_spinGroup_of_finrank_eq_two`: it is path-connected.
* `CliffordAlgebra.not_simplyConnectedSpace_spinGroup_of_finrank_eq_two`: it is not simply
  connected.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.2.
-/

public section

open Module QuadraticMap

namespace CliffordAlgebra

/-! ### Over a topological field containing `√-1`, with `2` invertible -/

section TopologicalField

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [Invertible (2 : K)]
  (i : K) (hi : i * i = -1)

/-- The unit attached to a Spin element depends continuously on it. -/
private theorem continuous_coe_spinGroupEquivUnitsWeightedSumSquaresOne :
    Continuous fun g : spinGroup (weightedSumSquares K ![(1 : K), 1]) ↦
      (spinGroupEquivUnitsWeightedSumSquaresOne i hi g : K) := by
  let Q := weightedSumSquares K ![(1 : K), 1]
  let _ : ContinuousAdd (CliffordAlgebra Q) := IsModuleTopology.toContinuousAdd K _
  -- In coordinates the unit is `w₀ + i w₁` for `w = ιInv (ι e₀ * g)`, a linear function of `g`.
  have hw : Continuous fun g : spinGroup Q ↦ ιInv Q (ι Q ![1, 0] * (g : CliffordAlgebra Q)) :=
    (continuous_ιInv Q).comp ((IsModuleTopology.continuous_of_linearMap
      (LinearMap.mulLeft K (ι Q ![1, 0]))).comp continuous_subtype_val)
  simp only [coe_spinGroupEquivUnitsWeightedSumSquaresOne_apply,
    evenWeightedSumSquaresOneAlgHom_apply, coe_spinGroupToEven_apply]
  exact ((continuous_apply 0).comp hw).add (continuous_const.mul ((continuous_apply 1).comp hw))

/-- **The Spin group of the sum of two squares is `Kˣ` as a topological group**, over a
topological field `K` in which `2` is invertible and which contains a square root `i` of `-1`.
This is `spinGroupEquivUnitsWeightedSumSquaresOne`, sending `u + v J` to `u + i v`, for the
subtype topology on the Spin group from the module topology of the Clifford algebra. -/
noncomputable def spinGroupContinuousMulEquivUnitsWeightedSumSquaresOne :
    spinGroup (weightedSumSquares K ![(1 : K), 1]) ≃ₜ* Kˣ where
  toMulEquiv := spinGroupEquivUnitsWeightedSumSquaresOne i hi
  continuous_toFun := Units.continuous_iff.2
    ⟨continuous_coe_spinGroupEquivUnitsWeightedSumSquaresOne i hi, by
      simpa only [MulEquiv.toFun_eq_coe, ← map_inv, Function.comp_def] using
        (continuous_coe_spinGroupEquivUnitsWeightedSumSquaresOne i hi).comp continuous_inv⟩
  continuous_invFun := by
    let Q := weightedSumSquares K ![(1 : K), 1]
    have hv : Continuous fun z : Kˣ ↦
        (![((z : K) + z⁻¹) / 2, i * ((z⁻¹ : Kˣ) - z) / 2] : Fin 2 → K) := by
      refine continuous_pi fun j ↦ ?_
      fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> fun_prop
    refine continuous_induced_rng.2 ?_
    simp only [Function.comp_def, MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
      MulEquiv.coe_toEquiv_symm, coe_spinGroupEquivUnitsWeightedSumSquaresOne_symm_apply]
    exact continuous_const.mul ((continuous_ι Q).comp hv)

/-- The topological isomorphism evaluates as the algebraic one. -/
@[simp]
theorem coe_spinGroupContinuousMulEquivUnitsWeightedSumSquaresOne :
    ⇑(spinGroupContinuousMulEquivUnitsWeightedSumSquaresOne i hi) =
      spinGroupEquivUnitsWeightedSumSquaresOne i hi :=
  (rfl)

/-- The inverse topological isomorphism evaluates as the inverse algebraic one. -/
@[simp]
theorem coe_spinGroupContinuousMulEquivUnitsWeightedSumSquaresOne_symm :
    ⇑(spinGroupContinuousMulEquivUnitsWeightedSumSquaresOne i hi).symm =
      (spinGroupEquivUnitsWeightedSumSquaresOne i hi).symm :=
  (rfl)

end TopologicalField

/-! ### Complex two-dimensional Spin groups -/

section Complex

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **The complex two-dimensional Spin group is `ℂˣ`**: the Spin group of a nondegenerate quadratic
form on a two-dimensional complex space is isomorphic to `ℂˣ` as a topological group. The
isomorphism depends on an isometry with the sum of two squares, and on the choice of `i` against
`-i`. -/
theorem nonempty_spinGroup_continuousMulEquiv_units_of_finrank_eq_two (Q : QuadraticForm ℂ V)
    (hQ : Q.Nondegenerate) (hV : finrank ℂ V = 2) : Nonempty (spinGroup Q ≃ₜ* ℂˣ) := by
  let _ : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  let _ : FiniteDimensional ℂ V := .of_finrank_pos (by rw [hV]; decide)
  obtain ⟨e⟩ := (QuadraticForm.equivalent_weightedSumSquares_one_iff_finrank_eq Q hQ 2).2 hV
  have h1 : (1 : Fin 2 → ℂ) = ![1, 1] := by
    ext j
    fin_cases j <;> rfl
  rw [h1] at e
  exact ⟨e.spinGroupContinuousMulEquiv.trans
    (spinGroupContinuousMulEquivUnitsWeightedSumSquaresOne Complex.I Complex.I_mul_I)⟩

/-- **The complex two-dimensional Spin group is path-connected.** -/
theorem pathConnectedSpace_spinGroup_of_finrank_eq_two (Q : QuadraticForm ℂ V)
    (hQ : Q.Nondegenerate) (hV : finrank ℂ V = 2) : PathConnectedSpace (spinGroup Q) :=
  let ⟨e⟩ := nonempty_spinGroup_continuousMulEquiv_units_of_finrank_eq_two Q hQ hV
  e.symm.surjective.pathConnectedSpace e.symm.continuous

/-- **The complex two-dimensional Spin group is not simply connected**, being homeomorphic to the
punctured plane `ℂˣ`. -/
theorem not_simplyConnectedSpace_spinGroup_of_finrank_eq_two (Q : QuadraticForm ℂ V)
    (hQ : Q.Nondegenerate) (hV : finrank ℂ V = 2) : ¬ SimplyConnectedSpace (spinGroup Q) :=
  fun _ ↦
    let ⟨e⟩ := nonempty_spinGroup_continuousMulEquiv_units_of_finrank_eq_two Q hQ hV
    Complex.not_simplyConnectedSpace_units e.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

end Complex

end CliffordAlgebra
