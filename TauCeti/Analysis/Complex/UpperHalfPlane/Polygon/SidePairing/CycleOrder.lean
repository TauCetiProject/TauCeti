/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.VertexSector
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer

/-!
# Exact orders of finite vertex-cycle transformations

The derivative of a side-pairing cycle transformation at its finite vertex is
`exp (i * cycleAngleSum)`. Thus a cycle with angle sum `2π / t` has transformation of exact
order `t`, including `t = 1`. This supplies the finite-cycle relations used in polygon
presentations. Neither discreteness nor a fundamental-domain assumption is needed: the angle
condition alone determines this order. The converse angle condition for a fundamental polygon
requires no-overlap and is a separate statement.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 9.
* Svetlana Katok, *Fuchsian Groups*, Chapter 3.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups Real

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- The derivative of a cycle transformation at a finite vertex is the unit complex number
whose counterclockwise angle is the cycle angle sum. -/
@[simp]
theorem smulDeriv_cycleMap {j : Fin n} {z : ℍ} (hz : P.vertex j = .inl z) :
    smulDeriv (σ.cycleMap j) z = Complex.exp (σ.cycleAngleSum j * Complex.I) := by
  have hfix : σ.cycleMap j • z = z := by
    simpa only [hz, Sum.smul_inl, Sum.inl.injEq] using σ.cycleMap_smul_vertex j
  apply Complex.ext_norm_arg
  · rw [norm_smulDeriv_of_smul_eq_self hfix, Complex.norm_exp_ofReal_mul_I]
  · apply Complex.arg_coe_angle_eq_iff.mp
    rw [σ.arg_smulDeriv_cycleMap hz, Complex.exp_mul_I]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Real.Angle.cos_coe,
      ← Real.Angle.sin_coe, Complex.arg_cos_add_sin_mul_I_coe_angle]

/-- If the angle sum at a finite vertex cycle is `2π / t`, its cycle transformation has exact
order `t`. In particular, the relation cannot be shortened to a proper divisor of `t`. -/
theorem orderOf_cycleMap_of_cycleAngleSum {j : Fin n} {z : ℍ}
    (hz : P.vertex j = .inl z) {t : ℕ}
    (hangle : σ.cycleAngleSum j = 2 * π / t) : orderOf (σ.cycleMap j) = t := by
  have ht : t ≠ 0 := by
    intro ht
    have hpos := σ.cycleAngleSum_pos_of_isLeft_vertex (j := j) (by simp [hz])
    simp only [ht, Nat.cast_zero, div_zero] at hangle
    exact hpos.ne' hangle
  have hfix : σ.cycleMap j • z = z := by
    simpa only [hz, Sum.smul_inl, Sum.inl.injEq] using σ.cycleMap_smul_vertex j
  let q : MulAction.stabilizer (⊤ : Subgroup PSL(2, ℝ)) z := ⟨⟨σ.cycleMap j, by simp⟩, hfix⟩
  have horder : orderOf (smulDeriv (σ.cycleMap j) z) = orderOf (σ.cycleMap j) := by
    calc
      orderOf (smulDeriv (σ.cycleMap j) z) = orderOf q :=
        by simpa only [Subgroup.stabilizerDeriv_apply] using
          Subgroup.orderOf_stabilizerDeriv (⊤ : Subgroup PSL(2, ℝ)) z q
      _ = orderOf (q : (⊤ : Subgroup PSL(2, ℝ))) := (Subgroup.orderOf_coe q).symm
      _ = orderOf (σ.cycleMap j) :=
        (Subgroup.orderOf_coe (q : (⊤ : Subgroup PSL(2, ℝ)))).symm
  rw [← horder, σ.smulDeriv_cycleMap hz, hangle]
  have he : ((2 * π / t : ℝ) : ℂ) * Complex.I = 2 * (π : ℂ) * Complex.I / t := by
    push_cast
    ring
  rw [he]
  exact (Complex.isPrimitiveRoot_exp t ht).eq_orderOf.symm

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
