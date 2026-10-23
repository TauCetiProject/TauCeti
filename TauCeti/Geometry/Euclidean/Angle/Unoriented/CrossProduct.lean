/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

/-!
# Completing an orthonormal pair by the cross product

The cross product of two orthogonal unit vectors in `ℝ³` completes them to an orthonormal
basis. Every vector orthogonal to the first vector is therefore a linear combination of
the second vector and their cross product. This supplies the normal-plane frame used by
`TauCeti.exists_isSolidTorusNeighborhood`.

## Main results

* `TauCeti.cross_orthonormal`: the cross product completes an orthonormal pair and gives
  coordinates for the plane orthogonal to its first vector.
-/

public section

open WithLp
open scoped Matrix RealInnerProductSpace

namespace TauCeti

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Completing an orthonormal pair `u, n` of `ℝ³` by the cross product `u × n` gives an
orthonormal basis; in particular every vector orthogonal to `u` is a combination of `n` and
`u × n`. -/
theorem cross_orthonormal {u n : ℝ³} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1) (hun : ⟪u, n⟫ = 0) :
    ‖toLp 2 (ofLp u ⨯₃ ofLp n)‖ = 1 ∧ ⟪u, toLp 2 (ofLp u ⨯₃ ofLp n)⟫ = 0 ∧
      ⟪n, toLp 2 (ofLp u ⨯₃ ofLp n)⟫ = 0 ∧
      ∀ v : ℝ³, ⟪u, v⟫ = 0 →
        v = ⟪n, v⟫ • n + ⟪toLp 2 (ofLp u ⨯₃ ofLp n), v⟫ • toLp 2 (ofLp u ⨯₃ ofLp n) := by
  set c : ℝ³ := toLp 2 (ofLp u ⨯₃ ofLp n)
  have hc : ‖c‖ = 1 := by
    rw [InnerProductGeometry.norm_ofLp_crossProduct, hu, hn,
      (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two u n).mp hun, Real.sin_pi_div_two,
      one_mul, one_mul]
  have huc : ⟪u, c⟫ = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm, ofLp_toLp,
      dot_self_cross]
  have hnc : ⟪n, c⟫ = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm, ofLp_toLp,
      dot_cross_self]
  refine ⟨hc, huc, hnc, fun v hv => ?_⟩
  -- `u, n, c` is an orthonormal family of three vectors, hence an orthonormal basis of `ℝ³`.
  have hon : Orthonormal ℝ ![u, n, c] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hu, hn, hc, hun, huc, hnc, real_inner_comm u, real_inner_comm n]
  let b := (basisOfOrthonormalOfCardEqFinrank hon (by simp)).toOrthonormalBasis
    (by rwa [coe_basisOfOrthonormalOfCardEqFinrank])
  have hb : ∀ i, b i = ![u, n, c] i := fun i => by
    simp [b, coe_basisOfOrthonormalOfCardEqFinrank]
  have := b.sum_repr' v
  simp only [Fin.sum_univ_three, hb] at this
  simpa [hv] using this.symm

end TauCeti
