/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Quaternionic tangent vector fields on the spheres `S^{4k-1}`

Let `E` be a real inner product space on which the quaternions act on the right, written
`x <• q`, with `‖x <• q‖ = ‖q‖ * ‖x‖`. The model case is the quaternionic coordinate space
`ℍ^ι = PiLp 2 (fun _ : ι => ℍ)`, of real dimension `4 * Fintype.card ι`
(`TauCeti.finrank_piLp_quaternion`), whose unit sphere is `S^{4k-1}` for `k = Fintype.card ι`.

The quaternionic inner-product facts used here are developed in `TauCeti.Analysis.Quaternion.Basic`.
For a unit vector `x`, the three vectors `x <• i`, `x <• j`, `x <• k` are orthonormal and
orthogonal to `x`: they are three pointwise orthonormal tangent vector fields on the unit sphere of
`E`, and they are restrictions of real-linear maps of `E`, hence analytic. For `E = ℍ^ι` these are
the classical vector fields on `S^{4k-1}` coming from quaternionic multiplication.

Tangent vector fields on a sphere are represented, as usual in topology, by maps
`v : sphere (0 : E) 1 → E` with `⟪v x, x⟫ = 0`.

## Main declarations

* `TauCeti.quaternionFrame`: the three vectors `x <• i`, `x <• j`, `x <• k`.
* `TauCeti.orthonormal_quaternionFrame`, `TauCeti.inner_quaternionFrame_self`: the three
  vectors are orthogonal to `x`, and orthonormal when `x` is a unit vector.
* `TauCeti.orthonormal_vecCons_quaternionFrame`: with `x`, they form an orthonormal four-frame.
* `TauCeti.orthonormal_quaternionFrame_pair_of_ne`: any two of them are orthonormal.
* `TauCeti.continuous_quaternionFrame`: they are continuous on `E`.
* `TauCeti.contDiff_quaternionFrame`, `TauCeti.contMDiff_quaternionFrame`: they are analytic on
  `E` and on the unit sphere.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.3.
-/

public section

open Metric Module MulOpposite Quaternion
open scoped RealInnerProductSpace RightActions Manifold ContDiff

namespace TauCeti

variable {E : Type*}

section Frame

variable [SMul ℍᵐᵒᵖ E]

/-- The three vectors `x <• i`, `x <• j`, `x <• k` obtained from `x` by right multiplication by
the imaginary quaternion units. On the unit sphere they are three pointwise orthonormal tangent
vector fields. -/
def quaternionFrame (x : E) : Fin 3 → E :=
  ![x <• (⟨0, 1, 0, 0⟩ : ℍ), x <• (⟨0, 0, 1, 0⟩ : ℍ), x <• (⟨0, 0, 0, 1⟩ : ℍ)]

@[simp]
theorem quaternionFrame_zero (x : E) : quaternionFrame x 0 = x <• (⟨0, 1, 0, 0⟩ : ℍ) :=
  (rfl)

@[simp]
theorem quaternionFrame_one (x : E) : quaternionFrame x 1 = x <• (⟨0, 0, 1, 0⟩ : ℍ) :=
  (rfl)

@[simp]
theorem quaternionFrame_two (x : E) : quaternionFrame x 2 = x <• (⟨0, 0, 0, 1⟩ : ℍ) :=
  (rfl)

/-- Each vector field of the quaternionic frame is a continuous map of `E`. -/
theorem continuous_quaternionFrame [TopologicalSpace E] [ContinuousConstSMul ℍᵐᵒᵖ E] (j : Fin 3) :
    Continuous fun x : E ↦ quaternionFrame x j := by
  fin_cases j <;> exact continuous_const_smul _

end Frame

section Smooth

variable [NormedAddCommGroup E] [DistribSMul ℍᵐᵒᵖ E] [ContinuousConstSMul ℍᵐᵒᵖ E]

/-- Each vector field of the quaternionic frame extends to an analytic map of `E`. -/
theorem contDiff_quaternionFrame [NormedSpace ℝ E] [SMulCommClass ℝ ℍᵐᵒᵖ E] {m : ℕ∞ω}
    (j : Fin 3) : ContDiff ℝ m fun x : E ↦ quaternionFrame x j := by
  fin_cases j <;> exact contDiff_const_smul _

/-- Each vector field of the quaternionic frame is an analytic map on the unit sphere. -/
theorem contMDiff_quaternionFrame [InnerProductSpace ℝ E] [SMulCommClass ℝ ℍᵐᵒᵖ E] {m : ℕ∞ω} {n : ℕ}
    [Fact (finrank ℝ E = n + 1)] (j : Fin 3) :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) m fun x : sphere (0 : E) 1 ↦ quaternionFrame (x : E) j :=
  (contDiff_quaternionFrame j).contMDiff.comp contMDiff_coe_sphere

end Smooth

variable [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] [Module ℍᵐᵒᵖ E] [NormSMulClass ℍᵐᵒᵖ E]

/-- Each vector of the quaternionic frame of `x` is orthogonal to `x`: on the unit sphere the
frame consists of tangent vectors. -/
@[simp]
theorem inner_quaternionFrame_self (x : E) (j : Fin 3) : ⟪quaternionFrame x j, x⟫ = 0 := by
  fin_cases j <;> simp

/-- The quaternionic frame of a unit vector is orthonormal. -/
theorem orthonormal_quaternionFrame {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ (quaternionFrame x) := by
  -- The imaginary units `i`, `j`, `k` are orthonormal in `ℍ`.
  have hijk : Orthonormal ℝ (![⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] : Fin 3 → ℍ) := by
    simp [orthonormal_iff_ite, Fin.forall_fin_succ, inner_def]
  convert orthonormal_op_smul hx hijk using 1
  ext j
  fin_cases j <;> simp

/-- A unit vector `x` followed by its quaternionic frame `x <• i`, `x <• j`, `x <• k` is
orthonormal. -/
theorem orthonormal_vecCons_quaternionFrame {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ (Matrix.vecCons x (quaternionFrame x)) :=
  orthonormal_vecCons_iff.2 ⟨hx, fun i ↦ by rw [real_inner_comm, inner_quaternionFrame_self],
    orthonormal_quaternionFrame hx⟩

/-- A unit vector `x` followed by two distinct vectors of its quaternionic frame is orthonormal:
any two of `x <• i`, `x <• j`, `x <• k` are two pointwise orthonormal tangent vector fields on the
unit sphere. -/
theorem orthonormal_vecCons_quaternionFrame_of_ne {x : E} (hx : ‖x‖ = 1) {i j : Fin 3}
    (hij : i ≠ j) : Orthonormal ℝ ![x, quaternionFrame x i, quaternionFrame x j] := by
  have hinj : Function.Injective ![0, i.succ, j.succ] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
  convert (orthonormal_vecCons_quaternionFrame hx).comp _ hinj using 1
  ext a
  fin_cases a <;> rfl

/-- Two distinct vectors of the quaternionic frame of a unit vector are orthonormal. -/
theorem orthonormal_quaternionFrame_pair_of_ne {x : E} (hx : ‖x‖ = 1) {i j : Fin 3}
    (hij : i ≠ j) : Orthonormal ℝ ![quaternionFrame x i, quaternionFrame x j] :=
  (orthonormal_vecCons_iff.1 (orthonormal_vecCons_quaternionFrame_of_ne hx hij)).2.2

end TauCeti
