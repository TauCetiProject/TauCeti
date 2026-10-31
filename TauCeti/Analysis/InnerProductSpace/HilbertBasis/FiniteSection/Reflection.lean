/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Basic
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Data.Fin.Rev
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Reflections of finite Hilbert sections

The finite reflection reverses the first `n + 1` coordinates of a countable Hilbert basis
and vanishes on the remaining coordinates. It is a self-adjoint contraction whose square
is the finite-coordinate projection. Finite reflections converge weakly to zero, while the
norms of reflected vectors converge to their original norms. These operators describe the
second boundary of finite Toeplitz sections.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  for the reflection operators in the finite-section method.
-/

public section

open scoped InnerProductSpace Topology
open Filter

namespace HilbertBasis

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Reverse the first `n + 1` Hilbert coordinates, with zero on the remaining coordinates. -/
noncomputable def finiteReflection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) : H →L[𝕜] H :=
  (b.finiteInclusion n).toContinuousLinearMap ∘L
    (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 (Fin.revPerm (n := n + 1)) :
      EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))
      ∘L b.coordinateCutoff n

/-- The reflected vector is the reversed finite Hilbert expansion. -/
theorem finiteReflection_apply (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H) :
    b.finiteReflection n x = ∑ i : Fin (n + 1), b.repr x i.rev • b i := by
  simp [finiteReflection, finiteInclusion_apply, Equiv.piCongrLeft']

/-- Coordinates inside the finite section are reversed; all other coordinates vanish. -/
@[simp]
theorem repr_finiteReflection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H) (i : ℕ) :
    b.repr (b.finiteReflection n x) i = if i < n + 1 then b.repr x (n - i) else 0 := by
  rw [b.repr_apply_apply, finiteReflection_apply]
  simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  simp only [Fin.rev, Fin.val_mk, Nat.add_sub_add_right, mul_ite, mul_one, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ if i = j then b.repr x (n - j) else 0)]
  simp [Finset.mem_range]

/-- Reflection sends an included basis vector to the basis vector at the reversed index. -/
@[simp]
theorem finiteReflection_basis (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (i : Fin (n + 1)) :
    b.finiteReflection n (b i) = b i.rev := by
  have hcut := b.coordinateCutoff_finiteInclusion n (PiLp.single 2 i (1 : 𝕜))
  rw [finiteInclusion_single] at hcut
  simp only [finiteReflection, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, hcut,
    LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.piLpCongrLeft_single,
    Fin.revPerm_apply, finiteInclusion_single]

/-- A finite reflection is self-adjoint. -/
@[simp]
theorem adjoint_finiteReflection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    (b.finiteReflection n).adjoint = b.finiteReflection n := by
  have h := congrArg ContinuousLinearMap.adjoint (b.adjoint_coordinateCutoff n)
  simp only [ContinuousLinearMap.adjoint_adjoint] at h
  simp [finiteReflection, ContinuousLinearMap.adjoint_comp, ← h,
    LinearIsometryEquiv.adjoint_eq_symm, ContinuousLinearMap.comp_assoc]

/-- Reflecting twice is the finite-coordinate projection. -/
@[simp]
theorem finiteReflection_comp_self (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    b.finiteReflection n ∘L b.finiteReflection n = b.finiteProjection n := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext i
  simp only [ContinuousLinearMap.comp_apply, repr_finiteReflection, repr_finiteProjection]
  by_cases hi : i < n + 1
  · have hj : n - i < n + 1 := by omega
    have hsub : n - (n - i) = i := Nat.sub_sub_self (by omega)
    simp only [ite_eq_left hi, ite_eq_left hj, hsub]
  · simp [hi]

/-- Reflection already lies in the finite-coordinate range. -/
@[simp]
theorem finiteProjection_comp_finiteReflection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    b.finiteProjection n ∘L b.finiteReflection n = b.finiteReflection n := by
  ext x
  apply b.repr.injective
  ext i
  simp only [ContinuousLinearMap.comp_apply, repr_finiteProjection, repr_finiteReflection]
  split_ifs <;> rfl

/-- Reflection ignores all coordinates outside the finite section. -/
@[simp]
theorem finiteReflection_comp_finiteProjection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    b.finiteReflection n ∘L b.finiteProjection n = b.finiteReflection n := by
  have h := congrArg ContinuousLinearMap.adjoint (b.finiteProjection_comp_finiteReflection n)
  simpa only [ContinuousLinearMap.adjoint_comp, adjoint_finiteReflection,
    adjoint_finiteProjection] using h

/-- The norm of a reflected vector is the norm of its finite-coordinate projection. -/
theorem norm_finiteReflection_apply (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) (x : H) :
    ‖b.finiteReflection n x‖ = ‖b.finiteProjection n x‖ := by
  rw [← finiteInclusion_coordinateCutoff]
  simp only [finiteReflection, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
    LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.norm_map]

/-- Finite reflections are contractions, uniformly in the section size. -/
theorem norm_finiteReflection_le (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖b.finiteReflection n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  rw [norm_finiteReflection_apply, one_mul]
  simpa using (b.finiteProjection n).le_of_opNorm_le (b.norm_finiteProjection_le n) x

/-- Every finite reflection has operator norm exactly one. -/
@[simp]
theorem norm_finiteReflection (b : HilbertBasis ℕ 𝕜 H) (n : ℕ) :
    ‖b.finiteReflection n‖ = 1 := by
  apply le_antisymm (b.norm_finiteReflection_le n)
  have h := (b.finiteReflection n).le_opNorm (b (0 : Fin (n + 1)))
  simpa only [finiteReflection_basis, b.orthonormal.norm_eq_one, mul_one] using h

/-- Reflected vectors asymptotically retain the full norm, despite weak convergence to zero. -/
theorem tendsto_norm_finiteReflection_apply (b : HilbertBasis ℕ 𝕜 H) (x : H) :
    Tendsto (fun n ↦ ‖b.finiteReflection n x‖) atTop (𝓝 ‖x‖) := by
  simpa only [norm_finiteReflection_apply] using (b.tendsto_finiteProjection x).norm

/-- Every fixed inner-product test of the finite reflections tends to zero. -/
theorem tendsto_inner_finiteReflection (b : HilbertBasis ℕ 𝕜 H) (x y : H) :
    Tendsto (fun n ↦ ⟪y, b.finiteReflection n x⟫_𝕜) atTop (𝓝 0) := by
  have hnorm (n : ℕ) : ‖b.finiteReflection n x‖ ≤ ‖x‖ := by
    simpa using (b.finiteReflection n).le_of_opNorm_le (b.norm_finiteReflection_le n) x
  have hcoeff : Tendsto (fun i ↦ b.repr x i) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [norm_smul, b.orthonormal.norm_eq_one] using
      (b.hasSum_repr x).summable.tendsto_atTop_zero.norm
  have htest (i : ℕ) :
      Tendsto (fun n ↦ ⟪b.finiteReflection n x, b i⟫_𝕜) atTop (𝓝 0) := by
    have h := (hcoeff.comp (tendsto_sub_atTop_nat i)).star
    rw [star_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop i] with n hn
    rw [← inner_conj_symm, ← b.repr_apply_apply, repr_finiteReflection]
    simp [Nat.lt_succ_of_le hn, RCLike.star_def]
  -- The uniform norm bound makes convergence of the inner-product tests a closed condition.
  have hequi : Equicontinuous (fun n (z : H) ↦ ⟪b.finiteReflection n x, z⟫_𝕜) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ ‖x‖₊
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, ← inner_sub_right, dist_eq_norm]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hnorm n) (norm_nonneg _))
  have hclosed := hequi.isClosed_setOfPred_tendsto (l := atTop)
    (f := fun _ : H ↦ (0 : 𝕜)) continuous_const
  have hy : Tendsto (fun n ↦ ⟪b.finiteReflection n x, y⟫_𝕜) atTop (𝓝 0) := by
    apply hclosed.mem_of_tendsto (b.tendsto_finiteProjection y)
    apply Eventually.of_forall
    intro m
    simp only [Set.mem_ofPred_eq, finiteProjection_apply, inner_sum, inner_smul_right]
    simpa using tendsto_finsetSum Finset.univ
      (fun (i : Fin (m + 1)) _ ↦ (htest i).const_mul (b.repr y i))
  simpa only [RCLike.star_def, inner_conj_symm, star_zero] using hy.star

/-- Finite reflections converge to zero in the weak operator topology. -/
theorem tendsto_finiteReflection_wot (b : HilbertBasis ℕ 𝕜 H) :
    Tendsto (fun n ↦ ContinuousLinearMapWOT.ofCLM (b.finiteReflection n)) atTop (𝓝 0) := by
  apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
  intro x y
  simpa using b.tendsto_inner_finiteReflection x y

end HilbertBasis
