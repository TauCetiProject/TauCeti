/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Map
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Monotone renorming of a Schauder basis

The norm `x ↦ sup n, ‖b.proj n x‖` is equivalent to the original norm of a Banach
space with Schauder basis `b`. In this norm the initial basis projections are
contractions, so the norms of the initial partial sums of each expansion increase
monotonically to the norm of its sum.

`SchauderBasis.MonotoneRenorm` carries this norm, and `monotoneRenormEquiv` identifies
it with the original space by a bounded linear equivalence. The transported basis
`monotoneBasis` retains the original coordinates and conditional summation filter.
The norm comparison loses at most the original basis constant.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (b : SchauderBasis 𝕜 E)
  [CompleteSpace E]

private def projectionSequence (x : E) : ℕ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun n ↦ b.proj n x)
    continuous_of_discreteTopology (b.nnnormProjBound * ‖x‖)
    (fun n ↦ ((b.proj n).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (b.norm_proj_le_nnnormProjBound n) (norm_nonneg x)))

private def projectionSequenceLinearMap : E →ₗ[𝕜] (ℕ →ᵇ E) where
  toFun := b.projectionSequence
  map_add' x y := by ext n; exact (b.proj n).map_add x y
  map_smul' c x := by ext n; exact (b.proj n).map_smul c x

/-- Send a vector to the bounded sequence of its initial basis projections. -/
def partialSums : E →L[𝕜] (ℕ →ᵇ E) :=
  b.projectionSequenceLinearMap.mkContinuous b.nnnormProjBound fun x ↦
    (BoundedContinuousFunction.norm_le (by positivity)).2 fun n ↦
      ((b.proj n).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (b.norm_proj_le_nnnormProjBound n) (norm_nonneg x))

@[simp]
theorem partialSums_apply (x : E) (n : ℕ) : b.partialSums x n = b.proj n x := (rfl)

/-- The partial-sum embedding is injective. -/
theorem partialSums_injective : Function.Injective b.partialSums := by
  intro x y h
  have hp : ∀ n, b.proj n x = b.proj n y := fun n ↦ DFunLike.congr_fun h n
  exact tendsto_nhds_unique (b.tendsto_proj x)
    ((b.tendsto_proj y).congr fun n ↦ (hp n).symm)

/-- The partial-sum embedding dominates the original norm. -/
theorem norm_le_norm_partialSums (x : E) : ‖x‖ ≤ ‖b.partialSums x‖ := by
  apply le_of_tendsto (b.tendsto_proj x).norm
  exact Eventually.of_forall fun n ↦ (b.partialSums x).norm_coe_le_norm n

/-- The partial-sum embedding is bounded by the basis constant. -/
theorem norm_partialSums_le (x : E) :
    ‖b.partialSums x‖ ≤ b.nnnormProjBound * ‖x‖ := by
  exact (BoundedContinuousFunction.norm_le (by positivity)).2 fun n ↦
    ((b.proj n).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (b.norm_proj_le_nnnormProjBound n) (norm_nonneg x))

/-- The partial-sum embedding preserves the norms of the individual basis vectors. -/
@[simp]
theorem norm_partialSums_basis (i : ℕ) : ‖b.partialSums (b i)‖ = ‖b i‖ := by
  apply le_antisymm _ (b.norm_le_norm_partialSums (b i))
  apply (BoundedContinuousFunction.norm_le (norm_nonneg (b i))).2
  intro n
  rw [b.partialSums_apply, b.proj_apply_basis_mem]
  split_ifs <;> simp

/-- The monotone renorming, realized as the range of the partial-sum embedding with
the inherited supremum norm. -/
abbrev MonotoneRenorm := LinearMap.range b.partialSums.toLinearMap

private def renormLinearEquiv : E ≃ₗ[𝕜] b.MonotoneRenorm :=
  LinearEquiv.ofInjective b.partialSums.toLinearMap b.partialSums_injective

private theorem norm_renormLinearEquiv (x : E) :
    ‖b.renormLinearEquiv x‖ = ‖b.partialSums x‖ := (rfl)

/-- The canonical bounded linear equivalence from the original space to its monotone
renorming, sending each vector to its sequence of partial sums. Its norm is at most
the basis constant and its inverse is contractive. -/
def monotoneRenormEquiv : E ≃L[𝕜] b.MonotoneRenorm :=
  b.renormLinearEquiv.toContinuousLinearEquivOfBounds b.nnnormProjBound 1
    (fun x ↦ (b.norm_renormLinearEquiv x).trans_le (b.norm_partialSums_le x))
    (fun x ↦ by
      simpa only [one_mul, ← b.norm_renormLinearEquiv,
        LinearEquiv.apply_symm_apply] using
        b.norm_le_norm_partialSums (b.renormLinearEquiv.symm x))

/-- The renorming equivalence sends a vector to its sequence of partial sums. -/
@[simp]
theorem monotoneRenormEquiv_apply (x : E) :
    (b.monotoneRenormEquiv x : ℕ →ᵇ E) = b.partialSums x := (rfl)

/-- Reading a renormed vector in the original space recovers its partial sums. -/
@[simp]
theorem partialSums_monotoneRenormEquiv_symm (x : b.MonotoneRenorm) :
    b.partialSums (b.monotoneRenormEquiv.symm x) = (x : ℕ →ᵇ E) := by
  rw [← b.monotoneRenormEquiv_apply, b.monotoneRenormEquiv.apply_symm_apply]

/-- The renormed norm is the supremum of the original norms of the partial sums. -/
theorem norm_monotoneRenormEquiv (x : E) :
    ‖b.monotoneRenormEquiv x‖ = ⨆ n, ‖b.proj n x‖ := by
  rw [← Submodule.norm_coe, b.monotoneRenormEquiv_apply,
    BoundedContinuousFunction.norm_eq_iSup_norm]
  simp only [partialSums_apply]

/-- A bound for the renormed norm is exactly a common bound for the original partial sums. -/
theorem norm_monotoneRenormEquiv_le_iff (x : E) {C : ℝ} :
    ‖b.monotoneRenormEquiv x‖ ≤ C ↔ ∀ n, ‖b.proj n x‖ ≤ C := by
  rw [← Submodule.norm_coe, b.monotoneRenormEquiv_apply,
    BoundedContinuousFunction.norm_le_of_nonempty]
  simp only [partialSums_apply]

/-- The monotone renorming dominates the original norm. -/
theorem norm_le_norm_monotoneRenormEquiv (x : E) :
    ‖x‖ ≤ ‖b.monotoneRenormEquiv x‖ := by
  simpa only [← Submodule.norm_coe, b.monotoneRenormEquiv_apply] using
    b.norm_le_norm_partialSums x

/-- The monotone renorming is bounded by the basis constant times the original norm. -/
theorem norm_monotoneRenormEquiv_le (x : E) :
    ‖b.monotoneRenormEquiv x‖ ≤ b.nnnormProjBound * ‖x‖ := by
  simpa only [← Submodule.norm_coe, b.monotoneRenormEquiv_apply] using
    b.norm_partialSums_le x

/-- The equivalent monotone norm is complete. -/
instance : CompleteSpace b.MonotoneRenorm := by
  let e : E ≃ᵤ b.MonotoneRenorm :=
    { b.monotoneRenormEquiv.toEquiv with
      uniformContinuous_toFun := b.monotoneRenormEquiv.toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun :=
        b.monotoneRenormEquiv.symm.toContinuousLinearMap.uniformContinuous }
  exact e.completeSpace_iff.mp inferInstance

/-- The original basis, transported to the equivalent monotone norm. -/
def monotoneBasis : SchauderBasis 𝕜 b.MonotoneRenorm := b.map b.monotoneRenormEquiv

@[simp]
theorem monotoneBasis_apply (i : ℕ) :
    b.monotoneBasis i = b.monotoneRenormEquiv (b i) :=
  b.map_apply b.monotoneRenormEquiv i

@[simp]
theorem monotoneBasis_coord_apply (i : ℕ) (x : b.MonotoneRenorm) :
    b.monotoneBasis.coord i x = b.coord i (b.monotoneRenormEquiv.symm x) :=
  b.map_coord_apply b.monotoneRenormEquiv i x

/-- The transported partial sums are the original partial sums read in the new norm. -/
theorem monotoneBasis_proj_apply (n : ℕ) (x : b.MonotoneRenorm) :
    b.monotoneBasis.proj n x =
      b.monotoneRenormEquiv (b.proj n (b.monotoneRenormEquiv.symm x)) :=
  b.map_proj_apply b.monotoneRenormEquiv (Finset.range n) x

/-- Every initial projection is contractive in the monotone norm. -/
theorem norm_monotoneBasis_proj_apply_le (n : ℕ) (x : b.MonotoneRenorm) :
    ‖b.monotoneBasis.proj n x‖ ≤ ‖x‖ := by
  rw [b.monotoneBasis_proj_apply,
    b.norm_monotoneRenormEquiv_le_iff]
  intro m
  rw [b.proj_comp]
  have h := (b.norm_monotoneRenormEquiv_le_iff
    (b.monotoneRenormEquiv.symm x)).1 le_rfl (min m n)
  simpa using h

/-- The initial projection operators of the renormed basis have norm at most one. -/
theorem norm_monotoneBasis_proj_le (n : ℕ) : ‖b.monotoneBasis.proj n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    simpa using b.norm_monotoneBasis_proj_apply_le n x

/-- In the equivalent norm, norms of initial partial sums are monotone. -/
theorem monotone_norm_monotoneBasis_proj (x : b.MonotoneRenorm) :
    Monotone (fun n ↦ ‖b.monotoneBasis.proj n x‖) := by
  intro n m hnm
  have h := b.norm_monotoneBasis_proj_apply_le n (b.monotoneBasis.proj m x)
  simpa only [b.monotoneBasis.proj_comp, min_eq_left hnm] using h

end SchauderBasis
