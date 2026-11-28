/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.Analysis.InnerProductSpace.NearIsometry.SecondMoment
public import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.PosSemidef.Basic

/-!
# Positive type of compression energies

For a norm-preserving representation `ρ` and a linear map `B` to its representation space,
`g ↦ ‖B† ρ(g) B‖²` is of positive type. Its Gram vectors are the translates of `B B†`, read in
the Frobenius inner product. The energy at the identity bounds the energy at every group element.

This is the positive-type input for the whole-group second-moment estimate in
`New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sq_le` in
`New/Spanning/Unfolding/Moments.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead1/grh).
The Gram identity used here is `TauCeti.trace_adjoint_comp_eq_sq_frobenius_adjoint_comp_comp`.
-/

public section

open Module LinearMap TauCeti.UnitarilyInvariantSeminorm
open scoped ComplexOrder InnerProductSpace Matrix.Norms.Frobenius

namespace TauCeti

variable {𝕜 S T G : Type*} [RCLike 𝕜] [NormedAddCommGroup S] [InnerProductSpace 𝕜 S]
  [FiniteDimensional 𝕜 S] [NormedAddCommGroup T] [InnerProductSpace 𝕜 T] [FiniteDimensional 𝕜 T]
  [Group G] {ρ : Representation 𝕜 G T}

/-- The squared Frobenius norm of `B† ρ(g) B` is of positive type: its value at `a⁻¹ * b`
is the inner product of two vectors depending separately on `a` and `b`. The group need
not be finite. -/
theorem exists_inner_eq_sq_frobenius_compression (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (B : S →ₗ[𝕜] T) :
    ∃ u : G → Matrix (Fin (finrank 𝕜 T)) (Fin (finrank 𝕜 T)) 𝕜,
      ∀ a b, ⟪u a, u b⟫_𝕜 = (↑(frobenius 𝕜 S S (B.adjoint ∘ₗ ρ (a⁻¹ * b) ∘ₗ B) ^ 2) : 𝕜) := by
  let e := stdOrthonormalBasis 𝕜 T
  let X (a : G) : T →ₗ[𝕜] T := (ρ a ∘ₗ B) ∘ₗ (ρ a ∘ₗ B).adjoint
  refine ⟨fun a ↦ toMatrix e.toBasis e.toBasis (X a), fun a b ↦ ?_⟩
  rw [Matrix.frobenius_inner_eq_trace_conjTranspose_mul, ← toMatrix_adjoint e e,
    ← toMatrix_comp, ← trace_eq_matrix_trace 𝕜 e.toBasis]
  exact trace_adjoint_comp_eq_sq_frobenius_adjoint_comp_comp hρ B a b

/-- The kernel of squared Frobenius norms of compressions is positive semidefinite.
No finiteness assumption on the group is needed. -/
theorem posSemidef_sq_frobenius_compression (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (B : S →ₗ[𝕜] T) :
    (Matrix.of fun a b ↦
      (↑(frobenius 𝕜 S S (B.adjoint ∘ₗ ρ (a⁻¹ * b) ∘ₗ B) ^ 2) : 𝕜)).PosSemidef := by
  obtain ⟨u, hu⟩ := exists_inner_eq_sq_frobenius_compression hρ B
  convert Matrix.posSemidef_gram 𝕜 u using 1
  ext a b
  simp only [Matrix.of_apply, Matrix.gram_apply, hu]

/-- A compression by a norm-preserving group action has squared Frobenius norm at most that
of the compression at the identity. -/
theorem sq_frobenius_compression_le (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (B : S →ₗ[𝕜] T) (g : G) :
    frobenius 𝕜 S S (B.adjoint ∘ₗ ρ g ∘ₗ B) ^ 2 ≤ frobenius 𝕜 S S (B.adjoint ∘ₗ B) ^ 2 := by
  have h := (posSemidef_sq_frobenius_compression hρ B).norm_le_of_norm_apply_self_le
    (C := frobenius 𝕜 S S (B.adjoint ∘ₗ B) ^ 2) (fun a ↦ by
      simp only [Matrix.of_apply, inv_mul_cancel, map_one, Module.End.one_eq_id, id_comp,
        RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg (_ : ℝ)), le_refl]) 1 g
  simpa only [Matrix.of_apply, inv_one, one_mul, RCLike.norm_ofReal,
    abs_of_nonneg (sq_nonneg (_ : ℝ))] using h

end TauCeti
