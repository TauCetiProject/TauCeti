/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Frame.Basic

/-!
# Rank-one projections and orthonormal bases

A finite family of rank-one orthogonal projections comes from an orthonormal basis exactly when
the projections sum to the identity. This identifies the decompositions of the identity into
rank-one projections that can be used to express the basis-sum condition for frame functions.
The converse uses `TauCeti.re_inner_frameOperator_apply_self` to recover orthogonality.

For the frame-function condition, see A. M. Gleason,
*Measures on the Closed Subspaces of a Hilbert Space*, 1957, §1.
-/

public section

namespace TauCeti

open InnerProductSpace
open scoped InnerProductSpace

/-- A finite family consists of the projections onto the lines of an orthonormal basis exactly
when each term is the rank-one projection of a unit vector and the terms sum to the identity. -/
theorem exists_orthonormalBasis_eq_rankOne_iff
    {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Fintype ι] {p : ι → E →L[𝕜] E} :
    (∃ b : OrthonormalBasis ι 𝕜 E, ∀ i, p i = rankOne 𝕜 (b i) (b i)) ↔
      (∀ i, ∃ v : E, ‖v‖ = 1 ∧ p i = rankOne 𝕜 v v) ∧ (∑ i, p i = 1) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨fun i ↦ ⟨b i, b.norm_eq_one i, hb i⟩,
      (Finset.sum_congr rfl fun i _ ↦ hb i).trans b.sum_rankOne_eq_id⟩
  · rintro ⟨hunit, hsum⟩
    classical
    choose v hv hp using hunit
    have hframe : frameOperator 𝕜 v = LinearMap.id := by
      ext x
      simpa only [frameOperator_apply, LinearMap.id_apply, sum_apply, rankOne_apply,
        one_apply_eq_self, hp] using DFunLike.congr_fun hsum x
    have hon : Orthonormal 𝕜 v := by
      refine ⟨hv, fun i j hij ↦ ?_⟩
      -- In the sum of squared inner products with `v j`, the diagonal term is already one.
      have hsq := (re_inner_frameOperator_apply_self (𝕜 := 𝕜) v (v j)).symm
      rw [hframe, LinearMap.id_apply, inner_self_eq_norm_sq, hv j, one_pow] at hsq
      have hdiag : ‖⟪v j, v j⟫_𝕜‖ ^ 2 = 1 := by
        rw [inner_self_eq_one_of_norm_eq_one (hv j), norm_one, one_pow]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hdiag, add_eq_right] at hsq
      have hi := (Finset.sum_sq_eq_zero_iff _ _).mp hsq i
        (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
      exact norm_eq_zero.mp hi
    have hspan : ⊤ ≤ Submodule.span 𝕜 (Set.range v) := by
      intro x _
      apply (Submodule.mem_span_range_iff_exists_fun 𝕜).mpr
      refine ⟨fun i ↦ ⟪v i, x⟫_𝕜, ?_⟩
      simpa only [frameOperator_apply, LinearMap.id_apply] using DFunLike.congr_fun hframe x
    refine ⟨OrthonormalBasis.mk hon hspan, fun i ↦ ?_⟩
    simpa only [OrthonormalBasis.coe_mk] using hp i

end TauCeti
