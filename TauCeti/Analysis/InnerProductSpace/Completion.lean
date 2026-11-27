/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Adjoints of operators extended to completions

A bounded operator `f : E →L[𝕜] F` between inner product spaces that need not be complete extends
to the bounded operator `f.completion` between the Hilbert space completions. Even when `f` has no
adjoint, because `E` or `F` is not complete, it may have a *formal adjoint*: an operator
`g : F →L[𝕜] E` with `⟪f x, y⟫ = ⟪x, g y⟫` for all `x` and `y`. The extension of `g` is then the
Hilbert space adjoint of the extension of `f` (`ContinuousLinearMap.adjoint_completion`), because
both sides of the defining identity are continuous and the spaces are dense in their completions.

This computes adjoints of operators on completed tensor products of Hilbert spaces, where the
algebraic tensor product is not complete. For the same reason, the norm of an operator between
completions is bounded by its matrix coefficients between vectors of the uncompleted spaces
(`ContinuousLinearMap.opNorm_le_of_forall_inner_coe_le`).
-/

public section

open UniformSpace
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- If `g` is a formal adjoint of `f`, `⟪f x, y⟫ = ⟪x, g y⟫`, then the extension of `g` to the
completions is the adjoint of the extension of `f`. -/
theorem adjoint_completion {f : E →L[𝕜] F} {g : F →L[𝕜] E}
    (h : ∀ x y, ⟪f x, y⟫_𝕜 = ⟪x, g y⟫_𝕜) : adjoint f.completion = g.completion := by
  refine ((eq_adjoint_iff g.completion f.completion).2 fun y x ↦ ?_).symm
  induction y, x using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih y x =>
    simp only [completion_apply_coe, Completion.inner_coe]
    simpa only [inner_conj_symm] using (congrArg (starRingEnd 𝕜) (h x y)).symm

/-- For a submodule `M` of finite codimension in a seminormed inner product space `E` over `ℝ` or
`ℂ`, the orthogonal complement in `Completion E` of the image of `M` has dimension at most the
codimension `Module.rank 𝕜 (E ⧸ M)`: the orthogonal projection onto `M₀ᗮ` vanishes on `M` and so
descends to a linear map out of `E ⧸ M` with dense, finite-dimensional, hence closed range. -/
theorem rank_orthogonal_map_toComplL_le (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 (E ⧸ M)] :
    Module.rank 𝕜 (M.map (Completion.toComplL : E →L[𝕜] Completion E).toLinearMap)ᗮ ≤
      Module.rank 𝕜 (E ⧸ M) := by
  let j : E →L[𝕜] Completion E := Completion.toComplL
  let M₀ : Submodule 𝕜 (Completion E) := M.map j.toLinearMap
  let φ : E →L[𝕜] M₀ᗮ := M₀ᗮ.orthogonalProjectionOnto ∘L j
  have hker : M ≤ LinearMap.ker φ.toLinearMap := fun x hx ↦
    LinearMap.mem_ker.mpr <| M₀.orthogonalProjectionOnto_orthogonal_apply_eq_zero
      (Submodule.mem_map_of_mem hx)
  let ψ : (E ⧸ M) →ₗ[𝕜] M₀ᗮ := M.liftQ φ.toLinearMap hker
  have hrange : LinearMap.range φ.toLinearMap = LinearMap.range ψ := by
    rw [← M.liftQ_mkQ φ.toLinearMap hker, LinearMap.range_comp_of_range_eq_top _ M.range_mkQ]
  have : FiniteDimensional 𝕜 (LinearMap.range φ.toLinearMap) :=
    hrange ▸ LinearMap.finiteDimensional_range ψ
  have hsurj : Function.Surjective M₀ᗮ.orthogonalProjectionOnto :=
    fun y ↦ ⟨y, M₀ᗮ.orthogonalProjectionOnto_mem_subspace_eq_self y⟩
  have hdense : DenseRange φ :=
    hsurj.denseRange.comp Completion.denseRange_coe M₀ᗮ.orthogonalProjectionOnto.continuous
  have htop : LinearMap.range ψ = ⊤ := by
    rw [← hrange]
    exact SetLike.coe_injective <|
      (LinearMap.range φ.toLinearMap).isClosed_of_finiteDimensional.closure_eq.symm.trans
        hdense.closure_range
  exact LinearMap.rank_le_of_surjective ψ (LinearMap.range_eq_top.mp htop)

/-- An operator `T` between the completions of inner product spaces `E` and `F` with
`‖⟪y, T x⟫‖ ≤ C ‖y‖ ‖x‖` for all `y ∈ F` and `x ∈ E` has norm at most `C`. -/
theorem opNorm_le_of_forall_inner_coe_le (T : Completion E →L[𝕜] Completion F) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ (y : F) (x : E), ‖⟪(y : Completion F), T x⟫_𝕜‖ ≤ C * ‖y‖ * ‖x‖) :
    ‖T‖ ≤ C := by
  have h' (v : Completion F) (u : Completion E) : ‖⟪v, T u⟫_𝕜‖ ≤ C * ‖v‖ * ‖u‖ := by
    induction v, u using Completion.induction_on₂ with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih y x => simpa only [Completion.norm_coe] using h y x
  refine opNorm_le_of_re_inner_le hC fun u v hu hv ↦ ?_
  calc RCLike.re ⟪T u, v⟫_𝕜 ≤ ‖⟪T u, v⟫_𝕜‖ := RCLike.re_le_norm _
    _ = ‖⟪v, T u⟫_𝕜‖ := norm_inner_symm _ _
    _ ≤ C := by simpa [hu, hv] using h' v u

end ContinuousLinearMap
