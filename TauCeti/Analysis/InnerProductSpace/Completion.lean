/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal complements in completions of inner product spaces

For a submodule `M` of finite codimension in a seminormed inner product space `E` over `ℝ` or `ℂ`,
mapping `M` into `UniformSpace.Completion E` along `UniformSpace.Completion.toComplL` produces a
subspace whose orthogonal complement has dimension at most the codimension `Module.rank 𝕜 (E ⧸ M)`
(`Submodule.rank_orthogonal_map_toComplL_le`).

Indeed, let `M₀` be the image of `M` in `Completion E`. The orthogonal projection of `Completion E`
onto `M₀ᗮ` vanishes on `M₀`, so precomposing it with `toComplL` kills `M` and descends to a linear
map `(E ⧸ M) →ₗ[𝕜] M₀ᗮ`. Because `E` is dense in `Completion E` and the orthogonal projection onto
`M₀ᗮ` is surjective, this induced map has dense range; since `E ⧸ M` is finite-dimensional, its
range is also finite-dimensional and therefore closed, so the induced map is surjective.

Both the finite-codimension assumption and the direction of the inequality are sharp:
* Finite codimension is essential: if `E` is the dense subspace of finitely supported sequences in
  `ℓ²(ℕ, 𝕜)` and `M = ⊥`, then `Module.rank 𝕜 (E ⧸ ⊥) = ℵ₀`, whereas `(⊥.map toComplL)ᗮ = ⊤` in
  `Completion E ≃ₗᵢ[𝕜] ℓ²(ℕ, 𝕜)` has uncountable `𝕜`-dimension by the Baire category theorem.
* Strict inequality can occur when `M` is not closed: the kernel `M` of a discontinuous nonzero
  linear functional on `E` has codimension `1` yet is dense in `E`, so `M₀` is dense in
  `Completion E` and `M₀ᗮ = ⊥` has rank `0`.

## Main declarations

* `Submodule.rank_orthogonal_map_toComplL_le`: for `M : Submodule 𝕜 E` with
  `[FiniteDimensional 𝕜 (E ⧸ M)]`,
  `Module.rank 𝕜 (M.map (Completion.toComplL : E →L[𝕜] Completion E).toLinearMap)ᗮ ≤
    Module.rank 𝕜 (E ⧸ M)`.
-/

public section

open UniformSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

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

end Submodule
