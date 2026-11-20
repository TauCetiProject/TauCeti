/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint

/-!
# Compatibility conditions for Fredholm operators

For a continuous linear map `T : E → F` between Hilbert spaces with closed range, the equation
`T x = y` is solvable exactly when `y` is orthogonal to the kernel of the adjoint `T†`. If
`z₁, …, z_m` is a basis of `ker T†`, the solvability conditions are the `m` equations
`⟪zᵢ, y⟫ = 0`: these compatibility functionals are continuous and linearly independent, and their
number `m` is the dimension of `ker T†`, which is isomorphic to the cokernel of `T`. That no
family of fewer than `dim coker T` linear functionals, continuous or not, has the range of `T` as
its common kernel is the general codimension count of the module
`TauCeti.LinearAlgebra.Dual.Codimension`.

For a Fredholm operator of index zero this gives the **Fredholm alternative** in its quantitative
form: either `T` is bijective, or `T` has a nonzero kernel and `T x = y` is solvable exactly when
`y` satisfies `dim ker T` independent compatibility conditions `⟪zᵢ, y⟫ = 0`, with `zᵢ` running
over a basis of `ker T†`.

## Main results

* `ContinuousLinearMap.mem_range_iff_forall_mem_ker_adjoint_inner_eq_zero`: for closed range,
  `y ∈ range T` exactly when `⟪z, y⟫ = 0` for every `z ∈ ker T†`.
* `ContinuousLinearMap.mem_range_iff_forall_inner_basis_eq_zero` and
  `ContinuousLinearMap.iInf_ker_innerSL_basis_eq_range`: it suffices to test `z` against a basis
  of `ker T†`.
* `LinearIndependent.innerSL`: the functionals `⟪vᵢ, ·⟫` of a linearly independent family are
  linearly independent; in particular so are the compatibility functionals of a basis of
  `ker T†`.
* `ContinuousLinearMap.IsFredholm.bijective_or_exists_basis_of_index_eq_zero`: the Fredholm
  alternative for operators of index zero, with `dim ker T` compatibility conditions.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 2.19 (closed ranges are orthogonal to adjoint kernels) and Theorem 6.6 (the Fredholm
  alternative).
-/

public section

open Module
open scoped InnerProduct InnerProductSpace

/-- The inner-product functionals `⟪vᵢ, ·⟫` of a linearly independent family `vᵢ` are linearly
independent, since `v ↦ ⟪v, ·⟫` is injective and conjugate-linear. Applied to a basis `zᵢ` of
the kernel of the adjoint of a closed-range operator `T`, it shows that the compatibility
functionals `⟪zᵢ, ·⟫` are linearly independent. -/
theorem LinearIndependent.innerSL {𝕜 F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] {v : ι → F} (hv : LinearIndependent 𝕜 v) :
    LinearIndependent 𝕜 fun i ↦ _root_.innerSL 𝕜 (v i) :=
  -- `_root_` is needed because `innerSL` alone would refer to this theorem.
  hv.map_of_surjective_injectiveₛ (starRingEnd 𝕜)
    (_root_.innerSL 𝕜 : F →L⋆[𝕜] StrongDual 𝕜 F).toLinearMap.toAddMonoidHom
    (starRingEnd 𝕜).surjective (fun _ _ ↦ innerSL_inj.mp) fun _ _ ↦ by simp

namespace ContinuousLinearMap

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Compatibility conditions.** For a continuous linear map with closed range, `T x = y` is
solvable exactly when `y` is orthogonal to the kernel of the adjoint. -/
theorem mem_range_iff_forall_mem_ker_adjoint_inner_eq_zero (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F)) {y : F} :
    y ∈ LinearMap.range (T : E →ₗ[𝕜] F) ↔
      ∀ z ∈ LinearMap.ker (T† : F →ₗ[𝕜] E), ⟪z, y⟫_𝕜 = 0 := by
  rw [T.range_eq_orthogonal_ker_adjoint_of_isClosed_range hT, Submodule.mem_orthogonal]

/-- For a continuous linear map with closed range, `T x = y` is solvable exactly when `y` is
orthogonal to every vector of a basis of the kernel of the adjoint. -/
theorem mem_range_iff_forall_inner_basis_eq_zero (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (b : Basis ι 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E))) {y : F} :
    y ∈ LinearMap.range (T : E →ₗ[𝕜] F) ↔ ∀ i, ⟪(b i : F), y⟫_𝕜 = 0 := by
  rw [T.mem_range_iff_forall_mem_ker_adjoint_inner_eq_zero hT]
  refine ⟨fun h i ↦ h _ (b i).2, fun h z hz ↦ ?_⟩
  -- The linear functional `z ↦ ⟪y, z⟫` on `ker T†` vanishes on the basis `b`, hence everywhere.
  have hf : (innerSL 𝕜 y : F →ₗ[𝕜] 𝕜).comp (LinearMap.ker (T† : F →ₗ[𝕜] E)).subtype = 0 :=
    b.ext fun i ↦ by simpa [inner_eq_zero_symm] using h i
  simpa [inner_eq_zero_symm] using LinearMap.congr_fun hf ⟨z, hz⟩

/-- For a continuous linear map with closed range, the range is the common kernel of the
continuous compatibility functionals `⟪zᵢ, ·⟫`, for `zᵢ` running over a basis of the kernel of
the adjoint. -/
theorem iInf_ker_innerSL_basis_eq_range (T : E →L[𝕜] F)
    (hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F))
    (b : Basis ι 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E))) :
    ⨅ i, LinearMap.ker (innerSL 𝕜 (b i : F) : F →ₗ[𝕜] 𝕜) = LinearMap.range (T : E →ₗ[𝕜] F) := by
  ext y
  simp [T.mem_range_iff_forall_inner_basis_eq_zero hT b]

/-- **The Fredholm alternative** for a Fredholm operator `T` of index zero between Hilbert
spaces: either `T` is bijective, or `T` has a nonzero kernel and the kernel of the adjoint has a
basis `zᵢ` indexed by `Fin (dim ker T)` such that `T x = y` is solvable exactly when
`⟪zᵢ, y⟫ = 0` for every `i`. The compatibility functionals `⟪zᵢ, ·⟫` are linearly independent
by `LinearIndependent.innerSL`. -/
theorem IsFredholm.bijective_or_exists_basis_of_index_eq_zero {T : E →L[𝕜] F}
    (hT : T.IsFredholm) (h0 : T.index = 0) :
    Function.Bijective T ∨
      (LinearMap.ker (T : E →ₗ[𝕜] F) ≠ ⊥ ∧
        ∃ b : Basis (Fin (finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)))) 𝕜
            (LinearMap.ker (T† : F →ₗ[𝕜] E)),
          ∀ y, y ∈ LinearMap.range (T : E →ₗ[𝕜] F) ↔ ∀ i, ⟪(b i : F), y⟫_𝕜 = 0) := by
  have := hT.finite_coker
  by_cases hker : LinearMap.ker (T : E →ₗ[𝕜] F) = ⊥
  · exact Or.inl (T.bijective_of_injective_of_index_eq_zero (LinearMap.ker_eq_bot.mp hker) h0)
  refine Or.inr ⟨hker, ?_⟩
  -- Index zero and `coker T ≃ ker T†` give `dim ker T† = dim ker T`.
  have e := (T.cokerEquivKerAdjoint hT.isClosed_range).toLinearEquiv
  have := e.finiteDimensional
  have hdim : finrank 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E)) =
      finrank 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F)) := by
    have := T.index_eq_finrank_sub
    rw [← e.finrank_eq]
    omega
  let b := (finBasis 𝕜 (LinearMap.ker (T† : F →ₗ[𝕜] E))).reindex (finCongr hdim)
  exact ⟨b, fun y ↦ T.mem_range_iff_forall_inner_basis_eq_zero hT.isClosed_range b⟩

end ContinuousLinearMap
