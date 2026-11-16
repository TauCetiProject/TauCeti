/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Normed.Module.Dual.Adjoint
public import TauCeti.LinearAlgebra.Determinant.Dual
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# The transpose of a Fredholm operator

The transpose of a continuous linear map `T : E →L[𝕜] F` is precomposition with `T` on continuous
functionals, `T' = ContinuousLinearMap.precomp 𝕜 T : F' →L[𝕜] E'`, `φ ↦ φ ∘ T`, where
`E' = StrongDual 𝕜 E` and `F' = StrongDual 𝕜 F`. This file shows that for a Fredholm operator the
continuous duals see the same kernel and cokernel as the full algebraic duals. The algebraic dual
map `T^*` of `Module.Dual` restricts to `T'` on continuous functionals, and:

* every functional vanishing on the closed, finite-codimensional range of `T` is continuous, so
  the kernels of `T'` and `T^*` agree (`ContinuousLinearMap.kerPrecompEquivKerDualMap`), and both
  are the dual of the cokernel of `T`;
* a continuous functional vanishes on `ker T` exactly when it is of the form `ψ ∘ T` with `ψ`
  continuous (`ContinuousLinearMap.IsFredholm.range_precomp_eq_orthogonalBilin_ker`), the closed
  range theorem for Fredholm operators between arbitrary topological vector spaces; and every
  functional on the finite-dimensional `ker T` extends continuously along a closed complement.
  Hence the cokernels of `T'` and `T^*` agree
  (`ContinuousLinearMap.cokerPrecompEquivCokerDualMap`), and both are the dual of the kernel of
  `T`.

Consequently `T'` has index `-index T`, and between normed spaces over `ℝ` or `ℂ` it is again a
Fredholm operator. Its determinant line is identified with that of `T`
(`ContinuousLinearMap.detLinePrecompEquiv`) through the corresponding isomorphism
`LinearMap.detLineDualMapEquiv` for the algebraic dual map. On real Hilbert spaces the Riesz
isomorphisms carry the transpose to the Hilbert adjoint, which identifies the determinant line of
the adjoint `T†` with that of `T` as well (`ContinuousLinearMap.detLineAdjointEquiv`), using the
commuting square `ContinuousLinearMap.precomp_comp_toDual`.

## Main declarations

* `ContinuousLinearMap.IsFredholm.range_precomp_eq_orthogonalBilin_ker`: for Fredholm `T`, the
  range of the transpose is the annihilator of `ker T`.
* `ContinuousLinearMap.cokerPrecompEquivCokerDualMap`: the cokernel of the transpose agrees with
  that of the algebraic dual map. The kernel comparison
  `ContinuousLinearMap.kerPrecompEquivKerDualMap` needs only closed range of finite codimension and
  lives in `TauCeti.Analysis.Normed.Module.Dual.Adjoint`.
* `ContinuousLinearMap.index_precomp`: the transpose negates the index.
* `ContinuousLinearMap.IsFredholm.precomp`: the transpose of a Fredholm operator between normed
  spaces is Fredholm.
* `ContinuousLinearMap.detLinePrecompEquiv`: the isomorphism `det T' ≃ det T`.
* `ContinuousLinearMap.detLineAdjointEquiv`: the isomorphism `det T† ≃ det T` on real Hilbert
  spaces.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Theorem 2.19 (the closed range theorem).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. **118** (2016), 203–268, arXiv:1304.6368 (dualization of
  determinant lines).
-/

public section

noncomputable section

open Module TensorProduct

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

section Cokernel

variable [CompleteSpace 𝕜] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] {T : E →L[𝕜] F}

omit [ContinuousSMul 𝕜 E] in
/-- **The closed range theorem for Fredholm operators.** The range of the transpose of a Fredholm
operator `T` is the annihilator of `ker T`: a continuous functional on `E` is of the form `ψ ∘ T`
for a continuous functional `ψ` on `F` exactly when it vanishes on `ker T`. Unlike the closed
range theorem `ContinuousLinearMap.range_precomp_eq_orthogonalBilin_ker` for Banach spaces, this
holds between arbitrary topological vector spaces. -/
theorem IsFredholm.range_precomp_eq_orthogonalBilin_ker (hT : IsFredholm T) :
    (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range =
      T.ker.orthogonalBilin (topDualPairing 𝕜 E).flip := by
  refine le_antisymm T.range_precomp_le_orthogonalBilin_ker fun θ h ↦ ?_
  -- In a Fredholm package `T = ι ∘ Φ ∘ π` for the projection `π` of `E` onto a complement `X₁`
  -- of `ker T`, so `θ = θ ∘ ι ∘ π` factors as `(θ ∘ Q) ∘ T` for the quasi-inverse `Q`.
  obtain ⟨pkg⟩ := hT.nonempty_fredholmPackage
  refine ⟨θ ∘L pkg.quasiInverse, ContinuousLinearMap.ext fun x ↦ ?_⟩
  set π := pkg.decDom.proj
  have hTx : T x = (pkg.equiv (π x) : F) := by
    conv_lhs => rw [pkg.eq_equiv]
    simp [π]
  have hQ : pkg.quasiInverse (T x) = (π x : E) := by
    simp [FredholmPackage.quasiInverse, hTx]
  have hker : x - (π x : E) ∈ T.ker := by
    rw [pkg.ker_eq, ← Submodule.projectionOntoL_apply_eq_zero_iff pkg.decDom.isTopCompl, map_sub,
      Submodule.projectionOntoL_apply_left, sub_self]
  have := Submodule.mem_orthogonalBilin.1 h _ hker
  rw [LinearMap.flip_apply, topDualPairing_apply, map_sub, sub_eq_zero] at this
  simp [hQ, this]

variable [T2Space E]

/-- **The cokernel of the transpose.** For a Fredholm operator `T`, the inclusion of continuous
functionals into all functionals identifies the cokernel of the transpose `T'` with the cokernel
of the algebraic dual map `T^*`. Both are the dual of `ker T` (`LinearMap.cokerDualMapEquiv`). -/
def cokerPrecompEquivCokerDualMap (hT : IsFredholm T) :
    (StrongDual 𝕜 E ⧸ (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range) ≃ₗ[𝕜]
      (Dual 𝕜 E ⧸ LinearMap.range (T : E →ₗ[𝕜] F).dualMap) :=
  LinearEquiv.ofBijective
    (Submodule.mapQ _ _ (coeLM 𝕜 : StrongDual 𝕜 E →ₗ[𝕜] Dual 𝕜 E) <| by
      rintro _ ⟨ψ, rfl⟩
      exact ⟨ψ, rfl⟩)
    ⟨by
      -- Injectivity is the closed range theorem for Fredholm operators.
      refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
      obtain ⟨θ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hq
      rw [Submodule.Quotient.mk_eq_zero, hT.range_precomp_eq_orthogonalBilin_ker]
      exact Submodule.mem_orthogonalBilin.2 fun x hx ↦
        (Submodule.mem_dualAnnihilator _).1 hq x hx,
    by
      -- A functional on the finite-dimensional `ker T` extends continuously along a closed
      -- complement, and the extension agrees with `α` on `ker T`.
      intro q
      obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have := hT.finite_ker
      obtain ⟨C, hC⟩ := hT.closedComplemented_ker.exists_isTopCompl
      let θ : StrongDual 𝕜 E :=
        LinearMap.toContinuousLinearMap (α ∘ₗ T.ker.subtype) ∘L T.ker.projectionOntoL C hC
      refine ⟨Submodule.Quotient.mk θ, ?_⟩
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq,
        LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
      intro x hx
      simp [θ, Submodule.projection_apply_of_mem_left, hx]⟩

@[simp]
theorem cokerPrecompEquivCokerDualMap_mk (hT : IsFredholm T) (θ : StrongDual 𝕜 E) :
    cokerPrecompEquivCokerDualMap hT (Submodule.Quotient.mk θ) =
      Submodule.Quotient.mk (θ : Dual 𝕜 E) :=
  (rfl)

/-- The cokernel of the transpose has the dimension of the kernel of `T`. -/
theorem finrank_quotient_range_precomp (hT : IsFredholm T) :
    finrank 𝕜 (StrongDual 𝕜 E ⧸ (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range) =
      finrank 𝕜 T.ker :=
  (cokerPrecompEquivCokerDualMap hT).finrank_eq.trans
    (T : E →ₗ[𝕜] F).finrank_quotient_range_dualMap

/-- **The transpose negates the index** of a Fredholm operator. -/
@[simp]
theorem index_precomp (hT : IsFredholm T) :
    index (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) = -index T := by
  have := hT.finite_coker
  rw [index_eq_finrank_sub, index_eq_finrank_sub,
    finrank_ker_precomp_eq_finrank_quotient_range T hT.isClosed_range,
    finrank_quotient_range_precomp hT]
  ring

section DetLine

variable (hT : IsFredholm T)

/-- **The determinant line of the transpose.** For a Fredholm operator `T`, the determinant line
`det (ker T') ⊗ (det (coker T'))^*` of the transpose is identified with the determinant line
`det (ker T) ⊗ (det (coker T))^*` of `T`. The kernel and cokernel of `T'` are those of the
algebraic dual map `T^*` (`ContinuousLinearMap.kerPrecompEquivKerDualMap`,
`ContinuousLinearMap.cokerPrecompEquivCokerDualMap`), whose determinant line is identified with
that of `T` by `LinearMap.detLineDualMapEquiv`. Its value on exterior products is
`ContinuousLinearMap.smul_detLinePrecompEquiv_tmul`. -/
def detLinePrecompEquiv :
    ((precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
      StrongDual 𝕜 F →ₗ[𝕜] StrongDual 𝕜 E).detLine ≃ₗ[𝕜] (T : E →ₗ[𝕜] F).detLine :=
  have := hT.finite_ker
  have := hT.finite_coker
  (TensorProduct.congr (LinearEquiv.detLineCongr (kerPrecompEquivKerDualMap T hT.isClosed_range))
      (LinearEquiv.detLineCongr (cokerPrecompEquivCokerDualMap hT)).symm.dualMap).trans
    (T : E →ₗ[𝕜] F).detLineDualMapEquiv

/-- **The value of `ContinuousLinearMap.detLinePrecompEquiv` on exterior products.** Let
`φ₁, …, φ_c` be continuous functionals on `F` vanishing on `range T` and `β` a functional on
`det (coker T')`. The image of `(φ₁ ∧ ⋯ ∧ φ_c) ⊗ β` is `x ⊗ ψ`, where `ψ` is the functional on
`det (coker T)` sending the exterior product of the classes of `n₁, …, n_c` to `det (φⱼ nᵢ)`, and
`x ∈ det (ker T)` is determined by pairing with the classes of continuous functionals
`θ₁, …, θ_k` on `E`: for every `u₁, …, u_k` in `ker T`,
`det (θⱼ uᵢ) • x = β (θ₁ ∧ ⋯ ∧ θ_k) • (u₁ ∧ ⋯ ∧ u_k)`. -/
theorem smul_detLinePrecompEquiv_tmul
    (φ : Fin (finrank 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).ker) →
      (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).ker)
    (β : Dual 𝕜 (TauCeti.detLine 𝕜
      (StrongDual 𝕜 E ⧸ (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range)))
    (θ : Fin (finrank 𝕜
      (StrongDual 𝕜 E ⧸ (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range)) →
        StrongDual 𝕜 E)
    (u : Fin (finrank 𝕜 T.ker) → T.ker) (ψ : Dual 𝕜 (TauCeti.detLine 𝕜 (F ⧸ T.range)))
    (hψ : ∀ n : Fin (finrank 𝕜 (F ⧸ T.range)) → F,
      ψ (exteriorPower.ιMulti 𝕜 _ (T.range.mkQ ∘ n)) =
        (Matrix.of fun i j ↦
          (φ (Fin.cast (have := hT.finite_coker
            (finrank_ker_precomp_eq_finrank_quotient_range T hT.isClosed_range).symm) j) :
            StrongDual 𝕜 F)
            (n i)).det) :
    (Matrix.of fun i j ↦ θ (Fin.cast (finrank_quotient_range_precomp hT).symm j) (u i)).det •
        detLinePrecompEquiv hT (exteriorPower.ιMulti 𝕜 _ φ ⊗ₜ β) =
      β (exteriorPower.ιMulti 𝕜 _
          ((precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range.mkQ ∘ θ)) •
        (exteriorPower.ιMulti 𝕜 _ u ⊗ₜ ψ) := by
  have := hT.finite_ker
  have := hT.finite_coker
  unfold detLinePrecompEquiv
  rw [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.detLineCongr_ιMulti]
  have key := (T : E →ₗ[𝕜] F).smul_detLineDualMapEquiv_tmul
    (kerPrecompEquivKerDualMap T hT.isClosed_range ∘ φ ∘
      Fin.cast (kerPrecompEquivKerDualMap T hT.isClosed_range).finrank_eq.symm)
    ((cokerPrecompEquivCokerDualMap hT).detLineCongr.symm.dualMap β)
    (((↑) : StrongDual 𝕜 E → Dual 𝕜 E) ∘ θ ∘
      Fin.cast (cokerPrecompEquivCokerDualMap hT).finrank_eq.symm) u ψ
    (fun n ↦ by simp [hψ, Fin.cast_cast])
  convert key using 2
  · simp [Fin.cast_cast]
  · simp only [LinearEquiv.dualMap_apply, LinearEquiv.detLineCongr_symm,
      LinearEquiv.detLineCongr_ιMulti]
    congr 2
    funext i
    simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self, Submodule.mkQ_apply]
    exact ((LinearEquiv.symm_apply_eq _).2 (cokerPrecompEquivCokerDualMap_mk hT _).symm).symm

end DetLine

end Cokernel

section Normed

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The transpose of a Fredholm operator is Fredholm.** Between normed spaces over `ℝ` or `ℂ`,
the transpose `T' : F' →L[𝕜] E'` of a Fredholm operator `T` has finite-dimensional kernel and
cokernel, and the duals are Banach spaces, so `T'` is Fredholm. No completeness of `E` or `F` is
needed. -/
theorem IsFredholm.precomp {T : E →L[𝕜] F} (hT : IsFredholm T) :
    IsFredholm (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) := by
  have : CompleteSpace 𝕜 := by let := IsRCLikeNormedField.rclike 𝕜; infer_instance
  have := hT.finite_ker
  have := hT.finite_coker
  refine IsFredholm.of_finite_ker_coker _ ?_ ?_
  · exact ((kerPrecompEquivKerDualMap T hT.isClosed_range).trans
      (T : E →ₗ[𝕜] F).kerDualMapEquiv).symm.finiteDimensional
  · exact ((cokerPrecompEquivCokerDualMap hT).trans
      (T : E →ₗ[𝕜] F).cokerDualMapEquiv).symm.finiteDimensional

end Normed

section Hilbert

open InnerProductSpace
open scoped InnerProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] {T : E →L[ℝ] F}

/-- **The determinant line of the Hilbert adjoint.** For a Fredholm operator `T` between real
Hilbert spaces, the Riesz isomorphisms carry the adjoint `T†` to the transpose `T'`
(`ContinuousLinearMap.precomp_comp_toDual`), so `LinearMap.detLineCongr` and
`ContinuousLinearMap.detLinePrecompEquiv` identify the determinant line of `T†` with that
of `T`. -/
def detLineAdjointEquiv (hT : IsFredholm T) :
    (T† : F →ₗ[ℝ] E).detLine ≃ₗ[ℝ] (T : E →ₗ[ℝ] F).detLine :=
  ((T† : F →ₗ[ℝ] E).detLineCongr (toDual ℝ F).toLinearEquiv (toDual ℝ E).toLinearEquiv
    (precomp_comp_toDual T)).trans (detLinePrecompEquiv hT)

/-- `ContinuousLinearMap.detLineAdjointEquiv` transports along the Riesz isomorphisms and then
applies `ContinuousLinearMap.detLinePrecompEquiv`. The value of the first step on pure tensors is
`LinearMap.detLineCongr_tmul`, and that of the second is
`ContinuousLinearMap.smul_detLinePrecompEquiv_tmul`. -/
theorem detLineAdjointEquiv_apply (hT : IsFredholm T) (x : (T† : F →ₗ[ℝ] E).detLine) :
    detLineAdjointEquiv hT x = detLinePrecompEquiv hT
      ((T† : F →ₗ[ℝ] E).detLineCongr (toDual ℝ F).toLinearEquiv (toDual ℝ E).toLinearEquiv
        (precomp_comp_toDual T) x) :=
  (rfl)

end Hilbert

end ContinuousLinearMap
