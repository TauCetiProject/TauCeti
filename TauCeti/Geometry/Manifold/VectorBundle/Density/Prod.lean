/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import TauCeti.Geometry.Manifold.VectorBundle.ExternalTensor
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.LinearAlgebra.Density.Prod

/-!
# The density line of a product manifold

Let `M` and `N` be manifolds, with density lines `|Λ_M|` and `|Λ_N|`
(`TauCeti.DensityBundle`). The tangent space of `M × N` at `(x, y)` is `T_x M × T_y N`, so a
density `μ` on `T_x M` and a density `ν` on `T_y N` have a product `μ.prod ν`, a density on
`T_(x, y) (M × N)` (`TauCeti.DensityBundle.prod`), with value `μ v * ν w` on the frame listing the
vectors `(vᵢ, 0)` and `(0, wⱼ)` (`TauCeti.DensityBundle.prod_apply_sumElim`). Fibrewise this
identifies the external tensor product `|Λ_M| ⊠ |Λ_N|` (`TauCeti.ExternalTensor`) with the density
line `|Λ_{M × N}|` of the product (`TauCeti.DensityBundle.externalTensorEquiv`).

The product of smooth density sections is smooth (`TauCeti.DensityBundle.contMDiff_prod`): in the
frames of `M × N` given by its product charts, the product density is a constant multiple of the
product of the coordinate expressions of the factors. So a density `μ(x) ν(y)` on `M × N` built
from densities on `M` and on `N` is a smooth density whenever they are, as for the product
`dx dy` of Lebesgue densities in charts. This is the splitting of densities on `M × N` behind
the coefficients `F ⊠ (E* ⊗ |Λ_N|)` of the distributional kernel of an operator from sections of
`E` over `N` to distributional sections of `F` over `M`.

## Main definitions

* `TauCeti.DensityBundle.prod μ ν`: the product of a density on `T_x M` and a density on `T_y N`.
* `TauCeti.DensityBundle.externalTensorEquiv p`: the continuous linear equivalence between the
  fibre at `p` of `|Λ_M| ⊠ |Λ_N|` and the density line of `M × N` at `p`.

## Main results

* `TauCeti.DensityBundle.prod_apply_sumElim`: the value of the product on frames adapted to the
  product.
* `TauCeti.DensityBundle.add_prod`, `TauCeti.DensityBundle.prod_eq_zero_iff` and their
  companions: the product is bilinear and vanishes only when a factor does.
* `TauCeti.DensityBundle.prod_apply_trivializationAt_symm`: in the frames of a product chart, a
  product density is a constant times the product of the coordinates of its factors.
* `TauCeti.DensityBundle.contMDiffAt_prod`, `TauCeti.DensityBundle.contMDiff_prod`: products of
  `C^n` density sections are `C^n`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open Bundle Module Set
open scoped Manifold ContDiff TensorProduct

namespace TauCeti.DensityBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} {N : Type*} [TopologicalSpace N]
  [ChartedSpace G N]

/-- The product of a density `μ` on `T_x M` and a density `ν` on `T_y N`: the density on
`T_(x, y) (M × N) = T_x M × T_y N` with value `μ v * ν w` on the frame listing the vectors
`(vᵢ, 0)` and then `(0, wⱼ)` (`TauCeti.DensityBundle.prod_apply_sumElim`). -/
def prod {p : M × N} (μ : DensityBundle I M p.1) (ν : DensityBundle J N p.2) :
    DensityBundle (I.prod J) (M × N) p :=
  -- `Density.prod μ ν` is a density on `TangentSpace I p.1 × TangentSpace J p.2`, of index
  -- `finrank ℝ (TangentSpace I p.1 × TangentSpace J p.2)`. Since `TangentSpace` unfolds to the
  -- model space, both this type and `TangentSpace (I.prod J) p` are `E × F` by definition, and
  -- `tangentSpaceProdEquiv p` is the identity of `E × F`. So no transport is needed.
  Density.prod μ ν

/-- The product density on `M × N` is the product `TauCeti.Density.prod` of densities on
`T_x M × T_y N`, which is `T_(x, y) (M × N)` by definition (see `TauCeti.DensityBundle.prod`). -/
theorem prod_def {p : M × N} (μ : DensityBundle I M p.1) (ν : DensityBundle J N p.2) :
    μ.prod ν = Density.prod μ ν :=
  (rfl)

/-- Read through the identification `T_(x, y) (M × N) = T_x M × T_y N`
(`TauCeti.Manifold.tangentSpaceProdEquiv`), the product density is the product
`TauCeti.Density.prod` of densities on the two factors. -/
theorem prod_apply {p : M × N} (μ : DensityBundle I M p.1) (ν : DensityBundle J N p.2)
    (u : Fin (finrank ℝ (E × F)) → TangentSpace I p.1 × TangentSpace J p.2) :
    μ.prod ν ((Manifold.tangentSpaceProdEquiv (I := I) (J := J) p).symm ∘ u) =
      Density.prod μ ν u := by
  -- `tangentSpaceProdEquiv p` is the identity of `E × F` up to definitional unfolding.
  have h : (Manifold.tangentSpaceProdEquiv (I := I) (J := J) p).symm ∘ u = u :=
    funext fun k ↦ Manifold.tangentSpaceProdEquiv_symm_apply p (u k)
  rw [h, prod_def]
  -- The two sides now differ only in spelling the type of `u` as `Fin _ → T_p (M × N)` or as
  -- `Fin _ → T_x M × T_y N`, which are the same type by definition.
  rfl

/-- **The value of a product density.** On the frame of `T_(x, y) (M × N)` listing the vectors
`(vᵢ, 0)` and then `(0, wⱼ)`, in any order `e`, the product `μ.prod ν` takes the value
`μ v * ν w`. -/
theorem prod_apply_sumElim {p : M × N} (μ : DensityBundle I M p.1) (ν : DensityBundle J N p.2)
    (e : Fin (finrank ℝ E) ⊕ Fin (finrank ℝ F) ≃ Fin (finrank ℝ (E × F)))
    (v : Fin (finrank ℝ E) → TangentSpace I p.1) (w : Fin (finrank ℝ F) → TangentSpace J p.2) :
    μ.prod ν ((Manifold.tangentSpaceProdEquiv (I := I) (J := J) p).symm ∘
      (Sum.elim (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) ∘ e.symm)) = μ v * ν w := by
  rw [prod_apply]
  exact Density.prod_apply_sumElim μ ν e v w

@[simp]
theorem add_prod {p : M × N} (μ μ' : DensityBundle I M p.1) (ν : DensityBundle J N p.2) :
    (μ + μ').prod ν = μ.prod ν + μ'.prod ν :=
  Density.add_prod μ μ' ν

@[simp]
theorem prod_add {p : M × N} (μ : DensityBundle I M p.1) (ν ν' : DensityBundle J N p.2) :
    μ.prod (ν + ν') = μ.prod ν + μ.prod ν' :=
  Density.prod_add μ ν ν'

@[simp]
theorem smul_prod {p : M × N} (a : ℝ) (μ : DensityBundle I M p.1) (ν : DensityBundle J N p.2) :
    (a • μ).prod ν = a • μ.prod ν :=
  Density.smul_prod a μ ν

@[simp]
theorem prod_smul {p : M × N} (a : ℝ) (μ : DensityBundle I M p.1) (ν : DensityBundle J N p.2) :
    μ.prod (a • ν) = a • μ.prod ν :=
  Density.prod_smul a μ ν

@[simp]
theorem zero_prod {p : M × N} (ν : DensityBundle J N p.2) :
    (0 : DensityBundle I M p.1).prod ν = 0 :=
  Density.zero_prod ν

@[simp]
theorem prod_zero {p : M × N} (μ : DensityBundle I M p.1) :
    μ.prod (0 : DensityBundle J N p.2) = 0 :=
  Density.prod_zero μ

/-- The product of two densities vanishes only when one of them does. -/
@[simp]
theorem prod_eq_zero_iff {p : M × N} {μ : DensityBundle I M p.1} {ν : DensityBundle J N p.2} :
    μ.prod ν = 0 ↔ μ = 0 ∨ ν = 0 :=
  Density.prod_eq_zero_iff

/-- The fibre at `p` of the external tensor product `|Λ_M| ⊠ |Λ_N|` of the density lines of `M`
and `N` is the density line of `M × N` at `p`, the pure tensor `μ ⊗ ν` corresponding to the
product density `μ.prod ν` (`TauCeti.DensityBundle.externalTensorEquiv_tmul`). -/
def externalTensorEquiv (p : M × N) :
    ExternalTensor ℝ (DensityBundle I M) (DensityBundle J N) p ≃L[ℝ]
      DensityBundle (I.prod J) (M × N) p :=
  -- Two identifications hold by definition here: the fibres at `p` of the pullbacks of `|Λ_M|`
  -- and `|Λ_N|` along the projections are the fibres `|Λ_M|_{p.1}` and `|Λ_N|_{p.2}`, and
  -- `T_p (M × N)` is `T_{p.1} M × T_{p.2} N` (see `TauCeti.DensityBundle.prod`).
  let e : ExternalTensor ℝ (DensityBundle I M) (DensityBundle J N) p ≃ₗ[ℝ]
      DensityBundle (I.prod J) (M × N) p := Density.tensorProductEquiv
  -- The density line is finite-dimensional, being identified with `ℝ` by evaluation on a basis.
  haveI : FiniteDimensional ℝ (DensityBundle (I.prod J) (M × N) p) :=
    (finBasis ℝ (TangentSpace (I.prod J) p)).densityEquiv.symm.finiteDimensional
  { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := e.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]
theorem externalTensorEquiv_tmul {p : M × N} (μ : DensityBundle I M p.1)
    (ν : DensityBundle J N p.2) :
    externalTensorEquiv p (μ ⊗ₜ[ℝ] ν : ExternalTensor ℝ (DensityBundle I M) (DensityBundle J N) p) =
      μ.prod ν :=
  -- By the definitional identifications recorded in `externalTensorEquiv`.
  Density.tensorProductEquiv_tmul μ ν

@[simp]
theorem externalTensorEquiv_symm_prod {p : M × N} (μ : DensityBundle I M p.1)
    (ν : DensityBundle J N p.2) :
    (externalTensorEquiv p).symm (μ.prod ν) =
      (μ ⊗ₜ[ℝ] ν : ExternalTensor ℝ (DensityBundle I M) (DensityBundle J N) p) := by
  rw [← externalTensorEquiv_tmul, ContinuousLinearEquiv.symm_apply_apply]

variable [IsManifold I 1 M] [IsManifold J 1 N] {n : WithTop ℕ∞}

/-- **A product density in the frames of a product chart.** Over the domain of the chart of
`M × N` at `p`, the value of a product density `μ.prod ν` on the frame of `M × N` given by its
tangent-bundle trivialization at `p` is a constant, independent of `q`, `μ` and `ν`, times the
product of the values of `μ` and `ν` on the frames of `M` at `p.1` and of `N` at `p.2`. -/
theorem prod_apply_trivializationAt_symm {p q : M × N}
    (hq : q ∈ (chartAt (ModelProd H G) p).source) (μ : DensityBundle I M q.1)
    (ν : DensityBundle J N q.2)
    (e : Fin (finrank ℝ E) ⊕ Fin (finrank ℝ F) ≃ Fin (finrank ℝ (E × F))) :
    μ.prod ν (fun i ↦ (trivializationAt (E × F) (TangentSpace (I.prod J)) p).symm q
        (finBasis ℝ (E × F) i)) =
      |(((finBasis ℝ E).prod (finBasis ℝ F)).reindex e).det (finBasis ℝ (E × F))| *
        (μ (fun i ↦ (trivializationAt E (TangentSpace I) p.1).symm q.1 (finBasis ℝ E i)) *
          ν (fun i ↦ (trivializationAt F (TangentSpace J) p.2).symm q.2 (finBasis ℝ F i))) := by
  have hq' : q.1 ∈ (chartAt H p.1).source ∧ q.2 ∈ (chartAt G p.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, mem_prod] using hq
  have h₁ : q.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hq'.1
  have h₂ : q.2 ∈ (trivializationAt F (TangentSpace J) p.2).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hq'.2
  -- The inverse charts of the tangent bundles of `M` and `N` at `q`.
  let A : E ≃ₗ[ℝ] TangentSpace I q.1 :=
    ((trivializationAt E (TangentSpace I) p.1).continuousLinearEquivAt ℝ q.1 h₁).symm
  let B : F ≃ₗ[ℝ] TangentSpace J q.2 :=
    ((trivializationAt F (TangentSpace J) p.2).continuousLinearEquivAt ℝ q.2 h₂).symm
  have hA (v : E) : A v = (trivializationAt E (TangentSpace I) p.1).symm q.1 v := by
    simp [A]
  have hB (w : F) : B w = (trivializationAt F (TangentSpace J) p.2).symm q.2 w := by
    simp [B]
  -- The inverse chart of the tangent bundle of `M × N` is their product.
  have hframe : (fun i ↦ (trivializationAt (E × F) (TangentSpace (I.prod J)) p).symm q
      (finBasis ℝ (E × F) i)) = (Manifold.tangentSpaceProdEquiv (I := I) (J := J) q).symm ∘
        ((A.prodCongr B : E × F → TangentSpace I q.1 × TangentSpace J q.2) ∘
          finBasis ℝ (E × F)) := by
    funext i
    have h := Manifold.tangentSpaceProdEquiv_symmL_trivializationAt (I := I) (J := J) hq
      (finBasis ℝ (E × F) i)
    rw [Trivialization.symmL_apply _ (by simpa only [TangentBundle.trivializationAt_baseSet]
      using hq), Trivialization.symmL_apply _ h₁, Trivialization.symmL_apply _ h₂] at h
    simp only [Function.comp_apply, LinearEquiv.prodCongr_apply, hA, hB]
    rw [← h, ContinuousLinearEquiv.symm_apply_apply]
  have hA' : (A : E → TangentSpace I q.1) ∘ finBasis ℝ E =
      fun i ↦ (trivializationAt E (TangentSpace I) p.1).symm q.1 (finBasis ℝ E i) :=
    funext fun i ↦ hA _
  have hB' : (B : F → TangentSpace J q.2) ∘ finBasis ℝ F =
      fun i ↦ (trivializationAt F (TangentSpace J) p.2).symm q.2 (finBasis ℝ F i) :=
    funext fun i ↦ hB _
  rw [hframe, prod_apply]
  refine (Density.prod_apply_prodCongr_comp μ ν A B (finBasis ℝ E) (finBasis ℝ F) e
    (finBasis ℝ (E × F))).trans ?_
  exact congrArg (_ * ·) (congrArg₂ (· * ·) (congrArg μ hA') (congrArg ν hB'))

/-- **Products of smooth densities are smooth.** If the density sections `μ` of `M` and `ν` of `N`
are `C^n` at `p.1` and `p.2`, then the density section `(x, y) ↦ μ x · ν y` of `M × N` is `C^n`
at `p`. -/
theorem contMDiffAt_prod {μ : ∀ x : M, DensityBundle I M x} {ν : ∀ y : N, DensityBundle J N y}
    {p : M × N} (hμ : ContMDiffAt I (I.prod 𝓘(ℝ)) n (fun x ↦ TotalSpace.mk' ℝ x (μ x)) p.1)
    (hν : ContMDiffAt J (J.prod 𝓘(ℝ)) n (fun y ↦ TotalSpace.mk' ℝ y (ν y)) p.2) :
    ContMDiffAt (I.prod J) ((I.prod J).prod 𝓘(ℝ)) n
      (fun q : M × N ↦ TotalSpace.mk' ℝ (E := DensityBundle (I.prod J) (M × N)) q
        ((μ q.1).prod (ν q.2))) p := by
  rw [Density.contMDiffAt_section_iff] at hμ hν ⊢
  -- Any ordering of the product basis serves to name the constant.
  obtain ⟨e⟩ : Nonempty (Fin (finrank ℝ E) ⊕ Fin (finrank ℝ F) ≃ Fin (finrank ℝ (E × F))) :=
    Fintype.card_eq.mp (by simp [finrank_prod])
  -- Near `p`, the coordinate expression of the product is a constant times the product of the
  -- coordinate expressions of `μ` and `ν`.
  refine ((contMDiffAt_const (c := |(((finBasis ℝ E).prod (finBasis ℝ F)).reindex e).det
      (finBasis ℝ (E × F))|)).mul
    ((hμ.comp p contMDiffAt_fst).mul (hν.comp p contMDiffAt_snd))).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (ModelProd H G) p).open_source.mem_nhds (mem_chart_source _ p)]
    with q hq
  exact prod_apply_trivializationAt_symm hq (μ q.1) (ν q.2) e

/-- **Products of smooth densities are smooth.** If the density sections `μ` of `M` and `ν` of `N`
are `C^n`, then so is the density section `(x, y) ↦ μ x · ν y` of `M × N`. -/
theorem contMDiff_prod {μ : ∀ x : M, DensityBundle I M x} {ν : ∀ y : N, DensityBundle J N y}
    (hμ : ContMDiff I (I.prod 𝓘(ℝ)) n (fun x ↦ TotalSpace.mk' ℝ x (μ x)))
    (hν : ContMDiff J (J.prod 𝓘(ℝ)) n (fun y ↦ TotalSpace.mk' ℝ y (ν y))) :
    ContMDiff (I.prod J) ((I.prod J).prod 𝓘(ℝ)) n
      (fun q : M × N ↦ TotalSpace.mk' ℝ (E := DensityBundle (I.prod J) (M × N)) q
        ((μ q.1).prod (ν q.2))) :=
  fun p ↦ contMDiffAt_prod (hμ p.1) (hν p.2)

end TauCeti.DensityBundle
