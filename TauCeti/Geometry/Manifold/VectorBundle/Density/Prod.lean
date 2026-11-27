/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.LinearAlgebra.Density.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.ExternalTensor
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Densities on product manifolds

A density `μ` at a point `x` of a manifold `M` and a density `ν` at `y ∈ N` have a product
`TauCeti.DensityBundle.prod μ ν`, a density at `(x, y)` on `M × N`: the product of densities of
`TauCeti.Density.prod` on `T_x M × T_y N`, read on the tangent space of the product through
`TauCeti.Manifold.tangentSpaceProdEquiv`. On a pair of tuples of tangent vectors to the two
factors it is the product of the values of `μ` and `ν`
(`TauCeti.DensityBundle.prod_apply_append`), and it is bilinear.

The product of two `C^n` density sections is a `C^n` density section on `M × N`
(`TauCeti.DensityBundle.contMDiff_prod`). In the preferred local frames the product reads as the
product of the two factor readings, up to a constant depending only on the model spaces
(`TauCeti.DensityBundle.prod_apply_trivializationAt_symm`), since the inverse tangent
trivialization of a product is the product of the inverse trivializations of the factors.

On each fibre, the product of densities identifies the external tensor product
`|Λ|_M ⊠ |Λ|_N` of the density bundles of the factors with the density bundle `|Λ|_{M × N}` of
the product (`TauCeti.DensityBundle.externalTensorEquiv`). Only this fibrewise linear
identification is provided here. Carrying kernels on `M × N` of operators between bundles over `M`
and `N` across it, as in Hörmander's form of the Schwartz kernel theorem, needs a smooth bundle
isomorphism built from `externalTensorEquiv`, which is not yet formalized.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §6.3 (density bundles and kernels on products of manifolds).
-/

public section

noncomputable section

open Bundle Module Set
open scoped Manifold ContDiff TensorProduct

namespace TauCeti.DensityBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- The **product** of a density `μ` at `x ∈ M` and a density `ν` at `y ∈ N`: the density at
`(x, y)` on `M × N` given on `T_{(x, y)} (M × N) ≃ T_x M × T_y N` by the product of densities
`TauCeti.Density.prod`. -/
def prod {x : M} {y : N} (μ : DensityBundle I M x) (ν : DensityBundle J N y) :
    DensityBundle (I.prod J) (M × N) (x, y) :=
  Density.map (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (x, y)).symm.toLinearEquiv
    (Density.prod μ ν)

/-- The product density reads a tuple of tangent vectors to `M × N` through
`T_{(x, y)} (M × N) ≃ T_x M × T_y N`. -/
theorem prod_apply {x : M} {y : N} (μ : DensityBundle I M x) (ν : DensityBundle J N y)
    (v : Fin (finrank ℝ (E × E')) → TangentSpace (I.prod J) (x, y)) :
    prod μ ν v =
      Density.prod μ ν (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (x, y) ∘ v) := by
  simp [prod]

/-- The product of densities is bilinear. -/
theorem add_prod {x : M} {y : N} (μ μ' : DensityBundle I M x) (ν : DensityBundle J N y) :
    prod (μ + μ') ν = prod μ ν + prod μ' ν := by
  simp [prod, Density.add_prod]

theorem prod_add {x : M} {y : N} (μ : DensityBundle I M x) (ν ν' : DensityBundle J N y) :
    prod μ (ν + ν') = prod μ ν + prod μ ν' := by
  simp [prod, Density.prod_add]

theorem smul_prod {x : M} {y : N} (a : ℝ) (μ : DensityBundle I M x) (ν : DensityBundle J N y) :
    prod (a • μ) ν = a • prod μ ν := by
  simp [prod, Density.smul_prod]

theorem prod_smul {x : M} {y : N} (a : ℝ) (μ : DensityBundle I M x) (ν : DensityBundle J N y) :
    prod μ (a • ν) = a • prod μ ν := by
  simp [prod, Density.prod_smul]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- **The product density on product frames.** On tangent vectors `(v i, 0)` followed by
`(0, w j)`, the product of densities `μ` at `x` and `ν` at `y` takes the value `μ v * ν w`. -/
theorem prod_apply_append {x : M} {y : N} (μ : DensityBundle I M x) (ν : DensityBundle J N y)
    (v : Fin (finrank ℝ E) → TangentSpace I x) (w : Fin (finrank ℝ E') → TangentSpace J y) :
    prod μ ν (fun r ↦ (Manifold.tangentSpaceProdEquiv (I := I) (J := J) (x, y)).symm
      (Fin.append (fun i ↦ (v i, 0)) (fun j ↦ (0, w j)) (Fin.cast finrank_prod r))) =
      μ v * ν w := by
  rw [prod_apply]
  simp only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply]
  exact Density.prod_apply_append μ ν (TauCeti.finrank_tangentSpace x)
    (TauCeti.finrank_tangentSpace y) finrank_prod.symm v w

/-- **The density line of a product manifold.** At `p ∈ M × N`, the fibre of the external tensor
product `|Λ|_M ⊠ |Λ|_N` of the density bundles of the factors is identified with the density line
of `M × N` by the product of densities. -/
def externalTensorEquiv (p : M × N) :
    ExternalTensor ℝ (DensityBundle I M) (DensityBundle J N) p ≃ₗ[ℝ]
      DensityBundle (I.prod J) (M × N) p :=
  Density.prodTensorEquiv (V := TangentSpace I p.1) (W := TangentSpace J p.2)
      (TauCeti.finrank_tangentSpace p.1) (TauCeti.finrank_tangentSpace p.2) finrank_prod.symm ≪≫ₗ
    Density.map (Manifold.tangentSpaceProdEquiv (I := I) (J := J) p).symm.toLinearEquiv

@[simp]
theorem externalTensorEquiv_tmul (p : M × N) (μ : DensityBundle I M p.1)
    (ν : DensityBundle J N p.2) :
    externalTensorEquiv p (μ ⊗ₜ ν : ExternalTensor ℝ (DensityBundle I M) (DensityBundle J N) p) =
      prod μ ν := by
  -- The fibres of `|Λ|_M ⊠ |Λ|_N` are tensor products of pullback fibres, which are the density
  -- lines at `p.1` and `p.2` by definition; `p` and `(p.1, p.2)` agree by eta for pairs.
  exact congrArg
    (Density.map (Manifold.tangentSpaceProdEquiv (I := I) (J := J) p).symm.toLinearEquiv)
    (Density.prodTensorEquiv_tmul (TauCeti.finrank_tangentSpace p.1)
      (TauCeti.finrank_tangentSpace p.2) finrank_prod.symm μ ν)

/-- The inverse of `TauCeti.DensityBundle.externalTensorEquiv` on a product of densities. -/
@[simp]
theorem externalTensorEquiv_symm_prod (p : M × N) (μ : DensityBundle I M p.1)
    (ν : DensityBundle J N p.2) :
    (externalTensorEquiv p).symm (prod μ ν) =
      (μ ⊗ₜ ν : ExternalTensor ℝ (DensityBundle I M) (DensityBundle J N) p) := by
  rw [LinearEquiv.symm_apply_eq, externalTensorEquiv_tmul]

variable [IsManifold I 1 M] [IsManifold J 1 N]

/-- **The product density in the preferred frames.** Near `p₀`, the product of densities at
`p.1` and `p.2`, evaluated on the inverse local frame of the tangent bundle of `M × N` at `p₀`, is
the product of their values on the inverse local frames of `M` at `p₀.1` and of `N` at `p₀.2`,
times the absolute determinant of the standard basis of `E × E'` in the product of the standard
bases of `E` and `E'`. -/
theorem prod_apply_trivializationAt_symm {p₀ p : M × N}
    (hp : p ∈ (chartAt (ModelProd H H') p₀).source) (μ : DensityBundle I M p.1)
    (ν : DensityBundle J N p.2) :
    prod μ ν (fun i ↦ (trivializationAt (E × E') (TangentSpace (I.prod J)) p₀).symm p
        (finBasis ℝ (E × E') i)) =
      |(((finBasis ℝ E).prod (finBasis ℝ E')).reindex
          (finSumFinEquiv.trans (finCongr finrank_prod.symm))).det (finBasis ℝ (E × E'))| *
        (μ (fun i ↦ (trivializationAt E (TangentSpace I) p₀.1).symm p.1 (finBasis ℝ E i)) *
          ν (fun j ↦ (trivializationAt E' (TangentSpace J) p₀.2).symm p.2 (finBasis ℝ E' j))) := by
  have hp' : p.1 ∈ (chartAt H p₀.1).source ∧ p.2 ∈ (chartAt H' p₀.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, mem_prod] using hp
  have h₀ : p ∈ (trivializationAt (E × E') (TangentSpace (I.prod J)) p₀).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have h₁ : p.1 ∈ (trivializationAt E (TangentSpace I) p₀.1).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hp'.1
  have h₂ : p.2 ∈ (trivializationAt E' (TangentSpace J) p₀.2).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hp'.2
  -- The inverse trivializations of the factors at `p`, as linear equivalences.
  set A := ((trivializationAt E (TangentSpace I) p₀.1).continuousLinearEquivAt ℝ p.1 h₁).symm
  set B := ((trivializationAt E' (TangentSpace J) p₀.2).continuousLinearEquivAt ℝ p.2 h₂).symm
  -- The inverse frame of the product is the image of the standard basis of `E × E'` under the
  -- product of the inverse trivializations of the factors.
  have hframe : Manifold.tangentSpaceProdEquiv (I := I) (J := J) p ∘
      (fun i ↦ (trivializationAt (E × E') (TangentSpace (I.prod J)) p₀).symm p
        (finBasis ℝ (E × E') i)) =
      (A.toLinearEquiv.prodCongr B.toLinearEquiv) ∘ finBasis ℝ (E × E') := by
    funext i
    rw [Function.comp_apply, ← Trivialization.symmL_apply (R := ℝ) _ h₀,
      Manifold.tangentSpaceProdEquiv_symmL_trivializationAt hp]
    simp [A, B, Trivialization.symm_continuousLinearEquivAt_eq (R := ℝ) _ h₁,
      Trivialization.symm_continuousLinearEquivAt_eq (R := ℝ) _ h₂]
  have hA : (fun i ↦ (trivializationAt E (TangentSpace I) p₀.1).symm p.1 (finBasis ℝ E i)) =
      A ∘ finBasis ℝ E := by
    funext i
    simp [A, Trivialization.symm_continuousLinearEquivAt_eq (R := ℝ) _ h₁,
      Trivialization.symmL_apply (R := ℝ) _ h₁]
  have hB : (fun j ↦ (trivializationAt E' (TangentSpace J) p₀.2).symm p.2 (finBasis ℝ E' j)) =
      B ∘ finBasis ℝ E' := by
    funext j
    simp [B, Trivialization.symm_continuousLinearEquivAt_eq (R := ℝ) _ h₂,
      Trivialization.symmL_apply (R := ℝ) _ h₂]
  -- Pull the inverse trivializations of the factors out of the product, then evaluate the product
  -- through the standard bases of `E` and `E'`.
  rw [prod_apply, hframe, Density.prod_apply_prodCongr_comp,
    Density.prod_apply_eq_abs_det_mul _ _ (finBasis ℝ E) (finBasis ℝ E') finrank_prod.symm, hA, hB]
  simp only [Density.map_apply, LinearEquiv.symm_symm, ContinuousLinearEquiv.coe_toLinearEquiv]

variable {n : WithTop ℕ∞}

/-- **Products of smooth densities are smooth.** If `μ` and `ν` are `C^n` density sections on `M`
and on `N`, then `(x, y) ↦ prod (μ x) (ν y)` is a `C^n` density section on `M × N`. -/
theorem contMDiff_prod {μ : ∀ x, DensityBundle I M x} {ν : ∀ y, DensityBundle J N y}
    (hμ : ContMDiff I (I.prod 𝓘(ℝ)) n (fun x ↦ TotalSpace.mk' ℝ x (μ x)))
    (hν : ContMDiff J (J.prod 𝓘(ℝ)) n (fun y ↦ TotalSpace.mk' ℝ y (ν y))) :
    ContMDiff (I.prod J) ((I.prod J).prod 𝓘(ℝ)) n
      (fun p : M × N ↦
        TotalSpace.mk' ℝ (E := DensityBundle (I.prod J) (M × N)) p (prod (μ p.1) (ν p.2))) := by
  intro p₀
  refine (Density.contMDiffAt_section_iff (F := E × E') (V := TangentSpace (I.prod J))
    (s := fun p : M × N ↦ (prod (μ p.1) (ν p.2) : DensityBundle (I.prod J) (M × N) p)) p₀).2 ?_
  have h₁ := ((Density.contMDiffAt_section_iff p₀.1).1 (hμ p₀.1)).comp p₀
    (contMDiffAt_fst (I := I) (J := J))
  have h₂ := ((Density.contMDiffAt_section_iff p₀.2).1 (hν p₀.2)).comp p₀
    (contMDiffAt_snd (I := I) (J := J))
  -- In the preferred frames the product density is a constant times the product of the two
  -- factor readings; the constant is the one of `prod_apply_trivializationAt_symm`, read off by
  -- unification rather than written out again.
  exact (contMDiffAt_const.mul (h₁.mul h₂)).congr_of_eventuallyEq <|
    Filter.eventually_of_mem
      ((chartAt (ModelProd H H') p₀).open_source.mem_nhds (mem_chart_source _ p₀))
      fun p hp ↦ prod_apply_trivializationAt_symm hp (μ p.1) (ν p.2)

end TauCeti.DensityBundle
