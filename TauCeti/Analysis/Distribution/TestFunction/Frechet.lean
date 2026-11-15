/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.LocallyConvex.Barrelled
import TauCeti.Analysis.LocallyConvex.Multilinear

/-!
# The Fréchet space of functions supported in a fixed compact set

For a compact set `K` in a real normed space `E` and a real Banach space `F`, the space
`𝓓^{n}_{K}(E, F)` of `C^n` functions `E → F` supported in `K` is a Fréchet space: its topology is
given by the countably many seminorms `N_i` (the sup norms of the iterated derivatives of order
`i ≤ n`), and it is complete (`ContDiffMapSupportedIn.instCompleteSpace`). Completeness is the
classical fact that `C^n` functions whose derivatives of every order `i ≤ n` converge uniformly
have a `C^n` limit, whose derivatives are the limits of the derivatives
(`HasFTaylorSeriesUpTo.of_tendstoLocallyUniformly`); the support condition passes to the limit
pointwise.

Being completely metrizable, `𝓓^{n}_{K}(E, F)` is a Baire space and hence barrelled
(`BaireSpace.instBarrelledSpace`), so the Banach–Steinhaus theorem applies to it. The main
consequence proved here is that a bilinear map on `𝓓^{n₁}_{K₁}(E₁, F₁) × 𝓓^{n₂}_{K₂}(E₂, F₂)`
with values in a normed space that is continuous in each variable separately is bounded by a
product of the seminorms `N_{≤k}` of a single finite order `k`
(`LinearMap.exists_bound_supportedIn_of_continuous`). Such a bilinear map arises from every
continuous linear map from test functions to distributions, by pairing; the bound is the
continuity hypothesis of the Schwartz kernel theorem for test functions supported in small compact
sets, `LinearMap.exists_schwartzKernel_supportedIn`.

## Main results

* `ContDiffMapSupportedIn.instCompleteSpace`: `𝓓^{n}_{K}(E, F)` is complete when `F` is.
* `ContDiffMapSupportedIn.instBaireSpace`: with the countably generated uniformity
  (`ContDiffMapSupportedIn.instIsCountablyGeneratedUniformity`), completeness makes
  `𝓓^{n}_{K}(E, F)` completely metrizable, hence a Baire space and barrelled.
* `LinearMap.exists_bound_supportedIn_of_continuous`: a separately continuous bilinear map on two
  such spaces is bounded by `C N_{≤k}(φ) N_{≤k}(ψ)` for some `C` and `k`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §2.1 and the proof of Theorem 5.2.1.
* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Chapter 13 (the spaces
  `C^m_c(K)` are Fréchet spaces) and Theorem 34.1.
-/

public section

open Filter Function Set TopologicalSpace
open scoped Topology Uniformity ContDiff BoundedContinuousFunction Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {n : ℕ∞} {K : Compacts E}

/-- The topology of `𝓓^{n}_{K}(E, F)` is given by countably many seminorms, so it is first
countable. -/
instance instFirstCountableTopology : FirstCountableTopology 𝓓^{n}_{K}(E, F) :=
  (ContDiffMapSupportedIn.withSeminorms ℝ E F n K).firstCountableTopology

/-- The uniformity of `𝓓^{n}_{K}(E, F)` is countably generated, so with completeness the space is
completely metrizable. -/
instance instIsCountablyGeneratedUniformity : (𝓤 𝓓^{n}_{K}(E, F)).IsCountablyGenerated :=
  IsUniformAddGroup.uniformity_countably_generated

/-- The space `𝓓^{n}_{K}(E, F)` of `C^n` functions supported in `K` is complete when `F` is. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace 𝓓^{n}_{K}(E, F) := by
  refine ⟨fun {l} hl ↦ ?_⟩
  have := hl.1
  -- The images of `l` under the structure maps converge uniformly to some `g i`.
  let ι := ContinuousLinearMap.pi (structureMapCLM ℝ n (E := E) (F := F) (K := K))
  obtain ⟨g, hg⟩ :=
    CompleteSpace.complete (hl.map (isUniformEmbedding_pi_structureMapCLM ℝ).uniformContinuous)
  have hunif (i : ℕ) :
      TendstoUniformly (fun (f : 𝓓^{n}_{K}(E, F)) ↦ ⇑(structureMapCLM ℝ n i f)) (g i) l :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 (tendsto_pi_nhds.1 hg i)
  -- Up to the order `n` these are uniform limits of iterated derivatives.
  have hderiv (i : ℕ) (hi : (i : WithTop ℕ∞) ≤ n) :
      TendstoUniformly (fun (f : 𝓓^{n}_{K}(E, F)) ↦ iteratedFDeriv ℝ i f) (g i) l :=
    (tendstoUniformly_congr (Eventually.of_forall fun f ↦ by
      simp [structureMapCLM_apply, show (i : ℕ∞) ≤ n by exact_mod_cast hi])).1 (hunif i)
  -- Above the order `n` the structure maps vanish, so the limits do too.
  have hzero {i : ℕ} (hi : ¬(i : ℕ∞) ≤ n) (x : E) : g i x = 0 :=
    tendsto_nhds_unique ((hunif i).tendsto_at x) (tendsto_const_nhds.congr fun f ↦ by
      simp [structureMapCLM_apply, hi])
  -- The limit function `h` vanishes outside `K` and has the Taylor series `g`.
  let h : E → F := fun x ↦ (g 0 x).curry0
  have hlim (x : E) : Tendsto (fun f : 𝓓^{n}_{K}(E, F) ↦ f x) l (𝓝 (h x)) := by
    simpa [Function.comp_def, h] using ((continuousMultilinearCurryFin0 ℝ E F).continuous.tendsto
      _).comp ((hderiv 0 (by simp)).tendsto_at x)
  -- The coefficients of `ftaylorSeries ℝ f` are by definition the iterated derivatives of `f`.
  have hp : HasFTaylorSeriesUpTo n h fun x i ↦ g i x :=
    .of_tendstoLocallyUniformly (fun f ↦ f.contDiff.ftaylorSeries)
      (fun m hm ↦ (hderiv m hm).tendstoLocallyUniformly) hlim
  have hsupp : support h ⊆ K := fun x hx ↦ by_contra fun hxK ↦ hx <|
    tendsto_nhds_unique (hlim x) (tendsto_const_nhds.congr fun f ↦ (f.zero_on_compl hxK).symm)
  let f₀ : 𝓓^{n}_{K}(E, F) := .of_support_subset hp.contDiff hsupp
  -- Convergence to `f₀` is convergence of every structure map.
  have hf₀ : ι f₀ = g := by
    funext i
    ext x : 1
    by_cases hi : (i : ℕ∞) ≤ n
    · simp only [ι, ContinuousLinearMap.pi_apply, structureMapCLM_apply, hi, ite_true]
      exact (hp.eq_iteratedFDeriv (by exact_mod_cast hi) x).symm
    · simp [ι, structureMapCLM_apply, hi, hzero hi x]
  exact ⟨f₀, (isUniformEmbedding_pi_structureMapCLM ℝ).isInducing.tendsto_nhds_iff.2
    (hf₀ ▸ hg)⟩

/-- As a complete metrizable space, `𝓓^{n}_{K}(E, F)` is a Baire space; in particular it is
barrelled (`BaireSpace.instBarrelledSpace`), so the Banach–Steinhaus theorem applies to it. -/
instance instBaireSpace [CompleteSpace F] : BaireSpace 𝓓^{n}_{K}(E, F) :=
  BaireSpace.of_completelyPseudoMetrizable

end ContDiffMapSupportedIn

namespace LinearMap

variable {𝕜 E₁ F₁ E₂ F₂ G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedSpace 𝕜 F₁] [SMulCommClass ℝ 𝕜 F₁] [CompleteSpace F₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedSpace 𝕜 F₂] [SMulCommClass ℝ 𝕜 F₂]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n₁ n₂ : ℕ∞} {K₁ : Compacts E₁} {K₂ : Compacts E₂}

/-- **Separately continuous bilinear maps on functions with fixed compact supports have finite
order.** A bilinear map `B` on `𝓓^{n₁}_{K₁}(E₁, F₁) × 𝓓^{n₂}_{K₂}(E₂, F₂)` with values in a normed
space, continuous in each variable, satisfies `‖B φ ψ‖ ≤ C N_{≤k}(φ) N_{≤k}(ψ)` for a constant `C`
and a single order `k`, where `N_{≤k}` is the supremum of the sup norms of the derivatives of order
at most `k` (`ContDiffMapSupportedIn.supSeminorm`). -/
theorem exists_bound_supportedIn_of_continuous
    (B : 𝓓^{n₁}_{K₁}(E₁, F₁) →ₗ[𝕜] 𝓓^{n₂}_{K₂}(E₂, F₂) →ₗ[𝕜] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ)) :
    ∃ (C : ℝ) (k : ℕ), ∀ φ ψ, ‖B φ ψ‖ ≤
      C * ContDiffMapSupportedIn.supSeminorm 𝕜 E₁ F₁ n₁ K₁ k φ *
        ContDiffMapSupportedIn.supSeminorm 𝕜 E₂ F₂ n₂ K₂ k ψ := by
  obtain ⟨s₁, s₂, C, hC⟩ := TauCeti.exists_bilinearMap_seminorm_bound _ _
    (ContDiffMapSupportedIn.withSeminorms 𝕜 E₁ F₁ n₁ K₁)
    (ContDiffMapSupportedIn.withSeminorms 𝕜 E₂ F₂ n₂ K₂) (normSeminorm 𝕜 G) continuous_norm B
    (B.continuous_uncurry_of_barrelledSpace h₁ h₂)
  -- Both finite sets of orders lie below `k`.
  let k := (s₁ ∪ s₂).sup _root_.id
  have hle {σ : Finset ℕ} (hσ : σ ⊆ s₁ ∪ s₂) : σ ⊆ Finset.Iic k := fun i hi ↦
    Finset.mem_Iic.2 (Finset.le_sup (f := _root_.id) (hσ hi))
  refine ⟨C, k, fun φ ψ ↦ (hC φ ψ).trans ?_⟩
  gcongr
  · exact Seminorm.le_def.1 (Finset.sup_mono (hle Finset.subset_union_left)) φ
  · exact Seminorm.le_def.1 (Finset.sup_mono (hle Finset.subset_union_right)) ψ

end LinearMap
