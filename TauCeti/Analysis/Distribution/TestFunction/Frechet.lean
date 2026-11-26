/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Distribution.TestFunction
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
sets, `LinearMap.exists_schwartzKernel_supportedIn`. Conversely, a bilinear map on test functions on
open sets satisfying such a bound on each pair of compact sets is continuous in each variable
(`LinearMap.continuous_apply_left_of_bound`, `LinearMap.continuous_apply_right_of_bound`).

## Main results

* `ContDiffMapSupportedIn.instCompleteSpace`: `𝓓^{n}_{K}(E, F)` is complete when `F` is.
* `ContDiffMapSupportedIn.instBaireSpace`: with the countably generated uniformity
  (`ContDiffMapSupportedIn.instIsCountablyGeneratedUniformity`), completeness makes
  `𝓓^{n}_{K}(E, F)` completely metrizable, hence a Baire space and barrelled.
* `ContDiffMapSupportedIn.supSeminorm_apply_eq_of_scalars`: the seminorms `N_{≤i}` do not depend
  on the field of scalars.
* `ContDiffMapSupportedIn.supSeminorm_mono`: the seminorms `N_{≤i}` increase with `i`.
* `ContDiffMapSupportedIn.supSeminorm_eq_zero_iff`: each seminorm `N_{≤i}` vanishes only at zero.
* `ContDiffMapSupportedIn.withSeminorms_supSeminorm_self`: for finite `ℓ`, the single seminorm
  `max_{j ≤ ℓ} N_j` defines the topology of `𝓓^{ℓ}_{K}(E, F)`.
* `LinearMap.exists_bound_supportedIn_of_continuous`: a separately continuous bilinear map on two
  such spaces is bounded by `C N_{≤k}(φ) N_{≤k}(ψ)` for some `C` and `k`.
* `LinearMap.exists_bound_ofSupportedIn_of_continuous`: the same bound on each pair of compact
  sets for a separately continuous bilinear map on test functions on open sets.
* `LinearMap.continuous_apply_left_of_bound`, `LinearMap.continuous_apply_right_of_bound`:
  conversely, a bilinear map on test functions on open sets with such a bound on each pair of
  compact sets is continuous in each variable.
* `ContDiffMapSupportedIn.supSeminorm_le_of_forall_norm_iteratedFDeriv_le`: a uniform bound `B`
  on the derivatives of order at most `r` bounds the seminorm `N_{≤r}` by `B`.

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

section Scalars

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The seminorms `N_j` do not depend on the field of scalars. -/
theorem seminorm_apply_eq_of_scalars (j : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.seminorm 𝕜 E F n K j f =
      ContDiffMapSupportedIn.seminorm ℝ E F n K j f := by
  rw [ContDiffMapSupportedIn.seminorm_apply, ContDiffMapSupportedIn.seminorm_apply,
    structureMapCLM_eq_of_scalars 𝕜 ℝ]

/-- The seminorms `max_{j ≤ i} N_j` do not depend on the field of scalars. -/
theorem supSeminorm_apply_eq_of_scalars (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K i f =
      ContDiffMapSupportedIn.supSeminorm ℝ E F n K i f :=
  le_antisymm
    (Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun _ hj ↦
      (seminorm_apply_eq_of_scalars _ f).trans_le (Seminorm.le_finset_sup_apply hj))
    (Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun _ hj ↦
      (seminorm_apply_eq_of_scalars _ f).symm.trans_le (Seminorm.le_finset_sup_apply hj))

/-- The seminorms `max_{j ≤ i} N_j` increase with `i`. -/
theorem supSeminorm_mono : Monotone (ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K) := by
  intro i j hij
  -- By definition `max_{k ≤ i} N_k` is the supremum of the `N_k` over `Finset.Iic i`.
  unfold ContDiffMapSupportedIn.supSeminorm
  exact Finset.sup_mono (Finset.Iic_subset_Iic.2 hij)

/-- Each seminorm `max_{j ≤ i} N_j` vanishes only at zero, since it bounds the sup norm `N_0`. -/
theorem supSeminorm_eq_zero_iff (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K i f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ext fun x ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  have h0 := (norm_apply_le_seminorm 𝕜 (f := f) (x := x)).trans
    ((Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 (Nat.zero_le i))).trans h.le)
  simpa using h0

end Scalars

end ContDiffMapSupportedIn

/-! ### Finite order -/

namespace ContDiffMapSupportedIn

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  {ℓ : ℕ} {K : Compacts E}

variable (𝕜) in
/-- For a finite order `ℓ`, the seminorms of order above `ℓ` vanish, so every seminorm
`max_{j ≤ i} N_j` is at most `max_{j ≤ ℓ} N_j`. -/
theorem supSeminorm_le_supSeminorm_self (i : ℕ) (f : 𝓓^{ℓ}_{K}(E, F)) :
    ContDiffMapSupportedIn.supSeminorm 𝕜 E F ℓ K i f ≤
      ContDiffMapSupportedIn.supSeminorm 𝕜 E F ℓ K ℓ f := by
  refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun j _ ↦ ?_
  by_cases hjℓ : j ≤ ℓ
  · exact Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 hjℓ)
  · rw [ContDiffMapSupportedIn.seminorm_eq_bot_of_gt 𝕜 (by exact_mod_cast not_le.1 hjℓ)]
    exact apply_nonneg _ _

variable (𝕜 E F ℓ K) in
/-- **The `C^ℓ` norm defines the topology.** For a finite order `ℓ`, the single seminorm
`max_{j ≤ ℓ} N_j` defines the topology of `𝓓^{ℓ}_{K}(E, F)`. -/
theorem withSeminorms_supSeminorm_self :
    WithSeminorms fun _ : Unit ↦ ContDiffMapSupportedIn.supSeminorm 𝕜 E F ℓ K ℓ := by
  refine (ContDiffMapSupportedIn.withSeminorms' 𝕜 E F ℓ K).congr (fun _ ↦ ⟨{ℓ}, 1, ?_⟩)
    fun i ↦ ⟨{()}, 1, ?_⟩
  · rw [Finset.sup_singleton, one_smul]
    rfl
  · rw [Finset.sup_singleton, one_smul]
    exact supSeminorm_le_supSeminorm_self 𝕜 i

/-- For a finite order `ℓ`, the uniform structure of `𝓓^{ℓ}_{K}(E, F)` is the one of the
seminorm `max_{j ≤ ℓ} N_j`. -/
theorem uniformSpace_eq_supSeminorm_self :
    (uniformSpace : UniformSpace 𝓓^{ℓ}_{K}(E, F)) =
      (ContDiffMapSupportedIn.supSeminorm ℝ E F ℓ K ℓ).toSeminormedAddCommGroup.toUniformSpace := by
  rw [(SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf _).1
    (withSeminorms_supSeminorm_self ℝ E F ℓ K), ciInf_unique]

end ContDiffMapSupportedIn

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {K : Compacts E}

/-- A function supported in `K` whose derivatives of order at most `r` are bounded by `B`
has `sup_{i ≤ r} N_i χ ≤ B`. -/
theorem supSeminorm_le_of_forall_norm_iteratedFDeriv_le {χ : 𝓓_{K}(E, F)} {r : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i ≤ r, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B) :
    ContDiffMapSupportedIn.supSeminorm ℂ E F ⊤ K r χ ≤ B :=
  Seminorm.finset_sup_apply_le hB fun i hi ↦
    (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ hB i χ).2 fun x _ ↦ h i (Finset.mem_Iic.1 hi) x

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

/-- A bilinear map `B` on test functions on open sets `Ω ⊆ E₁` and `O ⊆ E₂`, continuous in each
variable, satisfies the estimate of the Schwartz kernel theorem: for all compact sets `K₁ ⊆ Ω` and
`K₂ ⊆ O` some `C` and `k` give `‖B φ ψ‖ ≤ C N_{≤k}(φ) N_{≤k}(ψ)` for `φ` supported in `K₁` and `ψ`
supported in `K₂`. -/
theorem exists_bound_ofSupportedIn_of_continuous {Ω : Opens E₁} {O : Opens E₂}
    (B : 𝓓^{n₁}(Ω, F₁) →ₗ[𝕜] 𝓓^{n₂}(O, F₂) →ₗ[𝕜] G)
    (h₁ : ∀ ψ, Continuous fun φ ↦ B φ ψ) (h₂ : ∀ φ, Continuous (B φ))
    (K₁ : Compacts E₁) (K₂ : Compacts E₂) (hK₁ : (K₁ : Set E₁) ⊆ Ω) (hK₂ : (K₂ : Set E₂) ⊆ O) :
    ∃ (C : ℝ) (k : ℕ), ∀ φ ψ,
      ‖B (TestFunction.ofSupportedIn hK₁ φ) (TestFunction.ofSupportedIn hK₂ ψ)‖ ≤
        C * ContDiffMapSupportedIn.supSeminorm 𝕜 E₁ F₁ n₁ K₁ k φ *
          ContDiffMapSupportedIn.supSeminorm 𝕜 E₂ F₂ n₂ K₂ k ψ :=
  exists_bound_supportedIn_of_continuous
    (B.compl₁₂ (TestFunction.ofSupportedInCLM 𝕜 hK₁).toLinearMap
      (TestFunction.ofSupportedInCLM 𝕜 hK₂).toLinearMap)
    (fun _ ↦ (h₁ _).comp (TestFunction.continuous_ofSupportedIn hK₁))
    (fun _ ↦ (h₂ _).comp (TestFunction.continuous_ofSupportedIn hK₂))

end LinearMap

namespace LinearMap

open TestFunction

variable {𝕜 E D F₁ F₂ G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedSpace 𝕜 F₁] [IsScalarTower ℝ 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedSpace 𝕜 F₂] [IsScalarTower ℝ 𝕜 F₂]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G]
  {n₁ n₂ : ℕ∞} {Ω : Opens E} {O : Opens D}

/-- Conversely to `LinearMap.exists_bound_ofSupportedIn_of_continuous`, a bilinear map `B` on test
functions on open sets `Ω` and `O` such that for all compact sets `K₁ ⊆ Ω` and `K₂ ⊆ O` some `C`
and `k` give `‖B φ ψ‖ ≤ C N_{≤k}(φ) N_{≤k}(ψ)` for `φ` supported in `K₁` and `ψ` supported in
`K₂` is continuous in its first variable. -/
theorem continuous_apply_left_of_bound (B : 𝓓^{n₁}(Ω, F₁) →ₗ[𝕜] 𝓓^{n₂}(O, F₂) →ₗ[𝕜] G)
    (hB : ∀ (K₁ : Compacts E) (K₂ : Compacts D) (hK₁ : (K₁ : Set E) ⊆ Ω)
      (hK₂ : (K₂ : Set D) ⊆ O), ∃ (C : ℝ) (k : ℕ), ∀ φ ψ,
        ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
          C * ContDiffMapSupportedIn.supSeminorm 𝕜 E F₁ n₁ K₁ k φ *
            ContDiffMapSupportedIn.supSeminorm 𝕜 D F₂ n₂ K₂ k ψ)
    (ψ : 𝓓^{n₂}(O, F₂)) : Continuous fun φ ↦ B φ ψ := by
  -- `ψ` is supported in the compact set `tsupport ψ`, so on the tests supported in a compact `K₁`
  -- the map `φ ↦ B φ ψ` is bounded by a multiple of one seminorm.
  let K₂ : Compacts D := ⟨tsupport ψ, ψ.hasCompactSupport⟩
  let ψ₀ : 𝓓^{n₂}_{K₂}(D, F₂) := .of_support_subset ψ.contDiff (subset_tsupport _)
  have hψ : ofSupportedIn ψ.tsupport_subset ψ₀ = ψ := TestFunction.ext fun _ ↦ rfl
  refine (TestFunction.continuous_iff_continuous_comp (B.flip ψ)).2 fun K₁ hK₁ ↦ ?_
  obtain ⟨C, k, hC⟩ := hB K₁ K₂ hK₁ ψ.tsupport_subset
  have h (φ : 𝓓^{n₁}_{K₁}(E, F₁)) : ‖B (ofSupportedIn hK₁ φ) ψ‖ ≤
      ((C * ContDiffMapSupportedIn.supSeminorm 𝕜 D F₂ n₂ K₂ k ψ₀).toNNReal : ℝ) *
        ContDiffMapSupportedIn.supSeminorm 𝕜 E F₁ n₁ K₁ k φ := by
    calc ‖B (ofSupportedIn hK₁ φ) ψ‖
        = ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn ψ.tsupport_subset ψ₀)‖ := by rw [hψ]
      _ ≤ C * ContDiffMapSupportedIn.supSeminorm 𝕜 E F₁ n₁ K₁ k φ *
            ContDiffMapSupportedIn.supSeminorm 𝕜 D F₂ n₂ K₂ k ψ₀ := hC φ ψ₀
      _ ≤ _ := by
        rw [mul_right_comm, Real.coe_toNNReal']
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg _ _)
  exact WithSeminorms.continuous_normedSpace_rng G
    (ContDiffMapSupportedIn.withSeminorms' 𝕜 E F₁ n₁ K₁)
    ((B.flip ψ).comp (ofSupportedInCLM 𝕜 hK₁).toLinearMap)
    ⟨{k}, (C * ContDiffMapSupportedIn.supSeminorm 𝕜 D F₂ n₂ K₂ k ψ₀).toNNReal, fun φ ↦ by
      simpa [NNReal.smul_def] using h φ⟩

/-- Conversely to `LinearMap.exists_bound_ofSupportedIn_of_continuous`, a bilinear map `B` on test
functions on open sets `Ω` and `O` such that for all compact sets `K₁ ⊆ Ω` and `K₂ ⊆ O` some `C`
and `k` give `‖B φ ψ‖ ≤ C N_{≤k}(φ) N_{≤k}(ψ)` for `φ` supported in `K₁` and `ψ` supported in
`K₂` is continuous in its second variable. -/
theorem continuous_apply_right_of_bound (B : 𝓓^{n₁}(Ω, F₁) →ₗ[𝕜] 𝓓^{n₂}(O, F₂) →ₗ[𝕜] G)
    (hB : ∀ (K₁ : Compacts E) (K₂ : Compacts D) (hK₁ : (K₁ : Set E) ⊆ Ω)
      (hK₂ : (K₂ : Set D) ⊆ O), ∃ (C : ℝ) (k : ℕ), ∀ φ ψ,
        ‖B (ofSupportedIn hK₁ φ) (ofSupportedIn hK₂ ψ)‖ ≤
          C * ContDiffMapSupportedIn.supSeminorm 𝕜 E F₁ n₁ K₁ k φ *
            ContDiffMapSupportedIn.supSeminorm 𝕜 D F₂ n₂ K₂ k ψ)
    (φ : 𝓓^{n₁}(Ω, F₁)) : Continuous (B φ) := by
  refine continuous_apply_left_of_bound B.flip (fun K₂ K₁ hK₂ hK₁ ↦ ?_) φ
  obtain ⟨C, k, hC⟩ := hB K₁ K₂ hK₁ hK₂
  exact ⟨C, k, fun ψ φ ↦ by simpa only [flip_apply, mul_right_comm C] using hC φ ψ⟩

end LinearMap
