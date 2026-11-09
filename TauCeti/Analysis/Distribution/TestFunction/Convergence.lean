/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Convergence of test functions with a common compact support

Mathlib's LF topology on the test functions `𝓓^{n}(Ω, F)` is the finest locally convex topology
making every inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` of the tests supported in a compact
`K ⊆ Ω` continuous, and the topology of `𝓓^{n}_{K}(E, F)` is that of uniform convergence of all
derivatives of order at most `n`. Consequently a family of test functions supported in one fixed
compact subset of `Ω` converges as soon as each of its derivatives of order at most `n` converges
uniformly. This is the usual way to prove convergence in `𝓓^{n}(Ω, F)` concretely, for instance for
approximations by mollification or by truncated Fourier series. In particular a family of test
functions depending jointly smoothly on a parameter, with a common compact support, depends
continuously on the parameter.

## Main declarations

* `TestFunction.tendsto_of_tendstoUniformly_iteratedFDeriv`: test functions supported in a common
  compact subset of `Ω` whose derivatives of order at most `n` converge uniformly converge in
  `𝓓^{n}(Ω, F)`.
* `TestFunction.continuous_of_contDiff_uncurry`: a family of test functions supported in a common
  compact subset of `Ω` and jointly `Cⁿ` in the parameter and the point is continuous.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1 (the topology of
  test functions).
-/

public section

open Filter TopologicalSpace
open scoped Distributions Topology

namespace TestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}

/-- **Convergence of test functions with a common compact support.** If the test functions `φ i`
and `ψ` on `Ω` are all supported in a fixed compact subset `K` of `Ω`, and for every order
`k ≤ n` the `k`-th derivatives of the `φ i` converge uniformly to that of `ψ`, then `φ i → ψ` in
the LF topology of `𝓓^{n}(Ω, F)`. -/
theorem tendsto_of_tendstoUniformly_iteratedFDeriv {ι : Type*} {l : Filter ι}
    {φ : ι → 𝓓^{n}(Ω, F)} {ψ : 𝓓^{n}(Ω, F)} {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hφK : ∀ i, tsupport (φ i) ⊆ K) (hψK : tsupport ψ ⊆ K)
    (h : ∀ k : ℕ, (k : ℕ∞) ≤ n →
      TendstoUniformly (fun i ↦ iteratedFDeriv ℝ k (φ i)) (iteratedFDeriv ℝ k ψ) l) :
    Tendsto φ l (𝓝 ψ) := by
  let K' : Compacts E := ⟨K, hK⟩
  -- The same functions, as tests supported in `K`.
  let φK : ι → 𝓓^{n}_{K'}(E, F) := fun i ↦
    .of_support_subset (φ i).contDiff ((subset_tsupport _).trans (hφK i))
  let ψK : 𝓓^{n}_{K'}(E, F) := .of_support_subset ψ.contDiff ((subset_tsupport _).trans hψK)
  have hlim : Tendsto φK l (𝓝 ψK) := by
    rw [(ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
      ℝ).isEmbedding.tendsto_nhds_iff]
    refine tendsto_pi_nhds.2 fun k ↦ BoundedContinuousFunction.tendsto_iff_tendstoUniformly.2 ?_
    simp only [Function.comp_apply, ContinuousLinearMap.pi_apply,
      ContDiffMapSupportedIn.structureMapCLM_apply, φK, ψK]
    split_ifs with hk
    · exact h k hk
    · exact tendsto_const_nhds.tendstoUniformly_const
  have ht := ((continuous_ofSupportedIn hKΩ).tendsto ψK).comp hlim
  have hφ : (ofSupportedIn hKΩ ∘ φK) = φ := funext fun i ↦ by
    ext x
    simp [φK]
  have hψ : ofSupportedIn hKΩ ψK = ψ := by
    ext x
    simp [ψK]
  rwa [hφ, hψ] at ht

/-- **Continuity of jointly smooth families of test functions.** Let `φ p`, for `p` in a real
normed space `P`, be test functions on `Ω` all supported in a fixed compact subset `K` of `Ω`. If
`(p, x) ↦ φ p x` is `Cⁿ` on `P × E`, then `p ↦ φ p` is continuous for the LF topology of
`𝓓^{n}(Ω, F)`. -/
theorem continuous_of_contDiff_uncurry {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {φ : P → 𝓓^{n}(Ω, F)} {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hφK : ∀ p, tsupport (φ p) ⊆ K) (hφ : ContDiff ℝ n fun q : P × E ↦ φ q.1 q.2) :
    Continuous φ := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦
    tendsto_of_tendstoUniformly_iteratedFDeriv hK hKΩ hφK (hφK p₀) fun k hk ↦ ?_
  have hk' : (k : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
  -- The `k`-th derivative in the point variable is the `k`-th derivative on `P × E` restricted
  -- to the directions of `E`, hence jointly continuous in `(p, x)`.
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (ι := Fin k)
    (F := F) fun _ ↦ ContinuousLinearMap.inr ℝ P E
  have hD (p : P) (x : E) :
      iteratedFDeriv ℝ k (φ p) x = L (iteratedFDeriv ℝ k (fun q : P × E ↦ φ q.1 q.2) (p, x)) := by
    have h : (φ p : E → F) =
        (fun q : P × E ↦ φ ((p, 0) + q).1 ((p, 0) + q).2) ∘ ContinuousLinearMap.inr ℝ P E := by
      funext y
      simp
    have hf : ContDiff ℝ n fun q : P × E ↦ φ ((p, 0) + q).1 ((p, 0) + q).2 :=
      hφ.comp (contDiff_const.add contDiff_id)
    rw [h, ContinuousLinearMap.iteratedFDeriv_comp_right _ hf _ hk',
      iteratedFDeriv_comp_add_left (f := fun q : P × E ↦ φ q.1 q.2)]
    simp [L]
  have hcont : Continuous fun q : P × E ↦ iteratedFDeriv ℝ k (φ q.1) q.2 := by
    simp only [hD]
    exact L.continuous.comp (hφ.continuous_iteratedFDeriv hk')
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  -- Uniformly on `K` by compactness; outside `K` all the derivatives vanish.
  obtain ⟨v, hv, hvK⟩ := hK.mem_uniformity_of_prod (f := fun p x ↦ iteratedFDeriv ℝ k (φ p) x)
    hcont.continuousOn (Set.mem_univ p₀) (Metric.dist_mem_uniformity hε)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with p hp x
  by_cases hx : x ∈ K
  · rw [dist_comm]
    exact hvK p hp x hx
  · have hzero (q : P) : iteratedFDeriv ℝ k (φ q) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφK q (tsupport_iteratedFDeriv_subset k h))
    simpa [hzero] using hε

end TestFunction
