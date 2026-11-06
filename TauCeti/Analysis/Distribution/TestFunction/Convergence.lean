/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Convergence of test functions with a common compact support

Mathlib's LF topology on the test functions `𝓓^{n}(Ω, F)` is the finest locally convex topology
making every inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` of the tests supported in a compact
`K ⊆ Ω` continuous, and the topology of `𝓓^{n}_{K}(E, F)` is that of uniform convergence of all
derivatives of order at most `n`. Consequently a family of test functions supported in one fixed
compact subset of `Ω` converges as soon as each of its derivatives of order at most `n` converges
uniformly. This is the usual way to prove convergence in `𝓓^{n}(Ω, F)` concretely, for instance for
approximations by mollification or by truncated Fourier series.

## Main declarations

* `TestFunction.tendsto_of_tendstoUniformly_iteratedFDeriv`: test functions supported in a common
  compact subset of `Ω` whose derivatives of order at most `n` converge uniformly converge in
  `𝓓^{n}(Ω, F)`.

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

end TestFunction
