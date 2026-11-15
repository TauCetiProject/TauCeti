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
* `ContDiffMapSupportedIn.continuous_of_continuous_iteratedFDeriv`,
  `TestFunction.continuous_of_continuous_iteratedFDeriv`: a family of test functions supported in a
  common compact set, whose derivatives of order at most `n` are jointly continuous in the
  parameter and the point, is continuous.
* `TestFunction.continuous_of_contDiff_uncurry`: in particular, so is a family of test functions
  supported in a common compact subset of `Ω` and jointly `Cⁿ` in the parameter and the point.

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
on `Ω` are all supported in a fixed compact subset `K` of `Ω`, and for every order
`k ≤ n` the `k`-th derivatives of the `φ i` converge uniformly to that of `ψ`, then `φ i → ψ` in
the LF topology of `𝓓^{n}(Ω, F)`. -/
theorem tendsto_of_tendstoUniformly_iteratedFDeriv {ι : Type*} {l : Filter ι}
    {φ : ι → 𝓓^{n}(Ω, F)} {ψ : 𝓓^{n}(Ω, F)} {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hφK : ∀ i, tsupport (φ i) ⊆ K)
    (h : ∀ k : ℕ, (k : ℕ∞) ≤ n →
      TendstoUniformly (fun i ↦ iteratedFDeriv ℝ k (φ i)) (iteratedFDeriv ℝ k ψ) l) :
    Tendsto φ l (𝓝 ψ) := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  have hψK : tsupport ψ ⊆ K := by
    refine closure_minimal (fun x hx ↦ ?_) hK.isClosed
    by_contra hxK
    refine hx ?_
    have h0 := (h 0 (by simp)).tendsto_at x
    have hz : ∀ i, iteratedFDeriv ℝ 0 (φ i) x = 0 := fun i ↦ by
      ext m
      simp [iteratedFDeriv_zero_apply,
        image_eq_zero_of_notMem_tsupport fun hmem ↦ hxK (hφK i hmem)]
    simp_rw [hz] at h0
    have := tendsto_nhds_unique h0 tendsto_const_nhds
    simpa [iteratedFDeriv_zero_apply] using congrArg (fun f ↦ f 0) this
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

/-- **Continuity of families with continuous jets.** Let `φ y`, for `y` in a topological space
`Y`, be `Cⁿ` functions supported in a compact set `K`. If for every order `k ≤ n` the `k`-th
derivative `(y, x) ↦ D^k (φ y) x` is jointly continuous, then `y ↦ φ y` is continuous for the
topology of `𝓓^{n}_{K}(E, F)`. -/
theorem _root_.ContDiffMapSupportedIn.continuous_of_continuous_iteratedFDeriv {Y : Type*}
    [TopologicalSpace Y] {K : Compacts E} {φ : Y → 𝓓^{n}_{K}(E, F)}
    (hφ : ∀ k : ℕ, (k : ℕ∞) ≤ n → Continuous fun p : Y × E ↦ iteratedFDeriv ℝ k (φ p.1) p.2) :
    Continuous φ := by
  refine continuous_iff_continuousAt.2 fun y₀ ↦ ?_
  refine ((ContDiffMapSupportedIn.withSeminorms ℝ E F n K).tendsto_nhds φ (φ y₀)).2
    fun k ε hε ↦ ?_
  by_cases hk : (k : ℕ∞) ≤ n
  swap
  · refine Eventually.of_forall fun y ↦ lt_of_le_of_lt ?_ hε
    exact (ContDiffMapSupportedIn.seminorm_le_iff ℝ le_rfl k (φ y - φ y₀)).2 fun h ↦ absurd h hk
  -- By the tube lemma, the `k`-th derivatives converge uniformly on `K`: near each `(y₀, x)`,
  -- the `k`-th derivative at `y` is `ε / 2`-close to the one at `y₀`.
  have hclose : ∀ x ∈ (K : Set E), ∀ᶠ p : Y × E in 𝓝 (y₀, x),
      ‖iteratedFDeriv ℝ k (φ p.1) p.2 - iteratedFDeriv ℝ k (φ y₀) p.2‖ < ε / 2 := by
    intro x _
    have hc : Continuous fun p : Y × E ↦
        iteratedFDeriv ℝ k (φ p.1) p.2 - iteratedFDeriv ℝ k (φ y₀) p.2 :=
      (hφ k hk).sub ((hφ k hk).comp (continuous_const.prodMk continuous_snd))
    have h0 := hc.tendsto (y₀, x)
    simp only [sub_self] at h0
    exact (tendsto_norm_zero.comp h0).eventually (gt_mem_nhds (half_pos hε))
  have hk' : (k : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
  filter_upwards [K.isCompact.eventually_forall_of_forall_eventually (P := fun y x ↦
    ‖iteratedFDeriv ℝ k (φ y) x - iteratedFDeriv ℝ k (φ y₀) x‖ < ε / 2) hclose] with y hy
  refine lt_of_le_of_lt ((ContDiffMapSupportedIn.seminorm_le_iff ℝ (half_pos hε).le k
    (φ y - φ y₀)).2
    fun _ x hx ↦ ?_) (half_lt_self hε)
  rw [FunLike.coe_sub, iteratedFDeriv_sub_apply ((φ y).contDiff.contDiffAt.of_le hk')
    ((φ y₀).contDiff.contDiffAt.of_le hk')]
  exact (hy x hx).le

/-- **Continuity of families of test functions with continuous jets.** Let `φ y`, for `y` in a
topological space `Y`, be test functions on `Ω` all supported in a fixed compact subset `K` of
`Ω`. If for every order `k ≤ n` the `k`-th derivative `(y, x) ↦ D^k (φ y) x` is jointly
continuous, then `y ↦ φ y` is continuous for the LF topology of `𝓓^{n}(Ω, F)`. -/
theorem continuous_of_continuous_iteratedFDeriv {Y : Type*} [TopologicalSpace Y]
    {φ : Y → 𝓓^{n}(Ω, F)} {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hφK : ∀ y, tsupport (φ y) ⊆ K)
    (hφ : ∀ k : ℕ, (k : ℕ∞) ≤ n → Continuous fun p : Y × E ↦ iteratedFDeriv ℝ k (φ p.1) p.2) :
    Continuous φ := by
  let K' : Compacts E := ⟨K, hK⟩
  let φK : Y → 𝓓^{n}_{K'}(E, F) := fun y ↦
    .of_support_subset (φ y).contDiff ((subset_tsupport _).trans (hφK y))
  have hφK' (y : Y) : ⇑(φK y) = φ y := funext <| ContDiffMapSupportedIn.coe_of_support_subset _ _
  have hc : Continuous φK :=
    ContDiffMapSupportedIn.continuous_of_continuous_iteratedFDeriv fun k hk ↦ by
      simpa only [hφK'] using hφ k hk
  refine ((continuous_ofSupportedIn hKΩ).comp hc).congr fun y ↦ ?_
  ext x
  simp [φK]

/-- **Continuity of jointly smooth families of test functions.** Let `φ p`, for `p` in a real
normed space `P`, be test functions on `Ω` all supported in a fixed compact subset `K` of `Ω`. If
`(p, x) ↦ φ p x` is `Cⁿ` on `P × E`, then `p ↦ φ p` is continuous for the LF topology of
`𝓓^{n}(Ω, F)`. -/
theorem continuous_of_contDiff_uncurry {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {φ : P → 𝓓^{n}(Ω, F)} {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hφK : ∀ p, tsupport (φ p) ⊆ K) (hφ : ContDiff ℝ n fun q : P × E ↦ φ q.1 q.2) :
    Continuous φ := by
  refine continuous_of_continuous_iteratedFDeriv hK hKΩ hφK fun k hk ↦ ?_
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
  simp only [hD]
  exact L.continuous.comp (hφ.continuous_iteratedFDeriv hk')

end TestFunction
