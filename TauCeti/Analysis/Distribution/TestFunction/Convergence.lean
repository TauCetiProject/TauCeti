/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Convergence of test functions with a common compact support

Mathlib's LF topology on the test functions `𝓓^{n}(Ω, F)` is the finest locally convex topology
making every inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` of the tests supported in a compact
`K ⊆ Ω` continuous, and the topology of `𝓓^{n}_{K}(E, F)` is that of uniform convergence of all
derivatives of order at most `n`. Consequently a family of test functions supported in one fixed
compact subset of `Ω` converges as soon as each of its derivatives of order at most `n` converges
uniformly. This is the usual way to prove convergence in `𝓓^{n}(Ω, F)` concretely, for instance for
approximations by mollification, by truncated Fourier series, or by multiplying a fixed cutoff by
locally `Cⁿ` functions whose derivatives converge uniformly on the cutoff's support. In particular a
family of test functions depending jointly smoothly on a parameter, with a common compact support,
depends continuously on the parameter.

## Main declarations

* `TestFunction.tendsto_of_tendstoUniformly_iteratedFDeriv`: test functions supported in a common
  compact subset of `Ω` whose derivatives of order at most `n` converge uniformly converge in
  `𝓓^{n}(Ω, F)`.
* `TestFunction.tendsto_smulOfContDiffOn`: multiplying a fixed scalar cutoff `χ ∈ 𝓓^{n}(Ω, ℝ)` by
  functions `g i` that are `Cⁿ` on an open neighbourhood of `tsupport χ` converges in `𝓓^{n}(Ω, F)`
  whenever the derivatives of `g i` up to order `n` converge uniformly on `tsupport χ`.
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

/-- Pointwise Leibniz bound for the `k`-th derivative of
`χ.smulOfContDiffOn hU hχU hg₁ - χ.smulOfContDiffOn hU hχU hg₂`. -/
private theorem norm_iteratedFDeriv_smulOfContDiffOn_sub_le (χ : 𝓓^{n}(Ω, ℝ)) {U : Set E}
    (hU : IsOpen U) (hχU : tsupport (χ : E → ℝ) ⊆ U) {g₁ g₂ : E → F}
    (hg₁ : ContDiffOn ℝ n g₁ U) (hg₂ : ContDiffOn ℝ n g₂ U) {k : ℕ} (hk : (k : ℕ∞) ≤ n)
    {M : ℕ → ℝ} (hM0 : ∀ j ∈ Finset.range (k + 1), 0 ≤ M j)
    (hM : ∀ j ∈ Finset.range (k + 1), ∀ y, ‖iteratedFDeriv ℝ j (χ : E → ℝ) y‖ ≤ M j)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hg_le : ∀ j ∈ Finset.range (k + 1), ∀ y ∈ tsupport (χ : E → ℝ),
      ‖iteratedFDeriv ℝ (k - j) g₁ y - iteratedFDeriv ℝ (k - j) g₂ y‖ ≤ δ)
    (y : E) :
    ‖iteratedFDeriv ℝ k (χ.smulOfContDiffOn hU hχU hg₁ : E → F) y -
        iteratedFDeriv ℝ k (χ.smulOfContDiffOn hU hχU hg₂ : E → F) y‖ ≤
      (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * M j) * δ := by
  let ψ₁ := χ.smulOfContDiffOn hU hχU hg₁
  let ψ₂ := χ.smulOfContDiffOn hU hχU hg₂
  have hk' : (k : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
  rw [← iteratedFDeriv_sub_apply (ψ₁.contDiff.contDiffAt.of_le hk')
    (ψ₂.contDiff.contDiffAt.of_le hk')]
  by_cases hy : y ∈ tsupport (χ : E → ℝ)
  · have hsub_eq : ((ψ₁ : E → F) - (ψ₂ : E → F)) = fun z ↦ χ z • (g₁ - g₂) z := by
      ext z
      simp [ψ₁, ψ₂, smul_sub]
    have hyU : y ∈ U := hχU hy
    have hle := norm_iteratedFDerivWithin_smul_le χ.contDiff.contDiffOn (hg₁.sub hg₂)
      hU.uniqueDiffOn hyU (n := k) hk'
    rw [iteratedFDerivWithin_of_isOpen k hU hyU] at hle
    rw [hsub_eq]
    refine hle.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj ↦ ?_
    have hkj : ((k - j : ℕ) : WithTop ℕ∞) ≤ n :=
      le_trans (by exact_mod_cast Nat.sub_le k j) hk'
    rw [iteratedFDerivWithin_of_isOpen j hU hyU, iteratedFDerivWithin_of_isOpen (k - j) hU hyU,
      ← Pi.sub_def,
      iteratedFDeriv_sub_apply ((hg₁.contDiffAt (hU.mem_nhds hyU)).of_le hkj)
        ((hg₂.contDiffAt (hU.mem_nhds hyU)).of_le hkj), mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hM j hj y) (hg_le j hj y hy) (norm_nonneg _) (hM0 j hj))
      (Nat.cast_nonneg _)
  · have h0 : ((ψ₁ : E → F) - (ψ₂ : E → F)) =ᶠ[𝓝 y] 0 := by
      filter_upwards [(isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hy] with z hz
      simp [ψ₁, ψ₂, image_eq_zero_of_notMem_tsupport hz]
    rw [(h0.iteratedFDeriv ℝ k).eq_of_nhds]
    simpa using mul_nonneg
      (Finset.sum_nonneg fun j hj ↦ mul_nonneg (Nat.cast_nonneg _) (hM0 j hj)) hδ0

/-- **Convergence of cutoff products in `𝓓^{n}(Ω, F)`.** Let `χ ∈ 𝓓^{n}(Ω, ℝ)` be a fixed cutoff
supported in an open set `U`, and let `g i`, `g₀ : E → F` be `Cⁿ` on `U`. If for every order
`k ≤ n` the `k`-th derivatives of `g i` converge uniformly to that of `g₀` on `tsupport χ`, then
`χ • g i → χ • g₀` in the LF topology of `𝓓^{n}(Ω, F)`. -/
theorem tendsto_smulOfContDiffOn {ι : Type*} {l : Filter ι} (χ : 𝓓^{n}(Ω, ℝ))
    {U : Set E} (hU : IsOpen U) (hχU : tsupport (χ : E → ℝ) ⊆ U) {g : ι → E → F} {g₀ : E → F}
    (hg : ∀ i, ContDiffOn ℝ n (g i) U) (hg₀ : ContDiffOn ℝ n g₀ U)
    (hlim : ∀ k : ℕ, (k : ℕ∞) ≤ n →
      TendstoUniformlyOn (fun i ↦ iteratedFDeriv ℝ k (g i)) (iteratedFDeriv ℝ k g₀) l
        (tsupport (χ : E → ℝ))) :
    Tendsto (fun i ↦ χ.smulOfContDiffOn hU hχU (hg i)) l
      (𝓝 (χ.smulOfContDiffOn hU hχU hg₀)) := by
  refine tendsto_of_tendstoUniformly_iteratedFDeriv χ.hasCompactSupport χ.tsupport_subset
    (fun i ↦ χ.tsupport_smulOfContDiffOn_subset hU hχU (hg i)) fun k hk ↦ ?_
  have hχb (j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧
      (j ∈ Finset.range (k + 1) → ∀ y, ‖iteratedFDeriv ℝ j (χ : E → ℝ) y‖ ≤ M) := by
    by_cases hj : j ∈ Finset.range (k + 1)
    · have hjk : (j : ℕ∞) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hjn : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hjk.trans hk
      obtain ⟨M, hM⟩ := (χ.hasCompactSupport.iteratedFDeriv j).exists_bound_of_continuous
        (χ.contDiff.continuous_iteratedFDeriv hjn)
      exact ⟨max M 0, le_max_right _ _, fun _ y ↦ (hM y).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h ↦ absurd h hj⟩
  choose M hM0 hM using hχb
  set C : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * M j + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (hM0 j)) zero_lt_one
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hev : ∀ᶠ i in l, ∀ j ∈ Finset.range (k + 1), ∀ y ∈ tsupport (χ : E → ℝ),
      ‖iteratedFDeriv ℝ (k - j) (g i) y - iteratedFDeriv ℝ (k - j) g₀ y‖ < ε / C := by
    rw [Filter.eventually_all_finset]
    intro j _
    have hkj : ((k - j : ℕ) : ℕ∞) ≤ n :=
      le_trans (by exact_mod_cast Nat.sub_le k j) hk
    simpa [dist_eq_norm, norm_sub_rev] using
      Metric.tendstoUniformlyOn_iff.1 (hlim (k - j) hkj) (ε / C) (div_pos hε hC)
  filter_upwards [hev] with i hi y
  rw [dist_eq_norm, norm_sub_rev]
  refine (norm_iteratedFDeriv_smulOfContDiffOn_sub_le χ hU hχU (hg i) hg₀ hk (fun j _ ↦ hM0 j)
    hM (div_pos hε hC).le (fun j hj z hz ↦ (hi j hj z hz).le) y).trans_lt ?_
  exact (mul_lt_mul_of_pos_right (lt_add_one _) (div_pos hε hC)).trans_eq
    (mul_div_cancel₀ ε hC.ne')

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
