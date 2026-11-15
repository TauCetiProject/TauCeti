/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# The little Besov spaces

Schwartz functions lie in every inhomogeneous Besov space `B^s_{p,q}`, `q ≠ 0`
(`SchwartzMap.memBesov`, with the inclusion `SchwartzMap.toBesovSpaceCLM`). Their closure in
`B^s_{p,∞}` is the **little Besov space** `b^s_{p,∞}` (`TauCeti.BesovSpace.littleBesov`); at
`p = ∞` it is the little Hölder–Zygmund space `c^s`, the closure of the Schwartz functions in
`𝒞^s = B^s_{∞,∞}`. A general element of `B^s_{p,∞}` only has bounded weighted blocks
`2^{js} ‖Δⱼ u‖_p`; the elements of `b^s_{p,∞}` are characterised through their Littlewood–Paley
blocks `Δⱼ u` (`TauCeti.BesovSpace.mem_littleBesov_iff`): `u ∈ b^s_{p,∞}` exactly when

* the weighted blocks vanish at high frequency, `2^{js} ‖Δⱼ u‖_p → 0`, and
* every block `Δⱼ u` lies in the `Lᵖ` closure of the Schwartz functions.

For `p < ∞` the Schwartz functions are dense in `Lᵖ`, so the second condition is automatic and
`b^s_{p,∞}` is cut out by the decay of the weighted blocks alone
(`TauCeti.BesovSpace.mem_littleBesov_iff_tendsto`). At `p = ∞` the `L^∞` closure of the Schwartz
functions consists of the classes of the continuous functions vanishing at infinity, and the
second condition is not automatic: the constant function `1` has `Δⱼ 1 = 0` for `j ≥ 1`, but its
block `Δ₀ 1 = 1` does not vanish at infinity.

## The argument

Both conditions pass to limits in `B^s_{p,∞}`, because the `j`-th block is bounded by `2^{-js}`
times the Besov norm, and both hold for Schwartz functions. For a Schwartz function the first
holds because it also lies in `B^s_{p,1}`, where the weighted blocks are summable; the second
because `Δⱼ f` is again a Schwartz function.

Conversely, let `u` satisfy both conditions. Its low-pass truncation `S_N u = ∑_{j ≤ N} Δⱼ u` is an
`Lᵖ` function. Since `Δₖ S_N u = S_N Δₖ u`, the block `Δₖ (u - S_N u)` vanishes when `k + L ≤ N`,
where `L` is the almost-orthogonality range of the blocks, and in general has norm at most
`(1 + K) ‖Δₖ u‖_p`, where `K` bounds the low-pass truncations on `Lᵖ` uniformly in `N`. So
`‖u - S_N u‖_{B^s_{p,∞}} ≤ (1 + K) sup_{k > N - L} 2^{ks} ‖Δₖ u‖_p`, which tends to zero.
Next, `S_N u` lies in the `Lᵖ` closure of the Schwartz functions; let `g` be a Schwartz function
close to it in `Lᵖ`. The truncation `S_{N+L}` fixes `S_N u` and maps `g` to a Schwartz function,
and `S_{N+L} (S_N u - g)` has only finitely many nonzero blocks, so its Besov norm is at most a
constant, depending on `N`, times `‖S_N u - g‖_p`.

## Main declarations

* `TauCeti.BesovSpace.littleBesov`: the little Besov space `b^s_{p,∞}`, the closure of the
  Schwartz functions in `B^s_{p,∞}`; at `p = ∞` the little Hölder–Zygmund space `c^s`. It is
  closed and complete (`TauCeti.BesovSpace.isClosed_littleBesov`), as a set it is
  `TauCeti.BesovSpace.coe_littleBesov`, and it is the smallest closed subspace containing the
  Schwartz functions (`TauCeti.BesovSpace.littleBesov_le`).
* `TauCeti.BesovSpace.mem_littleBesov_iff`: the characterisation by the blocks, assembled from
  `TauCeti.BesovSpace.tendsto_rpow_mul_norm_block_of_mem_littleBesov`,
  `TauCeti.BesovSpace.block_mem_closure_of_mem_littleBesov` and
  `TauCeti.BesovSpace.mem_littleBesov_of_tendsto`.
* `TauCeti.BesovSpace.mem_littleBesov_iff_tendsto`: for `p < ∞`, by the decay of the weighted
  blocks alone.
* `TauCeti.BesovSpace.map_mem_littleBesov`: the embeddings of the Besov scale preserve the little
  spaces; in particular `TauCeti.BesovSpace.bumpEquiv_mem_littleBesov_iff` (independence of the
  bump function), `TauCeti.BesovSpace.inclusion_mem_littleBesov`,
  `TauCeti.BesovSpace.inclusionOfExponentLE_mem_littleBesov`, and
  `TauCeti.BesovSpace.inclusionOfLT_mem_littleBesov` (`B^s_{p,q} ⊆ b^{s'}_{p,∞}` for `s' < s` and
  `p < ∞`).

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, Section 2.3.3.
-/

public section

noncomputable section

open Filter Topology MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

namespace BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The little Besov space -/

variable (F φ s p) in
/-- The **little Besov space** `b^s_{p,∞}`: the closure of the Schwartz functions in
`B^s_{p,∞}`. At `p = ∞` it is the little Hölder–Zygmund space `c^s`. -/
def littleBesov : Submodule ℂ (BesovSpace F φ s p ∞) :=
  (LinearMap.range (SchwartzMap.toBesovSpaceCLM F φ s p ∞).toLinearMap).topologicalClosure

/-- The little Besov space is closed in `B^s_{p,∞}`. -/
instance isClosed_littleBesov : IsClosed (littleBesov F φ s p : Set (BesovSpace F φ s p ∞)) :=
  Submodule.isClosed_topologicalClosure _

/-- The little Besov space is complete, as a closed subspace of `B^s_{p,∞}`. -/
instance : CompleteSpace (littleBesov F φ s p) :=
  isClosed_littleBesov.completeSpace_coe

/-- As a set, the little Besov space is the closure of the image of the Schwartz functions. -/
theorem coe_littleBesov : (littleBesov F φ s p : Set (BesovSpace F φ s p ∞)) =
    closure (Set.range (SchwartzMap.toBesovSpaceCLM F φ s p ∞)) := by
  rw [littleBesov, Submodule.topologicalClosure_coe, LinearMap.coe_range,
    ContinuousLinearMap.coe_coe]

/-- Schwartz functions lie in the little Besov space. -/
@[simp]
theorem toBesovSpaceCLM_mem_littleBesov (f : 𝓢(E, F)) :
    SchwartzMap.toBesovSpaceCLM F φ s p ∞ f ∈ littleBesov F φ s p :=
  Submodule.le_topologicalClosure _ ⟨f, rfl⟩

/-- **Minimality.** The little Besov space is contained in every closed subspace of `B^s_{p,∞}`
containing the Schwartz functions. -/
theorem littleBesov_le {S : Submodule ℂ (BesovSpace F φ s p ∞)}
    (hS : IsClosed (S : Set (BesovSpace F φ s p ∞)))
    (h : ∀ f : 𝓢(E, F), SchwartzMap.toBesovSpaceCLM F φ s p ∞ f ∈ S) :
    littleBesov F φ s p ≤ S :=
  Submodule.topologicalClosure_minimal _ (by rintro _ ⟨f, rfl⟩; exact h f) hS

/-- **The weighted blocks of an element of `b^s_{p,∞}` vanish at high frequency:**
`2^{js} ‖Δⱼ u‖_p → 0`. -/
theorem tendsto_rpow_mul_norm_block_of_mem_littleBesov {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) :
    Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0) := by
  rw [← SetLike.mem_coe, coe_littleBesov] at hu
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨_, ⟨f, rfl⟩, hf⟩ := Metric.mem_closure_iff.1 hu (ε / 2) (half_pos hε)
  -- A Schwartz function also lies in `B^s_{p,1}`, with the same blocks.
  have hdecay : Tendsto (fun j : ℕ ↦
      2 ^ (s * j) * ‖(SchwartzMap.toBesovSpaceCLM F φ s p ∞ f).block j‖) atTop (𝓝 0) := by
    simpa only [block_toBesovSpaceCLM] using
      tendsto_rpow_mul_norm_block ENNReal.one_ne_top (SchwartzMap.toBesovSpaceCLM F φ s p 1 f)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hdecay (ε / 2) (half_pos hε)
  refine ⟨N, fun j hj ↦ ?_⟩
  set v := SchwartzMap.toBesovSpaceCLM F φ s p ∞ f
  have hv := hN j hj
  rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at hv ⊢
  rw [dist_eq_norm] at hf
  have hsub : 2 ^ (s * j) * ‖(u - v).block j‖ ≤ ‖u - v‖ := rpow_mul_norm_block_le _ j
  rw [block_sub] at hsub
  calc 2 ^ (s * j) * ‖u.block j‖
      ≤ 2 ^ (s * j) * ‖u.block j - v.block j‖ + 2 ^ (s * j) * ‖v.block j‖ := by
        rw [← mul_add]
        gcongr
        exact norm_le_norm_sub_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hsub.trans hf.le) hv
    _ = ε := add_halves ε

/-- **The blocks of an element of `b^s_{p,∞}` are limits of Schwartz functions in `Lᵖ`.** -/
theorem block_mem_closure_of_mem_littleBesov {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) (j : ℕ) :
    u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p) := by
  rw [← SetLike.mem_coe, coe_littleBesov] at hu
  refine map_mem_closure (f := fun x : BesovSpace F φ s p ∞ ↦ x.block j) (continuous_block j) hu ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨_, (block_toBesovSpaceCLM f j).symm⟩

/-- **Truncation.** If the weighted blocks of `u` tend to zero, then `u` is within `ε` of the
low-pass truncation `S_N u = ∑_{j ≤ N} Δⱼ u` for some `N`: away from the transition range the
blocks of `u - S_N u` are either zero or the small high-frequency blocks of `u`, and in the
transition range they are at most `(1 + K)` times those of `u`. -/
private theorem exists_toDistr_eq_sum_block_and_norm_sub_le {u : BesovSpace F φ s p ∞}
    (hdecay : Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ v : BesovSpace F φ s p ∞,
      v.toDistr = ((∑ j ∈ Finset.range (N + 1), u.block j : Lp F p (volume : Measure E)) :
        𝓢'(E, F)) ∧ ‖u - v‖ ≤ ε := by
  obtain ⟨L, hL⟩ := exists_sum_littlewoodPaleyBlock_littlewoodPaleyBlock (F := F) φ
  set K : ℝ := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  have hK0 : 0 ≤ K := integral_nonneg fun _ ↦ norm_nonneg _
  have hK := exists_sum_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ (p := p)
  obtain ⟨C, -, hC⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq_zero F φ
  -- Past `N₀` the weighted blocks are at most `ε / (1 + K)`.
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hdecay (ε / (1 + K)) (by positivity)
  set N := N₀ + L
  set w : Lp F p (volume : Measure E) := ∑ j ∈ Finset.range (N + 1), u.block j
  have hw : (w : 𝓢'(E, F)) =
      ∑ j ∈ Finset.range (N + 1), littlewoodPaleyBlock F φ j u.toDistr := by
    simp only [w, Lp.toTemperedDistribution_sum, coe_block]
  obtain ⟨v, hvw, -⟩ := hC s (N + L) w fun k hk ↦ by
    rw [hw]
    exact (hL k N).2 hk u.toDistr
  refine ⟨N, v, hvw, (norm_eq_ciSup _).trans_le (ciSup_le fun k ↦ ?_)⟩
  -- The block `Δₖ v = S_N Δₖ u` is the `Lᵖ` function `g`.
  obtain ⟨g, hg, hgu⟩ := hK N (u.block k)
  have hvk : v.block k = g := Lp.toTemperedDistribution_injective <| by
    simp only [coe_block, hvw, hw, map_sum, ← hg]
    exact Finset.sum_congr rfl fun j _ ↦ littlewoodPaleyBlock_comm φ k j u.toDistr
  rw [block_sub, hvk]
  rcases le_or_gt (k + L) N with hkN | hkN
  · -- Low frequencies: `S_N` fixes `Δₖ u`.
    have hgk : g = u.block k := Lp.toTemperedDistribution_injective <| by
      simp only [← hg, coe_block]
      exact (hL k N).1 hkN u.toDistr
    rw [hgk, sub_self, norm_zero, mul_zero]
    positivity
  · -- High frequencies: the weighted block of `u` is small.
    have hak := hN₀ k (by omega)
    rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at hak
    calc 2 ^ (s * k) * ‖u.block k - g‖ ≤ 2 ^ (s * k) * ((1 + K) * ‖u.block k‖) := by
          gcongr
          exact (norm_sub_le _ _).trans (by linarith)
      _ = (1 + K) * (2 ^ (s * k) * ‖u.block k‖) := by ring
      _ ≤ (1 + K) * (ε / (1 + K)) := by gcongr
      _ = ε := by field_simp

/-- **Band-limited limits of Schwartz functions.** An `Lᵖ` function `w` whose blocks vanish from
some index `M` on, and which is an `Lᵖ` limit of Schwartz functions `g`, lies in `b^s_{p,∞}`: the
truncations `S_M g` are Schwartz functions, `S_M w = w`, and `S_M (w - g)` has finitely many
blocks, so its Besov norm is controlled by `‖w - g‖_p`. -/
private theorem mem_littleBesov_of_toDistr_eq {v : BesovSpace F φ s p ∞}
    {w : Lp F p (volume : Measure E)} (hvw : v.toDistr = w)
    (hw : w ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p)) {M : ℕ}
    (hM : ∀ k, M ≤ k → littlewoodPaleyBlock F φ k (w : 𝓢'(E, F)) = 0) :
    v ∈ littleBesov F φ s p := by
  obtain ⟨L, hL⟩ := exists_sum_littlewoodPaleyBlock_littlewoodPaleyBlock (F := F) φ
  set K : ℝ := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  have hK := exists_sum_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ (p := p)
  obtain ⟨C, hC0, hC⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq_zero F φ
  -- `S_M` fixes `w`.
  have hSw : ∑ j ∈ Finset.range (M + 1), littlewoodPaleyBlock F φ j (w : 𝓢'(E, F)) = w :=
    sum_littlewoodPaleyBlock_eq_self φ _ fun j hj ↦ hM j (Nat.le_of_lt (by simpa using hj))
  rw [← SetLike.mem_coe, coe_littleBesov]
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  set A := 2 ^ (|s| * ((M + L : ℕ) : ℝ)) * C * K
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := Metric.mem_closure_iff.1 hw (ε / (A + 1)) (by positivity)
  rw [dist_eq_norm] at hg
  -- The truncation `h = S_M g` is a Schwartz function, and `w - h = S_M (w - g)`.
  set h : 𝓢(E, F) := ∑ j ∈ Finset.range (M + 1),
    SchwartzMap.fourierMultiplierCLM F (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) g
  obtain ⟨r, hr, hrw⟩ := hK M (w - g.toLp p (volume : Measure E))
  have hrh : (r : 𝓢'(E, F)) = w - h := by
    rw [← hr, Lp.toTemperedDistribution_sub, Lp.toTemperedDistribution_toLp_eq]
    simp only [map_sub, Finset.sum_sub_distrib, h, map_sum,
      littlewoodPaleyBlock_toTemperedDistributionCLM_eq, hSw]
  obtain ⟨x, hxr, hx⟩ := hC s (M + L) r fun k hk ↦ by
    rw [← hr]
    exact (hL k M).2 hk _
  have hxv : x = v - SchwartzMap.toBesovSpaceCLM F φ s p ∞ h := ext <| by
    rw [hxr, hrh, toDistr_sub, hvw, SchwartzMap.toDistr_toBesovSpaceCLM]
  refine ⟨_, ⟨h, rfl⟩, ?_⟩
  rw [dist_eq_norm, ← hxv]
  calc ‖x‖ ≤ 2 ^ (|s| * ((M + L : ℕ) : ℝ)) * C * ‖r‖ := hx
    _ ≤ 2 ^ (|s| * ((M + L : ℕ) : ℝ)) * C * (K * (ε / (A + 1))) := by
        gcongr
        exact hrw.trans (by gcongr)
    _ = A * (ε / (A + 1)) := by ring
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **The converse.** If the weighted blocks of `u ∈ B^s_{p,∞}` vanish at high frequency and every
block is a limit of Schwartz functions in `Lᵖ`, then `u` lies in the little Besov space. -/
theorem mem_littleBesov_of_tendsto {u : BesovSpace F φ s p ∞}
    (hdecay : Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0))
    (hblock : ∀ j, u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p)) :
    u ∈ littleBesov F φ s p := by
  obtain ⟨L, hL⟩ := exists_sum_littlewoodPaleyBlock_littlewoodPaleyBlock (F := F) φ
  -- The `Lᵖ` closure of the Schwartz functions is a subspace.
  have hS : closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p (volume : Measure E)) =
      ((LinearMap.range (SchwartzMap.toLpCLM ℂ F p (volume : Measure E)).toLinearMap
        ).topologicalClosure : Set (Lp F p (volume : Measure E))) := by
    have hcoe : ⇑(SchwartzMap.toLpCLM ℂ F p (volume : Measure E)) = fun f ↦ f.toLp p :=
      funext fun _ ↦ SchwartzMap.toLpCLM_apply
    rw [Submodule.topologicalClosure_coe, LinearMap.coe_range, ContinuousLinearMap.coe_coe, hcoe]
  rw [← SetLike.mem_coe, ← isClosed_littleBesov.closure_eq]
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  obtain ⟨N, v, hvw, huv⟩ := exists_toDistr_eq_sum_block_and_norm_sub_le hdecay (half_pos hε)
  refine ⟨v, mem_littleBesov_of_toDistr_eq hvw ?_ (M := N + L) fun k hk ↦ ?_, ?_⟩
  · rw [hS]
    exact Submodule.sum_mem _ fun j _ ↦ by rw [← SetLike.mem_coe, ← hS]; exact hblock j
  · simp only [Lp.toTemperedDistribution_sum, coe_block]
    exact (hL k N).2 hk u.toDistr
  · rw [dist_eq_norm]
    linarith

/-- **The little Besov space `b^s_{p,∞}` is cut out by its blocks:** `u` lies in the closure of
the Schwartz functions in `B^s_{p,∞}` exactly when `2^{js} ‖Δⱼ u‖_p → 0` and every block `Δⱼ u` is
a limit of Schwartz functions in `Lᵖ`. -/
theorem mem_littleBesov_iff {u : BesovSpace F φ s p ∞} :
    u ∈ littleBesov F φ s p ↔
      Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0) ∧
        ∀ j, u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p) :=
  ⟨fun hu ↦ ⟨tendsto_rpow_mul_norm_block_of_mem_littleBesov hu,
    block_mem_closure_of_mem_littleBesov hu⟩, fun h ↦ mem_littleBesov_of_tendsto h.1 h.2⟩

/-- **For `p < ∞`, the little Besov space `b^s_{p,∞}` is cut out by the decay of the weighted
blocks:** `u ∈ b^s_{p,∞}` exactly when `2^{js} ‖Δⱼ u‖_p → 0`, since the Schwartz functions are
dense in `Lᵖ`. -/
theorem mem_littleBesov_iff_tendsto (hp : p ≠ ∞) {u : BesovSpace F φ s p ∞} :
    u ∈ littleBesov F φ s p ↔ Tendsto (fun j : ℕ ↦ 2 ^ (s * j) * ‖u.block j‖) atTop (𝓝 0) := by
  have hdense := SchwartzMap.denseRange_toLpCLM (F := F) (μ := (volume : Measure E)) hp
  rw [mem_littleBesov_iff, and_iff_left_iff_imp]
  intro _ j
  -- `SchwartzMap.toLpCLM_apply` holds by `rfl`, so the dense range is the required one.
  exact hdense (u.block j)

/-! ### The little Besov spaces under the embeddings of the Besov scale -/

/-- A continuous linear map between spaces `B^s_{p,∞}` that keeps the underlying tempered
distribution maps the little Besov space into the little Besov space. -/
theorem map_mem_littleBesov {φ' : ContDiffBump (0 : E)} {s' : ℝ} {p' : ℝ≥0∞} [Fact (1 ≤ p')]
    (T : BesovSpace F φ s p ∞ →L[ℂ] BesovSpace F φ' s' p' ∞) (hT : ∀ u, (T u).toDistr = u.toDistr)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) : T u ∈ littleBesov F φ' s' p' := by
  rw [← SetLike.mem_coe, coe_littleBesov] at hu ⊢
  refine map_mem_closure T.continuous hu ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨f, ext (by simp only [hT, SchwartzMap.toDistr_toBesovSpaceCLM])⟩

/-- **The little Besov space does not depend on the bump function.** -/
@[simp]
theorem bumpEquiv_mem_littleBesov_iff (φ' : ContDiffBump (0 : E)) {u : BesovSpace F φ s p ∞} :
    bumpEquiv F φ φ' s p ∞ u ∈ littleBesov F φ' s p ↔ u ∈ littleBesov F φ s p := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := map_mem_littleBesov
      (bumpEquiv F φ' φ s p ∞ : BesovSpace F φ' s p ∞ →L[ℂ] BesovSpace F φ s p ∞)
      (fun _ ↦ by simp) h
    rwa [ContinuousLinearEquiv.coe_coe, ← bumpEquiv_symm,
      ContinuousLinearEquiv.symm_apply_apply] at this
  · have := map_mem_littleBesov
      (bumpEquiv F φ φ' s p ∞ : BesovSpace F φ s p ∞ →L[ℂ] BesovSpace F φ' s p ∞)
      (fun _ ↦ by simp) h
    rwa [ContinuousLinearEquiv.coe_coe] at this

/-- **Monotonicity in the smoothness:** `b^s_{p,∞} ⊆ b^{s'}_{p,∞}` for `s' ≤ s`. -/
theorem inclusion_mem_littleBesov {s' : ℝ} (hs : s' ≤ s) {u : BesovSpace F φ s p ∞}
    (hu : u ∈ littleBesov F φ s p) : inclusion F φ p hs le_rfl u ∈ littleBesov F φ s' p :=
  map_mem_littleBesov _ (toDistr_inclusion hs le_rfl) hu

/-- **The Bernstein embedding of the little Besov spaces:**
`b^s_{p,∞} ⊆ b^{s - n (1/p - 1/r)}_{r,∞}` for `p ≤ r`. -/
theorem inclusionOfExponentLE_mem_littleBesov {r : ℝ≥0∞} [Fact (1 ≤ r)] (hpr : p ≤ r)
    {u : BesovSpace F φ s p ∞} (hu : u ∈ littleBesov F φ s p) :
    inclusionOfExponentLE F φ ∞ hpr u ∈
      littleBesov F φ (s - Module.finrank ℝ E * (p.toReal⁻¹ - r.toReal⁻¹)) r :=
  map_mem_littleBesov _ (toDistr_inclusionOfExponentLE hpr) hu

/-- **A loss of smoothness lands in the little space for `p < ∞`:** `B^s_{p,q} ⊆ b^{s'}_{p,∞}` for
`s' < s`, since the weighted blocks of `B^{s'}_{p,1}` vanish at high frequency. -/
theorem inclusionOfLT_mem_littleBesov (hp : p ≠ ∞) {s' : ℝ} (hs : s' < s) {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (u : BesovSpace F φ s p q) :
    inclusionOfLT F φ p q ∞ hs u ∈ littleBesov F φ s' p := by
  rw [mem_littleBesov_iff_tendsto hp]
  simpa only [block_inclusionOfLT] using
    tendsto_rpow_mul_norm_block ENNReal.one_ne_top (inclusionOfLT F φ p q 1 hs u)

end BesovSpace

end TauCeti
