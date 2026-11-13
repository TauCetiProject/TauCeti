/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Normed.Module.RieszLemma

/-!
# Peetre's compact-error estimate

An estimate `‖x‖ ≤ C * ‖T x‖ + ‖K x‖`, with `K` compact, forces the kernel of `T` to be
finite dimensional. If the domain is complete, the estimate also makes `T` bounded below
on any closed subspace disjoint from its kernel, and the range of `T` is closed over any
nontrivially normed field. The closed-range step needs no complement of the kernel: by
`ContinuousLinearMap.isClosed_range_of_exists_subseq_tendsto`, an operator has closed range as
soon as every bounded sequence with convergent images has a convergent subsequence.

This is the functional-analytic step that turns an elliptic estimate with a compact interior
error into finite-dimensional kernel and closed range. It does not assert finite-dimensional
cokernel: that requires a corresponding estimate for the adjoint or another argument.

The sequential form says that a bounded sequence whose `T`-images converge has a convergent
subsequence. Its limit solves the limiting equation. No completeness of either target space
is needed; the compact-error target may even be seminormed.

The argument uses Mathlib's Riesz lemma, its translated form `TauCeti.riesz_lemma_translate`,
uniform-inducing maps, and the compact-operator subsequence API in
`TauCeti.Analysis.Normed.Operator.Compact.Basic`.
The normalization argument extends the one for `1 - K` in
`IsCompactOperator.exists_pos_mul_norm_le_of_disjoint_ker` to operators with distinct targets
for the principal term and the compact error.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1: estimates with a compact error in the Fredholm criterion.
-/

public section

namespace ContinuousLinearMap

open Filter
open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {C : ℝ}

/-- An operator satisfying an a priori estimate with a compact error has finite-dimensional
kernel. The domain and the target spaces need not be complete, and the target spaces need
only be seminormed. -/
theorem finiteDimensional_ker_of_compact_estimate [CompleteSpace 𝕜]
    [SeminormedAddCommGroup F] [Module 𝕜 F] (T : E →L[𝕜] F) {K : E →L[𝕜] G}
    (hK : IsCompactOperator K) (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) :
    FiniteDimensional 𝕜 T.ker := by
  by_contra hfinite
  obtain ⟨R, v, _, hvbound, hvsep⟩ := exists_seq_norm_le_one_le_norm_sub hfinite
  have hKker : IsCompactOperator (K.comp T.ker.subtypeL : T.ker →ₗ[𝕜] G) := by
    simpa only [coe_coe, coe_comp] using hK.comp_clm T.ker.subtypeL
  obtain ⟨m, n, hmn, hclose⟩ := hKker.exists_dist_lt_of_norm_le hvbound zero_lt_one
  have h := hbound ((v m : E) - (v n : E))
  have hTv (i : ℕ) : T (v i : E) = 0 := (v i).property
  simp only [map_sub, hTv, sub_self, norm_zero, mul_zero, zero_add] at h
  have hsep : 1 ≤ ‖(v m : E) - (v n : E)‖ := hvsep hmn.ne
  exact (hsep.trans h).not_gt (by simpa [dist_eq_norm] using hclose)

/-- **Sequential closed-range criterion.** If every bounded sequence whose `T`-images converge
has a convergent subsequence, then `T` has closed range. Neither space needs to be complete.

Each point of the range has a preimage almost as far from `ker T` as its norm, by
`TauCeti.riesz_lemma_translate`; the subsequence hypothesis bounds the norms of such preimages by
a multiple of the norms of their images, so the preimages of a convergent sequence are bounded. -/
theorem isClosed_range_of_exists_subseq_tendsto [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F)
    (hT : ∀ {R : ℝ} {v : ℕ → E} {y : F}, (∀ n, ‖v n‖ ≤ R) →
      Tendsto (fun n ↦ T (v n)) atTop (𝓝 y) →
      ∃ (x : E) (ψ : ℕ → ℕ), StrictMono ψ ∧ Tendsto (fun n ↦ v (ψ n)) atTop (𝓝 x)) :
    IsClosed (T.range : Set F) := by
  -- `T` is bounded below on vectors almost as far from `ker T` as their norm.
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ w : E, (∀ z ∈ T.ker, 2⁻¹ * ‖w‖ ≤ ‖w - z‖) → ‖w‖ ≤ C * ‖T w‖ := by
    by_contra! hcon
    obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm 𝕜
    have hshell : ∀ n : ℕ, ∃ u : E, (∀ z ∈ T.ker, 2⁻¹ * ‖u‖ ≤ ‖u - z‖) ∧ ‖u‖ ≤ 1 ∧
        ‖a‖⁻¹ ≤ ‖u‖ ∧ ‖T u‖ ≤ 1 / (n + 1) := by
      intro n
      obtain ⟨w, hw, hlt⟩ := hcon (n + 1) (by positivity)
      have hw0 : w ≠ 0 := by rintro rfl; simp at hlt
      obtain ⟨d, hd0, hdlt, hdge, _⟩ := rescale_to_shell ha one_pos hw0
      refine ⟨d • w, fun z hz ↦ ?_, hdlt.le, by simpa using hdge, ?_⟩
      · calc 2⁻¹ * ‖d • w‖ = ‖d‖ * (2⁻¹ * ‖w‖) := by rw [norm_smul]; ring
          _ ≤ ‖d‖ * ‖w - d⁻¹ • z‖ := by gcongr; exact hw _ (T.ker.smul_mem _ hz)
          _ = ‖d • w - z‖ := by rw [← norm_smul, smul_sub, smul_inv_smul₀ hd0]
      · calc ‖T (d • w)‖ = ‖d‖ * ‖T w‖ := by rw [map_smul, norm_smul]
          _ ≤ ‖d‖ * (‖w‖ / (n + 1)) := by
            gcongr
            rw [le_div_iff₀ (by positivity), mul_comm]
            exact hlt.le
          _ = 1 / (n + 1) * ‖d • w‖ := by rw [norm_smul]; ring
          _ ≤ 1 / (n + 1) := mul_le_of_le_one_right (by positivity) hdlt.le
    choose u hu hule huge hTu using hshell
    have hTu0 := squeeze_zero_norm hTu tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨x, ψ, hψ, hx⟩ := hT hule hTu0
    have hxker : x ∈ T.ker := LinearMap.mem_ker.mpr <|
      tendsto_nhds_unique ((T.continuous.tendsto x).comp hx) (hTu0.comp hψ.tendsto_atTop)
    -- `‖u (ψ n)‖ ≤ 2 * ‖u (ψ n) - x‖ → 0`, although `‖u (ψ n)‖ ≥ ‖a‖⁻¹`.
    have hlim : Tendsto (fun n ↦ 2 * ‖u (ψ n) - x‖) atTop (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hx).const_mul 2
    have hge : ‖a‖⁻¹ ≤ 0 := ge_of_tendsto' hlim fun n ↦
      (huge (ψ n)).trans (by linarith [hu (ψ n) x hxker])
    exact hge.not_gt (by positivity)
  refine isSeqClosed_iff_isClosed.mp fun y z hy hyz ↦ ?_
  -- Replace arbitrary preimages by preimages almost as far from `ker T` as their norm.
  have hpre : ∀ n, ∃ w : E, T w = y n ∧ ∀ z ∈ T.ker, 2⁻¹ * ‖w‖ ≤ ‖w - z‖ := fun n ↦ by
    obtain ⟨x, hx⟩ := hy n
    obtain ⟨k, hk, hk'⟩ := TauCeti.riesz_lemma_translate T.isClosed_ker x (r := 2⁻¹) (by norm_num)
    have hk0 : T k = 0 := hk
    exact ⟨x - k, by rw [map_sub, hk0, sub_zero]; exact hx, hk'⟩
  choose w hTw hw using hpre
  obtain ⟨R, hR⟩ := hyz.norm.bddAbove_range
  have hwle (n : ℕ) : ‖w n‖ ≤ C * R :=
    (hC _ (hw n)).trans (by rw [hTw]; exact mul_le_mul_of_nonneg_left (hR ⟨n, rfl⟩) hC0)
  obtain ⟨x, ψ, hψ, hx⟩ := hT hwle (by simpa only [hTw] using hyz)
  exact ⟨x, tendsto_nhds_unique ((T.continuous.tendsto x).comp hx)
    (by simpa only [Function.comp_def, hTw] using hyz.comp hψ.tendsto_atTop)⟩

section CompleteDomain

variable [CompleteSpace E]

/-- Under a compact-error estimate, a bounded sequence whose operator images converge has a
convergent subsequence. The subsequential limit maps to the prescribed limit of the images. -/
theorem exists_subseq_tendsto_of_compact_estimate
    [NormedAddCommGroup F] [Module 𝕜 F] (T : E →L[𝕜] F) {K : E →L[𝕜] G}
    (hK : IsCompactOperator K)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖)
    {R : ℝ} {v : ℕ → E} (hvbound : ∀ n, ‖v n‖ ≤ R) {y : F}
    (hTv : Tendsto (fun n ↦ T (v n)) atTop (𝓝 y)) :
    ∃ (x : E) (ψ : ℕ → ℕ), StrictMono ψ ∧
      Tendsto (fun n ↦ v (ψ n)) atTop (𝓝 x) ∧ T x = y := by
  obtain ⟨z, ψ, hψ, hKψ⟩ := hK.exists_subseq_tendsto hvbound
  -- The estimate makes the combined map `(T, K)` a uniform embedding.
  obtain ⟨D, hanti⟩ : ∃ D, AntilipschitzWith D (T.prod K) := by
    apply antilipschitzWith_iff_exists_mul_le_norm.mpr
    refine ⟨(|C| + 1)⁻¹, by positivity, fun x ↦ ?_⟩
    have hTnorm : ‖T x‖ ≤ ‖(T.prod K) x‖ := by
      simpa only [prod_apply] using norm_fst_le (T x, K x)
    have hKnorm : ‖K x‖ ≤ ‖(T.prod K) x‖ := by
      simpa only [prod_apply] using norm_snd_le (T x, K x)
    have hx : ‖x‖ ≤ (|C| + 1) * ‖(T.prod K) x‖ := by
      nlinarith [hbound x, mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg (T x)),
        mul_le_mul_of_nonneg_left hTnorm (abs_nonneg C)]
    exact (inv_mul_le_iff₀ (by positivity : 0 < |C| + 1)).2 hx
  have hpair := (hTv.comp hψ.tendsto_atTop).prodMk_nhds hKψ
  have hcauchy : CauchySeq (fun n ↦ v (ψ n)) := by
    apply (hanti.isUniformInducing (T.prod K).uniformContinuous).cauchy_map_iff.mp
    exact hpair.cauchySeq
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨x, ψ, hψ, hx,
    tendsto_nhds_unique (T.continuous.continuousAt.tendsto.comp hx)
      (hTv.comp hψ.tendsto_atTop)⟩

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) {K : E →L[𝕜] G}

/-- A compact-error estimate makes an operator bounded below on every closed subspace
disjoint from its kernel. -/
theorem exists_pos_mul_norm_le_of_compact_estimate
    (hK : IsCompactOperator K)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖)
    {M : Submodule 𝕜 E} (hM : IsClosed (M : Set E)) (hdisj : Disjoint T.ker M) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ M, c * ‖x‖ ≤ ‖T x‖ := by
  by_contra! hcon
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm 𝕜
  -- Normalize counterexamples into a fixed shell, without assuming real scalars.
  have hshell : ∀ n : ℕ, ∃ x ∈ M, ‖x‖ ≤ 1 ∧ ‖a‖⁻¹ ≤ ‖x‖ ∧
      ‖T x‖ ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨u, huM, hu⟩ := hcon (1 / (n + 1)) (by positivity)
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨d, _, hdlt, hdge, _⟩ := rescale_to_shell ha one_pos hu0
    refine ⟨d • u, M.smul_mem d huM, hdlt.le, by simpa using hdge, ?_⟩
    calc ‖T (d • u)‖ = ‖d‖ * ‖T u‖ := by rw [map_smul, norm_smul]
      _ ≤ ‖d‖ * (1 / (n + 1) * ‖u‖) := by gcongr
      _ = 1 / (n + 1) * ‖d • u‖ := by rw [norm_smul]; ring
      _ ≤ 1 / (n + 1) := mul_le_of_le_one_right (by positivity) hdlt.le
  choose v hvM hvbound hvge hTv using hshell
  obtain ⟨x, ψ, _, hx, hTx⟩ := T.exists_subseq_tendsto_of_compact_estimate hK hbound
    hvbound (squeeze_zero_norm hTv tendsto_one_div_add_atTop_nhds_zero_nat)
  have hxM : x ∈ M := hM.mem_of_tendsto hx (.of_forall fun n ↦ hvM (ψ n))
  have hxzero : x = 0 := by
    simpa using hdisj.le_bot ⟨LinearMap.mem_ker.mpr hTx, hxM⟩
  have hxge : ‖a‖⁻¹ ≤ ‖x‖ := ge_of_tendsto' hx.norm fun n ↦ hvge (ψ n)
  rw [hxzero, norm_zero] at hxge
  exact hxge.not_gt (by positivity)

/-- **Peetre's lemma**: a compact-error estimate gives closed range. Together with
`finiteDimensional_ker_of_compact_estimate`, this proves the upper semi-Fredholm property. No
completeness of the codomain or of the scalar field is required. -/
theorem isClosed_range_of_compact_estimate
    (hK : IsCompactOperator K)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) : IsClosed (T.range : Set F) :=
  T.isClosed_range_of_exists_subseq_tendsto fun hv hTv ↦
    let ⟨x, ψ, hψ, hx, _⟩ := T.exists_subseq_tendsto_of_compact_estimate hK hbound hv hTv
    ⟨x, ψ, hψ, hx⟩

end CompleteDomain

end ContinuousLinearMap
