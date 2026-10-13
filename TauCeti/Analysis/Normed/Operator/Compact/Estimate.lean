/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Peetre's compact-error estimate

An estimate `‖x‖ ≤ C * ‖T x‖ + ‖K x‖`, with `K` compact, forces the kernel of `T` to be
finite dimensional. If the domain is complete, the estimate also makes `T` bounded below
on any closed subspace disjoint from its kernel. If the kernel is complemented, the range of
`T` is closed. In real or complex Banach spaces the finite-dimensional kernel is automatically
complemented.

This is the functional-analytic step that turns an elliptic estimate with a compact interior
error into finite-dimensional kernel and closed range. It does not assert finite-dimensional
cokernel: that requires a corresponding estimate for the adjoint or another argument.

The sequential form says that a bounded sequence whose `T`-images converge has a convergent
subsequence. Its limit solves the limiting equation. No completeness of either target space
is needed.

The argument uses Mathlib's Riesz lemma and uniform-inducing maps, and the compact-operator
subsequence API in `TauCeti.Analysis.Normed.Operator.Compact.Basic`.
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
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable (T : E →L[𝕜] F) {K : E →L[𝕜] G} {C : ℝ}

/-- An operator satisfying an a priori estimate with a compact error has finite-dimensional
kernel. The domain and the target spaces need not be complete. -/
theorem finiteDimensional_ker_of_compact_estimate [CompleteSpace 𝕜]
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
  have hsep : 1 ≤ ‖(v m : E) - (v n : E)‖ := hvsep hmn
  exact (hsep.trans h).not_gt (by simpa [dist_eq_norm] using hclose)

section CompleteDomain

variable [CompleteSpace E]

/-- Under a compact-error estimate, a bounded sequence whose operator images converge has a
convergent subsequence. The subsequential limit maps to the prescribed limit of the images. -/
theorem exists_subseq_tendsto_of_compact_estimate
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

/-- A compact-error estimate gives closed range when the kernel is complemented.
No completeness of the scalar field or either target space is required. -/
theorem isClosed_range_of_compact_estimate_of_closedComplemented
    (hK : IsCompactOperator K)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖)
    (hker : T.ker.ClosedComplemented) : IsClosed (T.range : Set F) := by
  obtain ⟨M, hMclosed, hMcompl⟩ := hker.exists_isClosed_isCompl
  obtain ⟨c, hcpos, hc⟩ :=
    T.exists_pos_mul_norm_le_of_compact_estimate hK hbound hMclosed hMcompl.disjoint
  let A : M →L[𝕜] F := T.comp M.subtypeL
  obtain ⟨D, hD⟩ : ∃ D, AntilipschitzWith D A :=
    antilipschitzWith_iff_exists_mul_le_norm.mpr ⟨c, hcpos, fun m ↦ hc m m.2⟩
  have hrange : Set.range A = (T.range : Set F) := by
    rw [← Submodule.map_eq_range_iff.mpr hMcompl.codisjoint.symm, Submodule.map_coe]
    ext y
    simp [A]
  have : CompleteSpace M := hMclosed.completeSpace_coe
  rw [← hrange]
  exact hD.isClosed_range A.uniformContinuous

/-- Peetre's lemma: a compact-error estimate gives closed range over real or complex scalars.
Together with `finiteDimensional_ker_of_compact_estimate`, this proves the upper semi-Fredholm
property. No completeness of the codomain is required. -/
theorem isClosed_range_of_compact_estimate [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜]
    (hK : IsCompactOperator K)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) : IsClosed (T.range : Set F) := by
  have := T.finiteDimensional_ker_of_compact_estimate hK hbound
  exact T.isClosed_range_of_compact_estimate_of_closedComplemented hK hbound
    (Submodule.ClosedComplemented.of_finiteDimensional T.ker)

end CompleteDomain

end ContinuousLinearMap
