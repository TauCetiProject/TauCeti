/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.HahnBanach
import TauCeti.Analysis.Normed.Operator.ClosedRange

/-!
# Peetre's compact-error estimate

An estimate `‖x‖ ≤ C * ‖T x‖ + ‖K x‖`, with `K` compact, forces the kernel of `T` to be
finite dimensional. If the domain is complete, the estimate also makes `T` bounded below
on any closed subspace disjoint from its kernel, and the range of `T` is closed over any
nontrivially normed field. The closed-range step needs no complement of the kernel: by the
sequential criterion `ContinuousLinearMap.isClosed_range_of_exists_subseq_tendsto` from
`TauCeti.Analysis.Normed.Operator.ClosedRange`, an operator has closed range as soon as every
bounded sequence with convergent images has a convergent subsequence.

This is the functional-analytic step that turns an elliptic estimate with a compact interior
error into finite-dimensional kernel and closed range. It does not assert finite-dimensional
cokernel: that requires a corresponding estimate for the adjoint or another argument.

The sequential form says that a bounded sequence whose `T`-images converge has a convergent
subsequence. Its limit solves the limiting equation. No completeness of either target space
is needed; the compact-error target may even be seminormed.

On a complete domain the estimate also bounds the distance to the kernel: the quotient norm of
`x` modulo `ker T` is at most `C' * ‖T x‖`, over any nontrivially normed field. Over `ℝ` or `ℂ`
(more generally, a field with `IsRCLikeNormedField`) the finite-dimensional kernel moreover has a
closed complement, and the distance is realized by a continuous projection `P` onto `ker T` with
`‖x - P x‖ ≤ C' * ‖T x‖`. This is the abstract form of the Deny–Lions lemma: applied to the highest
weak derivative of a Sobolev space with compact lower-order inclusion, it says that the quotient
norm modulo the kernel of the top derivative is equivalent to the top seminorm.

The argument uses Mathlib's Riesz lemma, uniform-inducing maps, the sequential closed-range
criterion, and the compact-operator subsequence API in
`TauCeti.Analysis.Normed.Operator.Compact.Basic`.
The normalization argument extends the one for `1 - K` in
`IsCompactOperator.exists_pos_mul_norm_le_of_disjoint_ker` to operators with distinct targets
for the principal term and the compact error.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1: estimates with a compact error in the Fredholm criterion.
* J. Peetre, *Another approach to elliptic boundary problems*, Comm. Pure Appl. Math. 14 (1961),
  711–731.
* L. Tartar, *An Introduction to Sobolev Spaces and Interpolation Spaces*, Springer (2007):
  the Peetre–Tartar lemma, the quotient estimate modulo the kernel.
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

/-- **Abstract Deny–Lions lemma.** A compact-error estimate `‖x‖ ≤ C * ‖T x‖ + ‖K x‖` on a
complete space bounds the quotient norm of `x` modulo `ker T`, that is the distance from `x` to
`ker T`, by a constant multiple of `‖T x‖`. No completeness of the target spaces is needed. -/
theorem exists_norm_mk_ker_le_of_compact_estimate
    (hK : IsCompactOperator K) (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x, ‖(Submodule.Quotient.mk x : E ⧸ T.ker)‖ ≤ C' * ‖T x‖ := by
  by_contra! hcon
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm 𝕜
  -- Counterexamples, normalized to quotient norm in a fixed shell, with bounded representatives.
  have hshell : ∀ n : ℕ, ∃ x : E, ‖x‖ ≤ 2 ∧
      ‖a‖⁻¹ ≤ ‖(Submodule.Quotient.mk x : E ⧸ T.ker)‖ ∧ ‖T x‖ ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨y, hy⟩ := hcon (n + 1) (by positivity)
    set q : E ⧸ T.ker := Submodule.Quotient.mk y
    obtain ⟨d, -, hdlt, hdge, -⟩ :=
      rescale_to_shell_semi_normed ha one_pos
        ((by positivity : (0 : ℝ) ≤ (n + 1) * ‖T y‖).trans_lt hy).ne'
    obtain ⟨x, hx, hxlt⟩ := Submodule.Quotient.norm_mk_lt (d • q) one_pos
    have hmem : x - d • y ∈ T.ker :=
      (Submodule.Quotient.eq _).1 (by rw [hx, Submodule.Quotient.mk_smul])
    have hTx : T x = d • T y := by
      rw [← map_smul, ← sub_eq_zero, ← map_sub]
      exact LinearMap.mem_ker.1 hmem
    refine ⟨x, by linarith, by simpa [hx] using hdge, ?_⟩
    rw [hTx, norm_smul, le_div_iff₀ (by positivity)]
    calc ‖d‖ * ‖T y‖ * (n + 1) = ‖d‖ * ((n + 1) * ‖T y‖) := by ring
      _ ≤ ‖d‖ * ‖q‖ := by gcongr
      _ = ‖d • q‖ := (norm_smul d q).symm
      _ ≤ 1 := hdlt.le
  choose v hvbound hvge hTv using hshell
  obtain ⟨x, ψ, -, hx, hTx⟩ := T.exists_subseq_tendsto_of_compact_estimate hK hbound
    hvbound (squeeze_zero_norm hTv tendsto_one_div_add_atTop_nhds_zero_nat)
  -- The classes of the subsequence converge to the class of `x ∈ ker T`, which is zero.
  have hmk : Tendsto (fun n ↦ (Submodule.Quotient.mk (v (ψ n)) : E ⧸ T.ker)) atTop (𝓝 0) := by
    have hx0 : (Submodule.Quotient.mk x : E ⧸ T.ker) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hTx
    simpa only [Function.comp_def, Submodule.coe_mkQL, Submodule.mkQ_apply, hx0] using
      (T.ker.mkQL.continuous.tendsto x).comp hx
  have hge : ‖a‖⁻¹ ≤ 0 := by
    simpa using ge_of_tendsto' hmk.norm fun n ↦ hvge (ψ n)
  exact hge.not_gt (by positivity)

section Projection

variable [IsRCLikeNormedField 𝕜]

/-- **Peetre's estimate modulo the kernel.** Over `ℝ` or `ℂ`, a compact-error estimate
`‖x‖ ≤ C * ‖T x‖ + ‖K x‖` on a complete space yields a continuous projection `P` onto the
(finite-dimensional) kernel of `T` such that `‖x - P x‖ ≤ C' * ‖T x‖` for every `x`. -/
theorem exists_projection_norm_sub_le_of_compact_estimate
    (hK : IsCompactOperator K) (hbound : ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖K x‖) :
    ∃ (P : E →L[𝕜] E) (C' : ℝ), 0 ≤ C' ∧ IsIdempotentElem P ∧ P.range = T.ker ∧
      ∀ x, ‖x - P x‖ ≤ C' * ‖T x‖ := by
  -- The `RCLike` structure carried by `𝕜` makes it complete.
  let := IsRCLikeNormedField.rclike 𝕜
  have := T.finiteDimensional_ker_of_compact_estimate hK hbound
  -- A finite-dimensional kernel has a closed complement `X`, on which `T` is bounded below.
  obtain ⟨X, h⟩ := (Submodule.ClosedComplemented.of_finiteDimensional T.ker).exists_isTopCompl
  obtain ⟨c, hc, hcX⟩ :=
    T.exists_pos_mul_norm_le_of_compact_estimate hK hbound h.isClosed' h.isCompl.disjoint
  refine ⟨T.ker.projectionL X h, c⁻¹, inv_nonneg.2 hc.le, Submodule.isIdempotentElem_projectionL h,
    Submodule.range_projectionL h, fun x ↦ ?_⟩
  -- `x - P x` is the component of `x` in `X`, and `T` does not see the kernel component.
  rw [← Submodule.projectionL_eq_self_sub_projectionL, le_inv_mul_iff₀ hc,
    ← T.apply_projectionL_ker h.symm x]
  exact hcX _ (Submodule.projectionL_apply_mem h.symm x)

end Projection

end CompleteDomain

end ContinuousLinearMap
