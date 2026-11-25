/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import Mathlib.RingTheory.Finiteness.Cofinite
import TauCeti.Analysis.Normed.Module.RieszLemma
import TauCeti.Analysis.Normed.Operator.ClosedRange
import TauCeti.Analysis.Normed.Operator.Compact.Eigenspace
import TauCeti.LinearAlgebra.End.RangePow

/-!
# Riesz theory for compact perturbations of the identity

Let `K` be a compact operator on a normed space `X` over a nontrivially normed field `𝕜` and write
`A = 1 - K`. This file proves three finiteness facts about `A`: its kernel is finite dimensional,
its range is closed, and its cokernel is finite dimensional; the two finite-dimensionality
statements need `𝕜` to be complete. Together they are the operator-theoretic half of
the Riesz--Schauder theory. When `X` is a Banach space they make `A` a Fredholm operator
(`TauCeti.isFredholm_one_sub`) and they upgrade Mathlib's spectral Fredholm alternative for compact
operators to a statement about Fredholm operators. On a general normed space a Fredholm operator
also needs `A` to be a strict map, which uses the lower bound
`IsCompactOperator.exists_pos_mul_norm_le_of_disjoint_ker` below.

The kernel argument is `IsCompactOperator.finiteDimensional_eigenspace` at the eigenvalue `1`,
and holds on any Hausdorff topological vector space. The closed-range argument uses the
sequential criterion `ContinuousLinearMap.isClosed_range_of_exists_subseq_tendsto` from
`TauCeti.Analysis.Normed.Operator.ClosedRange`. The cokernel argument uses the separation
consequence `IsCompactOperator.exists_dist_lt_of_norm_le`.

* On `ker A` the operator `K` restricts to the identity, and a compact identity forces finite
  dimension.
* For the range, if `A xₙ` converges and the `xₙ` are bounded, then along a subsequence on which
  `K` converges the identity `x = A x + K x` makes `xₙ` converge in `X`. The sequential criterion
  turns this into closedness of `range A`, choosing preimages almost as far from `ker A` as their
  norm. No completeness of `X` or of `𝕜` is needed.
* For the cokernel, run the classical Riesz argument on the decreasing chain of ranges
  `range A ⊇ range A² ⊇ ⋯`. Each `Aⁿ` is again `1` minus a compact operator, so each of these
  ranges is closed, and Riesz's lemma would otherwise produce a separated bounded sequence. Once
  the chain stabilises at `p`, the finite-dimensional `ker (A ^ p)` and `range (A ^ p) ≤ range A`
  together span `X`, so `ker (A ^ p)` surjects onto the cokernel.

## Main declarations

* `IsCompactOperator.exists_pos_mul_norm_le_of_disjoint_ker`: `1 - K` is bounded below on
  any closed subspace meeting its kernel trivially.
* `IsCompactOperator.isCompactOperator_one_sub_pow`: `1 - (1 - K) ^ n` is compact, so
  every power of `1 - K` is again a compact perturbation of the identity. This holds for any
  continuous endomorphism of a topological module.
* `IsCompactOperator.finiteDimensional_ker_one_sub`: `ker (1 - K)` is finite dimensional. This
  holds on any Hausdorff topological vector space.
* `IsCompactOperator.finiteDimensional_ker_pow_one_sub`: `ker ((1 - K) ^ n)` is finite dimensional.
* `IsCompactOperator.isClosed_range_one_sub`: `range (1 - K)` is closed; neither `X` nor `𝕜` need
  be complete.
* `IsCompactOperator.isClosed_range_pow_one_sub`: `range ((1 - K) ^ n)` is closed.
* `IsCompactOperator.exists_succ_eq_of_descending_chain`: for compact `K` on a seminormed space over
  a nontrivially normed field, a decreasing chain of subspaces, each closed in the previous one, on
  which `1 - K` steps down the chain, cannot be strictly decreasing: `V (p + 1) = V p` for some
  `p`.
* `IsCompactOperator.exists_succ_eq_of_ascending_chain`: for compact `K` on a seminormed space over
  a nontrivially normed field, an increasing chain of subspaces, each closed in the next one, on
  which `K - μ n • 1` steps down the chain for scalars `μ n` bounded away from zero, cannot be
  strictly increasing: `V (p + 1) = V p` for some `p`.
* `IsCompactOperator.finiteDimensional_quotient_range_one_sub`: `X ⧸ range (1 - K)` is
  finite dimensional.

The argument is the classical Riesz theory of compact operators; see, for example, Conway,
*A Course in Functional Analysis*, Chapter VI, Section 5, or Rudin, *Functional Analysis*,
Chapter 4.
-/

public section

namespace TauCeti

open Filter Module
open scoped Topology

section Pow

variable {R M : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
  [Module R M] {K : M →L[R] M}

/-- Every power of a compact perturbation of the identity is again a compact perturbation of the
identity. -/
theorem _root_.IsCompactOperator.isCompactOperator_one_sub_pow (hK : IsCompactOperator K) (n : ℕ) :
    IsCompactOperator ⇑((1 : M →L[R] M) - (1 - K) ^ n) := by
  rw [← geom_sum_mul_neg, sub_sub_cancel, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.coe_comp]
  exact hK.clm_comp _

end Pow

section Kernel

variable {𝕜 M : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup M]
  [Module 𝕜 M] [TopologicalSpace M] [T2Space M] [IsTopologicalAddGroup M] [ContinuousSMul 𝕜 M]
  {K : M →L[𝕜] M}

/-- The kernel of a compact perturbation of the identity is finite dimensional. The space need
only be a Hausdorff topological vector space. -/
theorem _root_.IsCompactOperator.finiteDimensional_ker_one_sub (hK : IsCompactOperator K) :
    FiniteDimensional 𝕜 (LinearMap.ker ((1 - K : M →L[𝕜] M) : M →ₗ[𝕜] M)) := by
  have h := hK.finiteDimensional_eigenspace one_ne_zero
  rwa [Module.End.eigenspace_def, ← LinearMap.ker_neg, neg_sub, one_smul] at h

/-- The kernel of every power of a compact perturbation of the identity is finite dimensional. -/
theorem _root_.IsCompactOperator.finiteDimensional_ker_pow_one_sub (hK : IsCompactOperator K)
    (n : ℕ) : FiniteDimensional 𝕜 (LinearMap.ker (((1 - K : M →L[𝕜] M) : M →ₗ[𝕜] M) ^ n)) := by
  have h := (hK.isCompactOperator_one_sub_pow n).finiteDimensional_ker_one_sub
  rwa [sub_sub_cancel, ContinuousLinearMap.toLinearMap_pow] at h

end Kernel

section Chain

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {K : X →L[𝕜] X}

/-- Let `K` be a compact operator on a seminormed space over a nontrivially normed field. A
decreasing chain of subspaces, each closed in the previous one and stable under `1 - K` in the
sense that `1 - K` carries the `n`-th one into the `(n + 1)`-st, cannot be strictly decreasing:
`V (p + 1) = V p` for some `p`. For a chain of closed subspaces
`hV : ∀ n, IsClosed (V n : Set X)`, the closedness hypothesis is
`fun n ↦ (hV (n + 1)).preimage continuous_subtypeVal`. -/
theorem _root_.IsCompactOperator.exists_succ_eq_of_descending_chain (hK : IsCompactOperator K)
    {V : ℕ → Submodule 𝕜 X} (hmono : ∀ n, V (n + 1) ≤ V n)
    (hclosed : ∀ n, IsClosed (((↑) : V n → X) ⁻¹' V (n + 1)))
    (hstep : ∀ n, ∀ x ∈ V n, x - K x ∈ V (n + 1)) :
    ∃ p, V (p + 1) = V p := by
  by_contra! hcon
  have hanti : Antitone V := antitone_nat_of_succ_le hmono
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  -- Riesz's lemma gives a bounded sequence whose images under `K` stay `1` apart.
  choose f hfmem hfnorm hfsep using fun n =>
    riesz_lemma_of_norm_lt_of_lt hc (lt_add_one ‖c‖) (hclosed n) ((hmono n).lt_of_ne (hcon n))
  have key : ∀ m n : ℕ, m < n → 1 ≤ ‖K (f m) - K (f n)‖ := by
    intro m n hmn
    have hy : (f m - K (f m)) + f n - (f n - K (f n)) ∈ V (m + 1) :=
      Submodule.sub_mem _ (Submodule.add_mem _ (hstep m _ (hfmem m)) (hanti hmn (hfmem n)))
        (hanti (Nat.succ_le_succ hmn.le) (hstep n _ (hfmem n)))
    have hrw : K (f m) - K (f n) = f m - ((f m - K (f m)) + f n - (f n - K (f n))) := by abel
    rw [hrw]
    exact hfsep m _ hy
  obtain ⟨m, n, hmn, hlt⟩ := hK.exists_dist_lt_of_norm_le hfnorm one_pos
  rw [dist_eq_norm] at hlt
  exact (key m n hmn).not_gt hlt

/-- Let `K` be a compact operator on a seminormed space over a nontrivially normed field, and let
`μ n` be scalars with `ε ≤ ‖μ n‖` for a fixed `ε > 0`. An increasing chain of subspaces, each
closed in the next one, such that `K - μ n • 1` carries the `(n + 1)`-st one into the `n`-th,
cannot be strictly increasing: `V (p + 1) = V p` for some `p`. For a chain of closed subspaces
`hV : ∀ n, IsClosed (V n : Set X)`, the closedness hypothesis is
`fun n ↦ (hV n).preimage continuous_subtypeVal`. -/
theorem _root_.IsCompactOperator.exists_succ_eq_of_ascending_chain (hK : IsCompactOperator K)
    {V : ℕ → Submodule 𝕜 X} {μ : ℕ → 𝕜} {ε : ℝ} (hε : 0 < ε) (hμ : ∀ n, ε ≤ ‖μ n‖)
    (hmono : ∀ n, V n ≤ V (n + 1)) (hclosed : ∀ n, IsClosed (((↑) : V (n + 1) → X) ⁻¹' V n))
    (hstep : ∀ n, ∀ x ∈ V (n + 1), K x - μ n • x ∈ V n) :
    ∃ p, V (p + 1) = V p := by
  by_contra! hcon
  have hmono' : Monotone V := monotone_nat_of_le_succ hmono
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  -- Riesz's lemma gives a bounded sequence whose images under `K` stay `ε` apart.
  choose f hfmem hfnorm hfsep using fun n =>
    riesz_lemma_of_norm_lt_of_lt hc (lt_add_one ‖c‖) (hclosed n) ((hmono n).lt_of_ne (hcon n).symm)
  have key (m n : ℕ) (hmn : m < n) : ε ≤ ‖K (f n) - K (f m)‖ := by
    have hne : μ n ≠ 0 := norm_pos_iff.mp (hε.trans_le (hμ n))
    have hKm : K (f m) ∈ V n := by
      have h := (V n).add_mem (hmono' hmn.le (hstep m _ (hfmem m)))
        ((V n).smul_mem (μ m) (hmono' hmn (hfmem m)))
      rwa [sub_add_cancel] at h
    let y := (μ n)⁻¹ • (K (f m) - (K (f n) - μ n • f n))
    have hy : y ∈ V n := (V n).smul_mem _ ((V n).sub_mem hKm (hstep n _ (hfmem n)))
    have hrw : K (f n) - K (f m) = μ n • (f n - y) := by
      simp only [y, smul_sub, smul_smul, mul_inv_cancel₀ hne, inv_mul_cancel₀ hne, one_smul]
      abel
    rw [hrw, norm_smul]
    exact (hμ n).trans (le_mul_of_one_le_right (norm_nonneg _) (hfsep n y hy))
  obtain ⟨m, n, hmn, hlt⟩ := hK.exists_dist_lt_of_norm_le hfnorm hε
  rw [dist_eq_norm'] at hlt
  exact (key m n hmn).not_gt hlt

end Chain

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {K : X →L[𝕜] X}

namespace IsCompactOperator

/-- A bounded sequence whose `(1 - K)`-images tend to `z` has a subsequence converging to a point
`y` with `(1 - K) y = z`. -/
private theorem _root_.IsCompactOperator.exists_subseq_tendsto_one_sub_apply_eq
    (hK : IsCompactOperator K) {R : ℝ} {v : ℕ → X} (hvle : ∀ n, ‖v n‖ ≤ R) {z : X}
    (hAtendsto : Tendsto (fun n => (1 - K : X →L[𝕜] X) (v n)) atTop (𝓝 z)) :
    ∃ (y : X) (ψ : ℕ → ℕ), StrictMono ψ ∧ Tendsto (fun k => v (ψ k)) atTop (𝓝 y) ∧
      (1 - K : X →L[𝕜] X) y = z := by
  obtain ⟨y, ψ, hψ, hψy⟩ := IsCompactOperator.exists_subseq_tendsto hK hvle
  have hAψ := hAtendsto.comp hψ.tendsto_atTop
  -- `v = (1 - K) v + K v`, and both summands converge along the subsequence.
  have hvsub : Tendsto (fun k => v (ψ k)) atTop (𝓝 (z + y)) := by
    simpa [Function.comp_def] using hAψ.add hψy
  exact ⟨z + y, ψ, hψ, hvsub,
    tendsto_nhds_unique (((1 - K : X →L[𝕜] X).continuous.tendsto (z + y)).comp hvsub) hAψ⟩

/-- On a closed subspace `M` meeting `ker (1 - K)` only in `0`, the operator `1 - K` is bounded
below. Unlike the general compact-error estimate theorem, this does not require a complete
domain: the identity `x = (1 - K) x + K x` supplies the subsequential limit in `X`. -/
theorem _root_.IsCompactOperator.exists_pos_mul_norm_le_of_disjoint_ker (hK : IsCompactOperator K)
    {M : Submodule 𝕜 X} (hM : IsClosed (M : Set X))
    (hdisj : Disjoint (LinearMap.ker ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X)) M) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ M, c * ‖x‖ ≤ ‖(1 - K : X →L[𝕜] X) x‖ := by
  by_contra! hcon
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  -- Otherwise `M` contains vectors in the shell `‖c‖⁻¹ ≤ ‖x‖ ≤ 1` with arbitrarily small images.
  have hshell : ∀ n : ℕ, ∃ x ∈ M, ‖x‖ ≤ 1 ∧ ‖c‖⁻¹ ≤ ‖x‖ ∧
      ‖(1 - K : X →L[𝕜] X) x‖ ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨u, huM, hu⟩ := hcon (1 / (n + 1)) (by positivity)
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨d, -, hdlt, hdge, -⟩ := rescale_to_shell hc one_pos hu0
    refine ⟨d • u, M.smul_mem d huM, hdlt.le, by simpa using hdge, ?_⟩
    calc ‖(1 - K : X →L[𝕜] X) (d • u)‖ = ‖d‖ * ‖(1 - K : X →L[𝕜] X) u‖ := by
          rw [map_smul, norm_smul]
      _ ≤ ‖d‖ * (1 / (n + 1) * ‖u‖) := by gcongr
      _ = 1 / (n + 1) * ‖d • u‖ := by rw [norm_smul]; ring
      _ ≤ 1 / (n + 1) := mul_le_of_le_one_right (by positivity) hdlt.le
  choose v hvM hvle hvge hAv using hshell
  obtain ⟨y, ψ, -, hvsub, hyker⟩ := hK.exists_subseq_tendsto_one_sub_apply_eq hvle
    (squeeze_zero_norm hAv tendsto_one_div_add_atTop_nhds_zero_nat)
  have hyM : y ∈ M := hM.mem_of_tendsto hvsub (.of_forall fun k => hvM (ψ k))
  have hy0 : y = 0 := by simpa using hdisj.le_bot ⟨LinearMap.mem_ker.2 hyker, hyM⟩
  have hyge : ‖c‖⁻¹ ≤ ‖y‖ := ge_of_tendsto' hvsub.norm fun k => hvge (ψ k)
  rw [hy0, norm_zero] at hyge
  exact hyge.not_gt (by positivity)

/-- A compact perturbation of the identity has closed range. Neither `X` nor the scalar field
needs to be complete. -/
theorem _root_.IsCompactOperator.isClosed_range_one_sub (hK : IsCompactOperator K) :
    IsClosed (LinearMap.range ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) : Set X) :=
  (1 - K : X →L[𝕜] X).isClosed_range_of_exists_subseq_tendsto fun hv hAv ↦
    let ⟨x, ψ, hψ, hx, _⟩ := hK.exists_subseq_tendsto_one_sub_apply_eq hv hAv
    ⟨x, ψ, hψ, hx⟩

/-- Every power of a compact perturbation of the identity has closed range. -/
theorem _root_.IsCompactOperator.isClosed_range_pow_one_sub
    (hK : IsCompactOperator K) (n : ℕ) :
    IsClosed (LinearMap.range (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ n) : Set X) := by
  have h := (hK.isCompactOperator_one_sub_pow n).isClosed_range_one_sub
  rwa [sub_sub_cancel, ContinuousLinearMap.toLinearMap_pow] at h

/-- The ranges of powers of a compact perturbation of the identity eventually stabilise. -/
theorem _root_.IsCompactOperator.exists_range_pow_succ_eq_one_sub
    (hK : IsCompactOperator K) :
    ∃ p : ℕ, LinearMap.range (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ (p + 1)) =
      LinearMap.range (((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) ^ p) := by
  -- Apply the chain criterion to Mathlib's decreasing chain `iterateRange` of the ranges of the
  -- powers of `A = 1 - K`.
  let A : X →ₗ[𝕜] X := ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X)
  -- `iterateRange` is monotone into the order dual, that is, `V` is antitone.
  let V (n : ℕ) : Submodule 𝕜 X := A.iterateRange n
  have hstep (n : ℕ) (x : X) (hx : x ∈ V n) : x - K x ∈ V (n + 1) := by
    have hV : V (n + 1) = (V n).map A := LinearMap.iterateRange_succ
    have hAx : A x ∈ V (n + 1) := hV ▸ Submodule.mem_map_of_mem hx
    simpa only [A, ContinuousLinearMap.coe_coe, sub_apply, one_apply_eq_self] using hAx
  have hclosed (n : ℕ) : IsClosed (V n : Set X) := by
    simpa only [V, A, LinearMap.iterateRange_coe] using hK.isClosed_range_pow_one_sub n
  obtain ⟨p, hp⟩ := hK.exists_succ_eq_of_descending_chain (V := V)
    (fun n ↦ A.iterateRange.monotone (Nat.le_succ n))
    (fun n ↦ (hclosed (n + 1)).preimage continuous_subtypeVal) hstep
  exact ⟨p, by simpa only [V, A, LinearMap.iterateRange_coe] using hp⟩

/-- The cokernel of a compact perturbation of the identity is finite dimensional. -/
theorem _root_.IsCompactOperator.finiteDimensional_quotient_range_one_sub [CompleteSpace 𝕜]
    (hK : IsCompactOperator K) :
    FiniteDimensional 𝕜 (X ⧸ LinearMap.range ((1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X)) := by
  set A : X →L[𝕜] X := 1 - K
  obtain ⟨p, hp⟩ := hK.exists_range_pow_succ_eq_one_sub
  -- Then `ker (A ^ p)`, which is finite dimensional, together with `range A` spans `X`.
  have hcod : Codisjoint (LinearMap.ker ((A : X →ₗ[𝕜] X) ^ p))
      (LinearMap.range (A : X →ₗ[𝕜] X)) := by
    refine (LinearMap.codisjoint_ker_pow_range_pow_of_range_pow_succ_eq hp).mono_right ?_
    rw [← hp, pow_succ', Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range _ _
  have hkerfin := hK.finiteDimensional_ker_pow_one_sub p
  exact Submodule.FG.cofg_of_codisjoint hcod (Module.Finite.iff_fg.mp hkerfin)

end IsCompactOperator

end TauCeti

end
