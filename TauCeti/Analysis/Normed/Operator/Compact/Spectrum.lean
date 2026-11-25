/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Countable
import TauCeti.Analysis.Normed.Operator.Compact.RieszTheory
import TauCeti.LinearAlgebra.Eigenspace.KernelChain
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Eigenvalue thresholds for compact operators

Let `K` be a compact operator on a normed space over a nontrivially normed field `𝕜`. Then `K` has
only finitely many eigenvalues outside any ball of positive radius about zero. Neither `𝕜` nor the
ambient normed space needs to be complete; only the nontrivial norm on `𝕜` is used. For
eigenvectors `v n` with distinct eigenvalues `μ n`, the kernels of the operators
`∏ i < n, (K - μ i • 1)` form a strictly increasing chain of closed subspaces that
`K - μ n • 1` steps down, which the ascending-chain criterion
`IsCompactOperator.exists_succ_eq_of_ascending_chain` rules out when the `μ n` are bounded away
from zero. On a complete ambient space, the Fredholm alternative then shows that the spectrum is
countable and can accumulate only at zero, still without completeness of `𝕜`.

## References

* J. B. Conway, *A Course in Functional Analysis*, Chapter VI, Section 5.
-/

public section

open Module Submodule

namespace IsCompactOperator

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {K : E →L[𝕜] E}

/-- For a compact operator on a normed space over a nontrivially normed field, a sequence of
eigenvalues whose norms are bounded below by a positive constant is not injective. -/
private theorem not_injective_eigenvalues_of_norm_ge (hK : IsCompactOperator K)
    {ε : ℝ} (hε : 0 < ε) (μ : ℕ → 𝕜)
    (hμ : ∀ n, Module.End.HasEigenvalue (K : Module.End 𝕜 E) (μ n)) (hnorm : ∀ n, ε ≤ ‖μ n‖) :
    ¬ Function.Injective μ := by
  intro hinj
  let f : Module.End 𝕜 E := K
  let q (n : ℕ) : Polynomial 𝕜 :=
    ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (μ i))
  have hlt (n : ℕ) :
      LinearMap.ker (Polynomial.aeval f (q n)) < LinearMap.ker (Polynomial.aeval f (q (n + 1))) :=
    f.ker_aeval_prod_range_lt_succ (fun _ hi ↦ hinj.ne hi.ne') (hμ n)
  have hclosed (n : ℕ) : IsClosed (LinearMap.ker (Polynomial.aeval f (q n)) : Set E) := by
    rw [← ContinuousLinearMap.toLinearMap_aeval K (q n)]
    exact (Polynomial.aeval K (q n)).isClosed_ker
  obtain ⟨p, hp⟩ := hK.exists_succ_eq_of_ascending_chain hε hnorm (fun n ↦ (hlt n).le)
    (fun n ↦ (hclosed n).preimage continuous_subtypeVal)
    (fun n _ hx ↦ (f.mem_ker_aeval_prod_range_succ_iff μ n).1 hx)
  exact (hlt p).ne' hp

/-- A compact operator on a normed space over a nontrivially normed field has only finitely many
eigenvalues whose norm is at least a fixed positive number. Neither the scalar field nor the
ambient normed space needs to be complete. -/
theorem finite_eigenvalues_norm_ge (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | Module.End.HasEigenvalue (K : Module.End 𝕜 E) μ ∧ ε ≤ ‖μ‖}.Finite := by
  classical
  by_contra h
  let e := (Set.not_finite.mp h).natEmbedding
  exact hK.not_injective_eigenvalues_of_norm_ge hε (fun n ↦ (e n).val)
    (fun n ↦ (e n).property.1) (fun n ↦ (e n).property.2) (Subtype.coe_injective.comp e.injective)

/-- The set of eigenvalues of a compact operator on a normed space over a nontrivially normed field
is countable. Neither the scalar field nor the ambient normed space needs to be complete. -/
theorem countable_eigenvalues (hK : IsCompactOperator K) :
    {μ : 𝕜 | Module.End.HasEigenvalue (K : Module.End 𝕜 E) μ}.Countable := by
  have hc := Set.countable_iUnion fun n : ℕ ↦
    (hK.finite_eigenvalues_norm_ge (by positivity : 0 < 1 / (n + 1 : ℝ))).countable
  refine ((Set.countable_singleton (0 : 𝕜)).union hc).mono ?_
  intro μ hμ
  by_cases hzero : μ = 0
  · exact Or.inl hzero
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hzero)
    exact Or.inr (Set.mem_iUnion.mpr ⟨n, hμ, hn.le⟩)

variable [CompleteSpace E]

/-- Away from any ball of positive radius about zero, the spectrum of a compact operator on a
Banach space over a nontrivially normed field is finite. The scalar field need not be complete. -/
theorem finite_spectrum_norm_ge (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | μ ∈ spectrum 𝕜 K ∧ ε ≤ ‖μ‖}.Finite :=
  (hK.finite_eigenvalues_norm_ge hε).subset fun _ hμ ↦
    ⟨(hK.hasEigenvalue_iff_mem_spectrum (norm_pos_iff.mp (hε.trans_le hμ.2))).mpr hμ.1,
      hμ.2⟩

/-- The spectrum of a compact operator on a Banach space over a nontrivially normed field is
countable. The scalar field need not be complete. -/
theorem countable_spectrum (hK : IsCompactOperator K) : (spectrum 𝕜 K).Countable := by
  refine ((Set.countable_singleton (0 : 𝕜)).union hK.countable_eigenvalues).mono ?_
  intro μ hμ
  by_cases hzero : μ = 0
  · exact Or.inl hzero
  · exact Or.inr ((hK.hasEigenvalue_iff_mem_spectrum hzero).mpr hμ)

open Filter Topology in
/-- Zero is the only possible accumulation point of the spectrum of a compact operator on a Banach
space over a nontrivially normed field. In particular, every nonzero spectral value is isolated. -/
theorem eq_zero_of_accPt_spectrum (hK : IsCompactOperator K) {μ : 𝕜}
    (hμ : AccPt μ (𝓟 (spectrum 𝕜 K))) : μ = 0 := by
  by_contra hzero
  have hpos : 0 < ‖μ‖ / 2 := by positivity
  let S := {ν : 𝕜 | ν ∈ spectrum 𝕜 K ∧ ‖μ‖ / 2 ≤ ‖ν‖}
  have hS : S.Finite := hK.finite_spectrum_norm_ge hpos
  have hnear : ∀ᶠ ν in 𝓝 μ, ‖μ‖ / 2 < ‖ν‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds
      (half_lt_self (norm_pos_iff.mpr hzero))
  have havoid : ∀ᶠ ν in 𝓝 μ, ν ∉ S \ {μ} :=
    (hS.sdiff).isClosed.compl_mem_nhds (by simp)
  obtain ⟨ν, ⟨hne, hν⟩, hnorm, hnot⟩ :=
    ((accPt_iff_frequently.mp hμ).and_eventually (hnear.and havoid)).exists
  exact hnot ⟨⟨hν, hnorm.le⟩, hne⟩

open Filter Topology in
/-- The nonzero points of the real spectrum of a compact operator on a complex Banach space are
isolated. -/
theorem eventually_mem_spectrum_real_imp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {T : E →L[ℂ] E} (hT : IsCompactOperator T) {μ : ℝ}
    (hμ : μ ≠ 0) : ∀ᶠ y in 𝓝 μ, y ∈ spectrum ℝ T → y = μ := by
  by_contra hacc
  simp only [not_eventually, Classical.not_imp] at hacc
  have hacc' : AccPt (μ : ℂ) (𝓟 (spectrum ℂ T)) :=
    accPt_iff_frequently.2 <| Complex.continuous_ofReal.tendsto μ |>.frequently <|
      hacc.mono fun _ ⟨hy, hne⟩ ↦
        ⟨Complex.ofReal_injective.ne hne, (spectrum.algebraMap_mem_iff ℂ).2 hy⟩
  exact hμ (Complex.ofReal_eq_zero.1 (hT.eq_zero_of_accPt_spectrum hacc'))

end IsCompactOperator
