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

/-!
# Eigenvalue thresholds for compact operators

A compact operator has only finitely many eigenvalues outside any ball of positive radius
about zero. Neither the scalar field nor the ambient normed space need be complete. For
eigenvectors `v n` with distinct eigenvalues `μ n`, the kernels of the operators
`∏ i < n, (K - μ i • 1)` form a strictly increasing chain of closed subspaces that
`K - μ n • 1` steps down, which the ascending-chain criterion
`IsCompactOperator.exists_succ_eq_of_ascending_chain` rules out when the `μ n` are bounded away
from zero. A nonzero spectral value is an eigenvalue: as for Riesz's form of the Fredholm
alternative, the ranges of the powers of `1 - μ⁻¹ • K` stabilise, so if this operator is
injective then it is surjective, and it is bounded below. Hence the spectrum is countable and
can accumulate only at zero, again without completeness.

## References

* J. B. Conway, *A Course in Functional Analysis*, Chapter VI, Section 5.
-/

public section

open Module Submodule

namespace IsCompactOperator

open Polynomial in
/-- For eigenvectors `v n` of a continuous linear endomorphism `K` of a `T1` topological vector
space, with distinct eigenvalues `μ n`, the kernels of the operators
`∏ i < n, (K - μ i • 1)` form a strictly increasing chain of closed subspaces, and
`K - μ n • 1` carries the `(n + 1)`-st one into the `n`-th. -/
private theorem exists_eigenvector_ker_chain {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    [T1Space E] {K : E →L[𝕜] E} (μ : ℕ → 𝕜) (hinj : Function.Injective μ) (v : ℕ → E)
    (hv : ∀ n, Module.End.HasEigenvector (K : Module.End 𝕜 E) (μ n) (v n)) :
    ∃ V : ℕ → Submodule 𝕜 E, (∀ n, IsClosed (V n : Set E)) ∧ (∀ n, V n < V (n + 1)) ∧
      (∀ n x, x ∈ V (n + 1) → K x - μ n • x ∈ V n) := by
  have hvapply (n : ℕ) : K (v n) = μ n • v n := (hv n).apply_eq_smul
  let P (n : ℕ) : E →L[𝕜] E := aeval K (∏ i ∈ Finset.range n, (X - C (μ i)))
  -- The factors of `P (n + 1)` commute, so `K - μ n • 1` can be split off on either side.
  have hP (n : ℕ) : P (n + 1) = P n * (K - μ n • 1) := by
    simp only [P, Finset.prod_range_succ, map_mul, map_sub, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one]
  have hP' (n : ℕ) : P (n + 1) = (K - μ n • 1) * P n := by
    simp only [P, Finset.prod_range_succ, mul_comm _ (X - C (μ n)), map_mul, map_sub, aeval_X,
      aeval_C, Algebra.algebraMap_eq_smul_one]
  have hPv (n m : ℕ) : P n (v m) = (∏ i ∈ Finset.range n, (μ m - μ i)) • v m := by
    induction n with
    | zero => simp [P]
    | succ n ih =>
      rw [hP', _root_.mul_apply_eq_comp, ih, map_smul, _root_.sub_apply, _root_.smul_apply,
        one_apply_eq_self, hvapply, ← sub_smul, smul_smul, Finset.prod_range_succ, mul_comm]
  let V (n : ℕ) : Submodule 𝕜 E := LinearMap.ker (P n : E →ₗ[𝕜] E)
  have hmem (n : ℕ) (x : E) : x ∈ V n ↔ P n x = 0 := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  refine ⟨V, fun n ↦ (P n).isClosed_ker,
    fun n ↦ IsConcreteLE.lt_iff_le_and_exists.2 ⟨?_, v n, ?_, ?_⟩, fun n x hx ↦ ?_⟩
  · intro x hx
    rw [hmem] at hx ⊢
    rw [hP', _root_.mul_apply_eq_comp, hx, map_zero]
  · rw [hmem, hPv, Finset.prod_eq_zero (Finset.self_mem_range_succ n) (sub_self _), zero_smul]
  · rw [hmem, hPv]
    refine smul_ne_zero (Finset.prod_ne_zero_iff.2 fun i hi ↦ sub_ne_zero.2 ?_)
      (Module.End.hasEigenvector_iff.1 (hv n)).2
    exact hinj.ne (Finset.mem_range.1 hi).ne'
  · rw [hmem] at hx ⊢
    rwa [hP, _root_.mul_apply_eq_comp, _root_.sub_apply, _root_.smul_apply,
      one_apply_eq_self] at hx

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {K : E →L[𝕜] E}

/-- An injective sequence of eigenvalues bounded away from zero would yield a strictly
increasing chain of closed subspaces that the compact operator steps down. -/
private theorem not_injective_eigenvalues_of_norm_ge (hK : IsCompactOperator K)
    {ε : ℝ} (hε : 0 < ε) (μ : ℕ → 𝕜)
    (hμ : ∀ n, Module.End.HasEigenvalue (K : Module.End 𝕜 E) (μ n)) (hnorm : ∀ n, ε ≤ ‖μ n‖) :
    ¬ Function.Injective μ := by
  intro hinj
  choose v hv using fun n ↦ (hμ n).exists_hasEigenvector
  obtain ⟨V, hclosed, hstrict, hstep⟩ := exists_eigenvector_ker_chain μ hinj v hv
  obtain ⟨p, hp⟩ := hK.exists_succ_eq_of_ascending_chain hε hnorm (fun n ↦ (hstrict n).le)
    (fun n ↦ (hclosed n).preimage continuous_subtypeVal) hstep
  exact (hstrict p).ne' hp

/-- A compact operator has only finitely many eigenvalues whose norm is at least a fixed
positive number. Neither the scalar field nor the ambient normed space need be complete. -/
theorem finite_eigenvalues_norm_ge (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | Module.End.HasEigenvalue (K : Module.End 𝕜 E) μ ∧ ε ≤ ‖μ‖}.Finite := by
  classical
  by_contra h
  let e := (Set.not_finite.mp h).natEmbedding
  exact hK.not_injective_eigenvalues_of_norm_ge hε (fun n ↦ (e n).val)
    (fun n ↦ (e n).property.1) (fun n ↦ (e n).property.2) (Subtype.coe_injective.comp e.injective)

/-- The set of eigenvalues of a compact operator is countable, even when the ambient space
is not complete. -/
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

/-- A nonzero spectral value of a compact operator is an eigenvalue, where the spectrum is taken
in the algebra of continuous endomorphisms. Unlike Mathlib's
`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`, neither the ambient normed space nor the
scalar field needs to be complete. -/
theorem hasEigenvalue_of_mem_spectrum (hK : IsCompactOperator K) {μ : 𝕜} (hμ : μ ≠ 0)
    (h : μ ∈ spectrum 𝕜 K) : Module.End.HasEigenvalue (K : Module.End 𝕜 E) μ := by
  by_contra hne
  -- Rescale to `A = 1 - μ⁻¹ • K`, a compact perturbation of the identity, with `ker A = 0`.
  let A : E →L[𝕜] E := 1 - μ⁻¹ • K
  have hK' : IsCompactOperator (μ⁻¹ • K : E →L[𝕜] E) := hK.smul μ⁻¹
  have hker : LinearMap.ker (A : E →ₗ[𝕜] E) = Module.End.eigenspace (K : Module.End 𝕜 E) μ := by
    ext x
    simp only [A, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, _root_.sub_apply,
      _root_.smul_apply, one_apply_eq_self, sub_eq_zero, eq_inv_smul_iff₀ hμ,
      Module.End.mem_eigenspace_iff]
    exact eq_comm
  have heig : Module.End.eigenspace (K : Module.End 𝕜 E) μ = ⊥ := by
    simpa only [Module.End.hasEigenvalue_iff, ne_eq, not_not] using hne
  have hinj : Function.Injective (A : E →ₗ[𝕜] E) := LinearMap.ker_eq_bot.1 (hker.trans heig)
  -- The ranges of the powers of `A` stabilise, so the injective `A` is surjective.
  have hsurj : Function.Surjective (A : E →ₗ[𝕜] E) := by
    obtain ⟨p, hp⟩ := hK'.exists_range_pow_succ_eq_one_sub
    intro y
    obtain ⟨z, hz⟩ : ((A : E →ₗ[𝕜] E) ^ p) y ∈ LinearMap.range ((A : E →ₗ[𝕜] E) ^ (p + 1)) :=
      hp ▸ LinearMap.mem_range_self _ y
    rw [pow_succ, _root_.mul_apply_eq_comp, FunLike.coe_pow_eq_iterate] at hz
    exact ⟨z, hinj.iterate p hz⟩
  -- `A` is bounded below, so its inverse is continuous and `A` is a unit.
  obtain ⟨c, hc, hbound⟩ := hK'.exists_pos_mul_norm_le_of_disjoint_ker (M := ⊤)
    (by simpa only [Submodule.top_coe] using isClosed_univ)
    (disjoint_top.2 (hker.trans heig))
  let e := LinearEquiv.ofBijective (A : E →ₗ[𝕜] E) ⟨hinj, hsurj⟩
  let e' := e.toContinuousLinearEquivOfBounds ‖A‖ c⁻¹ A.le_opNorm fun y ↦ by
    have hy : (1 - μ⁻¹ • K : E →L[𝕜] E) (e.symm y) = y := e.apply_symm_apply y
    rw [le_inv_mul_iff₀ hc]
    simpa only [hy] using hbound (e.symm y) Submodule.mem_top
  -- By construction `e'` applies `A`.
  have hunit : IsUnit A := ⟨ContinuousLinearEquiv.toUnit e', by ext x; rfl⟩
  have h1 : (1 : 𝕜) ∈ spectrum 𝕜 (μ⁻¹ • K) := by
    simpa [Units.smul_def, smul_eq_mul, hμ] using
      (spectrum.smul_mem_smul_iff (a := K) (s := μ) (r := Units.mk0 μ⁻¹ (inv_ne_zero hμ))).2 h
  rw [spectrum.mem_iff, map_one] at h1
  exact h1 hunit

/-- Away from any ball of positive radius about zero, the spectrum of a compact operator is
finite. Neither the scalar field nor the ambient normed space need be complete. -/
theorem finite_spectrum_norm_ge (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | μ ∈ spectrum 𝕜 K ∧ ε ≤ ‖μ‖}.Finite :=
  (hK.finite_eigenvalues_norm_ge hε).subset fun _ hμ ↦
    ⟨hK.hasEigenvalue_of_mem_spectrum (norm_pos_iff.mp (hε.trans_le hμ.2)) hμ.1, hμ.2⟩

/-- The spectrum of a compact operator is countable. Neither the scalar field nor the ambient
normed space need be complete. -/
theorem countable_spectrum (hK : IsCompactOperator K) : (spectrum 𝕜 K).Countable := by
  refine ((Set.countable_singleton (0 : 𝕜)).union hK.countable_eigenvalues).mono ?_
  intro μ hμ
  by_cases hzero : μ = 0
  · exact Or.inl hzero
  · exact Or.inr (hK.hasEigenvalue_of_mem_spectrum hzero hμ)

open Filter Topology in
/-- Zero is the only possible accumulation point of the spectrum of a compact operator. In
particular, every nonzero spectral value is isolated. -/
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
/-- The nonzero points of the real spectrum of a compact operator on a complex normed space are
isolated. -/
theorem eventually_mem_spectrum_real_imp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : E →L[ℂ] E} (hT : IsCompactOperator T) {μ : ℝ}
    (hμ : μ ≠ 0) : ∀ᶠ y in 𝓝 μ, y ∈ spectrum ℝ T → y = μ := by
  by_contra hacc
  simp only [not_eventually, Classical.not_imp] at hacc
  have hacc' : AccPt (μ : ℂ) (𝓟 (spectrum ℂ T)) :=
    accPt_iff_frequently.2 <| Complex.continuous_ofReal.tendsto μ |>.frequently <|
      hacc.mono fun _ ⟨hy, hne⟩ ↦
        ⟨Complex.ofReal_injective.ne hne, (spectrum.algebraMap_mem_iff ℂ).2 hy⟩
  exact hμ (Complex.ofReal_eq_zero.1 (hT.eq_zero_of_accPt_spectrum hacc'))

end IsCompactOperator
