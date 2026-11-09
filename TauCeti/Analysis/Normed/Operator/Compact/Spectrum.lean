/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Normed.Module.RieszLemma

/-!
# Eigenvalue thresholds for compact operators

A compact operator has only finitely many eigenvalues outside any ball of positive radius
about zero. The scalar field is complete, but the ambient normed space need not be complete.
The proof uses the linear independence of eigenvectors for distinct eigenvalues and Riesz's
lemma on their finite-dimensional spans. On a complete ambient space, the Fredholm
alternative then shows that the spectrum is countable and can accumulate only at zero.

## References

* J. B. Conway, *A Course in Functional Analysis*, Chapter VI, Section 5.
-/

public section

open Module Submodule

namespace IsCompactOperator

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {K : E →L[𝕜] E}

/-- The successive finite eigenvector spans form a strictly increasing closed flag;
subtracting the next eigenvalue lowers the flag by one step. -/
private theorem exists_eigenvector_span_chain (μ : ℕ → 𝕜) (hinj : Function.Injective μ)
    (v : ℕ → E) (hv : ∀ n, Module.End.HasEigenvector (K : Module.End 𝕜 E) (μ n) (v n)) :
    ∃ V : ℕ → Submodule 𝕜 E, Monotone V ∧ (∀ n, IsClosed (V n : Set E)) ∧
      (∀ n, V n < V (n + 1)) ∧ (∀ n x, x ∈ V (n + 1) → K x - μ n • x ∈ V n) := by
  classical
  have hvapply (n : ℕ) : K (v n) = μ n • v n := (hv n).apply_eq_smul
  have hli := Module.End.eigenvectors_linearIndependent' (K : Module.End 𝕜 E) μ hinj v hv
  let V (n : ℕ) := span 𝕜 (v '' Set.Iio n)
  have hmono : Monotone V := fun _ _ h ↦ span_mono (Set.image_mono (Set.Iio_subset_Iio h))
  have hclosed (n : ℕ) : IsClosed (V n : Set E) := by
    have := FiniteDimensional.span_of_finite 𝕜 ((Set.finite_Iio n).image v)
    exact (V n).closed_of_finiteDimensional
  have hstrict (n : ℕ) : V n < V (n + 1) := by
    refine (hmono (Nat.le_succ n)).lt_of_ne ?_
    intro heq
    have hn : v n ∈ V n := heq ▸ subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
    exact hli.notMem_span_image (by simp) hn
  have hstep (n : ℕ) : ∀ x ∈ V (n + 1), K x - μ n • x ∈ V n := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · rw [hvapply, ← sub_smul]
        exact (V n).smul_mem _ (subset_span ⟨i, hi, rfl⟩)
      · simp [hi, hvapply]
    | zero => simp
    | add x y _ _ hx hy => simpa [map_add, smul_add, add_sub_add_comm] using (V n).add_mem hx hy
    | smul a x _ hx =>
      simpa only [map_smul, smul_sub, smul_comm a (μ n)] using (V n).smul_mem a hx
  exact ⟨V, hmono, hclosed, hstrict, hstep⟩

/-- An injective sequence of eigenvalues bounded away from zero would yield a bounded
sequence whose compact-operator images remain separated. -/
private theorem not_injective_eigenvalues_of_norm_ge (hK : IsCompactOperator K)
    {ε : ℝ} (hε : 0 < ε) (μ : ℕ → 𝕜)
    (hμ : ∀ n, Module.End.HasEigenvalue (K : Module.End 𝕜 E) (μ n)) (hnorm : ∀ n, ε ≤ ‖μ n‖) :
    ¬ Function.Injective μ := by
  classical
  intro hinj
  choose v hv using fun n ↦ (hμ n).exists_hasEigenvector
  obtain ⟨V, hmono, hclosed, hstrict, hstep⟩ := exists_eigenvector_span_chain μ hinj v hv
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  choose f hfmem hfnorm hfsep using fun n ↦
    TauCeti.riesz_lemma_of_norm_lt_of_lt hc (lt_add_one ‖c‖) (hclosed n) (hstrict n)
  have hsep (m n : ℕ) (hmn : m < n) : ε ≤ ‖K (f n) - K (f m)‖ := by
    have hne : μ n ≠ 0 := norm_pos_iff.mp (hε.trans_le (hnorm n))
    let y := (μ n)⁻¹ • (K (f m) - (K (f n) - μ n • f n))
    have hKm : K (f m) ∈ V n := by
      have h := (V n).add_mem (hmono hmn.le (hstep m _ (hfmem m)))
        ((V n).smul_mem (μ m) (hmono hmn (hfmem m)))
      simpa only [sub_add_cancel] using h
    have hy : y ∈ V n := (V n).smul_mem _ ((V n).sub_mem hKm (hstep n _ (hfmem n)))
    have heq : K (f n) - K (f m) = μ n • (f n - y) := by
      simp only [y, smul_sub, smul_smul, mul_inv_cancel₀ hne, inv_mul_cancel₀ hne, one_smul]
      abel
    rw [heq, norm_smul]
    exact (hnorm n).trans (le_mul_of_one_le_right (norm_nonneg _) (hfsep n y hy))
  obtain ⟨m, n, hmn, hlt⟩ := hK.exists_dist_lt_of_norm_le hfnorm hε
  rw [dist_eq_norm'] at hlt
  exact (hsep m n hmn).not_gt hlt

/-- A compact operator has only finitely many eigenvalues whose norm is at least a fixed
positive number. The ambient normed space need not be complete. -/
theorem finite_eigenvalues_norm_ge (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | Module.End.HasEigenvalue (K : Module.End 𝕜 E) μ ∧ ε ≤ ‖μ‖}.Finite := by
  classical
  by_contra h
  let e := (Set.not_finite.mp h).natEmbedding
  exact hK.not_injective_eigenvalues_of_norm_ge hε (fun n ↦ (e n).1)
    (fun n ↦ (e n).2.1) (fun n ↦ (e n).2.2) (Subtype.coe_injective.comp e.injective)

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

variable [CompleteSpace E]

/-- Away from any ball of positive radius about zero, the spectrum of a compact operator
on a Banach space is finite. -/
theorem finite_spectrum_norm_ge (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | μ ∈ spectrum 𝕜 K ∧ ε ≤ ‖μ‖}.Finite :=
  (hK.finite_eigenvalues_norm_ge hε).subset fun _ hμ ↦
    ⟨(hK.hasEigenvalue_iff_mem_spectrum (norm_pos_iff.mp (hε.trans_le hμ.2))).mpr hμ.1,
      hμ.2⟩

/-- The spectrum of a compact operator on a Banach space is countable. -/
theorem countable_spectrum (hK : IsCompactOperator K) : (spectrum 𝕜 K).Countable := by
  refine ((Set.countable_singleton (0 : 𝕜)).union hK.countable_eigenvalues).mono ?_
  intro μ hμ
  by_cases hzero : μ = 0
  · exact Or.inl hzero
  · exact Or.inr ((hK.hasEigenvalue_iff_mem_spectrum hzero).mpr hμ)

open Filter Topology in
/-- Zero is the only possible accumulation point of the spectrum of a compact operator
on a Banach space. In particular, every nonzero spectral value is isolated. -/
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

end IsCompactOperator
