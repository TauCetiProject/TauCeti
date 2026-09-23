/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Dissipative.Basic
public import TauCeti.Analysis.Normed.Module.DualitySet
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The duality-map characterization of dissipativity

On a real normed space `X`, an unbounded operator `A : X →ₗ.[ℝ] X` is dissipative in the
resolvent-range sense of `TauCeti.Semigroups.IsDissipative`,

`lambda * ‖x‖ ≤ ‖lambda • x - A x‖` for all `lambda > 0` and `x ∈ D(A)`,

exactly when for every `x ∈ D(A)` **some** element `x'` of the duality set
`J(x) = {x' | x' x = ‖x‖², ‖x'‖ = ‖x‖}` satisfies `x' (A x) ≤ 0`
(`isDissipative_iff_exists_mem_dualitySet`). This is the Banach-space counterpart of the Hilbert
condition `⟪A x, x⟫ ≤ 0` of `TauCeti/Analysis/Semigroups/Dissipative/Hilbert.lean`, and the form in
which dissipativity is usually verified for concrete operators on `Lᵖ`, `C₀` or `ℓᵖ`, where the
duality set is explicit.

One direction is a one-line estimate. For the other, dissipativity at `lambda` provides a norming
functional `g_lambda` of `lambda x - A x` of norm at most one, and the dissipativity inequality
forces `g_lambda (A x) ≤ 0` and `g_lambda x ≥ ‖x‖ - ‖A x‖ / lambda`. A weak-* cluster point of
these functionals as `lambda → ∞`, which exists by the Banach--Alaoglu theorem, satisfies
`g x = ‖x‖` and `g (A x) ≤ 0`, and `‖x‖ • g` is the required element of `J(x)`.

For the generator of a contraction semigroup the inequality holds for **every** element of the
duality set (`ContractionSemigroup.apply_generator_nonpos_of_mem_dualitySet`), since
`x' (S(t) x - x) ≤ ‖x‖ ‖S(t) x‖ - ‖x‖² ≤ 0` for `x' ∈ J(x)`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Proposition II.3.23.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1, Theorem 4.2 and Theorem 4.3.
-/

public section

open Filter Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Dissipativity at `lambda = n + 1` supplies a functional of norm at most one that is
nonpositive on `A x` and nearly norming for `x`, with defect `‖A x‖ / (n + 1)`. -/
private theorem IsDissipative.exists_norm_le_one_apply_nonpos {A : X →ₗ.[ℝ] X}
    (hA : IsDissipative A) (x : A.domain) (n : ℕ) :
    ∃ g : StrongDual ℝ X, ‖g‖ ≤ 1 ∧ g (A x) ≤ 0 ∧
      ‖(x : X)‖ - ‖A x‖ * (1 / ((n : ℝ) + 1)) ≤ g x := by
  have hlam : (0 : ℝ) < n + 1 := by positivity
  obtain ⟨g, hg, hgy⟩ := exists_dual_vector'' ℝ (((n : ℝ) + 1) • (x : X) - A x)
  simp only [RCLike.ofReal_real_eq_id, id_eq, map_sub, map_smul, smul_eq_mul] at hgy
  have hdis := hA _ hlam x
  have hbound : ∀ z : X, |g z| ≤ ‖z‖ := fun z =>
    (g.le_opNorm z).trans (mul_le_of_le_one_left (norm_nonneg z) hg)
  have hgx := (le_abs_self _).trans (hbound x)
  have hgA := neg_le_of_abs_le (hbound (A x))
  refine ⟨g, hg, by nlinarith, ?_⟩
  rw [mul_one_div, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hlam]
  linarith

/-- **Dissipative operators are dissipative in the duality-map sense.** If `A` is dissipative,
then every `x ∈ D(A)` has an element `x'` of its duality set with `x' (A x) ≤ 0`.

The functional is a weak-* cluster point, supplied by the Banach--Alaoglu theorem, of norming
functionals of `lambda • x - A x` as `lambda → ∞`. -/
theorem IsDissipative.exists_mem_dualitySet_apply_nonpos {A : X →ₗ.[ℝ] X}
    (hA : IsDissipative A) (x : A.domain) :
    ∃ f ∈ dualitySet ℝ (x : X), f (A x) ≤ 0 := by
  let K : ℕ → Set (WeakDual ℝ X) := fun n =>
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1 ∩ {w | w (A x) ≤ 0} ∩
      {w | ‖(x : X)‖ - ‖A x‖ * (1 / ((n : ℝ) + 1)) ≤ w x}
  have hclosed : ∀ n, IsClosed (K n) := fun n =>
    ((WeakDual.isClosed_closedBall 0 1).inter
      (isClosed_le (WeakDual.eval_continuous _) continuous_const)).inter
      (isClosed_le continuous_const (WeakDual.eval_continuous _))
  have hmono : ∀ n, K (n + 1) ⊆ K n := by
    rintro n w ⟨hw, hwx⟩
    refine ⟨hw, ?_⟩
    simp only [Set.mem_ofPred_eq] at hwx ⊢
    refine le_trans ?_ hwx
    gcongr
    linarith
  have hne : ∀ n, (K n).Nonempty := fun n => by
    obtain ⟨g, hg, hgA, hgx⟩ := hA.exists_norm_le_one_apply_nonpos x n
    exact ⟨StrongDual.toWeakDual g, ⟨by simpa using hg, hgA⟩, hgx⟩
  have hcompact : IsCompact (K 0) :=
    (WeakDual.isCompact_closedBall 0 1).of_isClosed_subset (hclosed 0)
      (fun w hw => hw.1.1)
  obtain ⟨w, hw⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hmono hne hcompact
      hclosed
  rw [Set.mem_iInter] at hw
  obtain ⟨⟨hw1, hwA⟩, -⟩ := hw 0
  let g := WeakDual.toStrongDual w
  have hg : ‖g‖ ≤ 1 := by simpa using hw1
  have hgA : g (A x) ≤ 0 := hwA
  -- The defects `‖A x‖ / (n + 1)` tend to zero, so `g` norms `x`.
  have hgx : g x = ‖(x : X)‖ := by
    refine le_antisymm ((le_abs_self _).trans ((g.le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hg))) ?_
    have hlim : Tendsto (fun n : ℕ => ‖(x : X)‖ - ‖A x‖ * (1 / ((n : ℝ) + 1))) atTop
        (𝓝 ‖(x : X)‖) := by
      simpa using tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖A x‖)
    exact le_of_tendsto' hlim fun n => (hw n).2
  refine ⟨_, smul_mem_dualitySet hg (by simpa using hgx), ?_⟩
  simpa using mul_nonpos_of_nonneg_of_nonpos (norm_nonneg (x : X)) hgA

/-- **The duality-map characterization of dissipativity.** An unbounded operator on a real normed
space is dissipative exactly when every `x ∈ D(A)` has an element `x'` of its duality set
`J(x)` with `x' (A x) ≤ 0`. -/
theorem isDissipative_iff_exists_mem_dualitySet (A : X →ₗ.[ℝ] X) :
    IsDissipative A ↔ ∀ x : A.domain, ∃ f ∈ dualitySet ℝ (x : X), f (A x) ≤ 0 := by
  refine ⟨fun hA => hA.exists_mem_dualitySet_apply_nonpos, fun h lambda _ x => ?_⟩
  -- `‖x‖ ‖lambda x - A x‖ ≥ x' (lambda x - A x) = lambda ‖x‖² - x' (A x) ≥ lambda ‖x‖²`.
  obtain ⟨f, hf, hfA⟩ := h x
  obtain ⟨hfx, hnorm⟩ := mem_dualitySet_iff.mp hf
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hfx
  have hle : f (lambda • (x : X) - A x) ≤ ‖(x : X)‖ * ‖lambda • (x : X) - A x‖ :=
    hnorm ▸ (le_abs_self _).trans (f.le_opNorm _)
  rw [map_sub, map_smul, smul_eq_mul, hfx] at hle
  rcases (norm_nonneg (x : X)).eq_or_lt with hx | hx
  · rw [← hx, mul_zero]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left (by nlinarith) hx

namespace ContractionSemigroup

/-- **The generator of a contraction semigroup is dissipative for every element of the duality
set**: `x' (A x) ≤ 0` whenever `x ∈ D(A)` and `x' ∈ J(x)`. This strengthens the existential
condition that characterizes general dissipative operators
(`isDissipative_iff_exists_mem_dualitySet`). -/
theorem apply_generator_nonpos_of_mem_dualitySet (S : ContractionSemigroup X)
    (x : S.toStronglyContinuousSemigroup.generator.domain) {f : StrongDual ℝ X}
    (hf : f ∈ dualitySet ℝ (x : X)) :
    f (S.toStronglyContinuousSemigroup.generator x) ≤ 0 := by
  obtain ⟨hfx, hnorm⟩ := mem_dualitySet_iff.mp hf
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hfx
  refine le_of_tendsto ((f.continuous.tendsto _).comp
    (S.toStronglyContinuousSemigroup.generator_tendsto ⟨x, by simpa using x.2⟩)) ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  -- `x' (S(t) x) ≤ ‖x'‖ ‖S(t) x‖ ≤ ‖x‖ ‖x‖ = x' x`.
  have hSx : ‖S.realOperator t (x : X)‖ ≤ ‖(x : X)‖ :=
    ((S.realOperator t).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (S.contracting_real t ht.le))
  have hle : f (S.realOperator t (x : X)) ≤ ‖(x : X)‖ * ‖(x : X)‖ :=
    (le_abs_self _).trans ((f.le_opNorm _).trans (by rw [hnorm]; gcongr))
  simp only [Function.comp_apply, map_smul, map_sub, smul_eq_mul, hfx]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith)

end ContractionSemigroup

end TauCeti.Semigroups

end
