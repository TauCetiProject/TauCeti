/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the finitary permutation action on path space with its ergodicity interface, the
-- zero-one characterisation of i.i.d. laws, and the extremality of ergodic actions.
public import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.Ergodic
public import TauCeti.Probability.Exchangeability.PathSpace.Law.ZeroOne
public import TauCeti.MeasureTheory.Group.ErgodicExtreme
-- Non-public: shift-invariant events are exchangeable events; exchangeable path laws are
-- shift-preserving.
import TauCeti.Probability.Exchangeability.PathSpace.Invariant.Tail
import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.ToContractable

/-!
# Extreme exchangeable laws

The extreme points of the convex set of exchangeable probability measures on `ℕ → α` are exactly
the i.i.d. product laws. The main theorem `exchangeable_extreme_iff_iid` states this using Mathlib's
`Set.extremePoints` for the natural `ℝ≥0∞`-module structure on measures.

The exchangeable probability laws are the probability laws invariant under the action of the
finitely supported permutations of `ℕ` (`exchangeableLaw_iff_smulInvariantMeasure`). Extremality
among them is therefore ergodicity of that action, by the general characterisation
`ErgodicSMul.iff_mem_extremePoints` for a countable group; ergodicity is triviality of the
exchangeable σ-algebra (`exchangeableSigma_trivial_iff_ergodicSMul`); and, for a standard Borel
state space, triviality is the i.i.d. property (`exchangeableSigma_trivial_iff_iid`). The
implication from i.i.d. to extreme needs no standard Borel hypothesis.

The one-sided shift ergodicity of an i.i.d. law, `ergodic_shift_infinitePi_const`, is recorded
here as well: shift-invariant events are exchangeable events, so the Hewitt–Savage zero-one law
applies.

## Main results

* `exchangeableProbabilityMeasures_eq` — the exchangeable probability laws are the invariant
  probability laws of the finitary action.
* `ergodic_shift_infinitePi_const` — an i.i.d. product law is ergodic for the one-sided shift.
* `infinitePi_mem_extremePoints_exchangeable` — an i.i.d. product law is an extreme exchangeable
  law, over an arbitrary measurable space.
* `exchangeable_extreme_iff_iid` — the extreme exchangeable probability laws are exactly the
  i.i.d. product laws.

## References

* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1.
* Edwin Hewitt and Leonard J. Savage, *Symmetric measures on Cartesian products*, Transactions of
  the American Mathematical Society **80** (1955), 470–501.
-/

public section

noncomputable section

open Filter MeasurableSpace MeasureTheory TauCeti.MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The exchangeable probability laws are the invariant measures of total mass one of the finitary
permutation action. -/
theorem exchangeableProbabilityMeasures_eq :
    {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν}
      = invariantMeasuresOfMeasureUnivEq FinitaryPerm (ℕ → α) 1 := by
  ext ν
  rw [mem_invariantMeasuresOfMeasureUnivEq_iff]
  constructor
  · rintro ⟨hν, hp⟩; exact ⟨hν.smulInvariantMeasure, hp.measure_univ⟩
  · rintro ⟨hν, hp⟩
    have : IsProbabilityMeasure ν := ⟨hp⟩
    exact ⟨exchangeableLaw_iff_smulInvariantMeasure.2 hν, inferInstance⟩

/-- An i.i.d. infinite product law is ergodic for the one-sided shift.

The shift-invariant σ-algebra is contained in the exchangeable σ-algebra, and the coordinate
process is independent and identically distributed under the product law, so Hewitt–Savage makes
every shift-invariant event null or conull. -/
theorem ergodic_shift_infinitePi_const (P : ProbabilityMeasure α) :
    Ergodic (shift α) (Measure.infinitePi fun _ : ℕ => (P : Measure α)) := by
  have hexchLaw : ExchangeableLaw (Measure.infinitePi fun _ : ℕ => (P : Measure α)) :=
    exchangeableLaw_infinitePi_const P
  refine { hexchLaw.contractableLaw.measurePreserving_shift with aeconst_set := ?_ }
  intro s hs hs_shift
  have hs_inv : MeasurableSet[MeasurableSpace.invariants (shift α)] s := ⟨hs, hs_shift⟩
  have hzeroOne := exchangeableSigma_trivial_of_infinitePi P
    (invariants_shift_le_exchangeableSigma (α := α) s hs_inv)
  refine eventuallyEmptyOrUniv_iff.2 ?_
  rcases hzeroOne with hzero | hone
  · exact Or.inr (ae_iff.mpr (by simpa using hzero))
  · exact Or.inl ((_root_.MeasureTheory.mem_ae_iff_prob_eq_one hs).2 hone)

/-- **An i.i.d. law is an extreme exchangeable law.** The infinite product is ergodic for the
finitary permutation action, hence extreme among its invariant probability laws, which are the
exchangeable ones. -/
theorem infinitePi_mem_extremePoints_exchangeable (P : ProbabilityMeasure α) :
    (Measure.infinitePi fun _ : ℕ => (P : Measure α)) ∈ extremePoints ℝ≥0∞
      {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} := by
  rw [exchangeableProbabilityMeasures_eq]
  have := ergodicSMul_infinitePi_const P
  exact ErgodicSMul.mem_extremePoints

/-- **The extreme exchangeable laws are exactly the i.i.d. laws.** For a standard Borel
state space, a probability measure on `ℕ → α` is an extreme point of the set of exchangeable
probability measures if and only if it is an infinite product `P^{⊗ℕ}` for some probability
measure `P` on `α`: extremality is ergodicity of the finitary permutation action, which is
triviality of the exchangeable σ-algebra, which is the i.i.d. property. -/
theorem exchangeable_extreme_iff_iid [StandardBorelSpace α]
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] :
    ρ ∈ extremePoints ℝ≥0∞
        {ν : Measure (ℕ → α) | ExchangeableLaw ν ∧ IsProbabilityMeasure ν} ↔
      ∃ P : ProbabilityMeasure α,
        ρ = Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  constructor
  · intro h
    have hexch : ExchangeableLaw ρ := h.1.1
    rw [exchangeableProbabilityMeasures_eq, ← ErgodicSMul.iff_mem_extremePoints] at h
    exact (exchangeableSigma_trivial_iff_iid hexch).1
      ((exchangeableSigma_trivial_iff_ergodicSMul hexch).2 h)
  · rintro ⟨P, rfl⟩
    exact infinitePi_mem_extremePoints_exchangeable P

end Probability

end TauCeti
