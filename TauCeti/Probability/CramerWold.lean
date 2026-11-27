/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Pettis

/-!
# The Cramér–Wold theorem on varying probability spaces

Convergence in distribution of a sequence of random vectors `X n : Ω n → E` with values in a
finite-dimensional real inner product space `E` is equivalent to convergence in distribution of
every scalar inner-product projection `ω ↦ ⟪X n ω, t⟫` (`t : E`).

Mathlib's `tendstoInDistribution_iff_tendstoInDistribution_inner` states this equivalence when all
`X n` share a single probability space `(Ω, P)` and assumes almost-everywhere measurability of `X n`
and of the limit `X'` separately. Allowing `(Ω n, P n)` to depend on `n` is needed whenever row `n`
of a triangular array or an `n`-fold product sample space `(Fin n → α, Measure.pi …)` lives on its
own probability space. Moreover, no separate measurability hypotheses are needed: both sides of the
equivalence already entail almost-everywhere measurability of `X n` and `X'`.

## Main results

* `TauCeti.tendstoInDistribution_iff_tendstoInDistribution_inner_dep`: the Cramér–Wold theorem
  for sequences `X : (n : ℕ) → Ω n → E` on varying probability spaces `(Ω n, P n)`, without
  external measurability hypotheses.

## Implementation notes

The `_dep` suffix follows `MeasureTheory.Integrable.fintype_prod_dep` to distinguish the
dependent-space generalization `(Ω n, P n)` from Mathlib's root-level single-space theorem
`tendstoInDistribution_iff_tendstoInDistribution_inner`.

On the right-hand side of `tendstoInDistribution_iff_tendstoInDistribution_inner_dep`, each
projection `ω ↦ ⟪X n ω, t⟫` is almost everywhere measurable by
`TendstoInDistribution.forall_aemeasurable`; Pettis' measurability theorem
(`TauCeti.aestronglyMeasurable_iff_forall_inner`) reconstructs almost-everywhere strong
measurability (hence almost-everywhere measurability) of `X n` and `X'`, after which
`MeasureTheory.TendstoInDistribution.of_tendsto_charFun` and
`MeasureTheory.charFun_map_eq_charFun_map_inner_one` conclude on varying probability spaces.

## References

* H. Cramér and H. Wold, “Some theorems on distribution functions,” *Journal of the London
  Mathematical Society* 11 (1936), 290–294.
* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Theorem 29.4.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Section 2.2.
-/

public section

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Cramér–Wold theorem on varying probability spaces.** Convergence in distribution of random
vectors `X n : Ω n → E` on probability spaces `(Ω n, P n)` to `X' : Ω' → E` on `(Ω', P')`, where
`E` is a finite-dimensional real inner product space with its Borel σ-algebra, is equivalent to
convergence in distribution of all scalar projections `ω ↦ ⟪X n ω, t⟫` to `ω' ↦ ⟪X' ω', t⟫`. -/
theorem tendstoInDistribution_iff_tendstoInDistribution_inner_dep
    {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)} {P : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : (n : ℕ) → Ω n → E} {X' : Ω' → E} :
    TendstoInDistribution X atTop X' P P' ↔
      ∀ t, TendstoInDistribution (fun n ω ↦ ⟪X n ω, t⟫) atTop (fun ω' ↦ ⟪X' ω', t⟫) P P' where
  mp h t := h.continuous_comp (continuous_id.inner continuous_const)
  mpr h := by
    have hX (n : ℕ) : AEMeasurable (X n) (P n) :=
      ((aestronglyMeasurable_iff_forall_inner (𝕜 := ℝ)).mpr fun t ↦ by
        simpa only [real_inner_comm t] using
          ((h t).forall_aemeasurable n).aestronglyMeasurable).aemeasurable
    have hX' : AEMeasurable X' P' :=
      ((aestronglyMeasurable_iff_forall_inner (𝕜 := ℝ)).mpr fun t ↦ by
        simpa only [real_inner_comm t] using
          (h t).aemeasurable_limit.aestronglyMeasurable).aemeasurable
    refine .of_tendsto_charFun hX hX' fun t ↦ ?_
    rw [charFun_map_eq_charFun_map_inner_one hX']
    exact ((h t).tendsto_charFun 1).congr fun n ↦
      (charFun_map_eq_charFun_map_inner_one (hX n) t).symm

end TauCeti
