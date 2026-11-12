/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Exponential.Basic
-- Proof-only: Tannery's theorem, for continuity of a series at `0`.
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Pointwise limits and series of Bernstein functions

Bernstein functions are closed under pointwise limits on `(0, ∞)`, provided the limit is
right-continuous at `0`, and under series that converge at a single positive point.

The derivative condition in `TauCeti.IsBernsteinFunction` is not visibly stable under pointwise
limits, since nothing says that the derivatives converge. The proof instead uses the
characterization of Bernstein functions by their exponentials,
`TauCeti.isBernsteinFunction_of_forall_isCompletelyMonotoneOnIoi_exp_neg_mul`: each
`t ↦ e^{-x f(t)}` is a pointwise limit of completely monotone functions, so it is completely
monotone by `TauCeti.isCompletelyMonotoneOnIoi_of_tendsto`.

The right-continuity hypothesis cannot be dropped. The Bernstein functions `t ↦ 1 - e^{-n t}`
converge on all of `[0, ∞)` to the function that is `0` at `0` and `1` elsewhere, which is not
continuous at `0`. For a series of Bernstein functions no such hypothesis is needed: concavity
bounds each summand by a multiple of its value at one positive point
(`TauCeti.IsBernsteinFunction.apply_le_div_mul_apply`), so the series converges everywhere on
`[0, ∞)`, and by Tannery's theorem its sum is continuous at `0`.

## Main declarations

* `TauCeti.isBernsteinFunction_of_tendsto`: a pointwise limit on `(0, ∞)` of Bernstein functions
  that is right-continuous at `0` is a Bernstein function.
* `TauCeti.IsBernsteinFunction.summable_of_summable`: a series of Bernstein functions converging
  at one positive point converges at every point of `[0, ∞)`.
* `TauCeti.IsBernsteinFunction.tsum`: the sum of such a series is a Bernstein function.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Corollary 3.8.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- **Bernstein functions are closed under pointwise limits.** A pointwise limit on `(0, ∞)` of
Bernstein functions is a Bernstein function, once it is right-continuous at `0`. That hypothesis
cannot be dropped: see the module docstring. -/
theorem isBernsteinFunction_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {F : ι → ℝ → ℝ} (hF : ∀ᶠ i in L, IsBernsteinFunction (F i))
    (hlim : ∀ u : ℝ, 0 < u → Tendsto (fun i => F i u) L (𝓝 (f u)))
    (hzero : ContinuousWithinAt f (Ici 0) 0) :
    IsBernsteinFunction f := by
  have hpos : ∀ u : ℝ, 0 < u → 0 ≤ f u := fun u hu =>
    ge_of_tendsto (hlim u hu) (hF.mono fun i hi => hi.nonneg hu.le)
  refine isBernsteinFunction_of_forall_isCompletelyMonotoneOnIoi_exp_neg_mul hzero
    (fun t ht => ?_) fun x hx => ?_
  · rcases ht.lt_or_eq with ht | rfl
    · exact hpos t ht
    · exact ge_of_tendsto (hzero.mono Ioi_subset_Ici_self) (eventually_nhdsWithin_of_forall hpos)
  · refine isCompletelyMonotoneOnIoi_of_tendsto (hF.mono fun i hi =>
      (hi.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul hx.le).isCompletelyMonotoneOnIoi)
      fun u hu => ?_
    have hc : Continuous fun y : ℝ => Real.exp (-x * y) := by fun_prop
    exact (hc.tendsto (f u)).comp (hlim u hu)

namespace IsBernsteinFunction

variable {ι : Type*} {F : ι → ℝ → ℝ}

/-- A series of Bernstein functions that converges at one positive point `t₀` converges at every
point of `[0, ∞)`: below `t₀` by monotonicity, and above it by the linear growth bound
`TauCeti.IsBernsteinFunction.apply_le_div_mul_apply`. -/
theorem summable_of_summable (hF : ∀ i, IsBernsteinFunction (F i)) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hsum : Summable fun i => F i t₀) {t : ℝ} (ht : 0 ≤ t) : Summable fun i => F i t := by
  rcases le_total t t₀ with htt₀ | ht₀t
  · exact hsum.of_nonneg_of_le (fun i => (hF i).nonneg ht) fun i =>
      (hF i).monotoneOn (mem_Ici.mpr ht) (mem_Ici.mpr ht₀.le) htt₀
  · exact (hsum.mul_left (t / t₀)).of_nonneg_of_le (fun i => (hF i).nonneg ht) fun i =>
      (hF i).apply_le_div_mul_apply ht₀ ht₀t

/-- **Bernstein functions are closed under series.** If a series of Bernstein functions converges
at one positive point, then its sum is a Bernstein function. No continuity hypothesis is needed
at `0`: the summands are dominated near `0` by their values at `t₀`. -/
protected theorem tsum (hF : ∀ i, IsBernsteinFunction (F i)) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hsum : Summable fun i => F i t₀) : IsBernsteinFunction fun t => ∑' i, F i t := by
  refine isBernsteinFunction_of_tendsto (L := atTop) (F := fun s t => ∑ i ∈ s, F i t)
    (.of_forall fun s => IsBernsteinFunction.sum fun i _ => hF i)
    (fun u hu => (summable_of_summable hF ht₀ hsum hu.le).hasSum) ?_
  -- Near `0`, each summand is dominated by its value at `t₀` (Tannery's theorem).
  refine tendsto_tsum_of_dominated_convergence (bound := fun i => F i t₀) hsum
    (fun i => (hF i).continuousOn 0 (mem_Ici.mpr le_rfl)) ?_
  filter_upwards [inter_mem_nhdsWithin (Ici 0) (Iio_mem_nhds ht₀)] with t ht i
  rw [Real.norm_of_nonneg ((hF i).nonneg ht.1)]
  exact (hF i).monotoneOn ht.1 (mem_Ici.mpr ht₀.le) (le_of_lt ht.2)

end IsBernsteinFunction

end TauCeti
