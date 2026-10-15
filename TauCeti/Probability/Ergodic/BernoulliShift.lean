/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Tail.ShiftInvariant
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.ZeroOne

/-!
# Ergodicity of the Bernoulli shift

For a probability measure `μ` on an arbitrary measurable space `α`, the one-sided left shift on
`ℕ → α` is ergodic for the i.i.d. product law `μ^{⊗ℕ}` (`Measure.infinitePi fun _ => μ`). This is
the Bernoulli shift with state space `α`.

The shift preserves the product law because it is reindexing along the injective map `n ↦ n + 1`.
A shift-invariant event is a tail event (`invariants_shift_le_pathTail`), and the coordinates are
independent under the product law, so Kolmogorov's zero-one law makes every shift-invariant event
null or conull. No hypothesis on `α` is needed.

## Main results

* `TauCeti.Probability.ergodic_shift_infinitePi_const` — an i.i.d. product law is ergodic for the
  one-sided shift.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Chapter 1.
-/

public section

open Filter MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **The Bernoulli shift is ergodic.** For a probability measure `μ` on `α`, the one-sided left
shift on `ℕ → α` is ergodic for the i.i.d. product law `μ^{⊗ℕ}`. -/
theorem ergodic_shift_infinitePi_const (μ : Measure α) [IsProbabilityMeasure μ] :
    Ergodic (shift α) (Measure.infinitePi fun _ : ℕ => μ) := by
  have hshift : shift α = fun x n => x (n + 1) := by
    funext x n
    exact shift_apply x n
  have hmp : MeasurePreserving (shift α) (Measure.infinitePi fun _ : ℕ => μ)
      (Measure.infinitePi fun _ : ℕ => μ) := by
    refine ⟨measurable_shift, ?_⟩
    rw [hshift]
    exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ) (add_left_injective 1)
  refine Ergodic.of_preimage_eq hmp fun s hs hs_shift => ?_
  -- A shift-invariant event lies in the tail of the coordinate process, which is trivial by
  -- Kolmogorov's zero-one law since the coordinates are independent.
  have htail := invariants_shift_le_pathTail s ⟨hs, hs_shift⟩
  rw [pathTail_eq_tailProcess, tailProcess_eq_limsup] at htail
  have hindep : iIndepFun (fun n (x : ℕ → α) => x n) (Measure.infinitePi fun _ : ℕ => μ) :=
    iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  rcases measure_zero_or_one_of_measurableSet_limsup_atTop
      (fun n => (measurable_pi_apply n).comap_le) hindep.iIndep htail with hzero | hone
  · exact eventuallyEmptyOrUniv_iff.2 (Or.inr (ae_iff.mpr (by simpa using hzero)))
  · exact eventuallyEmptyOrUniv_iff.2 (Or.inl ((mem_ae_iff_prob_eq_one hs).2 hone))

end Probability

end TauCeti
