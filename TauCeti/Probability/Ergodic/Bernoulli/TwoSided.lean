/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Probability.ProductMeasure
import TauCeti.Dynamics.SymbolicDynamics.Shift
import TauCeti.MeasureTheory.Constructions.FullShift.Shift
import TauCeti.Probability.Ergodic.Bernoulli.Action

/-!
# Ergodicity of the two-sided Bernoulli shift

For a probability measure `p` on an alphabet `A`, the two-sided Bernoulli shift is
`SymbolicDynamics.FullShift.shift 1`, `x ↦ (n ↦ x (n + 1))`, on `ℤ → A` with the Bernoulli
measure `p^{⊗ℤ}` (`Measure.infinitePi fun _ => p`). Its measure preservation is
`SymbolicDynamics.FullShift.measurePreserving_shift` and its measurable inverse is
`SymbolicDynamics.FullShift.shiftEquiv` (both in
`TauCeti.MeasureTheory.Constructions.FullShift.Shift`).

The two-sided Bernoulli shift is ergodic
(`MeasureTheory.Measure.ergodic_shift_one_infinitePi_const`): a set invariant under `shift 1` is
invariant under every `shift k`, `k ∈ ℤ`
(`SymbolicDynamics.FullShift.preimage_shift_zsmul_eq_of_preimage_shift_eq`, in
`TauCeti.Dynamics.SymbolicDynamics.Shift`). The shifts `shift k` form the Bernoulli
action of `Multiplicative ℤ` on `ℤ → A`, with `ℤ` acting on itself by translation
(`SymbolicDynamics.FullShift.arrowAction_multiplicative_smul_eq_shift`), which is ergodic as the
Bernoulli action of a countable infinite group
(`TauCeti.Probability.ergodicSMul_arrowAction_multiplicative_infinitePi_const`).

## Main results

* `MeasureTheory.Measure.ergodic_shift_one_infinitePi_const`: the two-sided Bernoulli shift is
  ergodic.
-/

public section

open MeasureTheory Set

namespace MeasureTheory.Measure

open SymbolicDynamics.FullShift TauCeti.Probability

variable {A : Type*} [MeasurableSpace A]

/-- **The two-sided Bernoulli shift is ergodic.** For a probability measure `p` on `A`, the
shift `x ↦ (n ↦ x (n + 1))` on `ℤ → A` is ergodic for the Bernoulli measure `p^{⊗ℤ}`. -/
theorem ergodic_shift_one_infinitePi_const (p : Measure A) [IsProbabilityMeasure p] :
    Ergodic (shift (A := A) (1 : ℤ)) (Measure.infinitePi fun _ : ℤ ↦ p) := by
  let := arrowAction (G := Multiplicative ℤ) (A := ℤ) (B := A)
  have h := ergodicSMul_arrowAction_multiplicative_infinitePi_const (Λ := ℤ) (ν := p)
  refine Ergodic.of_preimage_eq (measurePreserving_shift p 1) fun s hs hinv ↦
    h.aeconst_of_forall_preimage_smul_ae_eq hs fun g ↦ ?_
  have hg : (fun x : ℤ → A ↦ g • x) = shift (-Multiplicative.toAdd g) :=
    funext (arrowAction_multiplicative_smul_eq_shift g)
  have hk := preimage_shift_zsmul_eq_of_preimage_shift_eq hinv (-Multiplicative.toAdd g)
  rw [smul_eq_mul, mul_one] at hk
  rw [hg, hk]

end MeasureTheory.Measure
