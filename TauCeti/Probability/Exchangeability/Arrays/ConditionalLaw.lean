/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Extreme
public import Mathlib.Probability.Kernel.Condexp
import TauCeti.Probability.Kernel.Invariant

/-!
# Conditional array laws retain joint exchangeability

Condition a jointly exchangeable array law on its corner-tail σ-algebra. Almost every resulting
conditional law is again jointly exchangeable. This supplies the symmetry of the conditional
components in the decomposition used by the Aldous--Hoover representation. Proving that these
components are dissociated, and constructing their vertex and cell noise, are separate steps.

We use Mathlib's `condExpKernel` on array path space. Although the conditioning σ-algebra need
not be standard Borel, the space of arrays is standard Borel when the value space is. Thus no
regularity assumption is imposed on a sample space carrying an original array process.

The corner-tail events are fixed by every finitely supported permutation. Disintegration
uniqueness gives invariance of the conditional laws under each such permutation; countability
puts these statements on one almost-sure set. Finite-dimensional determinacy then gives full
joint exchangeability, including permutations with infinite support.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- Almost every conditional law of a jointly exchangeable array, given its corner tail, is
jointly exchangeable. The almost-sure set works simultaneously for all coordinate permutations. -/
theorem JointlyExchangeable.ae_jointlyExchangeable_condExpKernel_arrayTail
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {ρ : Measure (ℕ × ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : JointlyExchangeable ρ fun p x => x p) :
    ∀ᵐ x ∂ρ, JointlyExchangeable
      (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x) (fun p y => y p) := by
  have hm := arrayTail_le_ambient (X := fun p (y : ℕ × ℕ → α) => y p) 0
    (fun p _ _ => measurable_pi_apply p)
  have := hρ.smulInvariantMeasure
  have hinv (g : FinitaryPerm) :
      ∀ᵐ x ∂ρ,
        (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x).map (fun y => g • y) =
          condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x :=
    map_condExpKernel_ae_eq_of_invariant hm (measurePreserving_smul g ρ)
      (fun _ hs => Filter.EventuallyEq.of_eq
        (preimage_finitaryPerm_smul_array_eq_self_of_measurableSet_arrayTail hs g))
  filter_upwards [ae_all_iff.2 hinv] with x hx
  have : SMulInvariantMeasure FinitaryPerm (ℕ × ℕ → α)
      (condExpKernel ρ (arrayTail (fun p (y : ℕ × ℕ → α) => y p)) x) := by
    constructor
    intro g s hs
    rw [← Measure.map_apply (measurable_const_smul g) hs, hx g]
  exact jointlyExchangeable_of_smulInvariantMeasure

end TauCeti.Probability
