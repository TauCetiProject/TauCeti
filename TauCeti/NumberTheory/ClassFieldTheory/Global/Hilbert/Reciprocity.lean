/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Hilbert.Invariant
public import TauCeti.NumberTheory.ClassFieldTheory.Global.InvariantSum

/-!
# Hilbert reciprocity

Let `K` be a number field and `a, b ∈ Kˣ`. Hilbert's reciprocity law says that the local Hilbert
invariants of `a` and `b` at all the places of `K` sum to zero (`hilbertProductFormula`). In its
cohomological form it is the statement that the local invariants of the Brauer class `(a) ∪ (b)`,
the cup product of the Kummer classes of `a` and `b`, sum to zero: by
`finiteInvAt_kummerBrauerClass` and `infiniteInvAt_kummerBrauerClass` these local invariants are
the Hilbert invariants read in `ℚ/ℤ` (`sumLocalInv_brLocalization_kummerBrauerClass`). The local
invariants of every Brauer class of `K` sum to zero (`sumLocalInv_brLocalization_eq_zero`), and so
Hilbert reciprocity holds.

## Main results

* `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_kummerBrauerClass`: the sum of the local
  invariants of the quadratic Kummer-cup class is the sum of the Hilbert invariants, read in
  `ℚ/ℤ`.
* `TauCeti.ClassFieldTheory.hilbertProductFormula`: Hilbert reciprocity over every number field.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Example 8.2, Lemmas 8.4 and 8.5, and
  Theorem 8.1.
* J. Neukirch, *Algebraic Number Theory*, Springer (1999), Chapter VI, §8.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter III, §2, Theorem 3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.NumberField

variable {K : Type} [Field K] [NumberField K]

/-- **The sum of the local invariants of the quadratic Kummer-cup class is the sum of the Hilbert
invariants.** For `a, b ∈ Kˣ`, the sum of the local invariants of the Brauer class `(a) ∪ (b)`
over all places of `K` is the sum of the Hilbert invariants of `a` and `b`, read in `ℚ/ℤ` through
`k ↦ k/2`. -/
theorem sumLocalInv_brLocalization_kummerBrauerClass (a b : Kˣ) :
    sumLocalInv K (brLocalization K (kummerBrauerClass (-1) (.neg_one 0 (by decide)) a b)) =
      ZMod.toRatAddCircle 2 ((∑ v ∈ finiteHilbertSupport K a b, finiteHilbertInvariantAt K v a b) +
        ∑ w : InfinitePlace K, infiniteHilbertInvariantAt K w a b) := by
  rw [sumLocalInv_brLocalization K _ (S := finiteHilbertSupport K a b) fun v hv ↦ ?_, map_add,
    map_sum, map_sum]
  · simp only [finiteInvAt_kummerBrauerClass, infiniteInvAt_kummerBrauerClass]
  · rw [mem_brauerSupport, finiteInvAt_kummerBrauerClass] at hv
    exact (mem_finiteHilbertSupport K).2 fun h ↦ hv (by rw [h, map_zero])

/-- **Hilbert reciprocity.** For `a, b ∈ Kˣ`, the Hilbert invariants of `a` and `b` at all the
finite and infinite places of the number field `K` sum to zero. -/
theorem hilbertProductFormula (a b : Kˣ) :
    (∑ v ∈ finiteHilbertSupport K a b, finiteHilbertInvariantAt K v a b) +
        ∑ w : InfinitePlace K, infiniteHilbertInvariantAt K w a b = 0 :=
  ZMod.toRatAddCircle_injective 2 <| by
    rw [← sumLocalInv_brLocalization_kummerBrauerClass, map_zero,
      sumLocalInv_brLocalization_eq_zero]

end TauCeti.ClassFieldTheory
