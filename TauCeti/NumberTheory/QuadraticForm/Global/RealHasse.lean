/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Archimedean
public import TauCeti.NumberTheory.QuadraticForm.Global.Signature

/-!
# The archimedean Hasse sign of a quadratic form over a number field

For a diagonalization of a quadratic form over a number field by global units, this file computes
the product of the real Hilbert symbols of the localized coefficients over the ordered pairs of
indices: it is `(-1)^(q(q-1)/2)`, where `q` is the negative index of the form at the real place.
In particular the product depends on the form and the place alone, not on the chosen
diagonalization; it is the archimedean factor of the product over all places of the Hasse signs
of a global form.

The archimedean classification that supplies the negative index is
`TauCeti.NumberTheory.QuadraticForm.Global.Signature` at the real places and
`TauCeti.NumberTheory.QuadraticForm.Global.ComplexPlaces` through the complex embeddings.

## Main results

* `TauCeti.prod_hilbertSymbol_unitAtRealPlace_of_equiv_weightedSumSquares`: the archimedean Hasse
  sign of a diagonalization.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:18 for the real Hilbert
  symbol and §61 for the archimedean classification.
-/

public section

open Finset NumberField NumberField.InfinitePlace QuadraticMap

namespace TauCeti

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- **The archimedean Hasse sign.** For a diagonalization `Q ≃ ⟨a₁, …, aₙ⟩` by global units, the
product of the real Hilbert symbols of the localized coefficients over the ordered pairs `i < j`
is `(-1)^(q(q-1)/2)`, where `q` is the negative index of `Q` at the real place.  In particular
the product depends on `Q` and the place alone, not on the chosen diagonalization. -/
theorem prod_hilbertSymbol_unitAtRealPlace_of_equiv_weightedSumSquares
    {ι : Type*} [Fintype ι] [LinearOrder ι] {Q : _root_.QuadraticForm K V}
    {a : ι → Kˣ} (h : Q.Equivalent (weightedSumSquares K fun i ↦ (a i : K)))
    (w : {w : InfinitePlace K // w.IsReal}) :
    ∏ ij ∈ univ.filter (fun ij : ι × ι => ij.1 < ij.2),
        hilbertSymbol (unitAtRealPlace w (a ij.1)) (unitAtRealPlace w (a ij.2)) =
      (-1) ^ (Q.realNegativeIndex w).choose 2 := by
  have hcoe : (fun i ↦ ((unitAtRealPlace w (a i) : ℝˣ) : ℝ)) =
      fun i ↦ embedding_of_isReal w.2 (a i : K) := by
    funext i
    simp
  have hloc : (Q.atRealPlace w).Equivalent
      (weightedSumSquares ℝ fun i ↦ ((unitAtRealPlace w (a i) : ℝˣ) : ℝ)) := by
    rw [hcoe]
    exact (h.atRealPlace w).trans ⟨QuadraticForm.atRealPlaceWeightedSumSquares w fun i ↦ (a i : K)⟩
  rw [prod_hilbertSymbol_real_of_equiv_weightedSumSquares hloc,
    QuadraticForm.realNegativeIndex_eq_sigNeg]

end TauCeti
