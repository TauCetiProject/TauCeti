/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Process.Array.Tail
public import TauCeti.Probability.Process.Tail.Basic
public import TauCeti.Probability.Exchangeability.Arrays.Basic

/-!
# Diagonal process and array tail

A diagonal coordinate is visible in the corresponding square block. Consequently, the tail
σ-algebra of the diagonal process is contained in the corner tail of the array.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace α]
  {X : ℕ × ℕ → Ω → α}

/-- **The diagonal entries indexed by `S` are read by the square block over `S`.** The entry
`arrayDiag X i` is `X (i, i)`, and `(i, i)` lies in `S ×ˢ S` for every `i ∈ S`. -/
theorem blockSigma_arrayDiag_le_blockSigma_prod_self (X : ℕ × ℕ → Ω → α) (S : Set ℕ) :
    blockSigma (arrayDiag X) S ≤ blockSigma X (S ×ˢ S) :=
  blockSigma_le_iff.mpr fun i hi => by
    simpa only [arrayDiag_apply] using
      measurable_blockSigma_of_mem (Z := X) (S := S ×ˢ S) (i := (i, i)) ⟨hi, hi⟩

/-- **The tail of the diagonal is an array tail event.** The diagonal entries from time `n` on have
both indices at least `n`, so they generate a sub-σ-algebra of the tail family at `n`. The
inclusion need not be an equality: the array tail may additionally read off-diagonal entries above
the cutoff. -/
theorem tailProcess_arrayDiag_le_arrayTail (X : ℕ × ℕ → Ω → α) :
    tailProcess (arrayDiag X) ≤ arrayTail X := by
  rw [le_arrayTail_iff]
  intro n
  refine (tailProcess_le_tailFamily _ n).trans (tailFamily_le_iff.mpr ?_)
  intro k hk
  simpa only [arrayDiag_apply] using measurable_arrayTailFamily_of_le (X := X) hk hk

end Probability

end TauCeti

end

end
