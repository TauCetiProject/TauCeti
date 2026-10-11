/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Jimbo.Stabilization
public import TauCeti.KnotTheory.Markov.Basic

/-!
# Writhe normalization of the Jimbo trace

Multiplying the weighted trace of a braid of exponent sum `e` by `(q ^ N) ^ (-e)`
cancels both Markov stabilization factors. The result is constant on ordinary
unframed Markov equivalence, on the existing braid presentation `MarkovBraid`.

This is the `sl_N` specialization of the enhanced braid-trace construction of
HOMFLY. Our normalization assigns the quantum dimension `∑ a, jimboWeight q a`
to the one-strand unknot, rather than one. No invertibility of that sum is assumed,
so the construction works over arbitrary commutative rings and at `q = 1`.
No geometric-to-diagram or Markov classification theorem is asserted here.

## References

* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527–553 (writhe normalization of enhanced braid traces).
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388.

The normalization and Markov-equivalence induction follow the existing
`MarkovBraid.jonesTrace` construction in `TauCeti.KnotTheory.TemperleyLieb`, with
the Jimbo stabilization factors in place of the Jones factors.
-/

public section

namespace TauCeti

open KnotTheory

variable {R : Type*} [CommRing R] {N n : ℕ}

namespace MarkovBraid

/-- The writhe-normalized Jimbo trace with `N` colours. Its one-strand unknot value
is the quantum dimension, with no division by that value. -/
noncomputable def jimboTrace (β : MarkovBraid) (q : Rˣ) : R :=
  ↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid))) *
    jimboWeightedTrace (N := N) q β.braid

/-- The normalized trace is the weighted trace times the inverse writhe factor. -/
theorem jimboTrace_def (β : MarkovBraid) (q : Rˣ) :
    jimboTrace (N := N) β q =
      ↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid))) *
        jimboWeightedTrace (N := N) q β.braid := (rfl)

/-- Conjugation preserves the normalized trace. -/
@[simp]
theorem jimboTrace_conj (q : Rˣ) (b c : BraidGroup (n + 1)) :
    jimboTrace (N := N) ⟨n, c * b * c⁻¹⟩ q = jimboTrace (N := N) ⟨n, b⟩ q := by
  simp [jimboTrace_def, map_mul, map_inv]

/-- Positive stabilization raises writhe by one and preserves the normalized trace. -/
@[simp]
theorem jimboTrace_stabilize (q : Rˣ) (b : BraidGroup (n + 1)) :
    jimboTrace (N := N) ⟨n + 1, BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)⟩ q =
      jimboTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboTrace_def, jimboWeightedTrace_stabilize, map_mul,
    BraidGroup.exponentSum_strandIncl, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_ofAdd, neg_add, zpow_add,
    zpow_neg_one, Units.val_mul]
  rw [mul_assoc _ _ (_ * _), ← mul_assoc _ (↑(q ^ N) : R), Units.inv_mul, one_mul]

/-- Negative stabilization lowers writhe by one and preserves the normalized trace. -/
@[simp]
theorem jimboTrace_stabilizeInv (q : Rˣ) (b : BraidGroup (n + 1)) :
    jimboTrace (N := N)
        ⟨n + 1, BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹⟩ q =
      jimboTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboTrace_def, jimboWeightedTrace_stabilizeInv, map_mul, map_inv,
    BraidGroup.exponentSum_strandIncl, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_inv, toAdd_ofAdd,
    neg_add, neg_neg, zpow_add, zpow_one, Units.val_mul, inv_pow]
  rw [mul_assoc _ _ (_ * _), ← mul_assoc _ (↑((q ^ N)⁻¹) : R), Units.mul_inv, one_mul]

/-- The identity braid on `n + 1` strands has normalized trace equal to the
`(n + 1)`-st power of the quantum dimension. In particular the unknot value is
that dimension itself. -/
@[simp]
theorem jimboTrace_one (q : Rˣ) :
    jimboTrace (N := N) ⟨n, 1⟩ q = (∑ a : Fin N, jimboWeight q a) ^ (n + 1) := by
  simp [jimboTrace_def]

end MarkovBraid

/-- Every generating Markov move preserves the writhe-normalized Jimbo trace. -/
theorem IsMarkovMove.jimboTrace_eq {β γ : MarkovBraid} (h : IsMarkovMove β γ) (q : Rˣ) :
    β.jimboTrace (N := N) q = γ.jimboTrace (N := N) q := by
  cases h with
  | conj b c => exact MarkovBraid.jimboTrace_conj q b c
  | stabilize b => exact MarkovBraid.jimboTrace_stabilize q b
  | stabilizeInv b => exact MarkovBraid.jimboTrace_stabilizeInv q b

/-- The writhe-normalized Jimbo trace is constant on unframed Markov equivalence. -/
theorem MarkovEquiv.jimboTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ) (q : Rˣ) :
    β.jimboTrace (N := N) q = γ.jimboTrace (N := N) q :=
  h.induction (fun hmove ↦ hmove.jimboTrace_eq q) (fun _ ↦ rfl) (fun _ ih ↦ ih.symm)
    (fun _ _ ih ih' ↦ ih.trans ih')

end TauCeti
