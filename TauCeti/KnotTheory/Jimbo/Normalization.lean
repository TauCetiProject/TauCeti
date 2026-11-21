/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Jimbo.Stabilization
public import TauCeti.KnotTheory.Markov.Basic
import TauCeti.KnotTheory.Markov.Skein

/-!
# Writhe normalization of the Jimbo trace

Multiplying the weighted trace of a braid of exponent sum `e` by `(q ^ N) ^ (-e)`
cancels both Markov stabilization factors. The result is constant on ordinary
unframed Markov equivalence, on the existing braid presentation `MarkovBraid`.

This is the `sl_N` specialization of the enhanced braid-trace construction of
HOMFLY. Our normalization assigns the quantum dimension `∑ a, jimboWeight q a`
to the one-strand unknot, rather than one. The normalized trace satisfies the
oriented HOMFLY skein relation with `a = q ^ N` and `z = q - q⁻¹`.
No invertibility of that sum is assumed, so the construction works over arbitrary
commutative rings and at `q = 1`. Moreover, the normalized trace of every braid closure is
divisible by the quantum dimension (`MarkovBraid.sum_jimboWeight_dvd_jimboTrace`).
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

/-- Adding an uncrossed strand multiplies the writhe-normalized Jimbo trace by the quantum
dimension. -/
@[simp]
theorem jimboTrace_strandIncl (q : Rˣ) (b : BraidGroup (n + 1)) :
    jimboTrace (N := N) ⟨n + 1, BraidGroup.strandIncl b⟩ q =
      (∑ a : Fin N, jimboWeight q a) * jimboTrace (N := N) ⟨n, b⟩ q := by
  rw [jimboTrace_def, jimboTrace_def, BraidGroup.exponentSum_strandIncl,
    jimboWeightedTrace_strandIncl]
  ring

/-- The writhe-normalized Jimbo trace satisfies the oriented HOMFLY skein relation
with `a = q ^ N` and `z = q - q⁻¹`, in any braid context. -/
theorem jimboTrace_skein (q : Rˣ) (b c : BraidGroup (n + 1)) (i : Fin n) :
    ↑(q ^ N) * jimboTrace (N := N) ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ q -
        ↑((q⁻¹) ^ N) * jimboTrace (N := N) ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ q =
      ((q : R) - ↑(q⁻¹)) * jimboTrace (N := N) ⟨n, b * c⟩ q := by
  have h := jimboWeightedTrace_skein (N := N) q b c i
  simp only [jimboTrace_def, map_mul, map_inv, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_inv, toAdd_ofAdd, neg_add, neg_neg, zpow_add,
    zpow_neg_one, zpow_one, Units.val_mul, inv_pow]
  have ha : (↑(q ^ N) : R) * ↑((q ^ N)⁻¹) = 1 := Units.mul_inv _
  linear_combination
    ↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ b))) *
      ↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ c))) * h +
    (↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ b))) *
      ↑((q ^ N) ^ (-Multiplicative.toAdd (ArtinGroup.exponentSum _ c))) *
      (jimboWeightedTrace (N := N) q (b * BraidGroup.sigma (n := n + 1) i * c) -
        jimboWeightedTrace (N := N) q (b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c))) * ha

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

namespace MarkovBraid

/-- Ring homomorphisms commute with the writhe-normalized Jimbo trace, mapping the parameter unit
along `Units.map`. -/
@[simp]
theorem map_jimboTrace {S : Type*} [CommRing S] (β : MarkovBraid)
    (f : R →+* S) (q : Rˣ) :
    f (β.jimboTrace (N := N) q) = β.jimboTrace (N := N) (Units.map (f : R →* S) q) := by
  let qS : Sˣ := Units.map (f : R →* S) q
  have hqS : (qS : S) = f q := by simp [qS]
  have hqS_inv : (↑qS⁻¹ : S) = f ↑q⁻¹ := by simp [qS]
  have hsum : f (∑ a : Fin N, jimboWeight q a) = ∑ a : Fin N, jimboWeight qS a := by
    simp [qS]
  refine congrFun (eq_of_skein (qS ^ N) ((qS : S) - ↑qS⁻¹) (∑ a : Fin N, jimboWeight qS a)
    (F := fun γ ↦ f (γ.jimboTrace (N := N) q))
    (G := fun γ ↦ γ.jimboTrace (N := N) qS)
    (fun _ _ h ↦ congrArg f (h.jimboTrace_eq q))
    (fun _ _ h ↦ h.jimboTrace_eq qS) ?_ ?_ ?_ ?_ ?_) β
  · intro m c i
    have hs := congrArg f (jimboTrace_skein (N := N) q 1 c i)
    simpa only [one_mul, map_sub, map_mul, Units.val_pow_eq_pow_val, map_pow, ← inv_pow,
      smul_eq_mul, hqS, hqS_inv] using hs
  · intro m c i
    simpa only [one_mul, smul_eq_mul, inv_pow] using jimboTrace_skein (N := N) qS 1 c i
  · intro m b
    simp [smul_eq_mul, hsum]
  · intro m b
    simp [smul_eq_mul]
  · simp [hsum]

/-- Over any commutative ring `R` and at any unit parameter `q : Rˣ`, the writhe-normalized
`N`-colour Jimbo trace is divisible by the quantum dimension `[N]_q`. -/
theorem sum_jimboWeight_dvd_jimboTrace (β : MarkovBraid) (q : Rˣ) :
    (∑ a : Fin N, jimboWeight q a) ∣ β.jimboTrace (N := N) q := by
  rw [jimboTrace_def]
  exact dvd_mul_of_dvd_right (sum_jimboWeight_dvd_jimboWeightedTrace q β.braid) _

end MarkovBraid

end TauCeti
