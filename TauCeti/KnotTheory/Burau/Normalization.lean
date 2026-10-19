/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Burau.Alexander

/-!
# Exact normalization of the Burau Alexander invariant

The corner determinant `MarkovBraid.burauAlexander` changes by units under Markov moves.
For a braid on `p + 1` strands with exponent sum `w`, evaluate that determinant at `s²`
and multiply it by `(-1)^p s^(-w-p)`. Positive stabilization multiplies the determinant
by `-s²` and increases both `w` and `p`; negative stabilization multiplies it by `-1`
and increases `p` while decreasing `w`. The correction therefore gives an exact Markov
invariant, including for links, without choosing a generator of a principal ideal.

The parameter `s` is a square root of the Alexander variable. Over Laurent polynomials,
odd powers are permitted, as required for links with an even number of components.
The unknot has value one, and the right-handed trefoil has value `s² - 1 + s⁻²`, exactly
matching the existing Conway-normalized Seifert-matrix computation. The comparison with
Seifert matrices of arbitrary geometric braid closures is a separate theorem.

The construction reuses the exact stabilization formulas of
`MarkovBraid.burauAlexander` and Tau Ceti's `ArtinGroup.exponentSum` homomorphism.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82,
  Princeton University Press (1974), Chapter 3 (the Burau Alexander formula).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997),
  Chapters 6 and 8 (Alexander and Conway normalization).
-/

public section

noncomputable section

namespace TauCeti

open KnotTheory BraidGroup

namespace MarkovBraid

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The Burau corner determinant with its exact Markov normalization. The unit `s` is a
square root of the Alexander parameter: for `p + 1` strands and exponent sum `w`, the
correction factor is `(-1)^p s^(-w-p)`. -/
def normalizedBurauAlexander (β : MarkovBraid) (s : Rˣ) : R :=
  (-1 : R) ^ β.predStrands *
    (s ^ (-(Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid) +
      (β.predStrands : ℤ))) : Rˣ).val * β.burauAlexander (s ^ 2)

/-- The correction-factor formula for the normalized invariant. -/
theorem normalizedBurauAlexander_def (β : MarkovBraid) (s : Rˣ) :
    β.normalizedBurauAlexander s = (-1 : R) ^ β.predStrands *
      (s ^ (-(Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid) +
        (β.predStrands : ℤ))) : Rˣ).val * β.burauAlexander (s ^ 2) :=
  (rfl)

/-- Conjugating a braid leaves the normalized Burau invariant unchanged. -/
@[simp] theorem normalizedBurauAlexander_conj (s : Rˣ) (b c : BraidGroup (n + 1)) :
    normalizedBurauAlexander ⟨n, c * b * c⁻¹⟩ s =
      normalizedBurauAlexander ⟨n, b⟩ s := by
  simp [normalizedBurauAlexander_def, burauAlexander_conj, map_mul, map_inv]

/-- Positive stabilization leaves the normalized Burau invariant unchanged. -/
@[simp] theorem normalizedBurauAlexander_stabilize (s : Rˣ) (b : BraidGroup (n + 1)) :
    normalizedBurauAlexander ⟨n + 1, strandIncl b * sigma (Fin.last n)⟩ s =
      normalizedBurauAlexander ⟨n, b⟩ s := by
  rw [normalizedBurauAlexander_def, normalizedBurauAlexander_def,
    burauAlexander_stabilize]
  simp only [map_mul, exponentSum_strandIncl, exponentSum_sigma,
    toAdd_mul, toAdd_ofAdd, Nat.cast_add, Nat.cast_one]
  have hexp (w : ℤ) : -(w + 1 + ((n : ℤ) + 1)) = -(w + (n : ℤ)) + -2 := by omega
  rw [hexp, zpow_add, Units.val_mul, pow_succ]
  have hcancel : (s ^ (-2 : ℤ) : Rˣ).val * (s ^ 2 : Rˣ).val = 1 := by
    rw [← Units.val_mul, ← zpow_natCast s 2, ← zpow_add]
    norm_num
  linear_combination (-1 : R) ^ n *
    (s ^ (-(Multiplicative.toAdd (ArtinGroup.exponentSum _ b) + (n : ℤ))) : Rˣ).val *
    (MarkovBraid.mk n b).burauAlexander (s ^ 2) * hcancel

/-- Negative stabilization leaves the normalized Burau invariant unchanged. -/
@[simp] theorem normalizedBurauAlexander_stabilizeInv (s : Rˣ) (b : BraidGroup (n + 1)) :
    normalizedBurauAlexander ⟨n + 1, strandIncl b * (sigma (Fin.last n))⁻¹⟩ s =
      normalizedBurauAlexander ⟨n, b⟩ s := by
  rw [normalizedBurauAlexander_def, normalizedBurauAlexander_def,
    burauAlexander_stabilizeInv]
  simp only [map_mul, map_inv, exponentSum_strandIncl, exponentSum_sigma,
    toAdd_mul, toAdd_inv, toAdd_ofAdd,
    Nat.cast_add, Nat.cast_one]
  have hexp (w : ℤ) : -(w + -1 + ((n : ℤ) + 1)) = -(w + (n : ℤ)) := by omega
  rw [hexp, pow_succ]
  ring

/-- The trivial one-strand braid, whose closure is the unknot, has normalized value one. -/
@[simp] theorem normalizedBurauAlexander_one_strand (s : Rˣ) :
    normalizedBurauAlexander ⟨0, 1⟩ s = 1 := by
  simp [normalizedBurauAlexander_def]

/-- The normalized value of the right-handed trefoil braid is `s² - 1 + s⁻²`. -/
theorem normalizedBurauAlexander_sigma_pow_three (s : Rˣ) :
    normalizedBurauAlexander ⟨1, sigma 0 ^ 3⟩ s =
      (s ^ 2 : Rˣ).val - 1 + (s ^ (-2 : ℤ) : Rˣ).val := by
  rw [normalizedBurauAlexander_def, burauAlexander_sigma_pow_three]
  simp only [map_pow, exponentSum_sigma, toAdd_pow,
    toAdd_ofAdd, nsmul_eq_mul, Nat.cast_ofNat, pow_one]
  norm_num only
  have hcancel : (s ^ (-4 : ℤ) : Rˣ).val * (s ^ 2 : Rˣ).val ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, ← zpow_natCast s 4, ← Units.val_mul,
      ← zpow_add]
    norm_num
  have hhalf : (s ^ (-4 : ℤ) : Rˣ).val * (s ^ 2 : Rˣ).val =
      (s ^ (-2 : ℤ) : Rˣ).val := by
    rw [← zpow_natCast s 2, ← Units.val_mul, ← zpow_add]
    norm_num
  linear_combination (s ^ 2 : Rˣ).val * hcancel - hcancel + hhalf

end MarkovBraid

/-- Every generating Markov move preserves the normalized Burau invariant exactly. -/
theorem IsMarkovMove.normalizedBurauAlexander_eq {β γ : MarkovBraid}
    (h : IsMarkovMove β γ) {R : Type*} [CommRing R] (s : Rˣ) :
    β.normalizedBurauAlexander s = γ.normalizedBurauAlexander s := by
  cases h <;> simp

/-- Markov-equivalent braids have equal normalized Burau invariants. -/
theorem MarkovEquiv.normalizedBurauAlexander_eq {β γ : MarkovBraid}
    (h : MarkovEquiv β γ) {R : Type*} [CommRing R] (s : Rˣ) :
    β.normalizedBurauAlexander s = γ.normalizedBurauAlexander s :=
  h.induction (fun hmove => hmove.normalizedBurauAlexander_eq s) (fun _ => rfl)
    (fun _ ih => ih.symm) (fun _ _ ih ih' => ih.trans ih')

namespace KnotTheory

open LaurentPolynomial

/-- On the right-handed trefoil, the normalized braid algorithm agrees exactly with the
Conway-normalized Seifert-matrix algorithm evaluated at the Alexander parameter `s²`. -/
theorem normalizedBurauAlexander_sigma_pow_three_eq_eval₂_alexander
    {R : Type*} [CommRing R] (s : Rˣ) :
    MarkovBraid.normalizedBurauAlexander ⟨1, sigma 0 ^ 3⟩ s =
      eval₂ (Int.castRingHom R) (s ^ 2) (alexander trefoilSeifertMatrix) := by
  rw [MarkovBraid.normalizedBurauAlexander_sigma_pow_three, alexander_trefoilSeifertMatrix]
  simp [zpow_neg]

end KnotTheory

end TauCeti
