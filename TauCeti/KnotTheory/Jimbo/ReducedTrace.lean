/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Jimbo.Normalization

/-!
# The reduced Jimbo trace

The writhe-normalized Jimbo trace assigns the quantum dimension to the unknot.
Over a field, dividing by that dimension gives the reduced `sl_N` specialization
of HOMFLY, with unknot value one whenever the quantum dimension is nonzero.
It retains Markov invariance and the skein relation with `a = q ^ N` and
`z = q - q⁻¹`.

The nonvanishing condition is used explicitly for the unlink and trefoil values.
The quotient is defined using total field division; at a zero quantum dimension
it is zero and is not an unknot-normalized invariant. No claim of Laurent
polynomial integrality or of a two-variable HOMFLY construction is made here.

## References

* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527–553 (the normalization of enhanced braid traces).
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388.

The construction uses `MarkovBraid.jimboTrace`, and the calculations use its
skein relation and `jimboWeight_sum`.
-/

public section

namespace TauCeti

open KnotTheory
open scoped BigOperators

variable {K : Type*} [Field K] {N n : ℕ}

namespace MarkovBraid

/-- Divide the writhe-normalized Jimbo trace by its unknot value. This gives the
reduced `sl_N` specialization when the quantum dimension is nonzero. -/
noncomputable def jimboReducedTrace (β : MarkovBraid) (q : Kˣ) : K :=
  β.jimboTrace (N := N) q / ∑ a : Fin N, jimboWeight q a

/-- The reduced trace is the normalized trace divided by the quantum dimension. -/
theorem jimboReducedTrace_def (β : MarkovBraid) (q : Kˣ) :
    β.jimboReducedTrace (N := N) q =
      β.jimboTrace (N := N) q / ∑ a : Fin N, jimboWeight q a := (rfl)

/-- Conjugation preserves the reduced trace. -/
@[simp]
theorem jimboReducedTrace_conj (q : Kˣ) (b c : BraidGroup (n + 1)) :
    jimboReducedTrace (N := N) ⟨n, c * b * c⁻¹⟩ q =
      jimboReducedTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboReducedTrace_def, jimboTrace_conj]

/-- Positive Markov stabilization preserves the reduced trace. -/
@[simp]
theorem jimboReducedTrace_stabilize (q : Kˣ) (b : BraidGroup (n + 1)) :
    jimboReducedTrace (N := N)
        ⟨n + 1, BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)⟩ q =
      jimboReducedTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboReducedTrace_def, jimboTrace_stabilize]

/-- Negative Markov stabilization preserves the reduced trace. -/
@[simp]
theorem jimboReducedTrace_stabilizeInv (q : Kˣ) (b : BraidGroup (n + 1)) :
    jimboReducedTrace (N := N)
        ⟨n + 1, BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹⟩ q =
      jimboReducedTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboReducedTrace_def, jimboTrace_stabilizeInv]

/-- Multiplying the reduced trace by the nonzero quantum dimension recovers the
writhe-normalized trace. -/
@[simp]
theorem jimboReducedTrace_mul_sum (β : MarkovBraid) (q : Kˣ)
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    β.jimboReducedTrace (N := N) q * (∑ a : Fin N, jimboWeight q a) =
      β.jimboTrace (N := N) q := by
  rw [jimboReducedTrace_def, div_mul_cancel₀ _ hδ]

/-- The `(n + 1)`-component unlink has reduced trace equal to the `n`-th power
of the quantum dimension. In particular the one-strand unknot has value one. -/
@[simp]
theorem jimboReducedTrace_one (q : Kˣ)
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    jimboReducedTrace (N := N) ⟨n, 1⟩ q = (∑ a : Fin N, jimboWeight q a) ^ n := by
  rw [jimboReducedTrace_def, jimboTrace_one, pow_succ, mul_div_cancel_right₀ _ hδ]

/-- The reduced trace satisfies the oriented HOMFLY skein relation in any braid context. -/
theorem jimboReducedTrace_skein (q : Kˣ) (b c : BraidGroup (n + 1)) (i : Fin n) :
    ↑(q ^ N) * jimboReducedTrace (N := N)
        ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ q -
      ↑((q⁻¹) ^ N) * jimboReducedTrace (N := N)
        ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ q =
      ((q : K) - ↑(q⁻¹)) * jimboReducedTrace (N := N) ⟨n, b * c⟩ q := by
  simp only [jimboReducedTrace_def, ← mul_div_assoc, ← sub_div]
  rw [jimboTrace_skein]

end MarkovBraid

/-- Markov-equivalent braids have the same reduced Jimbo trace. -/
theorem MarkovEquiv.jimboReducedTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (q : Kˣ) : β.jimboReducedTrace (N := N) q = γ.jimboReducedTrace (N := N) q := by
  rw [MarkovBraid.jimboReducedTrace_def, MarkovBraid.jimboReducedTrace_def,
    h.jimboTrace_eq q]

namespace MarkovBraid

/-- The closure of the positive two-strand braid `σ₀ ^ 3` has the reduced
trefoil value `a⁻² (z² + 2) - a⁻⁴`, where `a = q ^ N` and `z = q - q⁻¹`. -/
theorem jimboReducedTrace_trefoil (q : Kˣ)
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    jimboReducedTrace (N := N) ⟨1, BraidGroup.sigma (n := 2) 0 ^ 3⟩ q =
      (↑((q⁻¹) ^ N) : K) ^ 2 * (((q : K) - ↑(q⁻¹)) ^ 2 + 2) -
        (↑((q⁻¹) ^ N) : K) ^ 4 := by
  let s : BraidGroup 2 := BraidGroup.sigma 0
  have hs : jimboReducedTrace (N := N) ⟨1, s⟩ q = 1 := by
    simpa [s, Fin.last, hδ] using
      (markovEquiv_sigma_last_one_one.jimboReducedTrace_eq (N := N) q)
  have h₂ := jimboReducedTrace_skein (N := N) q s 1 (0 : Fin 1)
  have h₃ := jimboReducedTrace_skein (N := N) q (s ^ 2) 1 (0 : Fin 1)
  have hsig : BraidGroup.sigma (n := 2) 0 = s := rfl
  rw [hsig] at h₂ h₃
  -- Normalize the braid products to powers before using the two skein equations.
  simp only [mul_one] at h₂
  rw [← pow_two, mul_inv_cancel] at h₂
  simp only [jimboReducedTrace_one q hδ, pow_one, hs, mul_one] at h₂
  have hcancel : s ^ 2 * s⁻¹ = s := by group
  simp only [mul_one, ← pow_succ, hcancel, hs, mul_one] at h₃
  have hdim := jimboWeight_sum (N := N) q
  have ha : (↑(q ^ N) : K) * ↑((q⁻¹) ^ N) = 1 := by
    rw [inv_pow]
    exact Units.mul_inv _
  -- Eliminate the two-crossing value and the quantum dimension from the skein equations.
  linear_combination
    (↑((q⁻¹) ^ N) : K) ^ 2 * ↑(q ^ N) * h₃ +
    (↑((q⁻¹) ^ N) : K) ^ 2 * ((q : K) - ↑(q⁻¹)) * h₂ +
    (↑((q⁻¹) ^ N) : K) ^ 3 * hdim -
    (jimboReducedTrace (N := N) ⟨1, s ^ 3⟩ q *
      (↑(q ^ N) * ↑((q⁻¹) ^ N) + 1) - 2 * (↑((q⁻¹) ^ N) : K) ^ 2) * ha

/-- With two colours the trefoil value is `q⁻² + q⁻⁶ - q⁻⁸`, the Jones value
`t + t³ - t⁴` after the substitution `t = q⁻²`. -/
theorem jimboReducedTrace_trefoil_two (q : Kˣ)
    (hδ : (∑ a : Fin 2, jimboWeight q a) ≠ 0) :
    jimboReducedTrace (N := 2) ⟨1, BraidGroup.sigma (n := 2) 0 ^ 3⟩ q =
      (↑(q⁻¹) : K) ^ 2 + (↑(q⁻¹) : K) ^ 6 - (↑(q⁻¹) : K) ^ 8 := by
  rw [jimboReducedTrace_trefoil q hδ]
  simp only [Units.val_pow_eq_pow_val]
  have ha : (q : K) * ↑(q⁻¹) = 1 := Units.mul_inv _
  linear_combination
    ((↑(q⁻¹) : K) ^ 2 * ((q : K) * ↑(q⁻¹) + 1) - 2 * (↑(q⁻¹) : K) ^ 4) * ha

end MarkovBraid

end TauCeti
