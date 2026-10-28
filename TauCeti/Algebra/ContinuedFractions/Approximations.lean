/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.Approximations

/-!
# Integrality of continuants and a lower bound for the error of a convergent

For the continued fraction `GenContFract.of v` of an element `v` of a floor field, this file
proves two complements to Mathlib's `Mathlib.Algebra.ContinuedFractions.Computation.Approximations`.

* `GenContFract.exists_int_contsAux_eq`: the continuants `contsAux n = ⟨Aₙ₋₁, Bₙ₋₁⟩` are pairs of
  integers, since the partial numerators are `1` and the partial denominators are integers.
* `GenContFract.one_div_lt_abs_sub_convs`: if the continued fraction has not terminated at `n`,
  then `1 / (Bₙ (Bₙ + Bₙ₊₁)) < |v - Aₙ / Bₙ|`. Together with Mathlib's upper bound
  `GenContFract.abs_sub_convs_le`, `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ Bₙ₊₁)`, this determines the error
  of a convergent up to a factor of two. The proof writes the error exactly as
  `1 / (Bₙ (ξₙ₊₁ Bₙ + Bₙ₋₁))` (Mathlib's `GenContFract.sub_convs_eq`), where the complete
  quotient `ξₙ₊₁` is less than `bₙ₊₁ + 1`, and uses `Bₙ₊₁ = bₙ₊₁ Bₙ + Bₙ₋₁`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 1, Exercise 1.7.
* J. Sondow, *Irrationality measures, irrationality bases, and a theorem of Jarnik*, §3.
-/

public section

open GenContFract (of)

namespace GenContFract

variable {K : Type*} [Field K] [LinearOrder K] [FloorRing K]

/-- The continuants `⟨Aₙ₋₁, Bₙ₋₁⟩` of the continued fraction of `v` are pairs of integers. -/
theorem exists_int_contsAux_eq (v : K) (n : ℕ) :
    ∃ a b : ℤ, (of v).contsAux n = ⟨a, b⟩ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨1, 0, by simp [zeroth_contAux_eq_one_zero]⟩
    | 1 => exact ⟨⌊v⌋, 1, by simp [first_contAux_eq_h_one, of_h_eq_floor]⟩
    | n + 2 =>
      obtain ⟨a₀, b₀, h₀⟩ := ih n (by omega)
      obtain ⟨a₁, b₁, h₁⟩ := ih (n + 1) (by omega)
      cases hs : (of v).s.get? n with
      | none => exact ⟨a₁, b₁, by rw [contsAux, hs, h₁]⟩
      | some gp =>
        obtain ⟨ha, z, hz⟩ := of_partNum_eq_one_and_exists_int_partDen_eq hs
        refine ⟨z * a₁ + a₀, z * b₁ + b₀, ?_⟩
        rw [contsAux_recurrence hs h₀ h₁, ha, hz]
        push_cast
        ring_nf

variable [IsStrictOrderedRing K] {v : K} {n : ℕ}

/-- The error of a convergent exceeds `1 / (Bₙ (Bₙ + Bₙ₊₁))`. Together with
`GenContFract.abs_sub_convs_le` this determines `|v - Aₙ / Bₙ|` up to a factor of two. -/
theorem one_div_lt_abs_sub_convs (hn : ¬(of v).TerminatedAt n) :
    1 / ((of v).dens n * ((of v).dens n + (of v).dens (n + 1))) < |v - (of v).convs n| := by
  obtain ⟨gp, hs⟩ : ∃ gp, (of v).s.get? n = some gp := Option.ne_none_iff_exists'.1 hn
  obtain ⟨ifp', hstream', hb⟩ := IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some hs
  obtain ⟨ifp, hstream, hfr, hof⟩ := IntFractPair.succ_nth_stream_eq_some_iff.1 hstream'
  have hdens : (of v).dens n = ((of v).contsAux (n + 1)).b := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  -- The recurrence `Bₙ₊₁ = bₙ₊₁ Bₙ + Bₙ₋₁`, with `bₙ₊₁ = ⌊ξₙ₊₁⌋` and `ξₙ₊₁ = fr⁻¹`.
  have hdens' : (of v).dens (n + 1) =
      ⌊ifp.fr⁻¹⌋ * ((of v).contsAux (n + 1)).b + ((of v).contsAux n).b := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, contsAux_recurrence hs rfl rfl,
      of_partNum_eq_one (partNum_eq_s_a hs), ← hb, ← hof]
    simp [IntFractPair.of]
  set B := ((of v).contsAux (n + 1)).b
  set pB := ((of v).contsAux n).b
  have hB : 0 < B :=
    (fib_le_of_contsAux_b (v := v) (n := n + 1)
      (Or.inr (mt (terminated_stable (n.sub_le 1)) hn))).trans_lt'
      (mod_cast Nat.fib_pos.2 n.succ_pos)
  have hpB : 0 ≤ pB := zero_le_of_contsAux_b
  have hfr' : 0 < ifp.fr⁻¹ :=
    inv_pos.2 ((IntFractPair.nth_stream_fr_nonneg hstream).lt_of_ne' hfr)
  have herr : |v - (of v).convs n| = 1 / (B * (ifp.fr⁻¹ * B + pB)) := by
    rw [sub_convs_eq hstream, ite_eq_right hfr, abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (by positivity)]
  rw [herr, hdens, hdens']
  refine one_div_lt_one_div_of_lt (by positivity) (mul_lt_mul_of_pos_left ?_ hB)
  linarith [mul_lt_mul_of_pos_right (Int.lt_floor_add_one ifp.fr⁻¹) hB]

end GenContFract
