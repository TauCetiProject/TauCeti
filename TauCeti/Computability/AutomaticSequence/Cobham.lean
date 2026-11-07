/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.AutomaticSequence.ReadingDirection
import TauCeti.Computability.AutomaticSequence.LocalPeriod
import TauCeti.Combinatorics.Pigeonhole.RepeatedRepresentatives
import TauCeti.NumberTheory.ExponentialEquation.ClosePowers
import TauCeti.Data.Nat.Periodic.RadixWindows
import TauCeti.Data.Nat.Digits

/-!
# Cobham's base-independence theorem

A sequence is automatic in two multiplicatively independent bases if and only if it is
eventually periodic. The output type is arbitrary: finite state spaces already force the
used output range to be finite. Multiplicative independence is expressed by inequality of
all positive powers; unequal bases alone do not suffice.

The key automaton comparison is `IsAutomatic.exists_prefix_coloring`: equal prefix colours
give equal blocks of length `2 * k ^ n + 1`, uniformly in every positive exponent `n`.
Redundant most-significant-first digits allow such blocks to cross canonical radix boundaries.
Repeated prefix colours and close powers then give local periods on overlapping windows;
interval gluing retains the first period on the entire tail.

## References

* Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem* (2018),
  arXiv:1801.06704, Theorem 1 and Section 3, especially equation (1).
-/

public section

namespace TauCeti

variable {Δ : Type*} {f : ℕ → Δ} {a b k : ℕ}

/-- A finite prefix colouring of an automatic sequence controls all doubled radix blocks.
The same colouring works for every positive exponent, including the suffix value `2 * k ^ n`.
Equality of colours means equality of reached states, not merely equality of outputs. -/
theorem IsAutomatic.exists_prefix_coloring [NeZero k] (hf : IsAutomatic k f) (hk : 2 ≤ k) :
    ∃ q : ℕ, 0 < q ∧ ∃ C : ℕ → Fin q,
      ∀ x y, C x = C y → ∀ n, 0 < n → ∀ z, z ≤ 2 * k ^ n →
        f (x * k ^ n + z) = f (y * k ^ n + z) := by
  classical
  obtain ⟨σ, _, M, hM⟩ :=
    (isAutomatic_iff_exists_dfao_output_eval_eq_ofDigits_reverse (d := 2 * k) hk
      (by omega)).mp hf
  let word (x : ℕ) : List (Fin (2 * k + 1)) :=
    (((Nat.digits k x).map (Fin.ofNat k)).map (Fin.castLE (by omega))).reverse
  have hword (x : ℕ) : Nat.ofDigits k ((word x).map Fin.val).reverse = x := by
    simp only [word, List.map_reverse, List.reverse_reverse, List.map_map,
      Function.comp_def, Fin.val_castLE]
    simpa only [List.map_map, Function.comp_def, Nat.ofDigits_digits] using
      congrArg (Nat.ofDigits k) (Nat.map_val_map_ofNat_digits hk x)
  let : Nonempty σ := ⟨M.start⟩
  refine ⟨Fintype.card σ, Fintype.card_pos, fun x ↦ Fintype.equivFin σ (M.eval (word x)), ?_⟩
  intro x y hxy n hn z hz
  have hstate : M.eval (word x) = M.eval (word y) := (Fintype.equivFin σ).injective hxy
  obtain ⟨w, hw, hv⟩ := Nat.exists_list_fin_two_mul_length_ofDigits_eq (by omega : 0 < k) hn hz
  have hvalue (x : ℕ) :
      Nat.ofDigits k (((word x ++ w.reverse).map Fin.val).reverse) = x * k ^ n + z := by
    simp only [List.map_append, List.reverse_append, List.map_reverse, List.reverse_reverse,
      Nat.ofDigits_append, hv, List.length_map, hw, hword]
    ac_rfl
  calc
    f (x * k ^ n + z) = M.output (M.eval (word x ++ w.reverse)) := by rw [hM, hvalue]
    _ = M.output (M.eval (word y ++ w.reverse)) := by rw [M.eval_append, M.eval_append, hstate]
    _ = f (y * k ^ n + z) := by rw [hM, hvalue]

/-- **Cobham's theorem**, forward direction: a sequence automatic in two multiplicatively
independent bases has a positive period after a finite exceptional prefix. -/
theorem IsAutomatic.exists_eventually_periodic_of_forall_pow_ne_pow [NeZero a] [NeZero b]
    (hf : IsAutomatic a f) (hg : IsAutomatic b f) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : ∀ m n : ℕ, 0 < m → 0 < n → a ^ m ≠ b ^ n) :
    ∃ N p : ℕ, 0 < p ∧ ∀ t, N ≤ t → f (t + p) = f t := by
  obtain ⟨r, _, A, hA⟩ := hf.exists_prefix_coloring ha
  obtain ⟨s, _, B, hB⟩ := hg.exists_prefix_coloring hb
  obtain ⟨N, ξ, _, hrep⟩ := exists_uniform_repeated_representatives A B
  obtain ⟨m, n, hm, hn, hclose⟩ := Nat.exists_pos_mul_abs_pow_sub_pow_le a b (6 * ξ) ha hb
  have hclose' : 6 * (ξ : ℤ) * |(a ^ m : ℕ) - (b ^ n : ℤ)| ≤ b ^ n := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hclose
  have hlocal : ∀ x, N ≤ x → ∃ p, 0 < p ∧ 6 * p ≤ b ^ n ∧
      ∀ t, 3 * (x * b ^ n) + b ^ n ≤ 3 * t →
        3 * (t + p) ≤ 3 * (x * b ^ n) + 5 * b ^ n → f (t + p) = f t := by
    intro x hx
    obtain ⟨u, hu, v, hv, huv, hux, hvx, huvA⟩ := hrep x hx
    exact ⟨_, natAbs_sub_mul_sub_period_on_radix_window hu hv huv (hab m n hm hn)
      hclose' rfl (hB x u hux.symm n hn) (hB x v hvx.symm n hn) (hA u v huvA m hm)⟩
  obtain ⟨p, hp, _, htail⟩ := Nat.exists_periodic_tail_of_period_on_radix_windows hlocal
  exact ⟨(N + 1) * b ^ n, p, hp, htail⟩

/-- **Cobham's base-independence theorem.** For two bases at least two with no equal positive
powers, simultaneous automaticity is equivalent to eventual periodicity. -/
theorem isAutomatic_and_isAutomatic_iff_eventually_periodic [NeZero a] [NeZero b]
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : ∀ m n : ℕ, 0 < m → 0 < n → a ^ m ≠ b ^ n) :
    IsAutomatic a f ∧ IsAutomatic b f ↔
      ∃ N p : ℕ, 0 < p ∧ ∀ t, N ≤ t → f (t + p) = f t := by
  constructor
  · rintro ⟨hf, hg⟩
    exact hf.exists_eventually_periodic_of_forall_pow_ne_pow hg ha hb hab
  · rintro ⟨N, p, hp, h⟩
    exact ⟨isAutomatic_of_eventually_periodic hp h, isAutomatic_of_eventually_periodic hp h⟩

/-! ### Checks -/

-- Distinct bases need not be multiplicatively independent.
example : (2 : ℕ) ≠ 4 ∧ (2 : ℕ) ^ 2 = 4 ^ 1 := by decide

-- The concrete independent pair 2, 3 gives eventual, not necessarily global, periodicity.
example (hf : IsAutomatic 2 f) (hg : IsAutomatic 3 f) :
    ∃ N p : ℕ, 0 < p ∧ ∀ t, N ≤ t → f (t + p) = f t := by
  apply hf.exists_eventually_periodic_of_forall_pow_ne_pow hg (by decide) (by decide)
  intro m n hm _ heq
  have hmod := congrArg (· % 2) heq
  norm_num [Nat.pow_mod, hm.ne'] at hmod

-- The finite exceptional prefix is retained: this sequence is not periodic from zero.
example (ha : 2 ≤ a) (hb : 2 ≤ b) [NeZero a] [NeZero b]
    (hab : ∀ m n : ℕ, 0 < m → 0 < n → a ^ m ≠ b ^ n) :
    IsAutomatic a (fun t ↦ if t = 0 then 7 else t % 2) ∧
      IsAutomatic b (fun t ↦ if t = 0 then 7 else t % 2) := by
  apply (isAutomatic_and_isAutomatic_iff_eventually_periodic ha hb hab).mpr
  refine ⟨1, 2, by decide, ?_⟩
  intro t ht
  simp [show t ≠ 0 by omega]

example : ¬ ∃ p : ℕ, 0 < p ∧ ∀ t,
    (if t + p = 0 then 7 else (t + p) % 2) = (if t = 0 then 7 else t % 2) := by
  rintro ⟨p, hp, h⟩
  have := h 0
  simp [show p ≠ 0 by omega] at this
  omega

end TauCeti
