/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.AutomaticSequence.ReadingDirection
import TauCeti.Combinatorics.Pigeonhole.RepeatedRepresentatives
import TauCeti.Computability.AutomaticSequence.LocalPeriod
import TauCeti.Data.Nat.Digits
import TauCeti.Data.Nat.Periodic.RadixWindows
import TauCeti.NumberTheory.ExponentialEquation.ClosePowers

/-!
# Cobham's theorem

Two bases `k, l ≥ 2` are multiplicatively independent if `k ^ m ≠ l ^ n` for all `m, n ≥ 1`.
Cobham's theorem says that a sequence which is both `k`-automatic and `l`-automatic for
multiplicatively independent `k` and `l` is eventually periodic. Conversely, an eventually
periodic sequence is automatic in every base, so for independent bases the sequences automatic
in both are exactly the eventually periodic ones. Without independence this fails: the
sequence that is `1` at the powers of `2` and `0` elsewhere is `2`-automatic and `4`-automatic,
but not eventually periodic.

The proof follows Krebs. A `k`-automatic sequence `a` admits a colouring of `ℕ` by finitely many
colours such that equally coloured `x` and `y` give equal blocks
`a (x k ^ n + z) = a (y k ^ n + z)` for every `n ≥ 1` and every `z ≤ 2 k ^ n`: colour `x` by the
state an automaton reading redundant digits up to `2k`, most significant digit first, reaches on
the canonical word of `x`. Comparing the colourings in both bases at close powers `A = k ^ m` and
`B = l ^ n` gives a positive period on each window `[xB + B/3, xB + 5B/3]`, and these local periods
glue into a single period of a tail.

## Main results

* `TauCeti.IsAutomatic.exists_fin_apply_mul_pow_add_eq_of_eq`: finitely many prefix colours
  control all the blocks of length `2 k ^ n + 1` at the scales `k ^ n`.
* `TauCeti.IsAutomatic.exists_periodic_tail`: **Cobham's theorem**, a sequence automatic in two
  multiplicatively independent bases is eventually periodic.
* `TauCeti.isAutomatic_and_isAutomatic_iff`: for multiplicatively independent bases, automaticity
  in both bases is equivalent to eventual periodicity.

## References

* Alan Cobham, *On the base-dependence of sets of numbers recognizable by finite automata*,
  Math. Systems Theory 3 (1969), 186–192.
* Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem*, 2018, arXiv:1801.06704,
  Theorem 1 and its proof in §3, equation (1).
-/

public section

universe u

namespace TauCeti

variable {k l : ℕ} [NeZero k] [NeZero l] {Δ : Type u} {a : ℕ → Δ}

/-- **Finite prefix colours control wide radix blocks.** For `2 ≤ k`, a `k`-automatic sequence `a`
admits a colouring `C : ℕ → Fin q` such that `C x = C y` implies
`a (x * k ^ n + z) = a (y * k ^ n + z)` for every `n ≥ 1` and every `z ≤ 2 * k ^ n`. The same
colouring serves all the lengths `n` and all the offsets `z`. -/
theorem IsAutomatic.exists_fin_apply_mul_pow_add_eq_of_eq (hk : 2 ≤ k) (ha : IsAutomatic k a) :
    ∃ (q : ℕ) (C : ℕ → Fin q), ∀ x y, C x = C y → ∀ n, 0 < n → ∀ z ≤ 2 * k ^ n,
      a (x * k ^ n + z) = a (y * k ^ n + z) := by
  obtain ⟨σ, _, M, hM⟩ :=
    (isAutomatic_iff_exists_dfao_output_eval_eq_ofDigits_reverse (d := 2 * k) hk (by omega)).mp ha
  -- Every `x` is the value of its canonical digits, written most significant digit first.
  have hword (x : ℕ) : ∃ w : List (Fin (2 * k + 1)), Nat.ofDigits k (w.map Fin.val).reverse = x :=
    ⟨(((Nat.digits k x).map (Fin.ofNat k)).map (Fin.castLE (by omega))).reverse, by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      simp only [Function.comp_def, Fin.val_castLE]
      rw [Nat.map_val_map_ofNat_digits hk, Nat.ofDigits_digits]⟩
  choose w hw using hword
  refine ⟨Fintype.card σ, fun x ↦ Fintype.equivFin σ (M.eval (w x)), ?_⟩
  intro x y hxy n hn z hz
  -- Append to both prefixes a common suffix of length `n` and value `z`.
  obtain ⟨s, hs, hsz⟩ := Nat.exists_length_eq_ofDigits_eq_of_le_two_mul_pow hn hz
  have hval (x : ℕ) : Nat.ofDigits k ((w x ++ s.reverse).map Fin.val).reverse = x * k ^ n + z := by
    simp [Nat.ofDigits_append, hsz, hs, hw]
    ring
  have hstate : M.eval (w x) = M.eval (w y) := (Fintype.equivFin σ).injective hxy
  rw [← hval x, ← hval y, ← hM, ← hM, DFAO.eval_append, DFAO.eval_append, hstate]

/-- **Cobham's theorem.** Let `k, l ≥ 2` be multiplicatively independent, that is,
`k ^ m ≠ l ^ n` for all `m, n ≥ 1`. A sequence that is both `k`-automatic and `l`-automatic is
eventually periodic: there are `N` and `p > 0` with `a (t + p) = a t` for every `t ≥ N`. -/
theorem IsAutomatic.exists_periodic_tail (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hind : ∀ m n, 0 < m → 0 < n → k ^ m ≠ l ^ n) (hak : IsAutomatic k a)
    (hal : IsAutomatic l a) :
    ∃ N p, 0 < p ∧ ∀ t, N ≤ t → a (t + p) = a t := by
  obtain ⟨_, Ck, hCk⟩ := hak.exists_fin_apply_mul_pow_add_eq_of_eq hk
  obtain ⟨_, Cl, hCl⟩ := hal.exists_fin_apply_mul_pow_add_eq_of_eq hl
  -- Every tail `l`-colour has two bounded representatives with the same `k`-colour.
  obtain ⟨N, ξ, -, hrep⟩ := exists_uniform_repeated_representatives Ck Cl
  obtain ⟨m, n, hm, hn, hclose⟩ := Nat.exists_pos_mul_abs_pow_sub_pow_le k l (6 * ξ) hk hl
  have hclose' : 6 * ξ * |((k ^ m : ℕ) : ℤ) - ((l ^ n : ℕ) : ℤ)| ≤ ((l ^ n : ℕ) : ℤ) := by
    push_cast at hclose ⊢
    exact hclose
  -- Each radix window at the scale `l ^ n` carries a positive period at most `l ^ n / 6`.
  obtain ⟨p, hp, -, hper⟩ := Nat.exists_periodic_tail_of_period_on_radix_windows
    (f := a) (B := l ^ n) (N := N) fun x hx ↦ by
      obtain ⟨u, hu, v, hv, huv, hux, hvx, huv'⟩ := hrep x hx
      exact ⟨_, natAbs_sub_mul_sub_period_on_radix_window hu hv huv (hind m n hm hn) hclose' rfl
        (hCl x u hux.symm n hn) (hCl x v hvx.symm n hn) (hCk u v huv' m hm)⟩
  exact ⟨(N + 1) * l ^ n, p, hp, hper⟩

/-- **Cobham's theorem**, as an equivalence. For multiplicatively independent bases `k, l ≥ 2`,
a sequence is both `k`-automatic and `l`-automatic exactly when it is eventually periodic. -/
theorem isAutomatic_and_isAutomatic_iff (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hind : ∀ m n, 0 < m → 0 < n → k ^ m ≠ l ^ n) :
    IsAutomatic k a ∧ IsAutomatic l a ↔ ∃ N p, 0 < p ∧ ∀ t, N ≤ t → a (t + p) = a t :=
  ⟨fun h ↦ h.1.exists_periodic_tail hk hl hind h.2,
    fun ⟨_, _, hp, h⟩ ↦ ⟨isAutomatic_of_eventually_periodic hp h,
      isAutomatic_of_eventually_periodic hp h⟩⟩

/-! ### Checks -/

/-- The bases `2` and `3` are multiplicatively independent, since their powers are coprime. -/
example : ∀ m n : ℕ, 0 < m → 0 < n → 2 ^ m ≠ 3 ^ n := fun m n _ hn h ↦ by
  have := Nat.Coprime.pow m n (by decide : Nat.Coprime 2 3)
  rw [h, Nat.coprime_self] at this
  exact (Nat.one_lt_pow hn.ne' (by norm_num)).ne' this

/-- The distinct bases `2` and `4` are not multiplicatively independent. -/
example : ¬ ∀ m n : ℕ, 0 < m → 0 < n → 2 ^ m ≠ 4 ^ n :=
  fun h ↦ h 2 1 two_pos one_pos rfl

/-- The sequence equal to `7` at zero and to the parity of `t` elsewhere is both `2`-automatic and
`3`-automatic: its tail from `1` has period `2`. -/
example : IsAutomatic 2 (fun t : ℕ ↦ if t = 0 then 7 else t % 2) ∧
    IsAutomatic 3 (fun t : ℕ ↦ if t = 0 then 7 else t % 2) := by
  refine (isAutomatic_and_isAutomatic_iff (by norm_num) (by norm_num) fun m n _ hn h ↦ ?_).mpr
    ⟨1, 2, two_pos, fun t ht ↦ by simp [show t ≠ 0 by omega]⟩
  have := Nat.Coprime.pow m n (by decide : Nat.Coprime 2 3)
  rw [h, Nat.coprime_self] at this
  exact (Nat.one_lt_pow hn.ne' (by norm_num)).ne' this

end TauCeti
