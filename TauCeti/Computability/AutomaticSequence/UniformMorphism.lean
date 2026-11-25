/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.AutomaticSequence.Kernel
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import TauCeti.Data.Nat.Digits

/-!
# Cobham's characterisation of automatic sequences by uniform morphisms

Let `k ≥ 1`. A `k`-uniform morphism on a finite alphabet `Γ` sends each letter to a word of
length `k` over `Γ`; we write it as a map `φ : Γ → Fin k → Γ`, the `r`-th letter of the image of
`γ` being `φ γ r`. Applied letter by letter to an infinite word `s : ℕ → Γ`, it produces the word
whose letter at `k * n + r` is `φ (s n) r`, so `s` is a fixed point of `φ` exactly when
`s (k * n + r) = φ (s n) r` for all `n` and `r < k` (`TauCeti.IsUniformFixedPoint`). For `n = 0`
and `r = 0` this says `φ (s 0) 0 = s 0`; conversely, every letter `γ` with `φ γ 0 = γ` starts a
fixed point. For `k ≥ 2` that fixed point is unique: its letter at `n` is reached from `γ` by
applying `φ` along the base-`k` digits of `n`, most significant first. In base one every word is
a fixed point of the identity morphism, so uniqueness fails.

Cobham's theorem on uniform tag sequences characterises the `k`-automatic sequences, for `k ≥ 2`,
as the images under a letter-to-letter coding `τ : Γ → Δ` of the fixed points of `k`-uniform
morphisms on finite alphabets (`TauCeti.isAutomatic_iff_exists_isUniformFixedPoint`). The
Thue–Morse sequence, the fixed point of `0 ↦ 01`, `1 ↦ 10`, is the model example.

## Main definitions and results

* `TauCeti.IsUniformFixedPoint φ s`: the infinite word `s` is a fixed point of the `k`-uniform
  morphism `φ`.
* `TauCeti.IsUniformFixedPoint.foldl_reverse`: applying `φ` from `s m` along a word `w`, most
  significant digit first, reaches `s (k ^ |w| * m + v)`, where `v` is the value of `w`. Leading
  zeros and arbitrary words are allowed.
* `TauCeti.isUniformFixedPoint_foldl_reverse_map_digits`, `TauCeti.exists_isUniformFixedPoint`
  and `TauCeti.IsUniformFixedPoint.eq_of_apply_zero_eq`: a fixed point exists with any first
  letter `γ` such that `φ γ 0 = γ`, given explicitly by applying `φ` from `γ` along the digits,
  and for `k ≥ 2` it is determined by its first letter.
* `TauCeti.IsUniformFixedPoint.isAutomatic`: a fixed point of a `k`-uniform morphism on a finite
  alphabet is `k`-automatic, for `k ≥ 2`, and hence so are its codings (`TauCeti.IsAutomatic.map`).
* `TauCeti.IsAutomatic.exists_isUniformFixedPoint`: every `k`-automatic sequence is such a
  coding.
* `TauCeti.isAutomatic_iff_exists_isUniformFixedPoint`: **Cobham's theorem**, for `k ≥ 2` a
  sequence is `k`-automatic if and only if it is the coding of a fixed point of a `k`-uniform
  morphism on a finite alphabet.

## Implementation notes

For the converse direction, the reversal of the kernel automaton of `a` reads most significant
digit first and its initial state, the map `b ↦ b 0` on the `k`-kernel, is fixed by the digit
`0`, since `b (k * 0 + 0) = b 0`. Its transitions are therefore a `k`-uniform morphism on its
finite set of states, and the states it reaches on the digits of `n` form a fixed point.

## References

* Alan Cobham, *Uniform tag sequences*, Math. Systems Theory 6 (1972), 164–192.
* G. Christol, T. Kamae, M. Mendès France, G. Rauzy, *Suites algébriques, automates et
  substitutions*, Bull. Soc. Math. France 108 (1980), Section 3 and Section 5, Theorem 1.
-/

public section

universe u v

namespace TauCeti

variable {k : ℕ} {Γ : Type u} {Δ : Type v}

/-- The infinite word `s : ℕ → Γ` is a **fixed point of the `k`-uniform morphism** `φ`, which
sends the letter `γ` to the word `φ γ 0, …, φ γ (k - 1)`: for all `n` and `r < k`, the letter of
`s` at `k * n + r` is the `r`-th letter of the image of `s n`. -/
def IsUniformFixedPoint (φ : Γ → Fin k → Γ) (s : ℕ → Γ) : Prop :=
  ∀ (n : ℕ) (r : Fin k), s (k * n + r) = φ (s n) r

variable {φ : Γ → Fin k → Γ} {s t : ℕ → Γ}

/-- Unfolding `TauCeti.IsUniformFixedPoint`. -/
theorem isUniformFixedPoint_iff :
    IsUniformFixedPoint φ s ↔ ∀ (n : ℕ) (r : Fin k), s (k * n + r) = φ (s n) r :=
  Iff.rfl

namespace IsUniformFixedPoint

/-- The letter of a fixed point at `k * n + r` is the `r`-th letter of the image of `s n`. -/
@[grind =>]
theorem apply_mul_add (hs : IsUniformFixedPoint φ s) (n : ℕ) (r : Fin k) :
    s (k * n + r) = φ (s n) r :=
  hs n r

/-- `TauCeti.IsUniformFixedPoint.apply_mul_add` for a natural-number offset `d < k`. -/
theorem apply_mul_add_of_lt (hs : IsUniformFixedPoint φ s) (n : ℕ) {d : ℕ} (hd : d < k) :
    s (k * n + d) = φ (s n) ⟨d, hd⟩ :=
  hs n ⟨d, hd⟩

/-- The letter of a fixed point at `k * n` is the first letter of the image of `s n`. -/
theorem apply_mul [NeZero k] (hs : IsUniformFixedPoint φ s) (n : ℕ) : s (k * n) = φ (s n) 0 := by
  simpa using hs.apply_mul_add n 0

/-- The first letter of a fixed point is fixed by the first letter of the morphism. -/
theorem apply_apply_zero_zero [NeZero k] (hs : IsUniformFixedPoint φ s) : φ (s 0) 0 = s 0 := by
  simpa using (hs.apply_mul 0).symm

/-- Applying the morphism `φ` from the letter `s m` of a fixed point along the word `w`, most
significant digit first, reaches the letter of `s` at `k ^ |w| * m + v`, where `v` is the value of
`w`. The word may have leading zeros. -/
theorem foldl_reverse (hs : IsUniformFixedPoint φ s) (m : ℕ) (w : List (Fin k)) :
    w.reverse.foldl φ (s m) = s (k ^ w.length * m + Nat.ofDigits k (w.map Fin.val)) := by
  induction w with
  | nil => simp
  | cons d w ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rw [← hs.apply_mul_add]
    simp only [List.length_cons, List.map_cons, Nat.ofDigits_cons]
    congr 1
    ring

/-- For `k ≥ 2`, the letter of a fixed point at `n` is reached from its first letter by applying
the morphism along the base-`k` digits of `n`, most significant first. -/
theorem foldl_reverse_map_digits [NeZero k] (hk : 2 ≤ k) (hs : IsUniformFixedPoint φ s)
    (n : ℕ) : ((Nat.digits k n).map (Fin.ofNat k)).reverse.foldl φ (s 0) = s n := by
  rw [hs.foldl_reverse]
  simp [Nat.map_val_map_ofNat_digits hk, Nat.ofDigits_digits]

/-- For `k ≥ 2`, a fixed point of a `k`-uniform morphism is determined by its first letter. -/
theorem eq_of_apply_zero_eq (hk : 2 ≤ k) (hs : IsUniformFixedPoint φ s)
    (ht : IsUniformFixedPoint φ t) (h : s 0 = t 0) : s = t := by
  have : NeZero k := ⟨by omega⟩
  funext n
  rw [← hs.foldl_reverse_map_digits hk, ← ht.foldl_reverse_map_digits hk, h]

end IsUniformFixedPoint

/-- Applying `φ` from a letter `γ` with `φ γ 0 = γ` along the base-`k` digits of `n`, most
significant first, gives a fixed point of `φ` starting with `γ`, the only one for `k ≥ 2`. -/
theorem isUniformFixedPoint_foldl_reverse_map_digits [NeZero k] {γ : Γ} (hγ : φ γ 0 = γ) :
    IsUniformFixedPoint φ fun n ↦ ((Nat.digits k n).map (Fin.ofNat k)).reverse.foldl φ γ := by
  obtain rfl | hk : k = 1 ∨ 2 ≤ k := by
    have := NeZero.ne k
    omega
  · -- In base one every digit is `0`, which fixes `γ`, so the word is constantly `γ`.
    have h (w : List (Fin 1)) : w.foldl φ γ = γ :=
      List.foldl_fixed' (fun r ↦ by rw [Subsingleton.elim r 0, hγ]) w
    intro n r
    simp only [h]
    rw [Subsingleton.elim r 0, hγ]
  intro n r
  by_cases h : (r : ℕ) = 0 ∧ n = 0
  · obtain ⟨hr, rfl⟩ := h
    obtain rfl : r = 0 := Fin.ext hr
    simpa using hγ.symm
  · -- Otherwise the digits of `r + k * n` are `r` followed by the digits of `n`.
    dsimp only
    rw [add_comm, Nat.digits_add k (by omega) r n r.isLt (not_and_or.mp h)]
    simp

/-- Every letter `γ` with `φ γ 0 = γ` is the first letter of a fixed point of the `k`-uniform
morphism `φ`. -/
theorem exists_isUniformFixedPoint [NeZero k] {γ : Γ} (hγ : φ γ 0 = γ) :
    ∃ s, IsUniformFixedPoint φ s ∧ s 0 = γ :=
  ⟨_, isUniformFixedPoint_foldl_reverse_map_digits hγ, by simp⟩

/-- For `k ≥ 2`, a fixed point of a `k`-uniform morphism on a finite alphabet is
`k`-automatic. -/
theorem IsUniformFixedPoint.isAutomatic [NeZero k] [Finite Γ] (hk : 2 ≤ k)
    (hs : IsUniformFixedPoint φ s) : IsAutomatic k s := by
  let M : DFAO (Fin k) Γ Γ := ⟨φ, s 0, id⟩
  convert M.reverse.isAutomatic with n
  rw [DFAO.output_eval_reverse]
  simpa [M, DFAO.eval_eq_evalFrom, DFAO.evalFrom_eq_foldl] using
    (hs.foldl_reverse_map_digits hk n).symm

/-- Every `k`-automatic sequence is a letter-to-letter coding of a fixed point of a `k`-uniform
morphism on a finite alphabet. -/
theorem IsAutomatic.exists_isUniformFixedPoint [NeZero k] {a : ℕ → Δ} (ha : IsAutomatic k a) :
    ∃ (Γ : Type) (_ : Fintype Γ) (φ : Γ → Fin k → Γ) (s : ℕ → Γ) (τ : Γ → Δ),
      IsUniformFixedPoint φ s ∧ ∀ n, a n = τ (s n) := by
  obtain rfl | hk : k = 1 ∨ 2 ≤ k := by
    have := NeZero.ne k
    omega
  · -- In base one every sequence with finitely many values is a coding of a fixed point of the
    -- identity morphism on its range.
    have := ha.finite_range.to_subtype
    obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range a)
    refine ⟨Fin m, inferInstance, fun γ _ ↦ γ, fun n ↦ e ⟨a n, n, rfl⟩, fun γ ↦ (e.symm γ).val,
      fun n r ↦ ?_, fun n ↦ by simp⟩
    simp [Subsingleton.elim r 0]
  -- The reversed kernel automaton reads most significant digit first, and its initial state is
  -- fixed by the digit `0`.
  have := (isAutomatic_iff_finite_kernel hk).mp ha |>.to_subtype
  let N := (kernelDFAO k a).reverse
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (kernel k a → Set.range (kernelDFAO k a).output)
  let M := DFAO.reindex e N
  have hstart : M.step M.start 0 = M.start := by
    have : N.step N.start 0 = N.start := by
      funext b
      ext
      simp [N]
    simp [M, this]
  obtain ⟨s, hs, hs0⟩ := TauCeti.exists_isUniformFixedPoint hstart
  refine ⟨Fin m, inferInstance, M.step, s, M.output, hs, fun n ↦ ?_⟩
  -- The fixed point is the state that `M` reaches on the digits of `n`, read from the top.
  have hstate : s n = M.eval ((Nat.digits k n).map (Fin.ofNat k)).reverse := by
    rw [DFAO.eval_eq_evalFrom, DFAO.evalFrom_eq_foldl, ← hs0, hs.foldl_reverse_map_digits hk]
  rw [hstate, DFAO.output_eval_reindex, DFAO.output_eval_reverse, output_eval_kernelDFAO]
  simp [Nat.map_val_map_ofNat_digits hk, Nat.ofDigits_digits]

/-- **Cobham's theorem on uniform tag sequences.** For `k ≥ 2`, a sequence is `k`-automatic if
and only if it is a letter-to-letter coding of a fixed point of a `k`-uniform morphism on a
finite alphabet. -/
theorem isAutomatic_iff_exists_isUniformFixedPoint [NeZero k] (hk : 2 ≤ k) {a : ℕ → Δ} :
    IsAutomatic k a ↔
      ∃ (Γ : Type) (_ : Fintype Γ) (φ : Γ → Fin k → Γ) (s : ℕ → Γ) (τ : Γ → Δ),
        IsUniformFixedPoint φ s ∧ ∀ n, a n = τ (s n) := by
  refine ⟨IsAutomatic.exists_isUniformFixedPoint, ?_⟩
  rintro ⟨Γ, _, φ, s, τ, hs, ha⟩
  simpa only [← ha] using (hs.isAutomatic hk).map τ

/-! ### Checks -/

/-- The Thue–Morse sequence, the parity of the binary digit sum, is a fixed point of the
`2`-uniform morphism `0 ↦ 01`, `1 ↦ 10`. -/
private theorem isUniformFixedPoint_thueMorse :
    IsUniformFixedPoint (fun (x : ZMod 2) (r : Fin 2) ↦ x + (r : ℕ))
      fun n ↦ ((Nat.digits 2 n).sum : ZMod 2) := by
  intro n r
  dsimp only
  rw [add_comm, Nat.sum_digits_add_mul r.isLt]
  push_cast
  ring

/-- Every fixed point of `0 ↦ 01`, `1 ↦ 10` starting with `0` is `2`-automatic, and it is the
Thue–Morse sequence. -/
example {s : ℕ → ZMod 2}
    (hs : IsUniformFixedPoint (fun (x : ZMod 2) (r : Fin 2) ↦ x + (r : ℕ)) s)
    (h0 : s 0 = 0) :
    IsAutomatic 2 s ∧ s = fun n ↦ ((Nat.digits 2 n).sum : ZMod 2) :=
  ⟨hs.isAutomatic le_rfl,
    hs.eq_of_apply_zero_eq le_rfl isUniformFixedPoint_thueMorse (by simp [h0])⟩

/-- The fixed point of `0 ↦ 01`, `1 ↦ 10` starting with `1` is `2`-automatic too. -/
example : IsAutomatic 2 fun n ↦ 1 + ((Nat.digits 2 n).sum : ZMod 2) :=
  (isUniformFixedPoint_thueMorse.isAutomatic le_rfl).map (1 + ·)

/-- In base one the fixed-point equations do not determine the word: every word is a fixed point
of the identity morphism. -/
example (s : ℕ → Bool) : IsUniformFixedPoint (fun (γ : Bool) (_ : Fin 1) ↦ γ) s := by
  intro n r
  simp [Subsingleton.elim r 0]

end TauCeti
