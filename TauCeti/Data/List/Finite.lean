/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Basic.Finite.Prod

/-!
# Finitely many words of bounded degree

A positive integer weight bounds a word's length by its total weight. If the
letters of weight at most the cutoff are finite, the words are finite as well.
The proof uses Mathlib's `List.finite_length_le` with those letters as the alphabet.

-/

public section

namespace List

/-- Over an alphabet of positive integer weights, a fixed weight cutoff permits
only finitely many words whenever it permits only finitely many letters. -/
theorem finite_setOf_sum_map_le {α : Type*} {s : Set α} (w : α → ℤ) (k : ℕ)
    (hpos : ∀ a ∈ s, 0 < w a) (hcut : {a ∈ s | w a ≤ k}.Finite) :
    {l : List α | (∀ a ∈ l, a ∈ s) ∧ (l.map w).sum ≤ k}.Finite := by
  let : Finite {a ∈ s | w a ≤ k} := hcut.to_subtype
  apply ((finite_length_le {a ∈ s | w a ≤ k} k).image (map Subtype.val)).subset
  rintro l ⟨hs, hsum⟩
  have hweight (b : ℤ) (hb : b ∈ l.map w) : 1 ≤ b := by
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hb
    have := hpos a (hs a ha)
    omega
  have hentry (a : α) (ha : a ∈ l) : a ∈ {a ∈ s | w a ≤ k} :=
    ⟨hs a ha, (single_le_sum (fun b hb => (zero_le_one.trans (hweight b hb)))
      _ (mem_map.mpr ⟨a, ha, rfl⟩)).trans hsum⟩
  have hlen : (l.length : ℤ) ≤ (l.map w).sum := by
    simpa only [length_map, nsmul_eq_mul, mul_one] using
      (length_nsmul_le_sum (l.map w) (1 : ℤ) hweight)
  refine ⟨l.attachWith _ hentry, ?_, attachWith_map_subtype_val hentry⟩
  change (l.attachWith (· ∈ {a ∈ s | w a ≤ k}) hentry).length ≤ k
  rw [length_attachWith]
  exact_mod_cast hlen.trans hsum

/-- Over a finite alphabet `α`, there are finitely many words `l : List (α × ℕ)` whose total
degree `(l.map fun p => p.2 + 1).sum` is at most `K`. -/
theorem finite_setOf_sum_map_snd_add_one_le (α : Type*) [Finite α] (K : ℕ) :
    {l : List (α × ℕ) | (l.map fun p => p.2 + 1).sum ≤ K}.Finite := by
  let w (p : α × ℕ) : ℤ := (p.2 + 1 : ℕ)
  have hcut : {p ∈ (Set.univ : Set (α × ℕ)) | w p ≤ K}.Finite := by
    refine (Set.finite_range (fun p : α × Fin (K + 1) => (p.1, (p.2 : ℕ)))).subset ?_
    rintro ⟨a, n⟩ ⟨_, hn⟩
    change ((n + 1 : ℕ) : ℤ) ≤ K at hn
    exact ⟨(a, ⟨n, by omega⟩), rfl⟩
  have hpos (p : α × ℕ) : 0 < w p := by
    dsimp [w]
    omega
  refine (finite_setOf_sum_map_le w K (fun p _ => hpos p) hcut).subset ?_
  intro l hl
  refine ⟨fun _ _ => Set.mem_univ _, ?_⟩
  change (l.map fun p => p.2 + 1).sum ≤ K at hl
  change (l.map (Nat.castAddMonoidHom ℤ ∘ fun p => p.2 + 1)).sum ≤ K
  rw [← List.map_map, ← map_list_sum]
  exact Int.ofNat_le.mpr hl

end List
