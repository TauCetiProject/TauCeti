/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.GroupTheory.ProperPower
import TauCeti.Data.List.Commutation
import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced
import TauCeti.GroupTheory.FreeGroup.ProperPower.Computability

/-!
# Roots of cyclically reduced words

Write `wⁿ` for the concatenation `(List.replicate n w).flatten` of `n` copies of a word `w`.
A cyclically reduced word represents a proper power of the free group exactly when it is a word
power `uˡ` with `l ≥ 2` (`FreeGroup.IsCyclicallyReduced.isProperPower_mk_iff`). Hence a nonempty
cyclically reduced word `w` is a power `rᵏ`, `k ≠ 0`, of a word `r` representing an element that
is not a proper power
(`FreeGroup.IsCyclicallyReduced.exists_eq_flatten_replicate_not_isProperPower`); by uniqueness of
maximal roots (`IsFreeGroup.exists_maximalRoot`), `r` represents the maximal root of the element
represented by `w`. Two words `a`, `b` that represent non-proper-powers and have powers with a
common prefix of length `|a| + |b|` are equal (`FreeGroup.eq_of_prefix_flatten_replicate`).

These are the existence half of Corollary 4.2 (for cyclically reduced words) and Lemma 5 of
Lyndon and Schützenberger, where a word that is not a power `uᵐ` with `m > 1` is called
*primitive*. For a cyclically reduced word this is the same as representing an element that is
not a proper power; for other words it is weaker (`x y y x⁻¹` is primitive, but represents a
square), so the form of Lemma 5 stated here is a special case of theirs.

## References

* R. C. Lyndon, M. P. Schützenberger, *The equation `a^M = b^N c^P` in a free group*, Michigan
  Math. J. 9 (1962), 289–298, §2, Corollary 4.2 and Lemma 5.
-/

public section

open Group

namespace FreeGroup

variable {α : Type*}

/-- A cyclically reduced word represents a proper power exactly when it is the concatenation of
`l ≥ 2` copies of a single word. -/
theorem IsCyclicallyReduced.isProperPower_mk_iff {w : List (α × Bool)}
    (hw : IsCyclicallyReduced w) : IsProperPower (mk w) ↔
      ∃ u : List (α × Bool), ∃ l : ℕ, 2 ≤ l ∧ w = (List.replicate l u).flatten := by
  refine ⟨fun h ↦ ?_, fun ⟨u, l, hl, hu⟩ ↦ hu ▸ pow_mk (L := u) l ▸ isProperPower_pow _ hl⟩
  -- `w = c ++ uˡ ++ invRev c` for a prefix `c` of `w`, and `c = []` since `w` is cyclically
  -- reduced.
  obtain rfl | ⟨i, -, j, -, l, -, hl, hw'⟩ :=
    (isProperPower_mk_iff_exists_bounded_replicate hw.isReduced).1 h
  · exact ⟨[], 2, le_rfl, rfl⟩
  obtain hc | hc := eq_or_ne (w.take i) []
  · exact ⟨_, l, hl, by simpa [hc] using hw'⟩
  · exact absurd (hw' ▸ hw) (not_isCyclicallyReduced_append_append_invRev hc _)

/-- **Lyndon–Schützenberger, Corollary 4.2**, existence half, for cyclically reduced words: a
nonempty cyclically reduced word is a nonzero power of a word representing an element that is not
a proper power. -/
theorem IsCyclicallyReduced.exists_eq_flatten_replicate_not_isProperPower {w : List (α × Bool)}
    (hw : IsCyclicallyReduced w) (hw₀ : w ≠ []) : ∃ r : List (α × Bool), ∃ k : ℕ,
      k ≠ 0 ∧ w = (List.replicate k r).flatten ∧ ¬IsProperPower (mk r) := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases h : IsProperPower (mk w)
    · -- Then `w = uˡ` with `l ≥ 2`, and the shorter word `u` is cyclically reduced.
      obtain ⟨u, l, hl, rfl⟩ := hw.isProperPower_mk_iff.1 h
      have hl₀ : l ≠ 0 := by lia
      have hu₀ : u ≠ [] := by rintro rfl; simp at hw₀
      have hlen : u.length < l * u.length :=
        (Nat.lt_mul_iff_one_lt_left (List.length_pos_iff.2 hu₀)).2 (by lia)
      obtain ⟨r, k, hk, rfl, hr⟩ := ih u.length (by simpa [← hn] using hlen)
        ((isCyclicallyReduced_flatten_replicate_iff hl₀).1 hw) hu₀ rfl
      exact ⟨r, l * k, Nat.mul_ne_zero hl₀ hk, by
        rw [← List.flatten_replicate_replicate, List.flatten_flatten, List.map_replicate], hr⟩
    · exact ⟨w, 1, one_ne_zero, by simp, h⟩

/-- **Lyndon–Schützenberger, Lemma 5.** If the words `a` and `b` represent elements that are not
proper powers, and a power of `a` and a power of `b` have a common prefix of length at least
`|a| + |b|`, then `a = b`. -/
theorem eq_of_prefix_flatten_replicate {a b x : List (α × Bool)} {m n : ℕ}
    (ha : ¬IsProperPower (mk a)) (hb : ¬IsProperPower (mk b))
    (h₁ : x <+: (List.replicate m a).flatten) (h₂ : x <+: (List.replicate n b).flatten)
    (hx : a.length + b.length ≤ x.length) : a = b := by
  obtain ⟨w, i, j, rfl, rfl⟩ := List.exists_eq_flatten_replicate_of_append_comm
    (List.append_comm_of_prefix_flatten_replicate h₁ h₂ hx)
  -- A power `wᵏ` represents `mk w ^ k`, a proper power unless `k = 1`.
  have key (k : ℕ) (hk : ¬IsProperPower (mk (List.replicate k w).flatten)) : k = 1 := by
    rw [← pow_mk] at hk
    rcases k with _ | _ | k
    · simp at hk
    · rfl
    · exact absurd (isProperPower_pow _ (by lia)) hk
  rw [key i ha, key j hb]

end FreeGroup
