/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.Algebra.Group.ProperPower
import TauCeti.Data.List.Commutation
import TauCeti.GroupTheory.FreeGroup.Conjugacy.Basic
import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Proper powers represented by words

Write `wⁿ` for the concatenation `(List.replicate n w).flatten` of `n` copies of a word `w`.
A reduced word represents a proper power of the free group exactly when it is empty or has the
form `c ++ vⁿ ++ c⁻¹` with `n ≥ 2`, where the conjugator `c`, the block `v` and the exponent `n`
are bounded by the length of the word (`FreeGroup.isProperPower_mk_iff_exists_bounded_replicate`).
The word decomposition uses Mathlib's `FreeGroup.reduceCyclically.reduce_flatten_replicate`.

For a cyclically reduced word the conjugator is empty, so such a word represents a proper power
exactly when it is a word power `uˡ` with `l ≥ 2`
(`FreeGroup.IsCyclicallyReduced.isProperPower_mk_iff`): it represents a non-proper-power exactly
when it is *primitive* in the sense of Lyndon and Schützenberger. Hence a nonempty cyclically
reduced word `w` is a power `rᵏ`, `k ≠ 0`, of a word `r` representing an element that is not a
proper power (`FreeGroup.IsCyclicallyReduced.exists_eq_flatten_replicate_not_isProperPower`); by
uniqueness of maximal roots (`IsFreeGroup.exists_maximalRoot`), `r` represents the maximal root of
the element represented by `w`.

## References

* R. C. Lyndon and P. E. Schupp, *Combinatorial Group Theory*, Chapter I, §1
  (cyclic reduction and powers of cyclically reduced words).
* R. C. Lyndon, M. P. Schützenberger, *The equation `a^M = b^N c^P` in a free group*, Michigan
  Math. J. 9 (1962), 289–298, §2, Corollary 4.2.
-/

public section

open Monoid

namespace FreeGroup

variable {α : Type*}

/-- A reduced word represents a proper power exactly when it is empty or is a conjugate
of a repeated block. The conjugator and block are extracted from the input by bounded
indices, and the exponent is bounded by its length. -/
theorem isProperPower_mk_iff_exists_bounded_replicate {w : List (α × Bool)}
    (hw : IsReduced w) :
    Monoid.IsProperPower (mk w) ↔ w = [] ∨
      ∃ i ≤ w.length, ∃ j ≤ w.length, ∃ n ≤ w.length, 2 ≤ n ∧
        w = w.take i ++ (List.replicate n ((w.drop i).take j)).flatten ++
          invRev (w.take i) := by
  classical
  constructor
  · intro h
    by_cases hw0 : w = []
    · exact Or.inl hw0
    obtain ⟨y, n, hn, hy⟩ := Monoid.isProperPower_iff.mp h
    let c := reduceCyclically.conjugator y.toWord
    let v := reduceCyclically y.toWord
    have heq : w = c ++ (List.replicate n v).flatten ++ invRev c := by
      have hword := congrArg toWord hy
      simpa only [toWord_mk, hw.reduce_eq, toWord_pow,
        reduceCyclically.reduce_flatten_replicate isReduced_toWord,
        ite_eq_right (by omega : n ≠ 0)] using hword
    have hv : v ≠ [] := by
      intro hv0
      have hy1 : y = 1 := by
        have hc := mk_conjugator_mul_mk_reduceCyclically y.toWord
        dsimp only [v] at hv0
        rw [hv0, ← one_eq_mk, mul_one, mul_inv_cancel, mk_toWord] at hc
        exact hc.symm
      simp only [hy1, one_pow] at hy
      exact hw0 (hw.eq_of_mk_eq IsReduced.nil hy)
    have hlen : w.length = c.length + n * v.length + c.length := by
      rw [heq]
      simp [Nat.add_assoc]
    have hi : c.length ≤ w.length := by omega
    have hj : v.length ≤ w.length := by
      have := Nat.le_mul_of_pos_left v.length (by omega : 0 < n)
      omega
    have hnlen : n ≤ w.length := by
      have := Nat.le_mul_of_pos_right n (List.length_pos_iff.mpr hv)
      omega
    have htake : w.take c.length = c := by
      rw [heq, List.append_assoc]
      simp
    have hblock : (w.drop c.length).take v.length = v := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [heq, List.append_assoc]
      simp [List.replicate_succ, List.append_assoc]
    exact Or.inr ⟨c.length, hi, v.length, hj, n, hnlen, hn,
      by simpa only [htake, hblock] using heq⟩
  · rintro (rfl | ⟨i, _, j, _, n, _, hn, heq⟩)
    · simpa only [← one_eq_mk] using (Monoid.IsProperPower.one (M := FreeGroup α))
    · rw [heq, ← mul_mk, ← mul_mk, ← inv_mk, ← pow_mk]
      exact (Monoid.isProperPower_conj_iff _ _).mpr
        (Monoid.isProperPower_pow _ hn)

/-- A cyclically reduced word represents a proper power exactly when it is the concatenation of
`l ≥ 2` copies of a single word. This is `FreeGroup.isProperPower_mk_iff_exists_bounded_replicate`
for cyclically reduced words: a cyclically reduced word `c ++ vⁿ ++ c⁻¹` has `c = []`. -/
theorem IsCyclicallyReduced.isProperPower_mk_iff {w : List (α × Bool)}
    (hw : IsCyclicallyReduced w) : IsProperPower (mk w) ↔
      ∃ u : List (α × Bool), ∃ l : ℕ, 2 ≤ l ∧ w = (List.replicate l u).flatten := by
  refine ⟨fun h ↦ ?_, fun ⟨u, l, hl, hu⟩ ↦ hu ▸ pow_mk (L := u) l ▸ isProperPower_pow _ hl⟩
  obtain rfl | ⟨i, -, j, -, l, -, hl, hw'⟩ :=
    (isProperPower_mk_iff_exists_bounded_replicate hw.isReduced).1 h
  · exact ⟨[], 2, le_rfl, rfl⟩
  obtain hc | hc := eq_or_ne (w.take i) []
  · exact ⟨_, l, hl, by simpa [hc] using hw'⟩
  · exact absurd (hw' ▸ hw) (not_isCyclicallyReduced_append_append_invRev hc _)

/-- **Lyndon–Schützenberger, Corollary 4.2**, existence half, for cyclically reduced words: a
nonempty cyclically reduced word is a nonzero power of a word representing an element that is not
a proper power. This is `List.exists_eq_flatten_replicate_forall_ne_flatten_replicate`, since a
cyclically reduced word is primitive exactly when it represents a non-proper-power. -/
theorem IsCyclicallyReduced.exists_eq_flatten_replicate_not_isProperPower {w : List (α × Bool)}
    (hw : IsCyclicallyReduced w) (hw₀ : w ≠ []) : ∃ r : List (α × Bool), ∃ k : ℕ,
      k ≠ 0 ∧ w = (List.replicate k r).flatten ∧ ¬IsProperPower (mk r) := by
  obtain ⟨r, k, hk, rfl, hr⟩ := List.exists_eq_flatten_replicate_forall_ne_flatten_replicate hw₀
  refine ⟨r, k, hk, rfl, ?_⟩
  rw [(hw.of_flatten_replicate hk).isProperPower_mk_iff]
  exact fun ⟨u, l, hl, hu⟩ ↦ hr u l hl hu

end FreeGroup
