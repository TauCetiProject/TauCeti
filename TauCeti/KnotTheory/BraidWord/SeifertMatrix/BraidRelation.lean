/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.AppendCons
public import TauCeti.KnotTheory.BraidWord.ArtinEquivalence
public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Basic

/-!
# The braid relation and the Seifert matrix of a closed braid

The Seifert matrix `TauCeti.BraidWord.seifertMatrix w` of a braid word `w` is read off the canonical
Seifert surface of its closure: one disc for each strand position, one half-twisted band for each
letter, and a basis of loops `(t, t')` running up the band at position `t` and down the next band
`t'` on the same level. This file shows that the braid relation
`σᵢ^ε σᵢ₊₁^ε σᵢ^ε = σᵢ₊₁^ε σᵢ^ε σᵢ₊₁^ε` changes this matrix only by a unimodular congruence and a
relabelling of the loops. Together with the exchange of letters on distant levels, which only
relabels the loops, this covers every Artin relation, so Artin-equivalent braid words have Seifert
matrices with the same Alexander polynomial and the same Tristram–Levine signatures. Free
cancellation of a letter against its inverse, the other move relating words of the same braid,
changes the size of the matrix and is not treated here.

Write `p` for the position of the first of the three letters. On the left the letters at
`p, p + 1, p + 2` lie on the levels `i, i + 1, i`, on the right on the levels `i + 1, i, i + 1`, and
every other letter is unchanged. A loop of the left word is matched with the loop of the right word
obtained by exchanging `p + 1` and `p + 2` in its first position and `p` and `p + 1` in its second
position. So the middle loop `(p, p + 2)` on level `i` is matched with the middle loop `(p, p + 2)`
on level `i + 1`, a loop ending at `p` or `p + 1` with the loop ending at the other one, a loop
starting at `p + 1` or `p + 2` with the loop starting at the other one, and every other loop with
itself. In the matching basis the right Seifert matrix is `P V Pᵀ` for the left one `V`, where the
row of `P` at a loop `c` is `c` plus a multiple `t c` of the middle loop `m`: `t m = -2`, so that
`m` itself goes to `-m`; for `ε = 1`, `t c = 1` for the loops starting at `p + 2` or ending at
`p + 1`; for `ε = -1`, `t c = 1` for the loops ending at `p` or starting at `p + 1`; and `t c = 0`
otherwise. The matrix `P` has determinant `-1`.

The entries of the two Seifert matrices are compared directly from the formula
`TauCeti.BraidWord.seifertMatrix_apply`. A loop never runs past the three letters on the level `i`
or `i + 1`, and the middle loop meets no loop that avoids the three letters, so all the
comparisons reduce to linear arithmetic on positions.

## Main results

* `TauCeti.BraidWord.exists_seifertMatrix_append_cons_cons_cons_braid`: the braid relation changes
  the Seifert matrix by a unimodular congruence followed by a relabelling of the loops.
* `TauCeti.BraidWord.exists_seifertMatrix_of_artinStep`: the same for every Artin relation step.
* `TauCeti.BraidWord.alexander_seifertMatrix_eq_of_artinEquiv`,
  `TauCeti.BraidWord.tristramLevineSignature_seifertMatrix_eq_of_artinEquiv`: Artin-equivalent
  braid words have Seifert matrices with the same Alexander polynomial and the same
  Tristram–Levine signatures.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 2
  (Seifert's algorithm) and Chapter 6 (Seifert matrices and their change under isotopy of the
  surface).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 1 (the Artin presentation of the braid group).
-/

public section

namespace TauCeti

namespace BraidWord

open KnotTheory

open scoped Matrix

variable {n : ℕ}

section BraidRelation

variable (u v : BraidWord n) (a b : Fin (n - 1) × ℤˣ)

private theorem levelAt_append_cons_cons_cons_of_ne (a' b' c c' : Fin (n - 1) × ℤˣ) {k : ℕ}
    (h₀ : k ≠ u.length) (h₁ : k ≠ u.length + 1) (h₂ : k ≠ u.length + 2) :
    (u ++ a :: b :: c :: v).levelAt k = (u ++ a' :: b' :: c' :: v).levelAt k := by
  rw [levelAt_def, levelAt_def,
    List.getElem?_append_cons_cons_cons_of_ne u v _ _ _ _ _ _ h₀ h₁ h₂]

private theorem signAt_append_cons_cons_cons_of_ne (a' b' c c' : Fin (n - 1) × ℤˣ) {k : ℕ}
    (h₀ : k ≠ u.length) (h₁ : k ≠ u.length + 1) (h₂ : k ≠ u.length + 2) :
    (u ++ a :: b :: c :: v).signAt k = (u ++ a' :: b' :: c' :: v).signAt k := by
  rw [signAt_def, signAt_def,
    List.getElem?_append_cons_cons_cons_of_ne u v _ _ _ _ _ _ h₀ h₁ h₂]

variable (c : Fin (n - 1) × ℤˣ)

private theorem levelAt_append_cons_cons_cons_length :
    (u ++ a :: b :: c :: v).levelAt u.length = some (a.1 : ℕ) := by
  simp

private theorem levelAt_append_cons_cons_cons_length_add_one :
    (u ++ a :: b :: c :: v).levelAt (u.length + 1) = some (b.1 : ℕ) := by
  simp

private theorem levelAt_append_cons_cons_cons_length_add_two :
    (u ++ a :: b :: c :: v).levelAt (u.length + 2) = some (c.1 : ℕ) := by
  simp

/-- The relabelling of loops under the braid relation: the first position of a loop is moved by
exchanging `p + 1` and `p + 2`, its second position by exchanging `p` and `p + 1`. -/
private def braidSwap (p : ℕ) (c : ℕ × ℕ) : ℕ × ℕ :=
  (Equiv.swap (p + 1) (p + 2) c.1, Equiv.swap p (p + 1) c.2)

private theorem braidSwap_braidSwap (p : ℕ) (c : ℕ × ℕ) : braidSwap p (braidSwap p c) = c := by
  simp [braidSwap]

/-- `braidSwap` carries the loops of `u ++ a :: b :: a :: v` to loops of `u ++ b :: a :: b :: v`,
for letters `a` and `b` on different levels. -/
private theorem isSeifertLoop_braidSwap (hab : (a.1 : ℕ) ≠ b.1) {c : ℕ × ℕ}
    (hc : (u ++ a :: b :: a :: v).IsSeifertLoop c) :
    (u ++ b :: a :: b :: v).IsSeifertLoop (braidSwap u.length c) := by
  obtain ⟨c₁, c₂⟩ := c
  obtain ⟨h12, h2, hl, hb⟩ := (isSeifertLoop_iff _).1 hc
  have hout : ∀ k, k ≠ u.length → k ≠ u.length + 1 → k ≠ u.length + 2 →
      (u ++ b :: a :: b :: v).levelAt k = (u ++ a :: b :: a :: v).levelAt k :=
    fun k h₀ h₁ h₂ ↦ levelAt_append_cons_cons_cons_of_ne u v _ _ _ _ _ _ h₀ h₁ h₂
  have hlen : (u ++ b :: a :: b :: v).length = (u ++ a :: b :: a :: v).length := by simp
  have hA := levelAt_append_cons_cons_cons_length u v a b a
  have hB := levelAt_append_cons_cons_cons_length_add_one u v a b a
  have hA' := levelAt_append_cons_cons_cons_length_add_two u v a b a
  have hB₀ := levelAt_append_cons_cons_cons_length u v b a b
  have hA₀ := levelAt_append_cons_cons_cons_length_add_one u v b a b
  have hB₀' := levelAt_append_cons_cons_cons_length_add_two u v b a b
  have hlt := (u ++ a :: b :: a :: v).levelAt_ne_none_iff (k := c₁)
  rw [isSeifertLoop_iff]
  simp only [braidSwap, Equiv.swap_apply_def] at hl hb h12 h2 ⊢
  -- case analysis on the positions of the loop and of a letter between its ends
  grind

variable {u v} in
private theorem mem_seifertLoops_braidSwap (hab : (a.1 : ℕ) ≠ b.1) {c : ℕ × ℕ} :
    braidSwap u.length c ∈ (u ++ b :: a :: b :: v).seifertLoops ↔
      c ∈ (u ++ a :: b :: a :: v).seifertLoops := by
  simp only [mem_seifertLoops]
  refine ⟨fun h ↦ ?_, isSeifertLoop_braidSwap u v a b hab⟩
  simpa [braidSwap_braidSwap] using isSeifertLoop_braidSwap u v b a hab.symm h

/-- The loops of the canonical Seifert surfaces on the two sides of the braid relation, matched
by `braidSwap`. -/
private def braidLoopsEquiv (hab : (a.1 : ℕ) ≠ b.1) :
    (u ++ a :: b :: a :: v).seifertLoops ≃ (u ++ b :: a :: b :: v).seifertLoops where
  toFun c := ⟨braidSwap u.length c, (mem_seifertLoops_braidSwap a b hab).2 c.2⟩
  invFun c := ⟨braidSwap u.length c, by
    rw [← mem_seifertLoops_braidSwap a b hab, braidSwap_braidSwap]; exact c.2⟩
  left_inv c := Subtype.ext (braidSwap_braidSwap _ _)
  right_inv c := Subtype.ext (braidSwap_braidSwap _ _)

/-- How a loop of `u ++ a :: b :: a :: v` sits relative to the three letters after `u`, at
positions `p, p + 1, p + 2`: the middle loop `(p, p + 2)` is the only one starting at `p` or
ending at `p + 2`, a loop starting or ending at `p + 1` lies on the level of `b`, one starting at
`p + 2` or ending at `p` lies on the level of `a`, and no loop runs past the three letters on the
level of `a` or of `b`. -/
private theorem IsSeifertLoop.exists_levelAt_of_braid (hab : (a.1 : ℕ) ≠ b.1) {c : ℕ × ℕ}
    (hc : (u ++ a :: b :: a :: v).IsSeifertLoop c) :
    ∃ l, (u ++ a :: b :: a :: v).levelAt c.1 = some l ∧
      (u ++ a :: b :: a :: v).levelAt c.2 = some l ∧ c.1 < c.2 ∧
      c.2 < (u ++ a :: b :: a :: v).length ∧
      (c.1 = u.length ↔ c.2 = u.length + 2) ∧
      (c.1 = u.length → l = a.1) ∧
      (c.1 = u.length + 1 → u.length + 2 < c.2 ∧ l = b.1) ∧
      (c.1 = u.length + 2 → u.length + 2 < c.2 ∧ l = a.1) ∧
      (c.2 = u.length → l = a.1) ∧
      (c.2 = u.length + 1 → c.1 < u.length ∧ l = b.1) ∧
      (c.1 < u.length → u.length + 2 < c.2 → l ≠ a.1 ∧ l ≠ b.1) := by
  obtain ⟨c₁, c₂⟩ := c
  obtain ⟨h12, h2, hl, hb⟩ := (isSeifertLoop_iff _).1 hc
  have hA := levelAt_append_cons_cons_cons_length u v a b a
  have hB := levelAt_append_cons_cons_cons_length_add_one u v a b a
  have hA' := levelAt_append_cons_cons_cons_length_add_two u v a b a
  obtain ⟨l, hl'⟩ := Option.ne_none_iff_exists'.1
    ((levelAt_ne_none_iff (u ++ a :: b :: a :: v)).2 (h12.trans h2))
  refine ⟨l, hl', ?_⟩
  simp only at hl hb h12 h2 hl' ⊢
  grind

variable {u v} in
/-- Exchanging `p + 1` and `p + 2` in a position of the left word gives a position of the same
level in the right word, except at `p`, which moves from level `a` to level `b`. -/
private theorem levelAt_swap_braid {k l : ℕ} (h : (u ++ a :: b :: a :: v).levelAt k = some l) :
    (u ++ b :: a :: b :: v).levelAt (Equiv.swap (u.length + 1) (u.length + 2) k) =
      some (if k = u.length then (b.1 : ℕ) else l) := by
  by_cases h₀ : k = u.length
  · subst h₀
    simp [Equiv.swap_apply_of_ne_of_ne]
  by_cases h₁ : k = u.length + 1
  · subst h₁
    simpa using h
  by_cases h₂ : k = u.length + 2
  · subst h₂
    simpa using h
  simp only [Equiv.swap_apply_of_ne_of_ne h₁ h₂, h₀, ↓reduceIte, ← h]
  exact levelAt_append_cons_cons_cons_of_ne u v _ _ _ _ _ _ h₀ h₁ h₂

variable {i j : Fin (n - 1)} (ε : ℤˣ)

variable {u} in
/-- All three letters following `u` have the sign `ε`. -/
private theorem signAt_append_cons_cons_cons_of_le (i₁ i₂ i₃ : Fin (n - 1)) {k : ℕ}
    (h₀ : u.length ≤ k) (h₂ : k ≤ u.length + 2) :
    (u ++ (i₁, ε) :: (i₂, ε) :: (i₃, ε) :: v).signAt k = ε := by
  obtain rfl | rfl | rfl : k = u.length ∨ k = u.length + 1 ∨ k = u.length + 2 := by omega
  all_goals simp

variable {u} in
/-- Exchanging two of the three positions `p, p + 1, p + 2` does not change the sign of a letter:
all three letters of the braid relation have the sign `ε`. -/
private theorem signAt_swap_braid {x y : ℕ} (hx : u.length ≤ x ∧ x ≤ u.length + 2)
    (hy : u.length ≤ y ∧ y ≤ u.length + 2) (k : ℕ) :
    (u ++ (j, ε) :: (i, ε) :: (j, ε) :: v).signAt (Equiv.swap x y k) =
      (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).signAt k := by
  by_cases hk : u.length ≤ k ∧ k ≤ u.length + 2
  · have hσ : u.length ≤ Equiv.swap x y k ∧ Equiv.swap x y k ≤ u.length + 2 := by
      rw [Equiv.swap_apply_def]
      split_ifs <;> omega
    rw [signAt_append_cons_cons_cons_of_le v ε _ _ _ hσ.1 hσ.2,
      signAt_append_cons_cons_cons_of_le v ε _ _ _ hk.1 hk.2]
  · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega),
      signAt_append_cons_cons_cons_of_ne u v _ _ _ _ _ _ (by omega) (by omega) (by omega)]

/-- The coefficient `t c` of the middle loop `(p, p + 2)` in the image of the loop `c` under the
change of basis for the braid relation. -/
private def braidCoeff (p : ℕ) (ε : ℤˣ) (c : ℕ × ℕ) : ℤ :=
  if c = (p, p + 2) then -2
  else if ((ε : ℤ) = 1 ∧ (c.1 = p + 2 ∨ c.2 = p + 1)) ∨ ((ε : ℤ) = -1 ∧ (c.2 = p ∨ c.1 = p + 1))
    then 1 else 0

/-- The middle loop `(p, p + 2)` of `u ++ σᵢ^ε σᵢ₊₁^ε σᵢ^ε ++ v`, through the two letters on the
level `i`. -/
private def middleLoop (hij : (j : ℕ) = i + 1) :
    (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops :=
  ⟨(u.length, u.length + 2), by
    rw [mem_seifertLoops, isSeifertLoop_iff]
    refine ⟨by omega, by simp, by simp, fun k hk hk' ↦ ?_⟩
    obtain rfl : k = u.length + 1 := by omega
    simp [hij]⟩

/-- The entries of the two Seifert matrices across the braid relation: with `m` the middle loop
and `t = braidCoeff`, the entry of the right matrix at the matched loops of `c` and `d` is
`V(c + t c • m, d + t d • m)` for the left matrix `V`. -/
private theorem seifertMatrix_braid_entry (hij : (j : ℕ) = i + 1)
    (c d : (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops) :
    (u ++ (j, ε) :: (i, ε) :: (j, ε) :: v).seifertMatrix
        (braidLoopsEquiv u v _ _ (by simp [hij]) c) (braidLoopsEquiv u v _ _ (by simp [hij]) d) =
      (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertMatrix c d +
        braidCoeff u.length ε c *
          (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertMatrix (middleLoop u v ε hij) d +
        braidCoeff u.length ε d *
          (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertMatrix c (middleLoop u v ε hij) +
        braidCoeff u.length ε c * braidCoeff u.length ε d *
          (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertMatrix
            (middleLoop u v ε hij) (middleLoop u v ε hij) := by
  have hij' : ((i, ε).1 : ℕ) ≠ ((j, ε) : Fin (n - 1) × ℤˣ).1 := by simp [hij]
  obtain ⟨⟨c₁, c₂⟩, hc⟩ := c
  obtain ⟨⟨d₁, d₂⟩, hd⟩ := d
  obtain ⟨lc, hlc, hlc₂, hc⟩ :=
    IsSeifertLoop.exists_levelAt_of_braid u v _ _ hij' ((mem_seifertLoops _).1 hc)
  obtain ⟨ld, hld, hld₂, hd⟩ :=
    IsSeifertLoop.exists_levelAt_of_braid u v _ _ hij' ((mem_seifertLoops _).1 hd)
  simp only at hlc hld hlc₂ hld₂ hc hd
  -- a position carries a single level
  have hcd : (c₁ = d₁ ∨ c₁ = d₂ ∨ c₂ = d₁ ∨ c₂ = d₂) → lc = ld := by
    rintro (h | h | h | h) <;> subst h <;> simp_all
  -- the signs: `±1` everywhere, and `ε` on the three letters
  have hsign : ∀ k < (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).length,
      (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).signAt k = 1 ∨
        (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).signAt k = -1 := fun k hk ↦ by
    rw [signAt_of_lt _ hk]
    rcases Int.units_eq_one_or (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v)[k].2 with h | h <;> simp [h]
  have hsc₁ := hsign c₁ (by omega)
  have hsc₂ := hsign c₂ (by omega)
  have hε : (ε : ℤ) = 1 ∨ (ε : ℤ) = -1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hb₁ : u.length ≤ c₁ → c₁ ≤ u.length + 2 →
      (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).signAt c₁ = ε :=
    signAt_append_cons_cons_cons_of_le v ε _ _ _
  have hb₂ : u.length ≤ c₂ → c₂ ≤ u.length + 2 →
      (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).signAt c₂ = ε :=
    signAt_append_cons_cons_cons_of_le v ε _ _ _
  -- read every entry off `seifertMatrix_apply`, in terms of the levels and signs of the left word
  simp only [seifertMatrix_apply, braidLoopsEquiv, middleLoop, Equiv.coe_fn_mk, braidSwap,
    braidCoeff, Subtype.mk.injEq, Prod.mk.injEq, Equiv.apply_eq_iff_eq,
    levelAt_swap_braid _ _ hlc, levelAt_swap_braid _ _ hld,
    signAt_swap_braid v ε (x := u.length + 1) (y := u.length + 2) ⟨by omega, by omega⟩
      ⟨by omega, le_rfl⟩,
    signAt_swap_braid v ε (x := u.length) (y := u.length + 1) ⟨le_rfl, by omega⟩
      ⟨by omega, by omega⟩,
    hlc, hld, levelAt_append_cons_cons_cons_length,
    signAt_append_cons_cons_cons_of_le v ε _ _ _ (le_refl u.length) (Nat.le_add_right _ 2),
    signAt_append_cons_cons_cons_of_le v ε _ _ _ (Nat.le_add_right u.length 2) le_rfl,
    Option.some_inj, Option.map_some] at hc hd ⊢
  simp only [Equiv.swap_apply_def] at hc hd ⊢
  generalize (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).signAt c₁ = s₁ at *
  generalize (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).signAt c₂ = s₂ at *
  clear hsign hlc hld hlc₂ hld₂
  -- what is left is linear arithmetic on the positions, levels and signs
  grind (splits := 40)

variable {ε} in
/-- **The braid relation is a unimodular change of basis of the Seifert matrix.** Replacing the
three letters `σᵢ^ε σᵢ₊₁^ε σᵢ^ε` of a braid word by `σᵢ₊₁^ε σᵢ^ε σᵢ₊₁^ε` changes the Seifert
matrix of the canonical Seifert surface only by a congruence `P V Pᵀ` with `P` invertible over
`ℤ`, followed by a relabelling of the loops. For the three letters at the positions
`p, p + 1, p + 2`, the middle loop `(p, p + 2)` on level `i` becomes minus the middle loop on level
`i + 1`, and a loop with one end among the three letters keeps its other end, possibly picking up
the middle loop. -/
theorem exists_seifertMatrix_append_cons_cons_cons_braid (hij : (j : ℕ) = i + 1) :
    ∃ (ι : (u ++ (j, ε) :: (i, ε) :: (j, ε) :: v).seifertLoops ≃
        (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops)
      (P : Matrix (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops
        (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops ℤ),
      IsUnit P.det ∧ (u ++ (j, ε) :: (i, ε) :: (j, ε) :: v).seifertMatrix =
        (P * (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertMatrix * Pᵀ).submatrix ι ι := by
  set κ := braidLoopsEquiv u v (i, ε) (j, ε) (by simp [hij])
  set m := middleLoop u v ε hij
  set t := fun c : (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops ↦
    braidCoeff u.length ε c
  -- the loop `c` goes to the loop `κ c` plus `t c` times the middle loop `m`
  set P : Matrix (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops
      (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops ℤ :=
    Matrix.of fun c e ↦ (if c = e then 1 else 0) + if e = m then t c else 0 with hP
  refine ⟨κ.symm, P, ?_, ?_⟩
  · -- `Pᵀ` is the identity with the row of `m` replaced by `eₘ + t`, and `t m = -2`
    set g := fun k ↦ (1 : Matrix (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops
      (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops ℤ) m k + t k
    have hsum : ∑ k, g k • (1 : Matrix (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops
        (u ++ (i, ε) :: (j, ε) :: (i, ε) :: v).seifertLoops ℤ) k = g := by
      ext e
      simp [Matrix.one_apply]
    have hPt : Pᵀ = (1 : Matrix _ _ ℤ).updateRow m (∑ k, g k • (1 : Matrix _ _ ℤ) k) := by
      rw [hsum]
      ext c e
      by_cases hc : c = m
      · subst hc
        simp [hP, g, Matrix.one_apply, eq_comm]
      · simp [hP, Matrix.one_apply, hc, eq_comm]
    have htm : t m = -2 := by simp [t, m, middleLoop, braidCoeff]
    rw [← Matrix.det_transpose, hPt, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul,
      mul_one]
    simp [g, htm]
  · ext r r'
    obtain ⟨c, rfl⟩ := κ.surjective r
    obtain ⟨d, rfl⟩ := κ.surjective r'
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.mul_apply,
      Matrix.transpose_apply, hP, Matrix.of_apply, add_mul, mul_add, ite_mul, one_mul, zero_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [seifertMatrix_braid_entry u v ε hij c d]
    ring

end BraidRelation

/-! ### Artin relations -/

section Artin

variable {w w' : BraidWord n}

/-- **An Artin relation step is a unimodular change of basis of the Seifert matrix.** Exchanging
two letters on distant levels only relabels the loops of the canonical Seifert surface, and the
braid relation changes the Seifert matrix by a congruence `P V Pᵀ` with `P` invertible over `ℤ`,
followed by a relabelling of the loops. -/
theorem exists_seifertMatrix_of_artinStep (h : ArtinStep w w') :
    ∃ (ι : w'.seifertLoops ≃ w.seifertLoops) (P : Matrix w.seifertLoops w.seifertLoops ℤ),
      IsUnit P.det ∧ w'.seifertMatrix = (P * w.seifertMatrix * Pᵀ).submatrix ι ι := by
  cases h with
  | commute u v h =>
    obtain ⟨ι, hι⟩ := exists_seifertMatrix_append_cons_cons_comm u v h
    exact ⟨ι, 1, by simp, by simpa using hι⟩
  | braid u v ε hij => exact exists_seifertMatrix_append_cons_cons_cons_braid u v hij

/-- An Artin relation step keeps the Alexander polynomial of the Seifert matrix. -/
theorem alexander_seifertMatrix_eq_of_artinStep (h : ArtinStep w w') :
    alexander w.seifertMatrix = alexander w'.seifertMatrix := by
  obtain ⟨ι, P, hP, h⟩ := exists_seifertMatrix_of_artinStep h
  rw [h, Matrix.alexander_submatrix_equiv_self, alexander_congruence_of_det_sq_eq_one]
  rcases Int.isUnit_iff.1 hP with hP | hP <;> simp [hP]

/-- An Artin relation step keeps the Tristram–Levine signatures of the Seifert matrix. -/
theorem tristramLevineSignature_seifertMatrix_eq_of_artinStep (h : ArtinStep w w') (ω : ℂ) :
    tristramLevineSignature (w.seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature (w'.seifertMatrix.map ((↑) : ℤ → ℝ)) ω := by
  obtain ⟨ι, P, hP, h⟩ := exists_seifertMatrix_of_artinStep h
  have hPReal : IsUnit (P.map (Int.castRingHom ℝ)).det :=
    RingHom.map_det (Int.castRingHom ℝ) P ▸ hP.map (Int.castRingHom ℝ)
  have hmap : ∀ M : Matrix w.seifertLoops w.seifertLoops ℤ,
      M.map ((↑) : ℤ → ℝ) = M.map (Int.castRingHom ℝ) := fun M ↦ by simp
  rw [h, ← Matrix.submatrix_map, ← ι.symm_symm, tristramLevineSignature_submatrix_equiv_self,
    hmap, hmap, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    tristramLevineSignature_congr hPReal]

/-- **Artin-equivalent braid words have Seifert matrices with the same Alexander polynomial.** -/
theorem alexander_seifertMatrix_eq_of_artinEquiv (h : ArtinEquiv w w') :
    alexander w.seifertMatrix = alexander w'.seifertMatrix := by
  refine ArtinEquiv.induction
    (motive := fun w w' ↦ alexander w.seifertMatrix = alexander w'.seifertMatrix)
    alexander_seifertMatrix_eq_of_artinStep (fun _ ↦ rfl) (fun _ ih ↦ ih.symm)
    (fun _ _ ih₁ ih₂ ↦ ih₁.trans ih₂) h

/-- **Artin-equivalent braid words have Seifert matrices with the same Tristram–Levine
signatures.** -/
theorem tristramLevineSignature_seifertMatrix_eq_of_artinEquiv (h : ArtinEquiv w w') (ω : ℂ) :
    tristramLevineSignature (w.seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature (w'.seifertMatrix.map ((↑) : ℤ → ℝ)) ω := by
  refine ArtinEquiv.induction (motive := fun w w' ↦
      tristramLevineSignature (w.seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
        tristramLevineSignature (w'.seifertMatrix.map ((↑) : ℤ → ℝ)) ω)
    (fun h ↦ tristramLevineSignature_seifertMatrix_eq_of_artinStep h ω) (fun _ ↦ rfl)
    (fun _ ih ↦ ih.symm) (fun _ _ ih₁ ih₂ ↦ ih₁.trans ih₂) h

end Artin

end BraidWord

end TauCeti
