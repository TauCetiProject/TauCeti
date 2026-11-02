/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString.G2.Basic

/-!
# Simple divided powers generate the positive type-G₂ integral algebra

For the positive Chevalley root vectors `x, y, z, w, v, s`, with `x` short and `y` long,
the divided powers of the four nonsimple root vectors belong to every subring containing
the divided powers of `x` and `y`. Thus the simple-root and all-root integral algebras agree.
In particular no inversion of the bad primes two and three is needed.

`Subring.dividedPower_mem_of_g2` recovers the four families simultaneously. In each degree,
coefficient-one straightening first recovers `z`, then `w`, then `v`. Finally the class-two
pair `y, v` recovers `s`. This last step avoids requiring higher-degree divided powers of
`z` or `w` to recover `s`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TauCeti.Associative Finset

namespace Subring

variable {A : Type*} [Ring A] [Algebra ℚ A] {x y z w v s : A}

/-- In a positive type-G₂ root configuration, every nonsimple-root divided power belongs to
any subring containing the two simple-root divided-power families. The bracket constants
are integral; neither two nor three is required to be invertible in the subring. -/
theorem dividedPower_mem_of_g2 (S : Subring A)
    (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hyv : y * v = v * y + s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z)
    (hwv : Commute w v) (hzs : Commute z s) (hws : Commute w s)
    (hvs : Commute v s) (hys : Commute y s)
    (hx : ∀ n, dividedPower n x ∈ S) (hy : ∀ n, dividedPower n y ∈ S) (n : ℕ) :
    dividedPower n z ∈ S ∧ dividedPower n w ∈ S ∧
      dividedPower n v ∈ S ∧ dividedPower n s ∈ S := by
  classical
  let term (m n : ℕ) (p : ℕ × ℕ × ℕ × ℕ) :=
    dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) y * dividedPower p.1 z *
      dividedPower p.2.1 w * dividedPower p.2.2.1 v * dividedPower p.2.2.2 s *
      dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) x
  -- Each distinguished monomial has coefficient one, so subtracting the other summands
  -- recovers it inside the subring, not merely inside its rational span.
  have extract (m n : ℕ) (p : ℕ × ℕ × ℕ × ℕ) (hp : p ∈ chainG2Index m n)
      (hrest : ∀ q ∈ (chainG2Index m n).erase p, term m n q ∈ S) : term m n p ∈ S := by
    have hsum : ∑ q ∈ chainG2Index m n, term m n q ∈ S := by
      rw [← dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul
        hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs]
      exact S.mul_mem (hx m) (hy n)
    have heq : term m n p = (∑ q ∈ chainG2Index m n, term m n q) -
        ∑ q ∈ (chainG2Index m n).erase p, term m n q := by
      rw [← Finset.sum_erase_add _ _ hp]
      abel
    rw [heq]
    exact S.sub_mem hsum (S.sum_mem hrest)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn]
    have hpositive : 0 < n := Nat.pos_of_ne_zero hn
    have hz : dividedPower n z ∈ S := by
      have hp : (n, 0, 0, 0) ∈ chainG2Index n n := by simp
      have h := extract n n (n, 0, 0, 0) hp (by
        rintro ⟨b, c, d, e⟩ hq
        obtain ⟨hne, hq⟩ := Finset.mem_erase.mp hq
        have hbounds := mem_chainG2Index.mp hq
        dsimp only at hbounds
        have hb : b < n := by
          simp only [ne_eq, Prod.mk.injEq] at hne
          omega
        have hc : c < n := by omega
        have hd : d < n := by omega
        have he : e < n := by omega
        exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem
          (hy _) (ih b hb).1) (ih c hc).2.1) (ih d hd).2.2.1) (ih e he).2.2.2) (hx _))
      simpa [term] using h
    have hw : dividedPower n w ∈ S := by
      have hp : (0, n, 0, 0) ∈ chainG2Index (2 * n) n := by simp
      have h := extract (2 * n) n (0, n, 0, 0) hp (by
        rintro ⟨b, c, d, e⟩ hq
        obtain ⟨hne, hq⟩ := Finset.mem_erase.mp hq
        have hbounds := mem_chainG2Index.mp hq
        dsimp only at hbounds
        have hb : b ≤ n := by omega
        have hc : c < n := by
          simp only [ne_eq, Prod.mk.injEq] at hne
          omega
        have hd : d < n := by omega
        have he : e < n := by omega
        have hbmem : dividedPower b z ∈ S :=
          if h : b = n then by simpa [h] using hz else (ih b (by omega)).1
        exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem
          (hy _) hbmem) (ih c hc).2.1) (ih d hd).2.2.1) (ih e he).2.2.2) (hx _))
      simpa [term] using h
    have hv : dividedPower n v ∈ S := by
      have hp : (0, 0, n, 0) ∈ chainG2Index (3 * n) n := by simp
      have h := extract (3 * n) n (0, 0, n, 0) hp (by
        rintro ⟨b, c, d, e⟩ hq
        obtain ⟨hne, hq⟩ := Finset.mem_erase.mp hq
        have hbounds := mem_chainG2Index.mp hq
        dsimp only at hbounds
        have hb : b ≤ n := by omega
        have hc : c ≤ n := by omega
        have hd : d < n := by
          simp only [ne_eq, Prod.mk.injEq] at hne
          omega
        have he : e < n := by omega
        have hbmem : dividedPower b z ∈ S :=
          if h : b = n then by simpa [h] using hz else (ih b (by omega)).1
        have hcmem : dividedPower c w ∈ S :=
          if h : c = n then by simpa [h] using hw else (ih c (by omega)).2.1
        exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem
          (hy _) hbmem) hcmem) (ih d hd).2.2.1) (ih e he).2.2.2) (hx _))
      simpa [term] using h
    -- The highest root is recovered from the long-root A₂ pair, rather than from the
    -- G₂ sum: the latter would involve `z` and `w` at degrees larger than `n`.
    have hs : dividedPower n s ∈ S := by
      have hsum : ∑ k ∈ range (n + 1),
          dividedPower (n - k) v * dividedPower k s * dividedPower (n - k) y ∈ S := by
        have h := S.mul_mem (hy n) hv
        rw [dividedPower_mul_dividedPower_of_commutator_eq hyv hys hvs n n] at h
        simpa only [min_self] using h
      have hrest : ∑ k ∈ (range (n + 1)).erase n,
          dividedPower (n - k) v * dividedPower k s * dividedPower (n - k) y ∈ S := by
        apply S.sum_mem
        intro k hk
        obtain ⟨hkne, hk⟩ := Finset.mem_erase.mp hk
        have hkn : k < n := by have := Finset.mem_range.mp hk; omega
        have hv' : dividedPower (n - k) v ∈ S :=
          if h : n - k = n then by simpa only [h] using hv
          else (ih (n - k) (by omega)).2.2.1
        exact S.mul_mem (S.mul_mem hv' (ih k hkn).2.2.2) (hy _)
      have heq := Finset.sum_erase_add
        (s := range (n + 1))
        (fun k => dividedPower (n - k) v * dividedPower k s * dividedPower (n - k) y)
        (by simp : n ∈ range (n + 1))
      have h := S.sub_mem hsum hrest
      rw [← heq] at h
      simpa using h
    exact ⟨hz, hw, hv, hs⟩

end Subring

namespace TauCeti.Associative

variable {A : Type*} [Ring A] [Algebra ℚ A] {x y z w v s : A}

/-- The positive type-G₂ integral algebra generated by all six root divided-power families
is already generated by the two simple-root families. -/
theorem closure_dividedPowers_pair_eq_of_g2
    (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hyv : y * v = v * y + s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z)
    (hwv : Commute w v) (hzs : Commute z s) (hws : Commute w s)
    (hvs : Commute v s) (hys : Commute y s) :
    Subring.closure (Set.range (fun n => dividedPower n x) ∪
      Set.range (fun n => dividedPower n y)) =
    Subring.closure (Set.range (fun n => dividedPower n x) ∪
      Set.range (fun n => dividedPower n y) ∪ Set.range (fun n => dividedPower n z) ∪
      Set.range (fun n => dividedPower n w) ∪ Set.range (fun n => dividedPower n v) ∪
      Set.range (fun n => dividedPower n s)) := by
  apply le_antisymm
  · apply Subring.closure_mono
    intro a ha
    exact Or.inl (Or.inl (Or.inl (Or.inl ha)))
  · let S := Subring.closure (Set.range (fun n => dividedPower n x) ∪
        Set.range (fun n => dividedPower n y))
    have hx n : dividedPower n x ∈ S := Subring.subset_closure (.inl ⟨n, rfl⟩)
    have hy n : dividedPower n y ∈ S := Subring.subset_closure (.inr ⟨n, rfl⟩)
    have h n := S.dividedPower_mem_of_g2 hxy hxz hxw hwz hyv hxv hxs hyz hwv hzs hws
      hvs hys hx hy n
    apply Subring.closure_le.mpr
    rintro a (((((ha | ha) | ha) | ha) | ha) | ha)
    · obtain ⟨n, rfl⟩ := ha
      exact hx n
    · obtain ⟨n, rfl⟩ := ha
      exact hy n
    · obtain ⟨n, rfl⟩ := ha
      exact (h n).1
    · obtain ⟨n, rfl⟩ := ha
      exact (h n).2.1
    · obtain ⟨n, rfl⟩ := ha
      exact (h n).2.2.1
    · obtain ⟨n, rfl⟩ := ha
      exact (h n).2.2.2

end TauCeti.Associative
