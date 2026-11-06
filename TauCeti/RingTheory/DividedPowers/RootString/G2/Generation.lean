/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString.G2.Basic

/-!
# Simple divided powers generate the positive integral G₂ algebra

For normalized positive Chevalley root vectors `x, y, z, w, v, s` of respective roots
`α, β, α+β, 2α+β, 3α+β, 3α+2β`, the divided powers of `x` and `y` generate the
same subring as the divided powers of all six vectors. This recovers the nonsimple
root families integrally, without dividing by the structure constants two or three
in that subring.

The coefficient-one formula
`TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul`
is triangular for total root height. In `x⁽ᵐ⁾ y⁽ⁿ⁾`, isolate the pure-root term at
`(m,n) = (k,k), (2k,k), (3k,k), (3k,2k)` respectively. Every other factor has
strictly smaller height than the isolated term. A simultaneous induction therefore
recovers the four families without presupposing any of them integral.

## Main results

* `Subring.g2_dividedPower_mem_of_forall_dividedPower_mem`: a subring containing the two
  simple families contains all four nonsimple families.
* `TauCeti.Associative.G2.closure_rootDividedPowers_eq_closure_simpleRootDividedPowers`:
  equality of the two generated subrings.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TauCeti.Associative Finset

namespace TauCeti.Associative.G2

variable {A : Type*} [Semiring A] [Algebra ℚ A] {x y z w v s : A}

/-- The divided-power families of the two simple positive G₂ root vectors. -/
noncomputable def simpleRootDividedPowers (x y : A) : Set A :=
  Set.range (fun k => dividedPower k x) ∪ Set.range (fun k => dividedPower k y)

/-- Membership in the two simple-root divided-power families. -/
@[simp]
theorem mem_simpleRootDividedPowers_iff {a : A} :
    a ∈ simpleRootDividedPowers x y ↔
      (∃ k, dividedPower k x = a) ∨ ∃ k, dividedPower k y = a := by
  simp only [simpleRootDividedPowers, Set.mem_union, Set.mem_range]

/-- The six root divided-power families generating the positive integral G₂ algebra. -/
noncomputable def rootDividedPowers (x y z w v s : A) : Set A :=
  simpleRootDividedPowers x y ∪ Set.range (fun k => dividedPower k z) ∪
    Set.range (fun k => dividedPower k w) ∪ Set.range (fun k => dividedPower k v) ∪
    Set.range (fun k => dividedPower k s)

/-- Membership in the six root divided-power families. -/
@[simp]
theorem mem_rootDividedPowers_iff {a : A} :
    a ∈ rootDividedPowers x y z w v s ↔
      (∃ k, dividedPower k x = a) ∨ (∃ k, dividedPower k y = a) ∨
        (∃ k, dividedPower k z = a) ∨ (∃ k, dividedPower k w = a) ∨
          (∃ k, dividedPower k v = a) ∨ ∃ k, dividedPower k s = a := by
  simp only [rootDividedPowers, Set.mem_union, mem_simpleRootDividedPowers_iff,
    Set.mem_range, or_assoc]

end TauCeti.Associative.G2

namespace Subring

variable {A : Type*} [Ring A] [Algebra ℚ A] {x y z w v s : A}

-- Extract a single term of the G₂ formula once all other root factors are known to
-- be integral. The hypotheses refer to total root height, not the individual exponents.
private theorem g2_term_mem (S : Subring A)
    (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z)
    (hwv : Commute w v) (hzs : Commute z s) (hws : Commute w s) (hvs : Commute v s)
    (hx : ∀ k, dividedPower k x ∈ S) (hy : ∀ k, dividedPower k y ∈ S)
    (m n : ℕ) (p : ℕ × ℕ × ℕ × ℕ) (hp : p ∈ chainG2Index m n)
    (hz : ∀ k, 2 * k < m + n → dividedPower k z ∈ S)
    (hw : ∀ k, 3 * k < m + n → dividedPower k w ∈ S)
    (hv : ∀ k, 4 * k < m + n → dividedPower k v ∈ S)
    (hs : ∀ k, 5 * k < m + n → dividedPower k s ∈ S)
    (hlt : ∀ q ∈ chainG2Index m n, q ≠ p →
      2 * q.1 < m + n ∧ 3 * q.2.1 < m + n ∧
        4 * q.2.2.1 < m + n ∧ 5 * q.2.2.2 < m + n) :
    dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) y * dividedPower p.1 z *
      dividedPower p.2.1 w * dividedPower p.2.2.1 v * dividedPower p.2.2.2 s *
      dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) x ∈ S := by
  classical
  let f : (ℕ × ℕ × ℕ × ℕ) → A := fun q =>
    dividedPower (n - q.1 - q.2.1 - q.2.2.1 - 2 * q.2.2.2) y * dividedPower q.1 z *
      dividedPower q.2.1 w * dividedPower q.2.2.1 v * dividedPower q.2.2.2 s *
      dividedPower (m - q.1 - 2 * q.2.1 - 3 * q.2.2.1 - 3 * q.2.2.2) x
  have hsum : ∑ q ∈ chainG2Index m n, f q ∈ S := by
    rw [← dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul
      hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs]
    exact S.mul_mem (hx m) (hy n)
  have hrest : ∑ q ∈ (chainG2Index m n).erase p, f q ∈ S := by
    apply sum_mem
    intro q hq
    obtain ⟨hne, hq⟩ := mem_erase.mp hq
    obtain ⟨hb, hc, hd, he⟩ := hlt q hq hne
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (hy _)
      (hz _ hb)) (hw _ hc)) (hv _ hd)) (hs _ he)) (hx _)
  rw [← sum_erase_add _ _ hp] at hsum
  exact (S.add_mem_cancel_left hrest).mp hsum

/-- A subring containing the divided powers of the two simple root vectors of type G₂
contains the divided powers of all four nonsimple root vectors. The hypotheses use the
coefficient-one normalization of the G₂ straightening formula. -/
theorem g2_dividedPower_mem_of_forall_dividedPower_mem (S : Subring A)
    (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z)
    (hwv : Commute w v) (hzs : Commute z s) (hws : Commute w s) (hvs : Commute v s)
    (hx : ∀ k, dividedPower k x ∈ S) (hy : ∀ k, dividedPower k y ∈ S) (k : ℕ) :
    dividedPower k z ∈ S ∧ dividedPower k w ∈ S ∧
      dividedPower k v ∈ S ∧ dividedPower k s ∈ S := by
  -- Induct simultaneously on the heights 2k, 3k, 4k, 5k. Induction on k alone
  -- would not justify the other root families occurring in a straightening term.
  have hall (N : ℕ) :
      (∀ k, 2 * k = N → dividedPower k z ∈ S) ∧
      (∀ k, 3 * k = N → dividedPower k w ∈ S) ∧
      (∀ k, 4 * k = N → dividedPower k v ∈ S) ∧
      (∀ k, 5 * k = N → dividedPower k s ∈ S) := by
    induction N using Nat.strong_induction_on with
    | ind N ih =>
      have extract (m n : ℕ) (hmn : m + n = N) (p : ℕ × ℕ × ℕ × ℕ)
          (hp : p ∈ chainG2Index m n)
          (hlt : ∀ q ∈ chainG2Index m n, q ≠ p →
            2 * q.1 < m + n ∧ 3 * q.2.1 < m + n ∧
              4 * q.2.2.1 < m + n ∧ 5 * q.2.2.2 < m + n) :=
        g2_term_mem S hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs hx hy m n p hp
          (fun j hj => (ih (2 * j) (hmn ▸ hj)).1 j rfl)
          (fun j hj => (ih (3 * j) (hmn ▸ hj)).2.1 j rfl)
          (fun j hj => (ih (4 * j) (hmn ▸ hj)).2.2.1 j rfl)
          (fun j hj => (ih (5 * j) (hmn ▸ hj)).2.2.2 j rfl) hlt
      -- Each pure-root term has coefficient one; the two index inequalities
      -- bound every factor in any other term strictly below the current height.
      refine ⟨fun j hj => ?hz, fun j hj => ?hw, fun j hj => ?hv, fun j hj => ?hs⟩
      case' hz j hj =>
        have h := extract j j (by omega) (j, 0, 0, 0) (by simp) ?_
        · simpa using h
      case' hw j hj =>
        have h := extract (2 * j) j (by omega) (0, j, 0, 0) (by simp) ?_
        · simpa using h
      case' hv j hj =>
        have h := extract (3 * j) j (by omega) (0, 0, j, 0) (by simp) ?_
        · simpa using h
      case' hs j hj =>
        have h := extract (3 * j) (2 * j) (by omega) (0, 0, 0, j) (by simp) ?_
        · simpa using h
      all_goals
        rintro ⟨b, c, d, e⟩ hq hne
        simp only [mem_chainG2Index] at hq
        simp only [ne_eq, Prod.mk.injEq, not_and] at hne
        dsimp only at hq ⊢
        omega
  exact ⟨(hall (2 * k)).1 k rfl, (hall (3 * k)).2.1 k rfl,
    (hall (4 * k)).2.2.1 k rfl, (hall (5 * k)).2.2.2 k rfl⟩

end Subring

namespace TauCeti.Associative.G2

open Subring

variable {A : Type*} [Ring A] [Algebra ℚ A] {x y z w v s : A}

/-- The positive integral G₂ algebra is generated by the divided powers of its two simple
root vectors; adjoining the four nonsimple divided-power families does not enlarge it. -/
theorem closure_rootDividedPowers_eq_closure_simpleRootDividedPowers
    (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z)
    (hwv : Commute w v) (hzs : Commute z s) (hws : Commute w s) (hvs : Commute v s) :
    closure (G2.rootDividedPowers x y z w v s) =
      closure (G2.simpleRootDividedPowers x y) := by
  let S := closure (G2.simpleRootDividedPowers x y)
  have hx k : dividedPower k x ∈ S :=
    subset_closure (G2.mem_simpleRootDividedPowers_iff.mpr (Or.inl ⟨k, rfl⟩))
  have hy k : dividedPower k y ∈ S :=
    subset_closure (G2.mem_simpleRootDividedPowers_iff.mpr (Or.inr ⟨k, rfl⟩))
  have h := S.g2_dividedPower_mem_of_forall_dividedPower_mem
    hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs hx hy
  apply le_antisymm
  · apply closure_le.mpr
    intro a ha
    rcases G2.mem_rootDividedPowers_iff.mp ha with
      ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact hx k
    · exact hy k
    · exact (h k).1
    · exact (h k).2.1
    · exact (h k).2.2.1
    · exact (h k).2.2.2
  · apply closure_mono
    intro a ha
    simp only [G2.mem_simpleRootDividedPowers_iff] at ha
    simp only [G2.mem_rootDividedPowers_iff]
    tauto

end TauCeti.Associative.G2
