/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Commute

/-!
# Valley words on a ladder

Let `u d : ℕ → A` be two families in a ring, read as the steps of a ladder with rungs `0, 1, 2, …`:
`u w` climbs from rung `w` to rung `w + 1` and `d w` descends from rung `w + 1` to rung `w`, and a
product is read from right to left, so its rightmost factor is the first step. The **valley word**

```text
ladderValley u d m s r = u (m + r - 1) ⋯ u (m + 1) u m · d m d (m + 1) ⋯ d (m + s - 1)
```

descends `s` rungs to rung `m` and then climbs `r` rungs.

Suppose that at every rung the two turns cancel,

```text
d 0 * u 0 = 0    and    d (w + 1) * u (w + 1) + u w * d w = 0,
```

which are the relations of the signless preprojective algebra of the half-line
`0 — 1 — 2 — ⋯`. Then a descent following a valley word pushes the bottom of the valley one rung
down, at the cost of a sign (`TauCeti.d_mul_ladderValley`); if the valley already touches rung `0`
and then climbs, the product vanishes (`TauCeti.d_mul_ladderValley_zero_eq_zero`). Since a climb
following a valley word is again a valley word (`TauCeti.u_mul_ladderValley`), these moves reduce
every product of composable steps to a valley word up to sign, or to zero. A valley word from rung
`a` to rung `b` has length at most `a + b`, so longer products vanish; this bounds the length of
the nonzero paths in the preprojective algebra of type `A`. For two composable valley words,
`TauCeti.ladderValley_mul_ladderValley` gives their product with the exact crossing sign;
`TauCeti.ladderValley_mul_ladderValley_eq_zero` handles a negative formal bottom.

Without the relation `d 0 * u 0 = 0` at the bottom rung, a descent after a climb from rung `0`
leaves the turn `d 0 * u 0` (`TauCeti.d_mul_ladderValley_zero_zero`). Its powers are, up to sign,
the words climbing from rung `0` and descending back, so on a ladder with no climb from some rung
`N` the turn is nilpotent (`TauCeti.pow_d_mul_u_eq_zero`). This is the situation at the end of an
arm of a branched graph, read from its branch node.

## Main definitions

* `TauCeti.ladderValley`: the valley word descending `s` rungs to rung `m` and climbing `r` rungs.

## Main results

* `TauCeti.u_mul_ladderValley`, `TauCeti.ladderValley_mul_d`: extending a valley word by a final
  climb or an initial descent.
* `TauCeti.d_mul_ladderValley`: under the ladder relations, a final descent moves the valley one
  rung down.
* `TauCeti.d_mul_ladderValley_zero_eq_zero`: a final descent after a valley at rung `0` vanishes.
* `TauCeti.d_mul_ladderValley_zero_zero`: without the bottom relation, a descent after a climb from
  rung `0` leaves the turn at rung `0`.
* `TauCeti.pow_d_mul_u_eq_zero`: on a ladder with no climb from rung `N`, the turn at rung `0` has
  vanishing `N + 1`-st power.

## References

See W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
problem*, Section 1, for the preprojective relations of a quiver.
-/

public section

namespace TauCeti

variable {A : Type*}

section Monoid

variable [Monoid A] (u d : ℕ → A)

/-- The **valley word** `u (m + r - 1) ⋯ u m · d m ⋯ d (m + s - 1)`: starting from rung `m + s`, it
descends `s` rungs to rung `m` and then climbs `r` rungs to rung `m + r`. The first step is the
rightmost factor. -/
def ladderValley (m s r : ℕ) : A :=
  ((List.range r).map fun i => u (m + i)).reverse.prod *
    ((List.range s).map fun i => d (m + i)).prod

/-- The empty valley word is `1`. -/
@[simp]
theorem ladderValley_zero_zero (m : ℕ) : ladderValley u d m 0 0 = 1 := by
  simp [ladderValley]

/-- A final climb extends a valley word. -/
@[simp]
theorem u_mul_ladderValley (m s r : ℕ) :
    u (m + r) * ladderValley u d m s r = ladderValley u d m s (r + 1) := by
  simp [ladderValley, List.range_succ, mul_assoc]

/-- An initial descent extends a valley word. -/
@[simp]
theorem ladderValley_mul_d (m s r : ℕ) :
    ladderValley u d m s r * d (m + s) = ladderValley u d m (s + 1) r := by
  simp [ladderValley, List.range_succ, mul_assoc]

/-- A descent onto the bottom of a word without climbs lengthens the descent. -/
@[simp]
theorem d_mul_ladderValley_succ_zero (m s : ℕ) :
    d m * ladderValley u d (m + 1) s 0 = ladderValley u d m (s + 1) 0 := by
  simp [ladderValley, List.range_succ_eq_map, Function.comp_def, add_assoc, add_comm 1]

/-- An initial climb from rung `m` extends a climb from rung `m + 1`. -/
theorem ladderValley_succ_zero_mul_u (m r : ℕ) :
    ladderValley u d (m + 1) 0 r * u m = ladderValley u d m 0 (r + 1) := by
  simp [ladderValley, List.range_succ_eq_map, Function.comp_def, add_assoc, add_comm 1]

/-- A valley word is its descent followed by its climb. -/
theorem ladderValley_zero_mul_ladderValley (m s r : ℕ) :
    ladderValley u d m 0 r * ladderValley u d m s 0 = ladderValley u d m s r := by
  simp [ladderValley]

/-- Two consecutive climbs concatenate, including the descent preceding the first climb. -/
@[simp]
theorem ladderValley_climb_mul (m s r t : ℕ) :
    ladderValley u d (m + r) 0 t * ladderValley u d m s r =
      ladderValley u d m s (r + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← u_mul_ladderValley, mul_assoc, ih]
    simpa only [Nat.add_assoc] using u_mul_ladderValley u d m s (r + t)

end Monoid

section Ring

variable [Ring A] {u d : ℕ → A}

/-- **A final descent moves the valley down.** If the turns at every positive rung cancel, then
descending one rung after the valley word with bottom `m + 1` gives, up to the sign `(-1) ^ r`,
the valley word with bottom `m`, one more descent and the same number `r` of climbs. -/
@[simp]
theorem d_mul_ladderValley (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0) (m s r : ℕ) :
    d (m + r) * ladderValley u d (m + 1) s r = (-1) ^ r * ladderValley u d m (s + 1) r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← u_mul_ladderValley, ← u_mul_ladderValley, ← mul_assoc, add_right_comm, ← add_assoc,
      eq_neg_of_add_eq_zero_left (hud (m + r)), neg_mul, mul_assoc, ih]
    rcases neg_one_pow_eq_or A r with h | h <;> simp [h, pow_succ]

/-- **A valley at the bottom rung cannot be followed by a descent.** If the turns at every rung
cancel, then descending after a valley word which reaches rung `0` and climbs back up vanishes. -/
@[simp]
theorem d_mul_ladderValley_zero_eq_zero (hud₀ : d 0 * u 0 = 0)
    (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0) (s r : ℕ) :
    d r * ladderValley u d 0 s (r + 1) = 0 := by
  induction r with
  | zero => rw [← u_mul_ladderValley, ← mul_assoc, zero_add, hud₀, zero_mul]
  | succ r ih =>
    rw [← u_mul_ladderValley, ← mul_assoc, zero_add,
      eq_neg_of_add_eq_zero_left (hud r), neg_mul, mul_assoc, ih, mul_zero, neg_zero]

/-- Commuting a descent of `s` steps past a climb of `r` steps costs the sign `(-1)^(s*r)`.
The bottom of the resulting valley is `m`. No bottom-rung relation is needed. -/
@[simp]
private theorem ladderValley_descent_mul (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0)
    (m s t r : ℕ) :
    ladderValley u d (m + r) s 0 * ladderValley u d (m + s) t r =
      (-1) ^ (s * r) * ladderValley u d m (t + s) r := by
  induction s generalizing m with
  | zero => simp
  | succ s ih =>
    have hleft : m + r + 1 = (m + 1) + r := by omega
    have hright : m + (s + 1) = (m + 1) + s := by omega
    rw [← d_mul_ladderValley_succ_zero, hleft, hright, mul_assoc, ih]
    rw [← mul_assoc, ((Commute.neg_one_right _).pow_right (s * r)).eq, mul_assoc,
      d_mul_ladderValley hud, ← mul_assoc, ← pow_add]
    congr 2
    simp [Nat.add_mul]

/-- The product of two composable valley words, when its bottom is nonnegative.
Each descent in the later word crosses every climb in the earlier word. -/
@[simp]
theorem ladderValley_mul_ladderValley (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0)
    {m l s t r q : ℕ} (hcomp : m + s = l + q) (hbottom : s ≤ l) :
    ladderValley u d m s r * ladderValley u d l t q =
      (-1) ^ (s * q) * ladderValley u d (l - s) (t + s) (q + r) := by
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hbottom
  have hl : l = b + s := by omega
  have hm : m = b + q := by omega
  rw [hl, Nat.add_sub_cancel, hm, ← ladderValley_zero_mul_ladderValley u d (b + q) s r,
    mul_assoc, ladderValley_descent_mul hud]
  rw [← mul_assoc, ((Commute.neg_one_right _).pow_right (s * q)).eq, mul_assoc,
    ladderValley_climb_mul]

/-- A composable descent which pushes a valley below rung zero vanishes. -/
private theorem ladderValley_descent_mul_eq_zero (hud₀ : d 0 * u 0 = 0)
    (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0)
    {m l s t r : ℕ} (hcomp : m + s = l + r) (hbottom : l < s) :
    ladderValley u d m s 0 * ladderValley u d l t r = 0 := by
  induction s generalizing m l t r with
  | zero => omega
  | succ s ih =>
    rw [← d_mul_ladderValley_succ_zero, mul_assoc]
    by_cases hl : l < s
    · rw [ih (by omega) hl, mul_zero]
    · have hl' : l = s := by omega
      have hr : r = m + 1 := by omega
      have hcomp' : m + 1 + s = s + r := by omega
      rw [hl', ladderValley_mul_ladderValley hud hcomp' le_rfl, Nat.sub_self, hr,
        ← mul_assoc, ((Commute.neg_one_right _).pow_right (s * (m + 1))).eq, mul_assoc,
        d_mul_ladderValley_zero_eq_zero hud₀ hud, mul_zero]

/-- Two composable valley words multiply to zero if their formal bottom is negative. -/
@[simp]
theorem ladderValley_mul_ladderValley_eq_zero (hud₀ : d 0 * u 0 = 0)
    (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0)
    {m l s t r q : ℕ} (hcomp : m + s = l + q) (hbottom : l < s) :
    ladderValley u d m s r * ladderValley u d l t q = 0 := by
  rw [← ladderValley_zero_mul_ladderValley u d m s r, mul_assoc,
    ladderValley_descent_mul_eq_zero hud₀ hud hcomp hbottom, mul_zero]

/-- **A descent after a climb from rung `0` leaves a turn at rung `0`.** If the turns at every
positive rung cancel, then climbing `r + 1` rungs from rung `0` and descending one rung gives, up
to the sign `(-1) ^ r`, the turn `d 0 * u 0` at rung `0` followed by a climb of `r` rungs. -/
theorem d_mul_ladderValley_zero_zero (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0) (r : ℕ) :
    d r * ladderValley u d 0 0 (r + 1) = (-1) ^ r * (ladderValley u d 0 0 r * (d 0 * u 0)) := by
  have h := d_mul_ladderValley hud 0 0 r
  rw [zero_add, zero_add, ← ladderValley_mul_d, zero_add] at h
  rw [← ladderValley_succ_zero_mul_u, ← mul_assoc, h, mul_assoc, mul_assoc]

/-- **The turn at the bottom of a finite ladder is nilpotent.** If the turns at every positive
rung cancel and there is no climb from rung `N`, then `(d 0 * u 0) ^ (N + 1) = 0`: the power
`(d 0 * u 0) ^ j` is, up to sign, the word climbing `j` rungs from rung `0` and descending back,
and no word climbs `N + 1` rungs. -/
theorem pow_d_mul_u_eq_zero (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0) {N : ℕ}
    (hN : u N = 0) : (d 0 * u 0) ^ (N + 1) = 0 := by
  -- The climb of `j` rungs from rung `0` and the descent back.
  let P : ℕ → A := fun j => ladderValley u d 0 j 0 * ladderValley u d 0 0 j
  have hstep (j : ℕ) : P j * (d 0 * u 0) = (-1) ^ j * P (j + 1) := by
    have hP : P (j + 1) = (-1) ^ j * (P j * (d 0 * u 0)) := by
      simp only [P]
      rw [← ladderValley_mul_d, zero_add, mul_assoc, d_mul_ladderValley_zero_zero hud,
        ← mul_assoc, ((Commute.neg_one_right _).pow_right j).eq]
      simp only [mul_assoc]
    rw [hP, ← mul_assoc ((-1 : A) ^ j), ← (Commute.refl (-1 : A)).mul_pow, neg_one_mul, neg_neg,
      one_pow, one_mul]
  have hpow (j : ℕ) : ∃ e : ℕ, (d 0 * u 0) ^ j = (-1) ^ e * P j := by
    induction j with
    | zero => exact ⟨0, by simp [P]⟩
    | succ j ih =>
      obtain ⟨e, he⟩ := ih
      exact ⟨e + j, by rw [pow_succ, he, mul_assoc, hstep, ← mul_assoc, ← pow_add]⟩
  obtain ⟨e, he⟩ := hpow (N + 1)
  rw [he]
  simp only [P]
  rw [← u_mul_ladderValley, zero_add, hN, zero_mul, mul_zero, mul_zero]

end Ring

end TauCeti
