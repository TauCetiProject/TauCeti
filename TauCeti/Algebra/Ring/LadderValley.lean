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
the nonzero paths in the preprojective algebra of type `A`.

## Main definitions

* `TauCeti.ladderValley`: the valley word descending `s` rungs to rung `m` and climbing `r` rungs.

## Main results

* `TauCeti.u_mul_ladderValley`, `TauCeti.ladderValley_mul_d`: extending a valley word by a final
  climb or an initial descent.
* `TauCeti.d_mul_ladderValley`: under the ladder relations, a final descent moves the valley one
  rung down.
* `TauCeti.d_mul_ladderValley_zero_eq_zero`: a final descent after a valley at rung `0` vanishes.

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

end Monoid

section Ring

variable [Ring A] {u d : ℕ → A}

private theorem neg_mul_neg_one_pow (a b : A) (r : ℕ) :
    -(a * ((-1) ^ r * b)) = (-1) ^ (r + 1) * (a * b) := by
  rw [← mul_assoc, ((Commute.neg_one_right a).pow_right r).eq]
  simp [pow_succ, mul_assoc]

/-- **A final descent moves the valley down.** If the turns at every positive rung cancel, then
descending one rung after the valley word with bottom `m + 1` gives, up to the sign `(-1) ^ r`,
the valley word with bottom `m`, one more descent and the same number `r` of climbs. -/
@[simp]
theorem d_mul_ladderValley (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0) (m s r : ℕ) :
    d (m + r) * ladderValley u d (m + 1) s r = (-1) ^ r * ladderValley u d m (s + 1) r := by
  induction r with
  | zero => simp [d_mul_ladderValley_succ_zero]
  | succ r ih =>
    have hturn : d (m + r + 1) * u (m + r + 1) = -(u (m + r) * d (m + r)) :=
      eq_neg_of_add_eq_zero_left (hud (m + r))
    have hindex : m + 1 + r = m + r + 1 := by omega
    calc
      d (m + (r + 1)) * ladderValley u d (m + 1) s (r + 1) =
          -(u (m + r) * (d (m + r) * ladderValley u d (m + 1) s r)) := by
            rw [← u_mul_ladderValley, ← mul_assoc, ← add_assoc, hindex, hturn,
              neg_mul, mul_assoc]
      _ = -(u (m + r) * ((-1) ^ r * ladderValley u d m (s + 1) r)) := by rw [ih]
      _ = (-1) ^ (r + 1) * ladderValley u d m (s + 1) (r + 1) := by
        rw [neg_mul_neg_one_pow, u_mul_ladderValley]

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

end Ring

end TauCeti
