/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import TauCeti.Algebra.Algebra.CyclicQuotient
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

A valley word which descends and climbs the same number `s > 0` of rungs is closed. Rotating its
descent past its climb gives a peak word, which the relations turn back into a closed valley word
whose bottom is `s` rungs lower, or into zero. Hence every closed valley word of positive length
lies in the commutator submodule (`TauCeti.ladderValley_mem_commutatorSubmodule`). For the
preprojective algebra of type `A` this makes the cyclic quotient vanish in positive degrees.

Without the relation `d 0 * u 0 = 0` at the bottom rung, a descent after a climb from rung `0`
leaves the turn `d 0 * u 0` (`TauCeti.d_mul_ladderValley_zero_zero`). Its powers are, up to sign,
the words climbing from rung `0` and descending back, so on a ladder with no climb from some rung
`N` the turn is nilpotent (`TauCeti.pow_d_mul_u_eq_zero`). This is the situation at the end of an
arm of a branched graph, read from its branch node.

On such a finite ladder the turn and the closed valley words are also sums of commutators. The
power `(d r * u r) ^ j` rotates into `(u r * d r) ^ j`, which the relation at rung `r + 1` turns
into `± (d (r + 1) * u (r + 1)) ^ j`, so climbing to rung `N` shows that every positive power of
the bottom turn lies in the commutator submodule `[A, A]`
(`TauCeti.pow_d_mul_u_mem_commutatorSubmodule`). A closed valley word rotates into a closed valley
word with a lower bottom, and eventually into a power of the bottom turn, so it is also a sum of
commutators (`TauCeti.ladderValley_mem_commutatorSubmodule_of_u_eq_zero`). For the preprojective
algebra of a branched graph this controls the cyclic quotient along its arms.

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
* `TauCeti.ladderValley_mul_ladderValley_zero_eq_pow`: climbing `j` rungs from rung `0` and
  descending back is, up to sign, the `j`-th power of the turn at rung `0`.
* `TauCeti.pow_d_mul_u_eq_zero`: on a ladder with no climb from rung `N`, the turn at rung `0` has
  vanishing `N + 1`-st power.
* `TauCeti.ladderValley_mem_commutatorSubmodule`: under the ladder relations, a closed valley word
  of positive length is a sum of commutators.
* `TauCeti.pow_d_mul_u_mem_commutatorSubmodule` and
  `TauCeti.ladderValley_mem_commutatorSubmodule_of_u_eq_zero`: on such a ladder, the positive
  powers of the turn at rung `0` and the closed valley words of positive length are sums of
  commutators.

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the preprojective relations of a quiver.
* P. Etingof and C.-H. Eu, *Hochschild and cyclic homology of preprojective algebras of ADE
  quivers*, Mosc. Math. J. 7 (2007), https://arxiv.org/abs/math/0609006, for the vanishing of
  the positive-degree cyclic quotient of a Dynkin preprojective algebra.
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

/-- **Climbing from rung `0` and descending back is a power of the bottom turn.** If the turns at
every positive rung cancel, then climbing `j` rungs from rung `0` and descending back is, up to the
sign `(-1) ^ (j.choose 2)`, the `j`-th power of the turn `d 0 * u 0` at rung `0`. -/
theorem ladderValley_mul_ladderValley_zero_eq_pow
    (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0) (j : ℕ) :
    ladderValley u d 0 j 0 * ladderValley u d 0 0 j = (-1) ^ j.choose 2 * (d 0 * u 0) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hc : (j + 1).choose 2 = j + j.choose 2 :=
      (Nat.choose_succ_succ' j 1).trans (by rw [Nat.choose_one_right])
    -- The last descent leaves the turn at rung `0` after the shorter climb and descent.
    have hstep : ladderValley u d 0 (j + 1) 0 * ladderValley u d 0 0 (j + 1) =
        (-1) ^ j * (ladderValley u d 0 j 0 * ladderValley u d 0 0 j) * (d 0 * u 0) := by
      rw [← ladderValley_mul_d, zero_add, mul_assoc, d_mul_ladderValley_zero_zero hud,
        ← mul_assoc, ((Commute.neg_one_right _).pow_right j).eq]
      simp only [mul_assoc]
    rw [hstep, ih, hc, pow_add, pow_succ]
    simp only [mul_assoc]

/-- **The turn at the bottom of a finite ladder is nilpotent.** If the turns at every positive
rung cancel and there is no climb from rung `N`, then `(d 0 * u 0) ^ (N + 1) = 0`: the power
`(d 0 * u 0) ^ j` is, up to sign, the word climbing `j` rungs from rung `0` and descending back,
and no word climbs `N + 1` rungs. -/
theorem pow_d_mul_u_eq_zero (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0) {N : ℕ}
    (hN : u N = 0) : (d 0 * u 0) ^ (N + 1) = 0 := by
  have h := ladderValley_mul_ladderValley_zero_eq_pow hud (N + 1)
  rw [← u_mul_ladderValley, zero_add, hN, zero_mul, mul_zero, eq_comm] at h
  rcases neg_one_pow_eq_or A ((N + 1).choose 2) with hs | hs <;>
    simpa [hs] using h

section Commutator

variable (k : Type*) [Semiring k] [Module k A]

/-- **The powers of the bottom turn of a finite ladder are sums of commutators.** If the turns at
every positive rung cancel and there is no climb from rung `N`, then every positive power of the
turn `d 0 * u 0` lies in the commutator submodule `[A, A]`. Rotating `(d r * u r) ^ j` into
`(u r * d r) ^ j`, which is `(-1) ^ j (d (r + 1) * u (r + 1)) ^ j` by the relation at rung `r + 1`,
moves the power one rung up, and at rung `N` it vanishes. -/
theorem pow_d_mul_u_mem_commutatorSubmodule (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0)
    {N : ℕ} (hN : u N = 0) {j : ℕ} (hj : 0 < j) :
    (d 0 * u 0) ^ j ∈ commutatorSubmodule k A := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  -- Climbing from rung `N - i` to rung `N`, by induction on `i`.
  suffices h : ∀ i ≤ N, (d (N - i) * u (N - i)) ^ (j + 1) ∈ commutatorSubmodule k A by
    simpa using h N le_rfl
  intro i
  induction i with
  | zero => simp [hN]
  | succ i ih =>
    intro hi
    obtain ⟨r, hr, hr'⟩ : ∃ r, N - (i + 1) = r ∧ N - i = r + 1 := ⟨N - (i + 1), rfl, by omega⟩
    rw [hr]
    -- Rotating one factor `d r` to the end turns the power into one of `u r * d r`.
    have hdu : d r * (u r * (d r * u r) ^ j) = (d r * u r) ^ (j + 1) := by
      rw [← mul_assoc, ← pow_succ']
    have hud' :
        u r * (d r * u r) ^ j * d r = (-1) ^ (j + 1) * (d (r + 1) * u (r + 1)) ^ (j + 1) := by
      rw [mul_assoc, mul_pow_mul, ← mul_assoc, ← pow_succ', eq_neg_of_add_eq_zero_right (hud r),
        neg_pow]
    rw [← hdu, mul_mem_commutatorSubmodule_comm, hud']
    exact neg_one_pow_mul_mem_commutatorSubmodule (hr' ▸ ih (by omega)) (j + 1)

/-- **Closed valley words on a finite ladder are sums of commutators.** If the turns at every
positive rung cancel and there is no climb from rung `N`, then the valley word descending `s > 0`
rungs to rung `m` and climbing back lies in the commutator submodule `[A, A]`. Rotating its
descent past its climb gives, up to sign, a closed valley word whose bottom is `s` rungs lower;
once the bottom would pass below rung `0`, the rotated word is a closed valley word with bottom
`0`, which rotates into a power of the bottom turn. -/
theorem ladderValley_mem_commutatorSubmodule_of_u_eq_zero
    (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0) {N : ℕ} (hN : u N = 0) (m : ℕ) {s : ℕ}
    (hs : 0 < s) : ladderValley u d m s s ∈ commutatorSubmodule k A := by
  -- A closed valley with bottom `0` rotates into a power of the bottom turn.
  have hzero : ladderValley u d 0 s s ∈ commutatorSubmodule k A := by
    rw [← ladderValley_zero_mul_ladderValley, mul_mem_commutatorSubmodule_comm,
      ladderValley_mul_ladderValley_zero_eq_pow hud]
    exact neg_one_pow_mul_mem_commutatorSubmodule
      (pow_d_mul_u_mem_commutatorSubmodule k hud hN hs) (s.choose 2)
  induction m using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    rcases le_or_gt s m with hsm | hms
    · -- The rotated word is a closed valley word with bottom `m - s`.
      rw [← ladderValley_zero_mul_ladderValley, mul_mem_commutatorSubmodule_comm,
        ladderValley_mul_ladderValley hud rfl hsm, zero_add, add_zero]
      exact neg_one_pow_mul_mem_commutatorSubmodule (ih (m - s) (by omega) hs hzero) (s * s)
    · -- Rotating the last `m` steps of the descent gives the closed valley word with bottom `0`.
      -- Two descents concatenate: down to rung `m`, then on to rung `0`.
      have hsplit : ladderValley u d m (s - m) 0 * ladderValley u d s m 0 =
          ladderValley u d m s 0 := by
        rw [ladderValley_mul_ladderValley hud (by omega) (by omega)]
        simp only [mul_zero, pow_zero, one_mul]
        congr 1 <;> omega
      have hjoin : ladderValley u d 0 m s * ladderValley u d m (s - m) 0 =
          ladderValley u d 0 s s := by
        rw [ladderValley_mul_ladderValley hud (by omega) le_rfl]
        simp only [mul_zero, pow_zero, one_mul]
        congr 1 <;> omega
      -- The descent from rung `m` to rung `0`, rotated past the climb, crosses all `s` climbs.
      have hcross : ladderValley u d s m 0 * ladderValley u d m 0 s =
          (-1) ^ (m * s) * ladderValley u d 0 m s := by
        rw [ladderValley_mul_ladderValley hud (add_comm s m) le_rfl]
        simp
      have hAB : ladderValley u d m 0 s * ladderValley u d m (s - m) 0 * ladderValley u d s m 0 =
          ladderValley u d m s s := by
        rw [mul_assoc, hsplit, ladderValley_zero_mul_ladderValley]
      have hBA : ladderValley u d s m 0 * (ladderValley u d m 0 s * ladderValley u d m (s - m) 0) =
          (-1) ^ (m * s) * ladderValley u d 0 s s := by
        rw [← mul_assoc, hcross, mul_assoc, hjoin]
      rw [← hAB, mul_mem_commutatorSubmodule_comm, hBA]
      exact neg_one_pow_mul_mem_commutatorSubmodule hzero (m * s)

/-- **Closed valley words are sums of commutators.** If the turns at every rung cancel, including
the single turn `d 0 * u 0` at the bottom rung, then the valley word descending `s > 0` rungs to
rung `m` and climbing back lies in the commutator submodule `[A, A]`. -/
theorem ladderValley_mem_commutatorSubmodule (hud₀ : d 0 * u 0 = 0)
    (hud : ∀ w, d (w + 1) * u (w + 1) + u w * d w = 0) (m : ℕ) {s : ℕ} (hs : 0 < s) :
    ladderValley u d m s s ∈ commutatorSubmodule k A := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    -- The valley is its climb times its descent; the rotated word climbs first.
    rw [← ladderValley_zero_mul_ladderValley, mul_mem_commutatorSubmodule_comm]
    rcases lt_or_ge m s with hms | hsm
    · rw [ladderValley_mul_ladderValley_eq_zero hud₀ hud rfl hms]
      exact zero_mem _
    · rw [ladderValley_mul_ladderValley hud rfl hsm, zero_add, add_zero]
      exact neg_one_pow_mul_mem_commutatorSubmodule (ih (m - s) (by omega)) (s * s)

end Commutator

end Ring

end TauCeti
