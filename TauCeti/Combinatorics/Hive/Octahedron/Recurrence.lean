/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Combinatorics.Hive.Octahedron.Gluing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The bounded octahedron recurrence and section-to-section state transitions

For `1 ≤ n`, Henriques–Kamnitzer's bounded modified octahedron recurrence evolves functions on
`[0, n]² × ℝ` and on the discrete space-time parity lattice `Lₙ = SpaceTimePoint n`:

* in the interior `0 < x, y < n`,
  `f(x, y, t + 1) = max(f(x + 1, y, t) + f(x - 1, y, t), f(x, y + 1, t) + f(x, y - 1, t))`
  `- f(x, y, t - 1)`;
* along the horizontal walls `y ∈ {0, n}` (`0 < x < n`),
  `f(x, y, t + 1) = f(x + 1, y, t) + f(x - 1, y, t) - f(x, y, t - 1)`;
* along the vertical walls `x ∈ {0, n}` (`0 < y < n`),
  `f(x, y, t + 1) = f(x, y + 1, t) + f(x, y - 1, t) - f(x, y, t - 1)`;
* at each of the four corners `(0, 0), (0, n), (n, 0), (n, n)`,
  `f(x, y, t + 1)` subtracts `f(x, y, t - 1)` from the sum of its two inward grid neighbours.

This file develops the recurrence and its associator restriction in four steps:

1. **Unified two-branch spatial operator** (`branchNeighbors`, `branchSum`, `spatialSup`): all four
   spatial regimes are expressed by two grid-adjacent neighbour pairs (`Bool`), which coincide on
   walls and corners so `u ⊔ u = u`.
2. **Involutivity, continuous/discrete recurrence, and chirality check** (`octahedronRule`,
   `SatisfiesRealTimeRecurrence`, `SatisfiesRecurrence`, `not_isRhombusConcave_readOutputLeft_min`):
   the interior update `e ↦ (a + c) ⊔ (b + d) - e` is an involution in `e` so time reversal
   `t ↦ -t` inverts the recurrence; replacing `⊔` by `⊓` is also an involution in `e`, but fails to
   preserve hive rhombus concavity at `n = 2`.
3. **Finite dependency recursion and section transitions** (`evolveFuture`, `evolveFromSection`,
   `solutionEquivSection`, `sectionTransition`): initial data on any section `τ : Section n`
   determines a unique global solution on `Lₙ` (and uniquely determines values on any finite region
   `{τ₁ ≤ t ≤ τ₂}`), yielding bijections `sectionTransition hn τ₁ τ₂` compatible with lattice-group
   homomorphisms (`ℤ → ℚ → ℝ`) and nonnegative scaling.
4. **Associator transition and boundary preservation** (`associatorTransition`,
   `boundary_associatorTransition`): every dependency of an associator point strictly above `S`
   stays in `Aₙ` and uses the interior rule, wall values lie on `S ∩ S'` and remain fixed, all four
   exterior boundaries are preserved, and `n = 0` is the identity on the unique one-point hive.

Unit-cell excavation schedules and native piecewise-affineness (`TauCeti.IsPiecewiseAffineOn`) are
developed in `TauCeti.Combinatorics.Hive.Octahedron.Excavation`.

## References

* A. Henriques and J. Kamnitzer, *The octahedron recurrence and $\mathfrak{gl}_n$ crystals*,
  Adv. Math. **206** (2006), 211–249, §3, eq. (5).
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §5.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive.Octahedron

/-! ### Unified two-branch spatial neighbour sums for the bounded recurrence -/

section SpatialBranches

variable {n : ℕ}

/-- The two grid-adjacent spatial neighbours of `(x, y) ∈ [0, n]²` selected by branch `b : Bool`
in Henriques–Kamnitzer's bounded recurrence (`1 ≤ n`). In the interior `(0, n)²`, `true` selects
horizontal neighbours `(x ± 1, y)` and `false` selects vertical neighbours `(x, y ± 1)`; on walls
and corners both `Bool` branches return the unique pair of boundary/inward neighbours. -/
def branchNeighbors (hn : 1 ≤ n) (b : Bool) (x y : Fin (n + 1)) :
    (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)) :=
  if _hx0 : x.val = 0 then
    if _hy0 : y.val = 0 then
      ((⟨1, by omega⟩, 0), (0, ⟨1, by omega⟩))
    else if _hyn : y.val = n then
      ((⟨1, by omega⟩, Fin.last n), (0, ⟨n - 1, by omega⟩))
    else
      have := y.isLt
      ((0, ⟨y.val + 1, by omega⟩), (0, ⟨y.val - 1, by omega⟩))
  else if _hxn : x.val = n then
    if _hy0 : y.val = 0 then
      ((⟨n - 1, by omega⟩, 0), (Fin.last n, ⟨1, by omega⟩))
    else if _hyn : y.val = n then
      ((⟨n - 1, by omega⟩, Fin.last n), (Fin.last n, ⟨n - 1, by omega⟩))
    else
      have := y.isLt
      ((Fin.last n, ⟨y.val + 1, by omega⟩), (Fin.last n, ⟨y.val - 1, by omega⟩))
  else
    have := x.isLt
    if _hyw : y.val = 0 ∨ y.val = n then
      ((⟨x.val + 1, by omega⟩, y), (⟨x.val - 1, by omega⟩, y))
    else
      have := y.isLt
      if b then
        ((⟨x.val + 1, by omega⟩, y), (⟨x.val - 1, by omega⟩, y))
      else
        ((x, ⟨y.val + 1, by omega⟩), (x, ⟨y.val - 1, by omega⟩))

/-- Every neighbour returned by `branchNeighbors` is grid-adjacent to `(x, y)`. -/
theorem gridAdj_branchNeighbors (hn : 1 ≤ n) (b : Bool) (x y : Fin (n + 1)) :
    GridAdj x y (branchNeighbors hn b x y).1.1 (branchNeighbors hn b x y).1.2 ∧
      GridAdj x y (branchNeighbors hn b x y).2.1 (branchNeighbors hn b x y).2.2 := by
  have := x.isLt; have := y.isLt
  unfold branchNeighbors
  split_ifs <;> cases b <;> simp only [gridAdj_def, Fin.val_zero, Fin.val_last] <;> omega

/-- Sum of `g` at the two spatial neighbours of `(x, y)` in branch `b`. -/
def branchSum {R : Type*} [Add R] (hn : 1 ≤ n) (b : Bool)
    (g : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) : R :=
  g (branchNeighbors hn b x y).1.1 (branchNeighbors hn b x y).1.2 +
    g (branchNeighbors hn b x y).2.1 (branchNeighbors hn b x y).2.2

theorem branchSum_apply {R : Type*} [Add R] (hn : 1 ≤ n) (b : Bool)
    (g : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    branchSum hn b g x y =
      g (branchNeighbors hn b x y).1.1 (branchNeighbors hn b x y).1.2 +
        g (branchNeighbors hn b x y).2.1 (branchNeighbors hn b x y).2.2 := by
  unfold branchSum; rfl

/-- Spatial supremum in Henriques–Kamnitzer's bounded recurrence: maximum of the two opposite
neighbour sums in the interior, and the unique wall/corner neighbour sum on the boundary. -/
def spatialSup {R : Type*} [Add R] [SemilatticeSup R] (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) : R :=
  branchSum hn true g x y ⊔ branchSum hn false g x y

theorem spatialSup_def {R : Type*} [Add R] [SemilatticeSup R] (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    spatialSup hn g x y = branchSum hn true g x y ⊔ branchSum hn false g x y := by
  unfold spatialSup; rfl

theorem branchNeighbors_of_interior (hn : 1 ≤ n) (b : Bool) {x y : Fin (n + 1)}
    (hx0 : 0 < x.val) (hxn : x.val < n) (hy0 : 0 < y.val) (hyn : y.val < n) :
    branchNeighbors hn b x y =
      if b then ((⟨x.val + 1, by omega⟩, y), (⟨x.val - 1, by omega⟩, y))
      else ((x, ⟨y.val + 1, by omega⟩), (x, ⟨y.val - 1, by omega⟩)) := by
  rw [branchNeighbors, dite_eq_right_of_eq_false (eq_false (by omega)),
    dite_eq_right_of_eq_false (eq_false (by omega)),
    dite_eq_right_of_eq_false (eq_false (by omega))]

theorem branchNeighbors_of_horizontal_wall (hn : 1 ≤ n) (b : Bool) {x y : Fin (n + 1)}
    (hx0 : 0 < x.val) (hxn : x.val < n) (hyw : y.val = 0 ∨ y.val = n) :
    branchNeighbors hn b x y = ((⟨x.val + 1, by omega⟩, y), (⟨x.val - 1, by omega⟩, y)) := by
  rw [branchNeighbors, dite_eq_right_of_eq_false (eq_false (by omega)),
    dite_eq_right_of_eq_false (eq_false (by omega)),
    dite_eq_left_of_eq_true (eq_true hyw)]

theorem branchNeighbors_of_wall_x_zero (hn : 1 ≤ n) (b : Bool) {y : Fin (n + 1)}
    (hy0 : 0 < y.val) (hyn : y.val < n) :
    branchNeighbors hn b 0 y =
      ((0, ⟨y.val + 1, by omega⟩), (0, ⟨y.val - 1, by omega⟩)) := by
  rw [branchNeighbors, dite_eq_left_of_eq_true (eq_true (Fin.val_zero (n + 1))),
    dite_eq_right_of_eq_false (eq_false (by omega)),
    dite_eq_right_of_eq_false (eq_false (by omega))]

theorem branchNeighbors_of_wall_x_last (hn : 1 ≤ n) (b : Bool) {y : Fin (n + 1)}
    (hy0 : 0 < y.val) (hyn : y.val < n) :
    branchNeighbors hn b (Fin.last n) y =
      ((Fin.last n, ⟨y.val + 1, by omega⟩), (Fin.last n, ⟨y.val - 1, by omega⟩)) := by
  rw [branchNeighbors,
    dite_eq_right_of_eq_false (eq_false (by rw [Fin.val_last]; omega)),
    dite_eq_left_of_eq_true (eq_true (Fin.val_last n)),
    dite_eq_right_of_eq_false (eq_false (by omega)),
    dite_eq_right_of_eq_false (eq_false (by omega))]

theorem branchNeighbors_corner_zero_zero (hn : 1 ≤ n) (b : Bool) :
    branchNeighbors hn b 0 0 = ((⟨1, by omega⟩, 0), (0, ⟨1, by omega⟩)) := by
  rw [branchNeighbors, dite_eq_left_of_eq_true (eq_true (Fin.val_zero (n + 1))),
    dite_eq_left_of_eq_true (eq_true (Fin.val_zero (n + 1)))]

theorem branchNeighbors_corner_zero_last (hn : 1 ≤ n) (b : Bool) :
    branchNeighbors hn b 0 (Fin.last n) =
      ((⟨1, by omega⟩, Fin.last n), (0, ⟨n - 1, by omega⟩)) := by
  rw [branchNeighbors, dite_eq_left_of_eq_true (eq_true (Fin.val_zero (n + 1))),
    dite_eq_right_of_eq_false (eq_false (by rw [Fin.val_last]; omega)),
    dite_eq_left_of_eq_true (eq_true (Fin.val_last n))]

theorem branchNeighbors_corner_last_zero (hn : 1 ≤ n) (b : Bool) :
    branchNeighbors hn b (Fin.last n) 0 =
      ((⟨n - 1, by omega⟩, 0), (Fin.last n, ⟨1, by omega⟩)) := by
  rw [branchNeighbors,
    dite_eq_right_of_eq_false (eq_false (by rw [Fin.val_last]; omega)),
    dite_eq_left_of_eq_true (eq_true (Fin.val_last n)),
    dite_eq_left_of_eq_true (eq_true (Fin.val_zero (n + 1)))]

theorem branchNeighbors_corner_last_last (hn : 1 ≤ n) (b : Bool) :
    branchNeighbors hn b (Fin.last n) (Fin.last n) =
      ((⟨n - 1, by omega⟩, Fin.last n), (Fin.last n, ⟨n - 1, by omega⟩)) := by
  rw [branchNeighbors,
    dite_eq_right_of_eq_false (eq_false (by rw [Fin.val_last]; omega)),
    dite_eq_left_of_eq_true (eq_true (Fin.val_last n)),
    dite_eq_right_of_eq_false (eq_false (by rw [Fin.val_last]; omega)),
    dite_eq_left_of_eq_true (eq_true (Fin.val_last n))]

/-- In the interior `(0, n)²`, `spatialSup` takes the maximum of horizontal and vertical
opposite-neighbour sums. -/
theorem spatialSup_of_interior {R : Type*} [Add R] [SemilatticeSup R] (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → R) {x y : Fin (n + 1)}
    (hx0 : 0 < x.val) (hxn : x.val < n) (hy0 : 0 < y.val) (hyn : y.val < n) :
    spatialSup hn g x y =
      (g ⟨x.val + 1, by omega⟩ y + g ⟨x.val - 1, by omega⟩ y) ⊔
        (g x ⟨y.val + 1, by omega⟩ + g x ⟨y.val - 1, by omega⟩) := by
  unfold spatialSup branchSum
  rw [branchNeighbors_of_interior hn true hx0 hxn hy0 hyn,
    branchNeighbors_of_interior hn false hx0 hxn hy0 hyn]
  simp

/-- Along the horizontal walls `y = 0` or `y = n` (`0 < x < n`), `spatialSup` uses only
`g(x + 1, y) + g(x - 1, y)`. -/
theorem spatialSup_of_horizontal_wall {R : Type*} [Add R] [SemilatticeSup R] (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → R) {x y : Fin (n + 1)}
    (hx0 : 0 < x.val) (hxn : x.val < n) (hyw : y.val = 0 ∨ y.val = n) :
    spatialSup hn g x y = g ⟨x.val + 1, by omega⟩ y + g ⟨x.val - 1, by omega⟩ y := by
  unfold spatialSup branchSum
  rw [branchNeighbors_of_horizontal_wall hn true hx0 hxn hyw,
    branchNeighbors_of_horizontal_wall hn false hx0 hxn hyw, sup_idem]

/-- Along the vertical wall `x = 0` (`0 < y < n`), `spatialSup` uses only
`g(0, y + 1) + g(0, y - 1)`. -/
theorem spatialSup_of_wall_x_zero {R : Type*} [Add R] [SemilatticeSup R] (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → R) {y : Fin (n + 1)} (hy0 : 0 < y.val) (hyn : y.val < n) :
    spatialSup hn g 0 y = g 0 ⟨y.val + 1, by omega⟩ + g 0 ⟨y.val - 1, by omega⟩ := by
  unfold spatialSup branchSum
  rw [branchNeighbors_of_wall_x_zero hn true hy0 hyn,
    branchNeighbors_of_wall_x_zero hn false hy0 hyn, sup_idem]

/-- Along the vertical wall `x = n` (`0 < y < n`), `spatialSup` uses only
`g(n, y + 1) + g(n, y - 1)`. -/
theorem spatialSup_of_wall_x_last {R : Type*} [Add R] [SemilatticeSup R] (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → R) {y : Fin (n + 1)} (hy0 : 0 < y.val) (hyn : y.val < n) :
    spatialSup hn g (Fin.last n) y =
      g (Fin.last n) ⟨y.val + 1, by omega⟩ + g (Fin.last n) ⟨y.val - 1, by omega⟩ := by
  unfold spatialSup branchSum
  rw [branchNeighbors_of_wall_x_last hn true hy0 hyn,
    branchNeighbors_of_wall_x_last hn false hy0 hyn, sup_idem]

/-- Corner rule at `(0, 0)`: sum of the two inward neighbours `(1, 0)` and `(0, 1)`. -/
theorem spatialSup_corner_zero_zero {R : Type*} [Add R] [SemilatticeSup R] (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → R) :
    spatialSup hn g 0 0 = g ⟨1, by omega⟩ 0 + g 0 ⟨1, by omega⟩ := by
  unfold spatialSup branchSum
  rw [branchNeighbors_corner_zero_zero hn true,
    branchNeighbors_corner_zero_zero hn false, sup_idem]

/-- Corner rule at `(0, n)`: sum of the two inward neighbours `(1, n)` and `(0, n - 1)`. -/
theorem spatialSup_corner_zero_last {R : Type*} [Add R] [SemilatticeSup R] (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → R) :
    spatialSup hn g 0 (Fin.last n) =
      g ⟨1, by omega⟩ (Fin.last n) + g 0 ⟨n - 1, by omega⟩ := by
  unfold spatialSup branchSum
  rw [branchNeighbors_corner_zero_last hn true,
    branchNeighbors_corner_zero_last hn false, sup_idem]

/-- Corner rule at `(n, 0)`: sum of the two inward neighbours `(n - 1, 0)` and `(n, 1)`. -/
theorem spatialSup_corner_last_zero {R : Type*} [Add R] [SemilatticeSup R] (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → R) :
    spatialSup hn g (Fin.last n) 0 =
      g ⟨n - 1, by omega⟩ 0 + g (Fin.last n) ⟨1, by omega⟩ := by
  unfold spatialSup branchSum
  rw [branchNeighbors_corner_last_zero hn true,
    branchNeighbors_corner_last_zero hn false, sup_idem]

/-- Corner rule at `(n, n)`: sum of the two inward neighbours `(n - 1, n)` and `(n, n - 1)`. -/
theorem spatialSup_corner_last_last {R : Type*} [Add R] [SemilatticeSup R] (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → R) :
    spatialSup hn g (Fin.last n) (Fin.last n) =
      g ⟨n - 1, by omega⟩ (Fin.last n) + g (Fin.last n) ⟨n - 1, by omega⟩ := by
  unfold spatialSup branchSum
  rw [branchNeighbors_corner_last_last hn true,
    branchNeighbors_corner_last_last hn false, sup_idem]

end SpatialBranches

/-! ### Local octahedron rule, continuous/discrete recurrence, involutivity, and chirality check -/

section RecurrenceRule

variable {R : Type*} [AddCommGroup R]

/-- The local interior octahedron update `e' = (a + c) ⊔ (b + d) - e`. -/
def octahedronRule [SemilatticeSup R] (a b c d e : R) : R :=
  (a + c) ⊔ (b + d) - e

@[simp] theorem octahedronRule_apply [SemilatticeSup R] (a b c d e : R) :
    octahedronRule a b c d e = (a + c) ⊔ (b + d) - e := by
  unfold octahedronRule; rfl

/-- Applying `e ↦ (a + c) ⊔ (b + d) - e` twice returns `e`. -/
theorem octahedronRule_involutive [SemilatticeSup R] (a b c d : R) :
    Function.Involutive (octahedronRule a b c d) := fun e => by
  simp [octahedronRule_apply]

/-- Dual local rule `e' = (a + c) ⊓ (b + d) - e` using `min` in place of `max`. -/
def octahedronMinRule [SemilatticeInf R] (a b c d e : R) : R :=
  (a + c) ⊓ (b + d) - e

@[simp] theorem octahedronMinRule_apply [SemilatticeInf R] (a b c d e : R) :
    octahedronMinRule a b c d e = (a + c) ⊓ (b + d) - e := by
  unfold octahedronMinRule; rfl

/-- The `min` rule is also an involution in `e`, although it fails to preserve hive concavity. -/
theorem octahedronMinRule_involutive [SemilatticeInf R] (a b c d : R) :
    Function.Involutive (octahedronMinRule a b c d) := fun e => by
  simp [octahedronMinRule_apply]

/-- Henriques–Kamnitzer's bounded modified recurrence (equation (5)) on `[0, n]² × ℝ`. -/
def SatisfiesRealTimeRecurrence [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    (f : Fin (n + 1) → Fin (n + 1) → ℝ → R) : Prop :=
  ∀ x y : Fin (n + 1), ∀ t : ℝ,
    f x y (t + 1) = spatialSup hn (fun x' y' => f x' y' t) x y - f x y (t - 1)

theorem satisfiesRealTimeRecurrence_def [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    (f : Fin (n + 1) → Fin (n + 1) → ℝ → R) :
    SatisfiesRealTimeRecurrence hn f ↔
      ∀ x y : Fin (n + 1), ∀ t : ℝ,
        f x y (t + 1) = spatialSup hn (fun x' y' => f x' y' t) x y - f x y (t - 1) := by
  unfold SatisfiesRealTimeRecurrence; rfl

theorem odd_top_even {n : ℕ} {x y : Fin (n + 1)} {t : ℤ}
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : Even ((x.val : ℤ) + y.val + (t + 1)) := by
  obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by linarith⟩

theorem odd_bot_even {n : ℕ} {x y : Fin (n + 1)} {t : ℤ}
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : Even ((x.val : ℤ) + y.val + (t - 1)) := by
  obtain ⟨k, hk⟩ := hodd; exact ⟨k, by linarith⟩

theorem odd_adj_even {n : ℕ} {x y x' y' : Fin (n + 1)} {t : ℤ}
    (hadj : GridAdj x y x' y') (hodd : Odd ((x.val : ℤ) + y.val + t)) :
    Even ((x'.val : ℤ) + y'.val + t) := by
  rw [gridAdj_def] at hadj
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k + (((x'.val : ℤ) - x.val) + ((y'.val : ℤ) - y.val) + 1) / 2, ?_⟩
  omega

/-- Spatial supremum on `SpaceTimePoint n` around an odd centre `(x, y, t)`. -/
def paritySpatialSup [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n) (f : SpaceTimePoint n → R)
    (x y : Fin (n + 1)) (t : ℤ) (hodd : Odd ((x.val : ℤ) + y.val + t)) : R :=
  let htrue := gridAdj_branchNeighbors hn true x y
  let hfalse := gridAdj_branchNeighbors hn false x y
  (f ⟨(branchNeighbors hn true x y).1.1, (branchNeighbors hn true x y).1.2, t,
      odd_adj_even htrue.1 hodd⟩ +
    f ⟨(branchNeighbors hn true x y).2.1, (branchNeighbors hn true x y).2.2, t,
      odd_adj_even htrue.2 hodd⟩) ⊔
  (f ⟨(branchNeighbors hn false x y).1.1, (branchNeighbors hn false x y).1.2, t,
      odd_adj_even hfalse.1 hodd⟩ +
    f ⟨(branchNeighbors hn false x y).2.1, (branchNeighbors hn false x y).2.2, t,
      odd_adj_even hfalse.2 hodd⟩)

theorem paritySpatialSup_def [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n) (f : SpaceTimePoint n → R)
    (x y : Fin (n + 1)) (t : ℤ) (hodd : Odd ((x.val : ℤ) + y.val + t)) :
    paritySpatialSup hn f x y t hodd =
      (f ⟨(branchNeighbors hn true x y).1.1, (branchNeighbors hn true x y).1.2, t,
          odd_adj_even (gridAdj_branchNeighbors hn true x y).1 hodd⟩ +
        f ⟨(branchNeighbors hn true x y).2.1, (branchNeighbors hn true x y).2.2, t,
          odd_adj_even (gridAdj_branchNeighbors hn true x y).2 hodd⟩) ⊔
      (f ⟨(branchNeighbors hn false x y).1.1, (branchNeighbors hn false x y).1.2, t,
          odd_adj_even (gridAdj_branchNeighbors hn false x y).1 hodd⟩ +
        f ⟨(branchNeighbors hn false x y).2.1, (branchNeighbors hn false x y).2.2, t,
          odd_adj_even (gridAdj_branchNeighbors hn false x y).2 hodd⟩) := by
  unfold paritySpatialSup; rfl

theorem paritySpatialSup_eq_spatialSup [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → ℤ → R) (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) :
    paritySpatialSup hn (fun p => g p.x p.y p.t) x y t hodd =
      spatialSup hn (fun x' y' => g x' y' t) x y := by
  unfold paritySpatialSup spatialSup branchSum; rfl

/-- Bounded modified octahedron recurrence on the discrete space-time parity lattice `Lₙ`. -/
def SatisfiesRecurrence [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    (f : SpaceTimePoint n → R) : Prop :=
  ∀ x y : Fin (n + 1), ∀ t : ℤ, ∀ hodd : Odd ((x.val : ℤ) + y.val + t),
    f ⟨x, y, t + 1, odd_top_even hodd⟩ =
      paritySpatialSup hn f x y t hodd - f ⟨x, y, t - 1, odd_bot_even hodd⟩

theorem satisfiesRecurrence_def [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    (f : SpaceTimePoint n → R) :
    SatisfiesRecurrence hn f ↔
      ∀ x y : Fin (n + 1), ∀ t : ℤ, ∀ hodd : Odd ((x.val : ℤ) + y.val + t),
        f ⟨x, y, t + 1, odd_top_even hodd⟩ =
          paritySpatialSup hn f x y t hodd - f ⟨x, y, t - 1, odd_bot_even hodd⟩ := by
  unfold SatisfiesRecurrence; rfl

/-- Restricting a continuous-time solution on `[0, n]² × ℝ` to `Lₙ` yields a parity-lattice
solution. -/
theorem SatisfiesRealTimeRecurrence.restrictToLattice [SemilatticeSup R] {n : ℕ} {hn : 1 ≤ n}
    {f : Fin (n + 1) → Fin (n + 1) → ℝ → R} (hf : SatisfiesRealTimeRecurrence hn f) :
    SatisfiesRecurrence hn (fun p : SpaceTimePoint n => f p.x p.y (p.t : ℝ)) := by
  rw [satisfiesRecurrence_def]
  intro x y t hodd
  have hstep := hf x y (t : ℝ)
  have hcast1 : ((t + 1 : ℤ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
  have hcast2 : ((t - 1 : ℤ) : ℝ) = (t : ℝ) - 1 := by push_cast; ring
  simpa [paritySpatialSup_eq_spatialSup (g := fun x' y' s => f x' y' (s : ℝ)), hcast1, hcast2]
    using hstep

/-- Linear growth in time `(x, y, t) ↦ t` satisfies the continuous-time bounded recurrence on all
of `[0, n]² × ℝ` (interior, walls, and corners). -/
theorem satisfiesRealTimeRecurrence_time {n : ℕ} (hn : 1 ≤ n) :
    SatisfiesRealTimeRecurrence hn (fun (_ _ : Fin (n + 1)) (t : ℝ) => t) := fun x y t => by
  rw [spatialSup_def, branchSum_apply, branchSum_apply, sup_idem]; ring

/-- Reversing time `(x, y, t) ↦ (x, y, -t)` preserves solutions of the bounded recurrence. -/
theorem satisfiesRecurrence_timeRev_iff [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    (f : SpaceTimePoint n → R) :
    SatisfiesRecurrence hn (fun p => f p.timeRev) ↔ SatisfiesRecurrence hn f := by
  have hdir {g : SpaceTimePoint n → R} (hg : SatisfiesRecurrence hn g) :
      SatisfiesRecurrence hn (fun p => g p.timeRev) := by
    rw [satisfiesRecurrence_def]
    intro x y t hodd
    have hodd' : Odd ((x.val : ℤ) + y.val + (-t)) := by
      obtain ⟨k, hk⟩ := hodd; exact ⟨k - t, by linarith⟩
    have hstep := (satisfiesRecurrence_def hn g).mp hg x y (-t) hodd'
    have htop : (⟨x, y, t + 1, odd_top_even hodd⟩ : SpaceTimePoint n).timeRev =
        ⟨x, y, -t - 1, odd_bot_even hodd'⟩ := by
      ext <;> simp only [SpaceTimePoint.timeRev_x, SpaceTimePoint.timeRev_y,
        SpaceTimePoint.timeRev_t]; ring
    have hbot : (⟨x, y, t - 1, odd_bot_even hodd⟩ : SpaceTimePoint n).timeRev =
        ⟨x, y, -t + 1, odd_top_even hodd'⟩ := by
      ext <;> simp only [SpaceTimePoint.timeRev_x, SpaceTimePoint.timeRev_y,
        SpaceTimePoint.timeRev_t]; ring
    have hadj_rev {x' y' : Fin (n + 1)} (hadj : GridAdj x y x' y') :
        (⟨x', y', t, odd_adj_even hadj hodd⟩ : SpaceTimePoint n).timeRev =
          ⟨x', y', -t, odd_adj_even hadj hodd'⟩ := by
      ext <;> simp
    have hsup : paritySpatialSup hn (fun p => g p.timeRev) x y t hodd =
        paritySpatialSup hn g x y (-t) hodd' := by
      unfold paritySpatialSup
      dsimp only
      let ht := gridAdj_branchNeighbors hn true x y
      let hf := gridAdj_branchNeighbors hn false x y
      rw [hadj_rev ht.1, hadj_rev ht.2, hadj_rev hf.1, hadj_rev hf.2]
    rw [htop, hbot, hsup, hstep, sub_sub_self]
  exact ⟨fun h => by simpa using hdir h, hdir⟩

/-- Along the wall `y = 0` (`0 < x < n`), the bounded recurrence satisfies
`f(x, 0, t + 1) = f(x + 1, 0, t) + f(x - 1, 0, t) - f(x, 0, t - 1)`, so differences along
characteristics propagate unchanged. -/
theorem wall_y_zero_recurrence [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    {f : SpaceTimePoint n → R} (hf : SatisfiesRecurrence hn f)
    {x : Fin (n + 1)} (hx0 : 0 < x.val) (hxn : x.val < n) {t : ℤ}
    (hodd : Odd ((x.val : ℤ) + (0 : Fin (n + 1)).val + t)) :
    f ⟨x, 0, t + 1, odd_top_even hodd⟩ -
        f ⟨⟨x.val + 1, by omega⟩, 0, t,
          odd_adj_even
            (by simp only [gridAdj_def, Fin.val_zero, sub_self, Int.natAbs_zero, add_zero]; omega)
            hodd⟩ =
      f ⟨⟨x.val - 1, by omega⟩, 0, t,
          odd_adj_even
            (by simp only [gridAdj_def, Fin.val_zero, sub_self, Int.natAbs_zero, add_zero]; omega)
            hodd⟩ -
        f ⟨x, 0, t - 1, odd_bot_even hodd⟩ := by
  have hstep := (satisfiesRecurrence_def hn f).mp hf x 0 t hodd
  have hbn (b : Bool) : branchNeighbors hn b x 0 =
      ((⟨x.val + 1, by omega⟩, 0), (⟨x.val - 1, by omega⟩, 0)) :=
    branchNeighbors_of_horizontal_wall hn b hx0 hxn (Or.inl (Fin.val_zero (n + 1)))
  have hp1 (b : Bool) (hadj : GridAdj x 0 (branchNeighbors hn b x 0).1.1
      (branchNeighbors hn b x 0).1.2) :
      (⟨(branchNeighbors hn b x 0).1.1, (branchNeighbors hn b x 0).1.2, t,
        odd_adj_even hadj hodd⟩ : SpaceTimePoint n) =
        ⟨⟨x.val + 1, by omega⟩, 0, t, odd_adj_even
          (by simp only [gridAdj_def, Fin.val_zero, sub_self, Int.natAbs_zero, add_zero]; omega)
          hodd⟩ := by
    ext <;> simp [hbn]
  have hp2 (b : Bool) (hadj : GridAdj x 0 (branchNeighbors hn b x 0).2.1
      (branchNeighbors hn b x 0).2.2) :
      (⟨(branchNeighbors hn b x 0).2.1, (branchNeighbors hn b x 0).2.2, t,
        odd_adj_even hadj hodd⟩ : SpaceTimePoint n) =
        ⟨⟨x.val - 1, by omega⟩, 0, t, odd_adj_even
          (by simp only [gridAdj_def, Fin.val_zero, sub_self, Int.natAbs_zero, add_zero]; omega)
          hodd⟩ := by
    ext <;> simp [hbn]
  have hsup : paritySpatialSup hn f x 0 t hodd =
      f ⟨⟨x.val + 1, by omega⟩, 0, t, odd_adj_even
          (by simp only [gridAdj_def, Fin.val_zero, sub_self, Int.natAbs_zero, add_zero]; omega)
          hodd⟩ +
      f ⟨⟨x.val - 1, by omega⟩, 0, t, odd_adj_even
          (by simp only [gridAdj_def, Fin.val_zero, sub_self, Int.natAbs_zero, add_zero]; omega)
          hodd⟩ := by
    unfold paritySpatialSup
    dsimp only
    let ht := gridAdj_branchNeighbors hn true x 0
    let hf := gridAdj_branchNeighbors hn false x 0
    rw [hp1 true ht.1, hp2 true ht.2, hp1 false hf.1, hp2 false hf.2, sup_idem]
  rw [hstep, hsup]; abel

end RecurrenceRule

/-- Negative-control chirality check at `n = 2`: gluing the normalized hives `Hive.exampleTwo` and
`Hive.detTwo + Hive.detTwo` along their matching shared boundary and updating the unique interior
vertex `(1, 1)` by `octahedronMinRule` (`min` in place of `max`) violates rhombus concavity on the
first output face `readOutputLeft`. -/
theorem not_isRhombusConcave_readOutputLeft_min :
    let h₁ : IntegerHive 2 := Hive.exampleTwo
    let h₂ : IntegerHive 2 := Hive.detTwo + Hive.detTwo
    let F : Fin 3 → Fin 3 → ℤ := glueInput h₁ h₂
    let Fmin : Fin 3 → Fin 3 → ℤ := fun x y =>
      if x = 1 ∧ y = 1 then octahedronMinRule (F 2 1) (F 1 2) (F 0 1) (F 1 0) (F 1 1) else F x y
    (∀ i : Fin 2, h₁.boundary 2 i = -h₂.boundary 0 i.rev) ∧
      ¬ IsRhombusConcave (readOutputLeft Fmin) := by
  intro h₁ h₂ F Fmin
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> simp [h₁, h₂, Hive.boundary_exampleTwo, Hive.boundary_detTwo]
  · intro hconc
    have hr := (Hive.isRhombusConcave_def _).mp hconc Hive.isRhombus_at_cornerA
    have eval_eq (x y : Fin 3) (h : y.val ≤ x.val) :
        F x y = h₁ ⟨2 - x.val, x.val - y.val, y.val, by have := x.isLt; omega⟩ :=
      glueInput_of_le _ _ h
    have eval_gt (x y : Fin 3) (h : ¬ y.val ≤ x.val) :
        F x y = h₂ ⟨2 - y.val, x.val, y.val - x.val, by have := y.isLt; omega⟩ :=
      glueInput_of_gt _ _ h
    have h20 : F 2 0 = 1 := by rw [eval_eq 2 0 (by decide)]; simp [h₁]
    have h21 : F 2 1 = 2 := by rw [eval_eq 2 1 (by decide)]; simp [h₁]
    have h11 : F 1 1 = 2 := by rw [eval_eq 1 1 (by decide)]; simp [h₁]
    have h10 : F 1 0 = 1 := by rw [eval_eq 1 0 (by decide)]; simp [h₁]
    have h01 : F 0 1 = 2 := by rw [eval_gt 0 1 (by decide)]; simp [h₂]
    have h12 : F 1 2 = 4 := by rw [eval_gt 1 2 (by decide)]; simp [h₂]
    have hFmin_20 : Fmin (Fin.last 2) 0 = 1 := by
      dsimp only [Fmin]; rw [ite_eq_right (by decide)]; exact h20
    have hFmin_21 : Fmin 2 1 = 2 := by
      dsimp only [Fmin]; rw [ite_eq_right (by decide)]; exact h21
    have hFmin_12 : Fmin 1 2 = 4 := by
      dsimp only [Fmin]; rw [ite_eq_right (by decide)]; exact h12
    have hFmin_11 : Fmin 1 1 = 2 := by
      dsimp only [Fmin]
      rw [ite_eq_left (by decide), octahedronMinRule_apply, h21, h12, h01, h10, h11]; decide
    have hA : readOutputLeft Fmin (Vertex.cornerA 2) = 0 := readOutputLeft_cornerA Fmin
    have ha : readOutputLeft Fmin ⟨1, 1, 0, rfl⟩ = 1 := by
      have hx : (embedOutputLeft (⟨1, 1, 0, rfl⟩ : Vertex 2)).x = 2 := by ext; simp
      have hy : (embedOutputLeft (⟨1, 1, 0, rfl⟩ : Vertex 2)).y = 1 := by ext; simp
      rw [readOutputLeft_apply, hx, hy, hFmin_21, hFmin_20]; rfl
    have hc : readOutputLeft Fmin ⟨1, 0, 1, rfl⟩ = 1 := by
      have hx : (embedOutputLeft (⟨1, 0, 1, rfl⟩ : Vertex 2)).x = 1 := by ext; simp
      have hy : (embedOutputLeft (⟨1, 0, 1, rfl⟩ : Vertex 2)).y = 1 := by ext; simp
      rw [readOutputLeft_apply, hx, hy, hFmin_11, hFmin_20]; rfl
    have hd : readOutputLeft Fmin ⟨0, 1, 1, rfl⟩ = 3 := by
      have hx : (embedOutputLeft (⟨0, 1, 1, rfl⟩ : Vertex 2)).x = 1 := by ext; simp
      have hy : (embedOutputLeft (⟨0, 1, 1, rfl⟩ : Vertex 2)).y = 2 := by ext; simp
      rw [readOutputLeft_apply, hx, hy, hFmin_12, hFmin_20]; rfl
    rw [hA, hd, ha, hc] at hr
    omega

/-! ### Finite dependency recursion from a section and state-transition bijections -/

section Evolution

variable {n : ℕ}

/-- Minimum height of a section `τ : Section n` over the finite grid `[0, n]²`. -/
def Section.minHeight (τ : Section n) : ℤ :=
  (Finset.univ.image (fun q : Fin (n + 1) × Fin (n + 1) => τ q.1 q.2)).min'
    (Finset.univ_nonempty.image _)

theorem Section.minHeight_le (τ : Section n) (x y : Fin (n + 1)) : τ.minHeight ≤ τ x y := by
  unfold Section.minHeight
  exact Finset.min'_le _ (τ x y) (Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩)

variable {R : Type*} [AddCommGroup R] [SemilatticeSup R]

/-- Finite dependency recursion in forward time from initial data `F` on `τ : Section n`. -/
def evolveFuture (hn : 1 ≤ n) (τ : Section n) (F : Fin (n + 1) → Fin (n + 1) → R)
    (x : Fin (n + 1)) (y : Fin (n + 1)) (t : ℤ) : R :=
  if _h : t ≤ τ x y then
    F x y
  else
    have _ht1 : (t - 1 - τ.minHeight).toNat < (t - τ.minHeight).toNat := by
      have := τ.minHeight_le x y; omega
    have _ht2 : (t - 2 - τ.minHeight).toNat < (t - τ.minHeight).toNat := by
      have := τ.minHeight_le x y; omega
    spatialSup hn (fun x' y' => evolveFuture hn τ F x' y' (t - 1)) x y -
      evolveFuture hn τ F x y (t - 2)
termination_by (t - τ.minHeight).toNat

theorem evolveFuture_of_le (hn : 1 ≤ n) (τ : Section n) (F : Fin (n + 1) → Fin (n + 1) → R)
    {x y : Fin (n + 1)} {t : ℤ} (h : t ≤ τ x y) :
    evolveFuture hn τ F x y t = F x y := by
  rw [evolveFuture]
  exact dite_eq_left_of_eq_true (eq_true h)

theorem evolveFuture_of_gt (hn : 1 ≤ n) (τ : Section n) (F : Fin (n + 1) → Fin (n + 1) → R)
    {x y : Fin (n + 1)} {t : ℤ} (h : τ x y < t) :
    evolveFuture hn τ F x y t =
      spatialSup hn (fun x' y' => evolveFuture hn τ F x' y' (t - 1)) x y -
        evolveFuture hn τ F x y (t - 2) := by
  rw [evolveFuture]
  exact dite_eq_right_of_eq_false (eq_false (not_le.mpr h))

@[simp] theorem evolveFuture_section (hn : 1 ≤ n) (τ : Section n)
    (F : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    evolveFuture hn τ F x y (τ x y) = F x y :=
  evolveFuture_of_le hn τ F le_rfl

/-- Two-sided space-time evolution from initial data `F` on `τ : Section n`, combining forward
recursion in `{τ ≤ t}` with time-reversed recursion in `{t < τ}`. -/
def evolveFromSection (hn : 1 ≤ n) (τ : Section n) (F : Fin (n + 1) → Fin (n + 1) → R)
    (p : SpaceTimePoint n) : R :=
  if τ p.x p.y ≤ p.t then
    evolveFuture hn τ F p.x p.y p.t
  else
    evolveFuture hn τ.timeRev F p.x p.y (-p.t)

theorem evolveFromSection_of_ge (hn : 1 ≤ n) (τ : Section n) (F : Fin (n + 1) → Fin (n + 1) → R)
    {p : SpaceTimePoint n} (h : τ p.x p.y ≤ p.t) :
    evolveFromSection hn τ F p = evolveFuture hn τ F p.x p.y p.t := by
  unfold evolveFromSection; exact ite_eq_left h

theorem evolveFromSection_of_le (hn : 1 ≤ n) (τ : Section n) (F : Fin (n + 1) → Fin (n + 1) → R)
    {p : SpaceTimePoint n} (h : p.t ≤ τ p.x p.y) :
    evolveFromSection hn τ F p = evolveFuture hn τ.timeRev F p.x p.y (-p.t) := by
  unfold evolveFromSection
  by_cases hge : τ p.x p.y ≤ p.t
  · have heq : p.t = τ p.x p.y := le_antisymm h hge
    rw [ite_eq_left hge, heq, evolveFuture_section,
      evolveFuture_of_le hn τ.timeRev F (by simp)]
  · exact ite_eq_right hge

@[simp] theorem evolveFromSection_point (hn : 1 ≤ n) (τ : Section n)
    (F : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    evolveFromSection hn τ F (τ.point x y) = F x y := by
  rw [evolveFromSection_of_ge hn τ F (by simp)]; simp

@[simp] theorem evolveFromSection_timeRev (hn : 1 ≤ n) (τ : Section n)
    (F : Fin (n + 1) → Fin (n + 1) → R) (p : SpaceTimePoint n) :
    evolveFromSection hn τ.timeRev F p.timeRev = evolveFromSection hn τ F p := by
  by_cases h : τ p.x p.y ≤ p.t
  · rw [evolveFromSection_of_ge hn τ F h,
      evolveFromSection_of_le hn τ.timeRev F (by simpa using h)]
    simp
  · have hle : p.t ≤ τ p.x p.y := le_of_not_ge h
    rw [evolveFromSection_of_le hn τ F hle,
      evolveFromSection_of_ge hn τ.timeRev F (by simpa using hle)]
    simp

/-- `evolveFromSection hn τ F` satisfies the bounded octahedron recurrence everywhere on `Lₙ`. -/
theorem satisfiesRecurrence_evolveFromSection (hn : 1 ≤ n) (τ : Section n)
    (F : Fin (n + 1) → Fin (n + 1) → R) :
    SatisfiesRecurrence hn (evolveFromSection hn τ F) := by
  rw [satisfiesRecurrence_def]
  intro x y t hodd
  obtain ⟨k₁, hk₁⟩ := id hodd
  obtain ⟨k₂, hk₂⟩ := τ.even_sum x y
  rcases (by omega : τ x y ≤ t - 1 ∨ t + 1 ≤ τ x y) with hfut | hpast
  · have htop : evolveFromSection hn τ F ⟨x, y, t + 1, odd_top_even hodd⟩ =
        evolveFuture hn τ F x y (t + 1) :=
      evolveFromSection_of_ge hn τ F (by dsimp; omega)
    have hbot : evolveFromSection hn τ F ⟨x, y, t - 1, odd_bot_even hodd⟩ =
        evolveFuture hn τ F x y (t - 1) :=
      evolveFromSection_of_ge hn τ F hfut
    have hadj_ge {x' y' : Fin (n + 1)} (hadj : GridAdj x y x' y') : τ x' y' ≤ t := by
      have hs := τ.slope_eq_one hadj; omega
    have hsup : paritySpatialSup hn (evolveFromSection hn τ F) x y t hodd =
        spatialSup hn (fun x' y' => evolveFuture hn τ F x' y' t) x y := by
      unfold paritySpatialSup spatialSup branchSum
      have ht := gridAdj_branchNeighbors hn true x y
      have hf := gridAdj_branchNeighbors hn false x y
      rw [evolveFromSection_of_ge hn τ F (hadj_ge ht.1),
        evolveFromSection_of_ge hn τ F (hadj_ge ht.2),
        evolveFromSection_of_ge hn τ F (hadj_ge hf.1),
        evolveFromSection_of_ge hn τ F (hadj_ge hf.2)]
    have ht12 : t + 1 - 2 = t - 1 := by ring
    rw [htop, hbot, hsup, evolveFuture_of_gt hn τ F (by omega), add_sub_cancel_right, ht12]
  · have htop : evolveFromSection hn τ F ⟨x, y, t + 1, odd_top_even hodd⟩ =
        evolveFuture hn τ.timeRev F x y (-(t + 1)) :=
      evolveFromSection_of_le hn τ F hpast
    have hbot : evolveFromSection hn τ F ⟨x, y, t - 1, odd_bot_even hodd⟩ =
        spatialSup hn (fun x' y' => evolveFuture hn τ.timeRev F x' y' (-t)) x y -
          evolveFuture hn τ.timeRev F x y (-(t + 1)) := by
      have hsub1 : -(t - 1) = -t + 1 := by ring
      have hsub2 : -t + 1 - 2 = -(t + 1) := by ring
      rw [evolveFromSection_of_le hn τ F (by dsimp; omega)]
      dsimp only
      rw [hsub1, evolveFuture_of_gt hn τ.timeRev F (by rw [Section.timeRev_apply]; omega),
        add_sub_cancel_right, hsub2]
    have hadj_le {x' y' : Fin (n + 1)} (hadj : GridAdj x y x' y') : t ≤ τ x' y' := by
      have hs := τ.slope_eq_one hadj; omega
    have hsup : paritySpatialSup hn (evolveFromSection hn τ F) x y t hodd =
        spatialSup hn (fun x' y' => evolveFuture hn τ.timeRev F x' y' (-t)) x y := by
      unfold paritySpatialSup spatialSup branchSum
      have ht := gridAdj_branchNeighbors hn true x y
      have hf := gridAdj_branchNeighbors hn false x y
      rw [evolveFromSection_of_le hn τ F (hadj_le ht.1),
        evolveFromSection_of_le hn τ F (hadj_le ht.2),
        evolveFromSection_of_le hn τ F (hadj_le hf.1),
        evolveFromSection_of_le hn τ F (hadj_le hf.2)]
    rw [htop, hbot, hsup, sub_sub_self]

/-- Uniqueness on any finite future region `{τ₁ ≤ t ≤ τ₂}`: two functions agreeing on `τ₁` and
satisfying the bounded recurrence at all odd centres strictly between `τ₁` and `τ₂` agree on every
point between `τ₁` and `τ₂`. -/
theorem eq_on_between_of_recurrence (hn : 1 ≤ n) {τ₁ τ₂ : Section n} {f g : SpaceTimePoint n → R}
    (hinit : ∀ x y, f (τ₁.point x y) = g (τ₁.point x y))
    (hrec : ∀ x y t (hodd : Odd ((x.val : ℤ) + y.val + t)),
      τ₁ x y < t + 1 → t + 1 ≤ τ₂ x y →
        f ⟨x, y, t + 1, odd_top_even hodd⟩ - g ⟨x, y, t + 1, odd_top_even hodd⟩ =
          (paritySpatialSup hn f x y t hodd - f ⟨x, y, t - 1, odd_bot_even hodd⟩) -
            (paritySpatialSup hn g x y t hodd - g ⟨x, y, t - 1, odd_bot_even hodd⟩)) :
    ∀ p : SpaceTimePoint n, τ₁ p.x p.y ≤ p.t → p.t ≤ τ₂ p.x p.y → f p = g p := by
  suffices ∀ m : ℕ, ∀ p : SpaceTimePoint n, (p.t - τ₁.minHeight).toNat ≤ m →
      τ₁ p.x p.y ≤ p.t → p.t ≤ τ₂ p.x p.y → f p = g p by
    intro p h₁ h₂; exact this _ p le_rfl h₁ h₂
  intro m
  induction m with
  | zero =>
    intro p hm h₁ _
    have hmin := τ₁.minHeight_le p.x p.y
    have hteq : p.t = τ₁ p.x p.y := by omega
    have hp : p = τ₁.point p.x p.y := (τ₁.eq_point_iff).mp ⟨rfl, rfl, hteq⟩
    rw [hp]; exact hinit p.x p.y
  | succ m ih =>
    intro p hm h₁ h₂
    by_cases hteq : p.t = τ₁ p.x p.y
    · have hp : p = τ₁.point p.x p.y := (τ₁.eq_point_iff).mp ⟨rfl, rfl, hteq⟩
      rw [hp]; exact hinit p.x p.y
    · have hlt : τ₁ p.x p.y < p.t := lt_of_le_of_ne h₁ (Ne.symm hteq)
      obtain ⟨k₁, hk₁⟩ := p.even_sum
      obtain ⟨k₂, hk₂⟩ := τ₁.even_sum p.x p.y
      have hodd : Odd ((p.x.val : ℤ) + p.y.val + (p.t - 1)) := ⟨k₁ - 1, by linarith⟩
      have hbot_ge : τ₁ p.x p.y ≤ p.t - 2 := by omega
      have hbot_eq : f ⟨p.x, p.y, p.t - 2, by convert odd_bot_even hodd using 2; ring⟩ =
          g ⟨p.x, p.y, p.t - 2, by convert odd_bot_even hodd using 2; ring⟩ :=
        ih _ (by dsimp; omega) hbot_ge (by dsimp; omega)
      have hadj_eq {x' y' : Fin (n + 1)} (hadj : GridAdj p.x p.y x' y') :
          f ⟨x', y', p.t - 1, odd_adj_even hadj hodd⟩ =
            g ⟨x', y', p.t - 1, odd_adj_even hadj hodd⟩ := by
        have hs1 := τ₁.slope_eq_one hadj
        have hs2 := τ₂.slope_eq_one hadj
        exact ih _ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
      have hsup_eq : paritySpatialSup hn f p.x p.y (p.t - 1) hodd =
          paritySpatialSup hn g p.x p.y (p.t - 1) hodd := by
        unfold paritySpatialSup
        have ht := gridAdj_branchNeighbors hn true p.x p.y
        have hf := gridAdj_branchNeighbors hn false p.x p.y
        rw [hadj_eq ht.1, hadj_eq ht.2, hadj_eq hf.1, hadj_eq hf.2]
      have hstep := hrec p.x p.y (p.t - 1) hodd (by omega) (by omega)
      have hp_top : (⟨p.x, p.y, p.t - 1 + 1, odd_top_even hodd⟩ : SpaceTimePoint n) = p := by
        ext <;> simp
      have hp_bot : (⟨p.x, p.y, p.t - 1 - 1, odd_bot_even hodd⟩ : SpaceTimePoint n) =
          ⟨p.x, p.y, p.t - 2, by convert odd_bot_even hodd using 2; ring⟩ := by
        ext <;> simp only [sub_sub]; norm_num
      rw [hp_top, hp_bot, hsup_eq, hbot_eq, sub_self] at hstep
      exact sub_eq_zero.mp hstep

/-- Global uniqueness: a solution of `SatisfiesRecurrence hn` is uniquely determined by its
values on any section `τ : Section n`. -/
theorem eq_evolveFromSection_of_satisfiesRecurrence (hn : 1 ≤ n) (τ : Section n)
    {f : SpaceTimePoint n → R} (hf : SatisfiesRecurrence hn f) :
    f = evolveFromSection hn τ (fun x y => f (τ.point x y)) := by
  funext p
  set g := evolveFromSection hn τ (fun x y => f (τ.point x y))
  have hg := satisfiesRecurrence_evolveFromSection hn τ (fun x y => f (τ.point x y))
  by_cases hge : τ p.x p.y ≤ p.t
  · let τ_up : Section n :=
      Section.ofDistLeOne (fun x y => τ x y + 2 * (p.t - τ p.x p.y))
        (fun x y => by
          obtain ⟨k₁, hk₁⟩ := τ.even_sum x y
          exact ⟨k₁ + p.t - τ p.x p.y, by linarith⟩)
        (fun {x₁ y₁ x₂ y₂} hadj => by
          have hs := τ.abs_sub_eq_one hadj
          simpa [add_sub_add_comm] using hs.le)
    exact eq_on_between_of_recurrence (τ₁ := τ) (τ₂ := τ_up) hn
      (fun x y => by simp [g])
      (fun x y t hodd _ _ => by
        rw [(satisfiesRecurrence_def hn f).mp hf x y t hodd,
          (satisfiesRecurrence_def hn g).mp hg x y t hodd])
      p hge (by unfold τ_up; rw [Section.ofDistLeOne_apply]; omega)
  · have hle : p.t ≤ τ p.x p.y := le_of_not_ge hge
    have hf_rev : SatisfiesRecurrence hn (fun q => f q.timeRev) :=
      (satisfiesRecurrence_timeRev_iff hn f).mpr hf
    have hg_rev : SatisfiesRecurrence hn (fun q => g q.timeRev) :=
      (satisfiesRecurrence_timeRev_iff hn g).mpr hg
    let τ_dn : Section n :=
      Section.ofDistLeOne (fun x y => -τ x y + 2 * (τ p.x p.y - p.t))
        (fun x y => by
          obtain ⟨k₁, hk₁⟩ := τ.timeRev.even_sum x y
          rw [Section.timeRev_apply] at hk₁
          exact ⟨k₁ + τ p.x p.y - p.t, by linarith⟩)
        (fun {x₁ y₁ x₂ y₂} hadj => by
          have hs := τ.timeRev.abs_sub_eq_one hadj
          simpa [Section.timeRev_apply, add_sub_add_comm] using hs.le)
    have hrev_eq := eq_on_between_of_recurrence (τ₁ := τ.timeRev) (τ₂ := τ_dn)
      (f := fun q => f q.timeRev) (g := fun q => g q.timeRev) hn
      (fun x y => by
        have hpt : (τ.timeRev.point x y).timeRev = τ.point x y := by ext <;> simp
        simp [g, hpt])
      (fun x y t hodd _ _ => by
        rw [(satisfiesRecurrence_def hn (fun q => f q.timeRev)).mp hf_rev x y t hodd,
          (satisfiesRecurrence_def hn (fun q => g q.timeRev)).mp hg_rev x y t hodd])
      p.timeRev (by simpa using hle)
      (by unfold τ_dn; rw [Section.ofDistLeOne_apply, SpaceTimePoint.timeRev_x,
        SpaceTimePoint.timeRev_y, SpaceTimePoint.timeRev_t]; omega)
    rwa [SpaceTimePoint.timeRev_timeRev] at hrev_eq

/-- Equivalence between global solutions of the bounded recurrence on `Lₙ` and unrestricted
functions on any section `τ : Section n`. -/
def solutionEquivSection (hn : 1 ≤ n) (τ : Section n) :
    {f : SpaceTimePoint n → R // SatisfiesRecurrence hn f} ≃
      (Fin (n + 1) → Fin (n + 1) → R) where
  toFun f x y := f.1 (τ.point x y)
  invFun F := ⟨evolveFromSection hn τ F, satisfiesRecurrence_evolveFromSection hn τ F⟩
  left_inv f := Subtype.ext (eq_evolveFromSection_of_satisfiesRecurrence hn τ f.2).symm
  right_inv F := by funext x y; simp

/-- Section-to-section state-transition bijection induced by the bounded octahedron recurrence. -/
def sectionTransition (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    (Fin (n + 1) → Fin (n + 1) → R) ≃ (Fin (n + 1) → Fin (n + 1) → R) :=
  (solutionEquivSection hn τ₁).symm.trans (solutionEquivSection hn τ₂)

theorem sectionTransition_apply (hn : 1 ≤ n) (τ₁ τ₂ : Section n)
    (F : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    sectionTransition hn τ₁ τ₂ F x y = evolveFromSection hn τ₁ F (τ₂.point x y) := by
  unfold sectionTransition solutionEquivSection; rfl

@[simp] theorem sectionTransition_refl (hn : 1 ≤ n) (τ : Section n) :
    sectionTransition (R := R) hn τ τ = Equiv.refl _ := by
  ext F x y; simp [sectionTransition_apply]

@[simp] theorem sectionTransition_symm (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    (sectionTransition (R := R) hn τ₁ τ₂).symm = sectionTransition hn τ₂ τ₁ := by
  ext F x y; unfold sectionTransition solutionEquivSection; rfl

theorem sectionTransition_trans (hn : 1 ≤ n) (τ₁ τ₂ τ₃ : Section n) :
    (sectionTransition (R := R) hn τ₁ τ₂).trans (sectionTransition hn τ₂ τ₃) =
      sectionTransition hn τ₁ τ₃ := by
  ext F x y
  simp only [Equiv.trans_apply, sectionTransition_apply]
  have hf := satisfiesRecurrence_evolveFromSection hn τ₁ F
  have heq := eq_evolveFromSection_of_satisfiesRecurrence hn τ₂ hf
  exact (congrFun heq (τ₃.point x y)).symm

/-- Reversing time on both sections leaves `sectionTransition` unchanged. -/
@[simp] theorem sectionTransition_timeRev (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    sectionTransition (R := R) hn τ₁.timeRev τ₂.timeRev = sectionTransition hn τ₁ τ₂ := by
  ext F x y
  simp only [sectionTransition_apply]
  have hpt : τ₂.timeRev.point x y = (τ₂.point x y).timeRev := by ext <;> simp
  rw [hpt, evolveFromSection_timeRev]

/-- If `τ₁` and `τ₂` agree at `(x, y)`, then `sectionTransition hn τ₁ τ₂ F x y = F x y`. -/
theorem sectionTransition_eq_self_of_eq (hn : 1 ≤ n) {τ₁ τ₂ : Section n}
    (F : Fin (n + 1) → Fin (n + 1) → R) {x y : Fin (n + 1)} (h : τ₁ x y = τ₂ x y) :
    sectionTransition hn τ₁ τ₂ F x y = F x y := by
  rw [sectionTransition_apply]
  have hpt : τ₂.point x y = τ₁.point x y := by ext <;> simp [h]
  rw [hpt, evolveFromSection_point]

/-- Compatibility of `sectionTransition` with any additive group homomorphism preserving `⊔`
(in particular `Int.castAddHom ℚ`, `Int.castAddHom ℝ`, and `Rat.castAddHom ℝ`). -/
theorem map_sectionTransition {S : Type*} [AddCommGroup S] [SemilatticeSup S] (φ : R →+ S)
    (hsup : ∀ u v : R, φ (u ⊔ v) = φ u ⊔ φ v) (hn : 1 ≤ n) (τ₁ τ₂ : Section n)
    (F : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    φ (sectionTransition hn τ₁ τ₂ F x y) =
      sectionTransition hn τ₁ τ₂ (fun x' y' => φ (F x' y')) x y := by
  rw [sectionTransition_apply, sectionTransition_apply]
  let fS : SpaceTimePoint n → S := fun p => φ (evolveFromSection hn τ₁ F p)
  have hfS : SatisfiesRecurrence hn fS := by
    rw [satisfiesRecurrence_def]
    intro x₀ y₀ t hodd
    have hstep := (satisfiesRecurrence_def hn _).mp
      (satisfiesRecurrence_evolveFromSection hn τ₁ F) x₀ y₀ t hodd
    have hφsup : φ (paritySpatialSup hn (evolveFromSection hn τ₁ F) x₀ y₀ t hodd) =
        paritySpatialSup hn fS x₀ y₀ t hodd := by
      unfold paritySpatialSup
      rw [hsup, map_add, map_add]
    simpa [fS, map_sub, hφsup] using congrArg φ hstep
  have heq := eq_evolveFromSection_of_satisfiesRecurrence hn τ₁ hfS
  simpa [fS] using congrFun heq (τ₂.point x y)

end Evolution

/-- Nonnegative scaling equivariance of `sectionTransition` over any ordered commutative ring
(including `ℤ`, `ℚ`, and `ℝ`) for `0 ≤ c` (including `c = 0`). -/
theorem sectionTransition_smul_of_nonneg {n : ℕ} {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (hn : 1 ≤ n) (τ₁ τ₂ : Section n)
    {c : R} (hc : 0 ≤ c) (F : Fin (n + 1) → Fin (n + 1) → R) :
    sectionTransition hn τ₁ τ₂ (c • F) = c • sectionTransition hn τ₁ τ₂ F := by
  ext x y
  let φ : R →+ R := AddMonoidHom.mk' (fun r => c * r) (mul_add c)
  have hsup (u v : R) : φ (u ⊔ v) = φ u ⊔ φ v := by
    simp only [φ, AddMonoidHom.mk'_apply]
    exact mul_max_of_nonneg u v hc
  exact (map_sectionTransition φ hsup hn τ₁ τ₂ F x y).symm

/-! ### Associator dependency closure, `n = 0` identity, and exterior boundary preservation -/

section Associator

/-- Every associator point `(x, y, t + 1) ∈ Aₙ` strictly above the lower section `S` lies strictly
in the interior `(0, n)²`, and all five of its recurrence dependencies stay inside `Aₙ`. -/
theorem associator_dependencies_mem {n : ℕ} {x y : Fin (n + 1)} {t : ℤ}
    (hodd : Odd ((x.val : ℤ) + y.val + t))
    (htop : (⟨x, y, t + 1, odd_top_even hodd⟩ : SpaceTimePoint n).IsAssociator)
    (hlt : lowerSection n x y < t + 1) :
    0 < x.val ∧ x.val < n ∧ 0 < y.val ∧ y.val < n ∧
      (⟨x, y, t - 1, odd_bot_even hodd⟩ : SpaceTimePoint n).IsAssociator ∧
      ∀ {x' y' : Fin (n + 1)} (hadj : GridAdj x y x' y'),
        (⟨x', y', t, odd_adj_even hadj hodd⟩ : SpaceTimePoint n).IsAssociator := by
  have hnotwall : ¬ IsWall x y := not_isWall_of_isAssociator_of_lt htop hlt
  obtain ⟨hx0, hxn, hy0, hyn⟩ := not_isWall_iff.mp hnotwall
  have h4 := (SpaceTimePoint.isAssociator_iff_four_ineq _).mp htop
  rw [lowerSection_apply, Int.abs_eq_natAbs] at hlt
  obtain ⟨k, hk⟩ := hodd
  refine ⟨hx0, hxn, hy0, hyn, ?_, ?_⟩
  · rw [SpaceTimePoint.isAssociator_iff_four_ineq]
    dsimp at h4 ⊢; omega
  · intro x' y' hadj
    rw [gridAdj_def] at hadj
    rw [SpaceTimePoint.isAssociator_iff_four_ineq]
    dsimp at h4 ⊢; omega

/-- Associator transition from the lower section `S` to the upper section `S'`, defined for all
`n : ℕ` (`Equiv.refl` at `n = 0`, where `S = S'` is a single point, and `sectionTransition` for
`1 ≤ n`). -/
def associatorTransition (n : ℕ) {R : Type*} [AddCommGroup R] [SemilatticeSup R] :
    (Fin (n + 1) → Fin (n + 1) → R) ≃ (Fin (n + 1) → Fin (n + 1) → R) :=
  if hn : 1 ≤ n then
    sectionTransition hn (lowerSection n) (upperSection n)
  else
    Equiv.refl _

theorem associatorTransition_of_one_le {n : ℕ} (hn : 1 ≤ n)
    {R : Type*} [AddCommGroup R] [SemilatticeSup R] :
    associatorTransition (R := R) n = sectionTransition hn (lowerSection n) (upperSection n) := by
  unfold associatorTransition; exact dite_eq_left_of_eq_true (eq_true hn)

@[simp] theorem associatorTransition_zero {R : Type*} [AddCommGroup R] [SemilatticeSup R] :
    associatorTransition (R := R) 0 = Equiv.refl _ := by
  ext F x y; unfold associatorTransition; simp

/-- At `n = 0`, `A₀` is a single point, `S = S'`, and reading both output faces of
`associatorTransition 0 (glueInput h₁ h₂)` returns the unique normalized one-point hive `0`. -/
theorem associatorTransition_zero_hive {R : Type*} [AddCommGroup R] [SemilatticeSup R]
    (h₁ h₂ : Hive 0 R) :
    readOutputLeft (associatorTransition 0 (glueInput (⇑h₁) (⇑h₂))) = ⇑(0 : Hive 0 R) ∧
      readOutputRight (associatorTransition 0 (glueInput (⇑h₁) (⇑h₂))) = ⇑(0 : Hive 0 R) := by
  have hp (p : Vertex 0) : p = Vertex.cornerA 0 := by
    have := p.sum_eq
    ext <;> simp only [Vertex.cornerA_x, Vertex.cornerA_y, Vertex.cornerA_z] <;> omega
  refine ⟨funext fun p => ?_, funext fun p => ?_⟩
  · rw [hp p, readOutputLeft_cornerA]; rfl
  · rw [hp p, readOutputRight_cornerA, associatorTransition_zero]; simp

/-- Every wall point `(x, y)` lies in `S ∩ S'`, so `associatorTransition` leaves all four walls
unchanged. -/
theorem associatorTransition_eq_on_wall {n : ℕ} {R : Type*} [AddCommGroup R] [SemilatticeSup R]
    (F : Fin (n + 1) → Fin (n + 1) → R) {x y : Fin (n + 1)} (hw : IsWall x y) :
    associatorTransition n F x y = F x y := by
  by_cases hn : 1 ≤ n
  · rw [associatorTransition_of_one_le hn]
    exact sectionTransition_eq_self_of_eq hn F ((lowerSection_eq_upperSection_iff x y).mpr hw)
  · have hn0 : n = 0 := by omega
    subst hn0; simp

/-- Exterior boundary invariance of the associator transition: for any two hives `h₁, h₂` matching
along their shared boundary, evolving `glueInput h₁ h₂` from `S` to `S'` preserves `(0, 0) ↦ 0`,
`F'(n, 0) = |λ|`, and all four exterior boundaries `(μ, ν)` and `(λ, π*)`. -/
theorem boundary_associatorTransition {n : ℕ} {R : Type*} [AddCommGroup R] [SemilatticeSup R]
    {h₁ h₂ : Hive n R} (hb : ∀ i : Fin n, h₁.boundary 2 i = -h₂.boundary 0 i.rev) :
    let F' := associatorTransition n (glueInput (⇑h₁) (⇑h₂))
    F' 0 0 = 0 ∧
      F' (Fin.last n) 0 = (∑ i : Fin n, h₁.boundary 0 i) ∧
      Hive.boundaryLinear ℤ n R (readOutputLeft F') 0 = h₁.boundary 1 ∧
      Hive.boundaryLinear ℤ n R (readOutputLeft F') 1 = h₂.boundary 1 ∧
      Hive.boundaryLinear ℤ n R (readOutputRight F') 0 = h₁.boundary 0 ∧
      Hive.boundaryLinear ℤ n R (readOutputRight F') 2 = h₂.boundary 2 :=
  boundary_readOutput_of_eq_on_wall hb fun _ _ hw => associatorTransition_eq_on_wall _ hw

/-- Nonnegative scaling equivariance of `associatorTransition n` for all `n : ℕ` and `0 ≤ c`. -/
theorem associatorTransition_smul_of_nonneg (n : ℕ) {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {c : R} (hc : 0 ≤ c) (F : Fin (n + 1) → Fin (n + 1) → R) :
    associatorTransition n (c • F) = c • associatorTransition n F := by
  by_cases hn : 1 ≤ n
  · rw [associatorTransition_of_one_le hn]; exact sectionTransition_smul_of_nonneg hn _ _ hc F
  · have hn0 : n = 0 := by omega
    subst hn0; simp

end Associator

end TauCeti.Hive.Octahedron
