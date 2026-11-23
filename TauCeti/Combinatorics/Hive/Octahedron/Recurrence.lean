/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Basic.Real.Basic
public import TauCeti.Combinatorics.Hive.Octahedron.Lattice
import Mathlib.Tactic.Abel
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
2. **Involutivity, continuous/discrete recurrence, and wall propagation** (`octahedronRule`,
   `octahedronMinRule`, `SatisfiesRealTimeRecurrence`, `SatisfiesRecurrence`,
   `SatisfiesRecurrence.sub_eq_sub_of_horizontal_wall`): the interior update
   `e ↦ (a + c) ⊔ (b + d) - e` is an involution in `e` so time reversal `t ↦ -t` inverts the
   recurrence, and differences propagate along horizontal walls.
3. **Finite dependency recursion and section transitions** (`evolveFuture`, `evolveFromSection`,
   `solutionEquivSection`, `sectionTransition`): initial data on any section `τ : Section n`
   determines a unique global solution on `Lₙ` (and uniquely determines values on any finite region
   `{τ₁ ≤ t ≤ τ₂}`), yielding bijections `sectionTransition hn τ₁ τ₂` compatible with lattice-group
   homomorphisms (`ℤ → ℚ → ℝ`) and nonnegative scalar actions.
4. **Associator transition and dependency closure** (`associator_dependencies_mem`,
   `associatorTransition`, `associatorTransition_eq_on_wall`, `map_associatorTransition`): every
   dependency of an associator point strictly above `S` stays in `Aₙ` and uses the interior rule,
   wall values lie on `S ∩ S'` and remain fixed, and `n = 0` is `Equiv.refl`.

Associator hive-face gluing, the `n = 2` min-rule chirality counterexample, and exterior boundary
preservation are developed in `TauCeti.Combinatorics.Hive.Octahedron.Gluing`; unit-cell excavation
schedules and native piecewise-affineness (`TauCeti.IsPiecewiseAffineOn`) are developed in
`TauCeti.Combinatorics.Hive.Octahedron.Excavation`.

## References

* A. Henriques and J. Kamnitzer, *The octahedron recurrence and $\mathfrak{gl}_n$ crystals*,
  Adv. Math. **206** (2006), 211–249, §3, eq. (5).
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §5.
-/

public section

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
  unfold branchNeighbors; split_ifs <;> first | rfl | omega

theorem branchNeighbors_of_horizontal_wall (hn : 1 ≤ n) (b : Bool) {x y : Fin (n + 1)}
    (hx0 : 0 < x.val) (hxn : x.val < n) (hyw : y.val = 0 ∨ y.val = n) :
    branchNeighbors hn b x y = ((⟨x.val + 1, by omega⟩, y), (⟨x.val - 1, by omega⟩, y)) := by
  unfold branchNeighbors; split_ifs <;> first | rfl | omega

theorem branchNeighbors_of_wall_x_zero (hn : 1 ≤ n) (b : Bool) {y : Fin (n + 1)}
    (hy0 : 0 < y.val) (hyn : y.val < n) :
    branchNeighbors hn b 0 y =
      ((0, ⟨y.val + 1, by omega⟩), (0, ⟨y.val - 1, by omega⟩)) := by
  unfold branchNeighbors; simp only [Fin.val_zero]; split_ifs <;> first | rfl | omega

theorem branchNeighbors_of_wall_x_last (hn : 1 ≤ n) (b : Bool) {y : Fin (n + 1)}
    (hy0 : 0 < y.val) (hyn : y.val < n) :
    branchNeighbors hn b (Fin.last n) y =
      ((Fin.last n, ⟨y.val + 1, by omega⟩), (Fin.last n, ⟨y.val - 1, by omega⟩)) := by
  unfold branchNeighbors; simp only [Fin.val_last]; split_ifs <;> first | rfl | omega

theorem branchNeighbors_corner_zero_zero (hn : 1 ≤ n) (b : Bool) :
    branchNeighbors hn b 0 0 = ((⟨1, by omega⟩, 0), (0, ⟨1, by omega⟩)) := by
  unfold branchNeighbors; simp only [Fin.val_zero]; rfl

theorem branchNeighbors_corner_zero_last (hn : 1 ≤ n) (b : Bool) :
    branchNeighbors hn b 0 (Fin.last n) =
      ((⟨1, by omega⟩, Fin.last n), (0, ⟨n - 1, by omega⟩)) := by
  unfold branchNeighbors; simp only [Fin.val_zero, Fin.val_last]; split_ifs <;> first | rfl | omega

theorem branchNeighbors_corner_last_zero (hn : 1 ≤ n) (b : Bool) :
    branchNeighbors hn b (Fin.last n) 0 =
      ((⟨n - 1, by omega⟩, 0), (Fin.last n, ⟨1, by omega⟩)) := by
  unfold branchNeighbors; simp only [Fin.val_zero, Fin.val_last]; split_ifs <;> first | rfl | omega

theorem branchNeighbors_corner_last_last (hn : 1 ≤ n) (b : Bool) :
    branchNeighbors hn b (Fin.last n) (Fin.last n) =
      ((⟨n - 1, by omega⟩, Fin.last n), (Fin.last n, ⟨n - 1, by omega⟩)) := by
  unfold branchNeighbors; simp only [Fin.val_last]; split_ifs <;> first | rfl | omega

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

/-! ### Local octahedron rule, continuous/discrete recurrence, involutivity, and wall propagation -/

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

theorem even_add_one_of_odd {n : ℕ} {x y : Fin (n + 1)} {t : ℤ}
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : Even ((x.val : ℤ) + y.val + (t + 1)) := by
  obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by linarith⟩

theorem even_sub_one_of_odd {n : ℕ} {x y : Fin (n + 1)} {t : ℤ}
    (hodd : Odd ((x.val : ℤ) + y.val + t)) : Even ((x.val : ℤ) + y.val + (t - 1)) := by
  obtain ⟨k, hk⟩ := hodd; exact ⟨k, by linarith⟩

theorem even_of_gridAdj_of_odd {n : ℕ} {x y x' y' : Fin (n + 1)} {t : ℤ}
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
      even_of_gridAdj_of_odd htrue.1 hodd⟩ +
    f ⟨(branchNeighbors hn true x y).2.1, (branchNeighbors hn true x y).2.2, t,
      even_of_gridAdj_of_odd htrue.2 hodd⟩) ⊔
  (f ⟨(branchNeighbors hn false x y).1.1, (branchNeighbors hn false x y).1.2, t,
      even_of_gridAdj_of_odd hfalse.1 hodd⟩ +
    f ⟨(branchNeighbors hn false x y).2.1, (branchNeighbors hn false x y).2.2, t,
      even_of_gridAdj_of_odd hfalse.2 hodd⟩)

theorem paritySpatialSup_def [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n) (f : SpaceTimePoint n → R)
    (x y : Fin (n + 1)) (t : ℤ) (hodd : Odd ((x.val : ℤ) + y.val + t)) :
    paritySpatialSup hn f x y t hodd =
      (f ⟨(branchNeighbors hn true x y).1.1, (branchNeighbors hn true x y).1.2, t,
          even_of_gridAdj_of_odd (gridAdj_branchNeighbors hn true x y).1 hodd⟩ +
        f ⟨(branchNeighbors hn true x y).2.1, (branchNeighbors hn true x y).2.2, t,
          even_of_gridAdj_of_odd (gridAdj_branchNeighbors hn true x y).2 hodd⟩) ⊔
      (f ⟨(branchNeighbors hn false x y).1.1, (branchNeighbors hn false x y).1.2, t,
          even_of_gridAdj_of_odd (gridAdj_branchNeighbors hn false x y).1 hodd⟩ +
        f ⟨(branchNeighbors hn false x y).2.1, (branchNeighbors hn false x y).2.2, t,
          even_of_gridAdj_of_odd (gridAdj_branchNeighbors hn false x y).2 hodd⟩) := by
  unfold paritySpatialSup; rfl

theorem paritySpatialSup_congr [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    {f g : SpaceTimePoint n → R} {x y : Fin (n + 1)} {t₁ t₂ : ℤ}
    (hodd₁ : Odd ((x.val : ℤ) + y.val + t₁)) (hodd₂ : Odd ((x.val : ℤ) + y.val + t₂))
    (hfg : ∀ {x' y' : Fin (n + 1)} (hadj : GridAdj x y x' y'),
      f ⟨x', y', t₁, even_of_gridAdj_of_odd hadj hodd₁⟩ =
        g ⟨x', y', t₂, even_of_gridAdj_of_odd hadj hodd₂⟩) :
    paritySpatialSup hn f x y t₁ hodd₁ = paritySpatialSup hn g x y t₂ hodd₂ := by
  rw [paritySpatialSup_def, paritySpatialSup_def]
  have ht := gridAdj_branchNeighbors hn true x y
  have hf := gridAdj_branchNeighbors hn false x y
  rw [hfg ht.1, hfg ht.2, hfg hf.1, hfg hf.2]

theorem paritySpatialSup_eq_spatialSup_of_eq [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    {f : SpaceTimePoint n → R} {g : Fin (n + 1) → Fin (n + 1) → R}
    {x y : Fin (n + 1)} {t : ℤ} (hodd : Odd ((x.val : ℤ) + y.val + t))
    (hfg : ∀ {x' y' : Fin (n + 1)} (hadj : GridAdj x y x' y'),
      f ⟨x', y', t, even_of_gridAdj_of_odd hadj hodd⟩ = g x' y') :
    paritySpatialSup hn f x y t hodd = spatialSup hn g x y := by
  rw [paritySpatialSup_def, spatialSup_def, branchSum_apply, branchSum_apply]
  have ht := gridAdj_branchNeighbors hn true x y
  have hf := gridAdj_branchNeighbors hn false x y
  rw [hfg ht.1, hfg ht.2, hfg hf.1, hfg hf.2]

theorem paritySpatialSup_eq_spatialSup [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    (g : Fin (n + 1) → Fin (n + 1) → ℤ → R) (x y : Fin (n + 1)) (t : ℤ)
    (hodd : Odd ((x.val : ℤ) + y.val + t)) :
    paritySpatialSup hn (fun p => g p.x p.y p.t) x y t hodd =
      spatialSup hn (fun x' y' => g x' y' t) x y :=
  paritySpatialSup_eq_spatialSup_of_eq hn hodd fun _ => rfl

/-- Bounded modified octahedron recurrence on the discrete space-time parity lattice `Lₙ`. -/
def SatisfiesRecurrence [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    (f : SpaceTimePoint n → R) : Prop :=
  ∀ x y : Fin (n + 1), ∀ t : ℤ, ∀ hodd : Odd ((x.val : ℤ) + y.val + t),
    f ⟨x, y, t + 1, even_add_one_of_odd hodd⟩ =
      paritySpatialSup hn f x y t hodd - f ⟨x, y, t - 1, even_sub_one_of_odd hodd⟩

theorem satisfiesRecurrence_def [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    (f : SpaceTimePoint n → R) :
    SatisfiesRecurrence hn f ↔
      ∀ x y : Fin (n + 1), ∀ t : ℤ, ∀ hodd : Odd ((x.val : ℤ) + y.val + t),
        f ⟨x, y, t + 1, even_add_one_of_odd hodd⟩ =
          paritySpatialSup hn f x y t hodd - f ⟨x, y, t - 1, even_sub_one_of_odd hodd⟩ := by
  unfold SatisfiesRecurrence; rfl

/-- Restricting a continuous-time solution on `[0, n]² × ℝ` to `Lₙ` yields a parity-lattice
solution. -/
theorem SatisfiesRealTimeRecurrence.satisfiesRecurrence [SemilatticeSup R] {n : ℕ} {hn : 1 ≤ n}
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
@[simp] theorem satisfiesRecurrence_timeRev_iff [SemilatticeSup R] {n : ℕ} (hn : 1 ≤ n)
    (f : SpaceTimePoint n → R) :
    SatisfiesRecurrence hn (fun p => f p.timeRev) ↔ SatisfiesRecurrence hn f := by
  have hdir {g : SpaceTimePoint n → R} (hg : SatisfiesRecurrence hn g) :
      SatisfiesRecurrence hn (fun p => g p.timeRev) := by
    rw [satisfiesRecurrence_def]
    intro x y t hodd
    have hodd' : Odd ((x.val : ℤ) + y.val + (-t)) := by
      obtain ⟨k, hk⟩ := hodd; exact ⟨k - t, by linarith⟩
    have hstep := (satisfiesRecurrence_def hn g).mp hg x y (-t) hodd'
    have htop : (⟨x, y, t + 1, even_add_one_of_odd hodd⟩ : SpaceTimePoint n).timeRev =
        ⟨x, y, -t - 1, even_sub_one_of_odd hodd'⟩ := by
      ext <;> simp only [SpaceTimePoint.timeRev_x, SpaceTimePoint.timeRev_y,
        SpaceTimePoint.timeRev_t]; ring
    have hbot : (⟨x, y, t - 1, even_sub_one_of_odd hodd⟩ : SpaceTimePoint n).timeRev =
        ⟨x, y, -t + 1, even_add_one_of_odd hodd'⟩ := by
      ext <;> simp only [SpaceTimePoint.timeRev_x, SpaceTimePoint.timeRev_y,
        SpaceTimePoint.timeRev_t]; ring
    have hadj_rev {x' y' : Fin (n + 1)} (hadj : GridAdj x y x' y') :
        (⟨x', y', t, even_of_gridAdj_of_odd hadj hodd⟩ : SpaceTimePoint n).timeRev =
          ⟨x', y', -t, even_of_gridAdj_of_odd hadj hodd'⟩ := by
      ext <;> simp
    have hsup : paritySpatialSup hn (fun p => g p.timeRev) x y t hodd =
        paritySpatialSup hn g x y (-t) hodd' :=
      paritySpatialSup_congr hn hodd hodd' fun hadj => congrArg g (hadj_rev hadj)
    rw [htop, hbot, hsup, hstep, sub_sub_self]
  exact ⟨fun h => by simpa using hdir h, hdir⟩

/-- Along either horizontal wall `y = 0` or `y = n` (`0 < x < n`), the bounded recurrence satisfies
`f(x, y, t + 1) = f(x + 1, y, t) + f(x - 1, y, t) - f(x, y, t - 1)`, so differences along
characteristics propagate unchanged. -/
theorem SatisfiesRecurrence.sub_eq_sub_of_horizontal_wall [SemilatticeSup R] {n : ℕ} {hn : 1 ≤ n}
    {f : SpaceTimePoint n → R} (hf : SatisfiesRecurrence hn f)
    {x y : Fin (n + 1)} (hx0 : 0 < x.val) (hxn : x.val < n) (hyw : y.val = 0 ∨ y.val = n)
    {t : ℤ} (hodd : Odd ((x.val : ℤ) + y.val + t)) :
    f ⟨x, y, t + 1, even_add_one_of_odd hodd⟩ -
        f ⟨⟨x.val + 1, by omega⟩, y, t, even_of_gridAdj_of_odd gridAdj_add_one_left hodd⟩ =
      f ⟨⟨x.val - 1, by omega⟩, y, t,
          even_of_gridAdj_of_odd (gridAdj_sub_one_left hx0) hodd⟩ -
        f ⟨x, y, t - 1, even_sub_one_of_odd hodd⟩ := by
  classical
  let g : Fin (n + 1) → Fin (n + 1) → R := fun x' y' =>
    if hev : Even ((x'.val : ℤ) + y'.val + t) then f ⟨x', y', t, hev⟩ else 0
  have hg {x' y' : Fin (n + 1)} (hadj : GridAdj x y x' y') :
      f ⟨x', y', t, even_of_gridAdj_of_odd hadj hodd⟩ = g x' y' := by
    simp [g, even_of_gridAdj_of_odd hadj hodd]
  have hstep := (satisfiesRecurrence_def hn f).mp hf x y t hodd
  have hsup : paritySpatialSup hn f x y t hodd =
      f ⟨⟨x.val + 1, by omega⟩, y, t, even_of_gridAdj_of_odd gridAdj_add_one_left hodd⟩ +
        f ⟨⟨x.val - 1, by omega⟩, y, t,
          even_of_gridAdj_of_odd (gridAdj_sub_one_left hx0) hodd⟩ := by
    rw [paritySpatialSup_eq_spatialSup_of_eq hn hodd hg,
      spatialSup_of_horizontal_wall hn g hx0 hxn hyw,
      ← hg gridAdj_add_one_left, ← hg (gridAdj_sub_one_left hx0)]
  rw [hstep, hsup]; abel

end RecurrenceRule

/-! ### Finite dependency recursion from a section and state-transition bijections -/

section Evolution

variable {n : ℕ}

private def sectionMinHeight (τ : Section n) : ℤ :=
  (Finset.univ.image (fun q : Fin (n + 1) × Fin (n + 1) => τ q.1 q.2)).min'
    (Finset.univ_nonempty.image _)

private theorem sectionMinHeight_le (τ : Section n) (x y : Fin (n + 1)) :
    sectionMinHeight τ ≤ τ x y :=
  Finset.min'_le _ (τ x y) (Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩)

variable {R : Type*} [AddCommGroup R] [SemilatticeSup R]

/-- Finite dependency recursion in forward time from initial data `F` on `τ : Section n`. -/
def evolveFuture (hn : 1 ≤ n) (τ : Section n) (F : Fin (n + 1) → Fin (n + 1) → R)
    (x : Fin (n + 1)) (y : Fin (n + 1)) (t : ℤ) : R :=
  if _h : t ≤ τ x y then
    F x y
  else
    have _ht1 : (t - 1 - sectionMinHeight τ).toNat < (t - sectionMinHeight τ).toNat := by
      have := sectionMinHeight_le τ x y; omega
    have _ht2 : (t - 2 - sectionMinHeight τ).toNat < (t - sectionMinHeight τ).toNat := by
      have := sectionMinHeight_le τ x y; omega
    spatialSup hn (fun x' y' => evolveFuture hn τ F x' y' (t - 1)) x y -
      evolveFuture hn τ F x y (t - 2)
termination_by (t - sectionMinHeight τ).toNat

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

private theorem evolveFromSection_step_of_le (hn : 1 ≤ n) (τ : Section n)
    (F : Fin (n + 1) → Fin (n + 1) → R) {x y : Fin (n + 1)} {t : ℤ}
    (hodd : Odd ((x.val : ℤ) + y.val + t)) (hfut : τ x y ≤ t - 1) :
    evolveFromSection hn τ F ⟨x, y, t + 1, even_add_one_of_odd hodd⟩ =
      paritySpatialSup hn (evolveFromSection hn τ F) x y t hodd -
        evolveFromSection hn τ F ⟨x, y, t - 1, even_sub_one_of_odd hodd⟩ := by
  have htop : evolveFromSection hn τ F ⟨x, y, t + 1, even_add_one_of_odd hodd⟩ =
      evolveFuture hn τ F x y (t + 1) :=
    evolveFromSection_of_ge hn τ F (by dsimp; omega)
  have hbot : evolveFromSection hn τ F ⟨x, y, t - 1, even_sub_one_of_odd hodd⟩ =
      evolveFuture hn τ F x y (t - 1) :=
    evolveFromSection_of_ge hn τ F hfut
  have hsup : paritySpatialSup hn (evolveFromSection hn τ F) x y t hodd =
      spatialSup hn (fun x' y' => evolveFuture hn τ F x' y' t) x y :=
    paritySpatialSup_eq_spatialSup_of_eq hn hodd fun hadj =>
      evolveFromSection_of_ge hn τ F (by dsimp; have := τ.slope_eq_one hadj; omega)
  have ht12 : t + 1 - 2 = t - 1 := by ring
  rw [htop, hbot, hsup, evolveFuture_of_gt hn τ F (by omega), add_sub_cancel_right, ht12]

/-- `evolveFromSection hn τ F` satisfies the bounded octahedron recurrence everywhere on `Lₙ`. -/
theorem satisfiesRecurrence_evolveFromSection (hn : 1 ≤ n) (τ : Section n)
    (F : Fin (n + 1) → Fin (n + 1) → R) :
    SatisfiesRecurrence hn (evolveFromSection hn τ F) := by
  rw [satisfiesRecurrence_def]
  intro x y t hodd
  -- Parity of `x + y + τ x y` vs odd `x + y + t` forces `τ x y ≠ t`.
  obtain ⟨k₁, hk₁⟩ := id hodd
  obtain ⟨k₂, hk₂⟩ := τ.even_sum x y
  rcases (by omega : τ x y ≤ t - 1 ∨ t + 1 ≤ τ x y) with hfut | hpast
  · exact evolveFromSection_step_of_le hn τ F hodd hfut
  · -- Reduce the past half `{t + 1 ≤ τ x y}` to the future half on `τ.timeRev`.
    have hodd' : Odd ((x.val : ℤ) + y.val + (-t)) := ⟨k₁ - t, by linarith⟩
    have hrev := evolveFromSection_step_of_le hn τ.timeRev F hodd'
      (by rw [Section.timeRev_apply]; omega)
    have htop : (⟨x, y, -t + 1, even_add_one_of_odd hodd'⟩ : SpaceTimePoint n) =
        (⟨x, y, t - 1, even_sub_one_of_odd hodd⟩ : SpaceTimePoint n).timeRev := by
      ext <;> simp only [SpaceTimePoint.timeRev_x, SpaceTimePoint.timeRev_y,
        SpaceTimePoint.timeRev_t]; ring
    have hbot : (⟨x, y, -t - 1, even_sub_one_of_odd hodd'⟩ : SpaceTimePoint n) =
        (⟨x, y, t + 1, even_add_one_of_odd hodd⟩ : SpaceTimePoint n).timeRev := by
      ext <;> simp only [SpaceTimePoint.timeRev_x, SpaceTimePoint.timeRev_y,
        SpaceTimePoint.timeRev_t]; ring
    have hsup : paritySpatialSup hn (evolveFromSection hn τ.timeRev F) x y (-t) hodd' =
        paritySpatialSup hn (evolveFromSection hn τ F) x y t hodd :=
      paritySpatialSup_congr hn hodd' hodd fun hadj => by
        rw [← evolveFromSection_timeRev hn τ F ⟨_, _, t, even_of_gridAdj_of_odd hadj hodd⟩]
        congr 1; ext <;> simp
    rw [htop, hbot, evolveFromSection_timeRev, evolveFromSection_timeRev, hsup] at hrev
    rw [hrev, sub_sub_self]

/-- Uniqueness on any finite future region `{τ₁ ≤ t ≤ τ₂}`: two functions agreeing on `τ₁` and
satisfying the bounded recurrence at all odd centres strictly between `τ₁` and `τ₂` agree on every
point between `τ₁` and `τ₂`. -/
theorem eq_on_between_of_recurrence (hn : 1 ≤ n) {τ₁ τ₂ : Section n} {f g : SpaceTimePoint n → R}
    (hinit : ∀ x y, f (τ₁.point x y) = g (τ₁.point x y))
    (hrec : ∀ x y t (hodd : Odd ((x.val : ℤ) + y.val + t)),
      τ₁ x y < t + 1 → t + 1 ≤ τ₂ x y →
        f ⟨x, y, t + 1, even_add_one_of_odd hodd⟩ - g ⟨x, y, t + 1, even_add_one_of_odd hodd⟩ =
          (paritySpatialSup hn f x y t hodd - f ⟨x, y, t - 1, even_sub_one_of_odd hodd⟩) -
            (paritySpatialSup hn g x y t hodd - g ⟨x, y, t - 1, even_sub_one_of_odd hodd⟩)) :
    ∀ p : SpaceTimePoint n, τ₁ p.x p.y ≤ p.t → p.t ≤ τ₂ p.x p.y → f p = g p := by
  suffices ∀ m : ℕ, ∀ p : SpaceTimePoint n, (p.t - sectionMinHeight τ₁).toNat ≤ m →
      τ₁ p.x p.y ≤ p.t → p.t ≤ τ₂ p.x p.y → f p = g p by
    intro p h₁ h₂; exact this _ p le_rfl h₁ h₂
  intro m
  induction m with
  | zero =>
    intro p hm h₁ _
    have hmin := sectionMinHeight_le τ₁ p.x p.y
    have hteq : p.t = τ₁ p.x p.y := by omega
    have hp : p = τ₁.point p.x p.y := (τ₁.eq_point_iff).mpr ⟨rfl, rfl, hteq⟩
    rw [hp]; exact hinit p.x p.y
  | succ m ih =>
    intro p hm h₁ h₂
    by_cases hteq : p.t = τ₁ p.x p.y
    · have hp : p = τ₁.point p.x p.y := (τ₁.eq_point_iff).mpr ⟨rfl, rfl, hteq⟩
      rw [hp]; exact hinit p.x p.y
    · have hlt : τ₁ p.x p.y < p.t := lt_of_le_of_ne h₁ (Ne.symm hteq)
      obtain ⟨k₁, hk₁⟩ := p.even_sum
      obtain ⟨k₂, hk₂⟩ := τ₁.even_sum p.x p.y
      have hodd : Odd ((p.x.val : ℤ) + p.y.val + (p.t - 1)) := ⟨k₁ - 1, by linarith⟩
      have hbot_eq :
          f ⟨p.x, p.y, p.t - 1 - 1, even_sub_one_of_odd hodd⟩ =
            g ⟨p.x, p.y, p.t - 1 - 1, even_sub_one_of_odd hodd⟩ :=
        ih _ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
      have hadj_eq {x' y' : Fin (n + 1)} (hadj : GridAdj p.x p.y x' y') :
          f ⟨x', y', p.t - 1, even_of_gridAdj_of_odd hadj hodd⟩ =
            g ⟨x', y', p.t - 1, even_of_gridAdj_of_odd hadj hodd⟩ := by
        have hs1 := τ₁.slope_eq_one hadj
        have hs2 := τ₂.slope_eq_one hadj
        exact ih _ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
      have hsup_eq : paritySpatialSup hn f p.x p.y (p.t - 1) hodd =
          paritySpatialSup hn g p.x p.y (p.t - 1) hodd :=
        paritySpatialSup_congr hn hodd hodd hadj_eq
      have hstep := hrec p.x p.y (p.t - 1) hodd (by omega) (by omega)
      have hp_top :
          (⟨p.x, p.y, p.t - 1 + 1, even_add_one_of_odd hodd⟩ : SpaceTimePoint n) = p := by
        ext <;> simp
      rw [hp_top, hsup_eq, hbot_eq, sub_self] at hstep
      exact sub_eq_zero.mp hstep

private theorem eq_of_satisfiesRecurrence_of_ge (hn : 1 ≤ n) (σ : Section n)
    {f₁ f₂ : SpaceTimePoint n → R}
    (hf₁ : SatisfiesRecurrence hn f₁) (hf₂ : SatisfiesRecurrence hn f₂)
    (hinit : ∀ x y, f₁ (σ.point x y) = f₂ (σ.point x y))
    {p : SpaceTimePoint n} (hge : σ p.x p.y ≤ p.t) : f₁ p = f₂ p := by
  -- Shift `σ` upward by `2 * (p.t - σ p.x p.y)` to enclose `p` in a finite slab `{σ ≤ t ≤ σ_up}`.
  let σ_up : Section n :=
    Section.ofDistLeOne (fun x y => σ x y + 2 * (p.t - σ p.x p.y))
      (fun x y => by
        obtain ⟨k₁, hk₁⟩ := σ.even_sum x y
        exact ⟨k₁ + p.t - σ p.x p.y, by linarith⟩)
      (fun {x₁ y₁ x₂ y₂} hadj => by
        simpa [add_sub_add_comm] using (σ.abs_sub_eq_one hadj).le)
  exact eq_on_between_of_recurrence (τ₁ := σ) (τ₂ := σ_up) hn hinit
    (fun x y t hodd _ _ => by
      rw [(satisfiesRecurrence_def hn f₁).mp hf₁ x y t hodd,
        (satisfiesRecurrence_def hn f₂).mp hf₂ x y t hodd])
    p hge (by unfold σ_up; rw [Section.ofDistLeOne_apply]; omega)

/-- Global uniqueness: a solution of `SatisfiesRecurrence hn` is uniquely determined by its
values on any section `τ : Section n`. -/
theorem eq_evolveFromSection_of_satisfiesRecurrence (hn : 1 ≤ n) (τ : Section n)
    {f : SpaceTimePoint n → R} (hf : SatisfiesRecurrence hn f) :
    f = evolveFromSection hn τ (fun x y => f (τ.point x y)) := by
  funext p
  let g := evolveFromSection hn τ (fun x y => f (τ.point x y))
  have hg : SatisfiesRecurrence hn g := satisfiesRecurrence_evolveFromSection hn τ _
  have hinit (x y : Fin (n + 1)) : f (τ.point x y) = g (τ.point x y) :=
    (evolveFromSection_point hn τ (fun x y => f (τ.point x y)) x y).symm
  by_cases hge : τ p.x p.y ≤ p.t
  · exact eq_of_satisfiesRecurrence_of_ge hn τ hf hg hinit hge
  · -- Apply future uniqueness to the time-reversed solutions above `τ.timeRev`.
    have hrev := eq_of_satisfiesRecurrence_of_ge hn τ.timeRev
      ((satisfiesRecurrence_timeRev_iff hn f).mpr hf)
      ((satisfiesRecurrence_timeRev_iff hn g).mpr hg)
      (fun x y => by
        have hpt : (τ.timeRev.point x y).timeRev = τ.point x y := by ext <;> simp
        rw [hpt]; exact hinit x y)
      (p := p.timeRev) (by have := le_of_not_ge hge; simpa using this)
    simpa using hrev

/-- Equivalence between global solutions of the bounded recurrence on `Lₙ` and unrestricted
functions on any section `τ : Section n`. -/
def solutionEquivSection (hn : 1 ≤ n) (τ : Section n) :
    {f : SpaceTimePoint n → R // SatisfiesRecurrence hn f} ≃
      (Fin (n + 1) → Fin (n + 1) → R) where
  toFun f x y := f.val (τ.point x y)
  invFun F := ⟨evolveFromSection hn τ F, satisfiesRecurrence_evolveFromSection hn τ F⟩
  left_inv f := Subtype.ext (eq_evolveFromSection_of_satisfiesRecurrence hn τ f.property).symm
  right_inv F := by funext x y; simp

@[simp] theorem solutionEquivSection_apply (hn : 1 ≤ n) (τ : Section n)
    (f : {f : SpaceTimePoint n → R // SatisfiesRecurrence hn f}) (x y : Fin (n + 1)) :
    solutionEquivSection hn τ f x y = f.val (τ.point x y) := by
  unfold solutionEquivSection; rfl

@[simp] theorem solutionEquivSection_symm_apply (hn : 1 ≤ n) (τ : Section n)
    (F : Fin (n + 1) → Fin (n + 1) → R) :
    ((solutionEquivSection hn τ).symm F).val = evolveFromSection hn τ F := by
  unfold solutionEquivSection; rfl

/-- Section-to-section state-transition bijection induced by the bounded octahedron recurrence. -/
def sectionTransition (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    (Fin (n + 1) → Fin (n + 1) → R) ≃ (Fin (n + 1) → Fin (n + 1) → R) :=
  (solutionEquivSection hn τ₁).symm.trans (solutionEquivSection hn τ₂)

theorem sectionTransition_apply (hn : 1 ≤ n) (τ₁ τ₂ : Section n)
    (F : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    sectionTransition hn τ₁ τ₂ F x y = evolveFromSection hn τ₁ F (τ₂.point x y) := by
  simp [sectionTransition]

@[simp] theorem sectionTransition_refl (hn : 1 ≤ n) (τ : Section n) :
    sectionTransition (R := R) hn τ τ = Equiv.refl _ :=
  Equiv.symm_trans_self _

@[simp] theorem sectionTransition_symm (hn : 1 ≤ n) (τ₁ τ₂ : Section n) :
    (sectionTransition (R := R) hn τ₁ τ₂).symm = sectionTransition hn τ₂ τ₁ := by
  simp [sectionTransition, Equiv.symm_trans]

@[simp] theorem sectionTransition_trans (hn : 1 ≤ n) (τ₁ τ₂ τ₃ : Section n) :
    (sectionTransition (R := R) hn τ₁ τ₂).trans (sectionTransition hn τ₂ τ₃) =
      sectionTransition hn τ₁ τ₃ := by
  unfold sectionTransition
  rw [Equiv.trans_assoc, ← Equiv.trans_assoc (solutionEquivSection hn τ₂),
    Equiv.self_trans_symm, Equiv.refl_trans]

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
(in particular `Int.castAddHom ℚ`, `Int.castAddHom ℝ`, and `(Rat.castHom ℝ).toAddMonoidHom`). -/
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

/-- Nonnegative scaling equivariance of `sectionTransition` for any order-preserving distributive
scalar action (`0 ≤ c`, including `c = 0` and external scalars such as `ℕ`, `ℤ`, `ℚ`, or
`Nonneg S`). -/
theorem sectionTransition_smul_of_nonneg {n : ℕ} {S R : Type*} [Preorder S] [Zero S]
    [AddCommGroup R] [LinearOrder R] [DistribSMul S R] [PosSMulMono S R]
    (hn : 1 ≤ n) (τ₁ τ₂ : Section n) {c : S} (hc : 0 ≤ c)
    (F : Fin (n + 1) → Fin (n + 1) → R) :
    sectionTransition hn τ₁ τ₂ (c • F) = c • sectionTransition hn τ₁ τ₂ F := by
  ext x y
  exact (map_sectionTransition (DistribSMul.toAddMonoidHom R c) (smul_max_of_nonneg hc)
    hn τ₁ τ₂ F x y).symm

/-! ### Associator dependency closure, `n = 0` identity, and wall invariance -/

section Associator

/-- Every associator point `(x, y, t + 1) ∈ Aₙ` strictly above the lower section `S` lies strictly
in the interior `(0, n)²`, and all five of its recurrence dependencies stay inside `Aₙ`. -/
theorem associator_dependencies_mem {n : ℕ} {x y : Fin (n + 1)} {t : ℤ}
    (hodd : Odd ((x.val : ℤ) + y.val + t))
    (htop : (⟨x, y, t + 1, even_add_one_of_odd hodd⟩ : SpaceTimePoint n).IsAssociator)
    (hlt : lowerSection n x y < t + 1) :
    0 < x.val ∧ x.val < n ∧ 0 < y.val ∧ y.val < n ∧
      (⟨x, y, t - 1, even_sub_one_of_odd hodd⟩ : SpaceTimePoint n).IsAssociator ∧
      ∀ {x' y' : Fin (n + 1)} (hadj : GridAdj x y x' y'),
        (⟨x', y', t, even_of_gridAdj_of_odd hadj hodd⟩ : SpaceTimePoint n).IsAssociator := by
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

/-- Compatibility of `associatorTransition` with any additive group homomorphism preserving `⊔`,
for all `n : ℕ`. -/
theorem map_associatorTransition (n : ℕ) {R S : Type*} [AddCommGroup R] [SemilatticeSup R]
    [AddCommGroup S] [SemilatticeSup S] (φ : R →+ S)
    (hsup : ∀ u v : R, φ (u ⊔ v) = φ u ⊔ φ v)
    (F : Fin (n + 1) → Fin (n + 1) → R) (x y : Fin (n + 1)) :
    φ (associatorTransition n F x y) =
      associatorTransition n (fun x' y' => φ (F x' y')) x y := by
  by_cases hn : 1 ≤ n
  · rw [associatorTransition_of_one_le hn, associatorTransition_of_one_le hn]
    exact map_sectionTransition φ hsup hn (lowerSection n) (upperSection n) F x y
  · have hn0 : n = 0 := by omega
    subst hn0; simp

/-- Nonnegative scaling equivariance of `associatorTransition n` for all `n : ℕ` and `0 ≤ c`. -/
theorem associatorTransition_smul_of_nonneg (n : ℕ) {S R : Type*} [Preorder S] [Zero S]
    [AddCommGroup R] [LinearOrder R] [DistribSMul S R] [PosSMulMono S R]
    {c : S} (hc : 0 ≤ c) (F : Fin (n + 1) → Fin (n + 1) → R) :
    associatorTransition n (c • F) = c • associatorTransition n F := by
  ext x y
  exact (map_associatorTransition n (DistribSMul.toAddMonoidHom R c) (smul_max_of_nonneg hc)
    F x y).symm

end Associator

end TauCeti.Hive.Octahedron
