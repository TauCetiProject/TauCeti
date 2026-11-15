/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Order.Lattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The tetrahedral lattice, bounded space-time parity lattice, and sections

Combinatorial associativity of hive counts excavates a regular tetrahedron `Δ³ₙ` of edge length `n`
from its two input faces to its two output faces. This file constructs both lattice models of that
geometry and the exact dictionary between them:

1. **Tetrahedral lattice and unit subdivision** (`TetraVertex`, `IsUpTetrahedron`,
   `IsDownTetrahedron`, `IsUnitOctahedron`): nonnegative integer 4-tuples `(a, b, c, d)` of sum `n`,
   with unit upward tetrahedra (`m + 1 = n`), unit octahedra (`m + 2 = n`), and unit downward
   tetrahedra (`m + 3 = n`).
2. **Bounded space-time parity lattice** (`SpaceTimePoint`, `IsAssociator`, `AssociatorPoint`):
   Henriques–Kamnitzer's lattice `Lₙ = {(x, y, t) ∈ ℤ³ : 0 ≤ x, y ≤ n, x + y + t even}` and its
   associator region `Aₙ = {|x - y| ≤ t ≤ n - |n - x - y|}`, identified with `TetraVertex n` via
   `(a, b, c, d) ↦ (b + d, c + d, b + c)` (`TetraVertex.equivAssociator`).
3. **Sections** (`Section`, `lowerSection`, `upperSection`): graphs `τ : [0, n]² → ℤ` in the
   2-skeleton of `Lₙ` meeting every vertical line once, closed under time reversal and pointwise
   `max`/`min`. The lower and upper associator sections `S(x, y) = |x - y|` and
   `S'(x, y) = n - |n - x - y|` satisfy `S ≤ S'` with equality precisely along the four walls of
   `[0, n]²` (`lowerSection_eq_upperSection_iff`).

## Main definitions

* `TauCeti.Hive.Octahedron.TetraVertex`, `TauCeti.Hive.Octahedron.IsUpTetrahedron`,
  `TauCeti.Hive.Octahedron.IsDownTetrahedron`, `TauCeti.Hive.Octahedron.IsUnitOctahedron`:
  size-`n` tetrahedral lattice and its unit cells.
* `TauCeti.Hive.Octahedron.SpaceTimePoint`, `TauCeti.Hive.Octahedron.AssociatorPoint`,
  `TauCeti.Hive.Octahedron.TetraVertex.equivAssociator`: bounded parity lattice `Lₙ`, associator
  region `Aₙ`, and tetrahedral coordinate equivalence.
* `TauCeti.Hive.Octahedron.Section`, `TauCeti.Hive.Octahedron.lowerSection`,
  `TauCeti.Hive.Octahedron.upperSection`: sections in the 2-skeleton and the lower/upper associator
  sections `S`, `S'`.

## Main results

* `TauCeti.Hive.Octahedron.TetraVertex.equivAssociator`: `TetraVertex n ≃ AssociatorPoint n`.
* `TauCeti.Hive.Octahedron.IsUnitOctahedron.toSpaceTime_eq`: unit octahedra in `Δ³ₙ` map to the six
  parity-lattice neighbours around an interior odd centre `(x*, y*, t*)`.
* `TauCeti.Hive.Octahedron.lowerSection_eq_upperSection_iff`: `S(x, y) = S'(x, y)` iff `(x, y)` lies
  on one of the four walls of `[0, n]²`.

## References

* A. Henriques and J. Kamnitzer, *The octahedron recurrence and $\mathfrak{gl}_n$ crystals*,
  Adv. Math. **206** (2006), 211–249, §3.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §5.
-/

public section

namespace TauCeti.Hive.Octahedron

/-! ### The size-`n` tetrahedral lattice and its unit subdivision -/

/-- A nonnegative barycentric lattice point in the regular tetrahedron `Δ³ₙ` of edge length `n`. -/
@[ext]
structure TetraVertex (n : ℕ) where
  /-- First barycentric coordinate. -/
  a : ℕ
  /-- Second barycentric coordinate. -/
  b : ℕ
  /-- Third barycentric coordinate. -/
  c : ℕ
  /-- Fourth barycentric coordinate. -/
  d : ℕ
  /-- The four coordinates sum to `n`. -/
  sum_eq : a + b + c + d = n
  deriving DecidableEq

namespace TetraVertex

variable {n : ℕ}

/-- The four barycentric coordinates packaged as `Fin 4 → ℕ`. -/
def coord (p : TetraVertex n) : Fin 4 → ℕ := ![p.a, p.b, p.c, p.d]

@[simp] theorem coord_zero (p : TetraVertex n) : p.coord 0 = p.a := by unfold coord; rfl
@[simp] theorem coord_one (p : TetraVertex n) : p.coord 1 = p.b := by unfold coord; rfl
@[simp] theorem coord_two (p : TetraVertex n) : p.coord 2 = p.c := by unfold coord; rfl
@[simp] theorem coord_three (p : TetraVertex n) : p.coord 3 = p.d := by unfold coord; rfl

/-- Computable equivalence between `TetraVertex n` and `Finset.Nat.antidiagonalTuple 4 n`. -/
def equivAntidiagonalTuple : TetraVertex n ≃ ↥(Finset.Nat.antidiagonalTuple 4 n) where
  toFun p := ⟨p.coord, by
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [coord, Fin.sum_univ_succ, add_assoc] using p.sum_eq⟩
  invFun t := ⟨t.1 0, t.1 1, t.1 2, t.1 3, by
    have ht := Finset.Nat.mem_antidiagonalTuple.mp t.2
    simpa [Fin.sum_univ_succ, add_assoc] using ht⟩
  left_inv p := by ext <;> simp [coord]
  right_inv t := by apply Subtype.ext; funext i; fin_cases i <;> simp [coord]

instance : Fintype (TetraVertex n) := Fintype.ofEquiv _ equivAntidiagonalTuple.symm

instance uniqueZero : Unique (TetraVertex 0) where
  default := ⟨0, 0, 0, 0, rfl⟩
  uniq p := by have := p.sum_eq; ext <;> dsimp <;> omega

/-- Coordinatewise addition embedding translated subtetrahedra. -/
def add {m : ℕ} (p : TetraVertex n) (q : TetraVertex m) : TetraVertex (n + m) :=
  ⟨p.a + q.a, p.b + q.b, p.c + q.c, p.d + q.d, by have := p.sum_eq; have := q.sum_eq; omega⟩

@[simp] theorem add_a {m : ℕ} (p : TetraVertex n) (q : TetraVertex m) :
    (p.add q).a = p.a + q.a := by unfold add; rfl
@[simp] theorem add_b {m : ℕ} (p : TetraVertex n) (q : TetraVertex m) :
    (p.add q).b = p.b + q.b := by unfold add; rfl
@[simp] theorem add_c {m : ℕ} (p : TetraVertex n) (q : TetraVertex m) :
    (p.add q).c = p.c + q.c := by unfold add; rfl
@[simp] theorem add_d {m : ℕ} (p : TetraVertex n) (q : TetraVertex m) :
    (p.add q).d = p.d + q.d := by unfold add; rfl

end TetraVertex

/-- An upward unit tetrahedron in `Δ³ₙ`, obtained from a base vertex `p ∈ Δ³_{n-1}` by adding one
unit to each of the four barycentric coordinates. -/
def IsUpTetrahedron {n : ℕ} (v : Fin 4 → TetraVertex n) : Prop :=
  ∃ m : ℕ, ∃ p : TetraVertex m, m + 1 = n ∧
    ∀ i j : Fin 4, (v i).coord j = p.coord j + if i = j then 1 else 0

/-- A downward unit tetrahedron in `Δ³ₙ`, obtained from a base vertex `p ∈ Δ³_{n-3}` by adding
`1` to three of the four barycentric coordinates. -/
def IsDownTetrahedron {n : ℕ} (v : Fin 4 → TetraVertex n) : Prop :=
  ∃ m : ℕ, ∃ p : TetraVertex m, m + 3 = n ∧
    ∀ i j : Fin 4, (v i).coord j = p.coord j + if i = j then 0 else 1

/-- A unit octahedron in the tetrahedral subdivision of `Δ³ₙ`, parameterized by a base vertex
`p ∈ Δ³_{n-2}` and the six two-element subsets of the four coordinates, ordered as `(bot, top)`
along time and `(xp, xm)`, `(yp, ym)` along the two spatial axes. -/
def IsUnitOctahedron {n : ℕ} (bot top xp xm yp ym : TetraVertex n) : Prop :=
  ∃ m : ℕ, ∃ p : TetraVertex m, m + 2 = n ∧
    bot.coord = ![p.a + 1, p.b, p.c, p.d + 1] ∧
    top.coord = ![p.a, p.b + 1, p.c + 1, p.d] ∧
    xp.coord = ![p.a, p.b + 1, p.c, p.d + 1] ∧
    xm.coord = ![p.a + 1, p.b, p.c + 1, p.d] ∧
    yp.coord = ![p.a, p.b, p.c + 1, p.d + 1] ∧
    ym.coord = ![p.a + 1, p.b + 1, p.c, p.d]

/-! ### Bounded space-time parity lattice `Lₙ` and associator region `Aₙ` -/

/-- A point of Henriques–Kamnitzer's bounded space-time parity lattice
`Lₙ = {(x, y, t) ∈ ℤ³ : 0 ≤ x, y ≤ n, x + y + t even}`. -/
@[ext]
structure SpaceTimePoint (n : ℕ) where
  /-- First spatial coordinate in `{0, …, n}`. -/
  x : Fin (n + 1)
  /-- Second spatial coordinate in `{0, …, n}`. -/
  y : Fin (n + 1)
  /-- Discrete time coordinate. -/
  t : ℤ
  /-- Parity condition `x + y + t ≡ 0 (mod 2)`. -/
  even_sum : Even ((x.val : ℤ) + y.val + t)
  deriving DecidableEq

namespace SpaceTimePoint

variable {n : ℕ}

/-- Explicit comparison between `SpaceTimePoint n` and the integer subtype
`{(x, y, t) ∈ ℤ³ : 0 ≤ x, y ≤ n, x + y + t even}`. -/
def equivIntSubtype :
    SpaceTimePoint n ≃
      {v : ℤ × ℤ × ℤ //
        0 ≤ v.1 ∧ v.1 ≤ n ∧ 0 ≤ v.2.1 ∧ v.2.1 ≤ n ∧ Even (v.1 + v.2.1 + v.2.2)} where
  toFun p := ⟨(p.x.val, p.y.val, p.t),
    Nat.cast_nonneg _, Int.ofNat_le.mpr (Fin.is_le p.x),
    Nat.cast_nonneg _, Int.ofNat_le.mpr (Fin.is_le p.y), p.even_sum⟩
  invFun v := ⟨⟨v.1.1.toNat, by have := v.2.1; have := v.2.2.1; omega⟩,
    ⟨v.1.2.1.toNat, by have := v.2.2.2.1; have := v.2.2.2.2.1; omega⟩, v.1.2.2, by
    have hx : ((v.1.1.toNat : ℕ) : ℤ) = v.1.1 := Int.toNat_of_nonneg v.2.1
    have hy : ((v.1.2.1.toNat : ℕ) : ℤ) = v.1.2.1 := Int.toNat_of_nonneg v.2.2.2.1
    simpa [hx, hy] using v.2.2.2.2.2⟩
  left_inv p := by ext <;> simp
  right_inv v := by
    rcases v with ⟨⟨x, y, t⟩, hx0, _, hy0, _, _⟩
    ext <;> simp [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0]

/-- Time reversal `(x, y, t) ↦ (x, y, -t)` on `Lₙ`. -/
def timeRev (p : SpaceTimePoint n) : SpaceTimePoint n where
  x := p.x
  y := p.y
  t := -p.t
  even_sum := by
    obtain ⟨k, hk⟩ := p.even_sum
    exact ⟨k - p.t, by linarith⟩

@[simp] theorem timeRev_x (p : SpaceTimePoint n) : p.timeRev.x = p.x := by unfold timeRev; rfl
@[simp] theorem timeRev_y (p : SpaceTimePoint n) : p.timeRev.y = p.y := by unfold timeRev; rfl
@[simp] theorem timeRev_t (p : SpaceTimePoint n) : p.timeRev.t = -p.t := by unfold timeRev; rfl

@[simp] theorem timeRev_timeRev (p : SpaceTimePoint n) : p.timeRev.timeRev = p := by
  ext <;> simp

theorem timeRev_involutive : Function.Involutive (timeRev (n := n)) := timeRev_timeRev

/-- Membership in the associator region `Aₙ = {|x - y| ≤ t ≤ n - |n - x - y|}`. -/
def IsAssociator (p : SpaceTimePoint n) : Prop :=
  |(p.x.val : ℤ) - p.y.val| ≤ p.t ∧ p.t ≤ (n : ℤ) - |(n : ℤ) - p.x.val - p.y.val|

theorem isAssociator_def (p : SpaceTimePoint n) :
    p.IsAssociator ↔
      |(p.x.val : ℤ) - p.y.val| ≤ p.t ∧ p.t ≤ (n : ℤ) - |(n : ℤ) - p.x.val - p.y.val| := by
  unfold IsAssociator; rfl

instance (p : SpaceTimePoint n) : Decidable p.IsAssociator :=
  decidable_of_iff _ (isAssociator_def p).symm

theorem isAssociator_iff_four_ineq (p : SpaceTimePoint n) :
    p.IsAssociator ↔
      (p.x.val : ℤ) - p.y.val ≤ p.t ∧ (p.y.val : ℤ) - p.x.val ≤ p.t ∧
        p.t ≤ (p.x.val : ℤ) + p.y.val ∧ (p.x.val : ℤ) + p.y.val + p.t ≤ 2 * (n : ℤ) := by
  rw [isAssociator_def]
  simp only [Int.abs_eq_natAbs]
  omega

end SpaceTimePoint

/-- Points of the associator region `Aₙ = {|x - y| ≤ t ≤ n - |n - x - y|}` inside `Lₙ`. -/
abbrev AssociatorPoint (n : ℕ) := {p : SpaceTimePoint n // p.IsAssociator}

/-- Map a tetrahedral lattice point `(a, b, c, d) ∈ Δ³ₙ` to `(b + d, c + d, b + c) ∈ Lₙ`. -/
def TetraVertex.toSpaceTime {n : ℕ} (p : TetraVertex n) : SpaceTimePoint n where
  x := ⟨p.b + p.d, by have := p.sum_eq; omega⟩
  y := ⟨p.c + p.d, by have := p.sum_eq; omega⟩
  t := (p.b : ℤ) + p.c
  even_sum := ⟨p.b + p.c + p.d, by push_cast; ring⟩

@[simp] theorem TetraVertex.toSpaceTime_x_val {n : ℕ} (p : TetraVertex n) :
    p.toSpaceTime.x.val = p.b + p.d := by unfold toSpaceTime; rfl
@[simp] theorem TetraVertex.toSpaceTime_y_val {n : ℕ} (p : TetraVertex n) :
    p.toSpaceTime.y.val = p.c + p.d := by unfold toSpaceTime; rfl
@[simp] theorem TetraVertex.toSpaceTime_t {n : ℕ} (p : TetraVertex n) :
    p.toSpaceTime.t = (p.b : ℤ) + p.c := by unfold toSpaceTime; rfl

theorem TetraVertex.isAssociator_toSpaceTime {n : ℕ} (p : TetraVertex n) :
    p.toSpaceTime.IsAssociator := by
  rw [SpaceTimePoint.isAssociator_iff_four_ineq]
  have := p.sum_eq
  simp only [toSpaceTime_x_val, toSpaceTime_y_val, toSpaceTime_t, Nat.cast_add]
  omega

/-- Exact equivalence `TetraVertex n ≃ AssociatorPoint n` given by
`(a, b, c, d) ↦ (b + d, c + d, b + c)`. -/
def TetraVertex.equivAssociator (n : ℕ) : TetraVertex n ≃ AssociatorPoint n where
  toFun p := ⟨p.toSpaceTime, p.isAssociator_toSpaceTime⟩
  invFun q :=
    let x : ℤ := q.1.x.val
    let y : ℤ := q.1.y.val
    let t : ℤ := q.1.t
    ⟨((2 * (n : ℤ) - x - y - t) / 2).toNat,
     ((x - y + t) / 2).toNat,
     ((-x + y + t) / 2).toNat,
     ((x + y - t) / 2).toNat, by
      obtain ⟨k, hk⟩ := q.1.even_sum
      have h4 := (SpaceTimePoint.isAssociator_iff_four_ineq q.1).mp q.2
      omega⟩
  left_inv p := by
    have := p.sum_eq
    ext <;> simp [toSpaceTime] <;> omega
  right_inv q := by
    rcases q with ⟨p, hp⟩
    obtain ⟨k, hk⟩ := p.even_sum
    have h4 := (SpaceTimePoint.isAssociator_iff_four_ineq p).mp hp
    apply Subtype.ext
    ext <;> simp [toSpaceTime] <;> omega

instance {n : ℕ} : Fintype (AssociatorPoint n) :=
  Fintype.ofEquiv (TetraVertex n) (TetraVertex.equivAssociator n)

instance uniqueAssociatorPointZero : Unique (AssociatorPoint 0) :=
  (TetraVertex.equivAssociator 0).symm.unique

/-- Under `TetraVertex.toSpaceTime`, a unit octahedron in `Δ³ₙ` maps to the six parity-lattice
neighbours `(x*, y*, t* ± 1)`, `(x* ± 1, y*, t*)`, `(x*, y* ± 1, t*)` around an interior odd
centre `(x*, y*, t*)`. -/
theorem IsUnitOctahedron.toSpaceTime_eq {n : ℕ} {bot top xp xm yp ym : TetraVertex n}
    (ho : IsUnitOctahedron bot top xp xm yp ym) :
    ∃ x y t : ℤ, 0 < x ∧ x < n ∧ 0 < y ∧ y < n ∧ Odd (x + y + t) ∧
      ((bot.toSpaceTime.x.val : ℤ), (bot.toSpaceTime.y.val : ℤ), bot.toSpaceTime.t) =
        (x, y, t - 1) ∧
      ((top.toSpaceTime.x.val : ℤ), (top.toSpaceTime.y.val : ℤ), top.toSpaceTime.t) =
        (x, y, t + 1) ∧
      ((xp.toSpaceTime.x.val : ℤ), (xp.toSpaceTime.y.val : ℤ), xp.toSpaceTime.t) =
        (x + 1, y, t) ∧
      ((xm.toSpaceTime.x.val : ℤ), (xm.toSpaceTime.y.val : ℤ), xm.toSpaceTime.t) =
        (x - 1, y, t) ∧
      ((yp.toSpaceTime.x.val : ℤ), (yp.toSpaceTime.y.val : ℤ), yp.toSpaceTime.t) =
        (x, y + 1, t) ∧
      ((ym.toSpaceTime.x.val : ℤ), (ym.toSpaceTime.y.val : ℤ), ym.toSpaceTime.t) =
        (x, y - 1, t) := by
  obtain ⟨m, p, rfl, hbot, htop, hxp, hxm, hyp, hym⟩ := ho
  have coord_eq {q : TetraVertex (m + 2)} {a₀ b₀ c₀ d₀ : ℕ}
      (hq : q.coord = ![a₀, b₀, c₀, d₀]) : q.b = b₀ ∧ q.c = c₀ ∧ q.d = d₀ :=
    ⟨(TetraVertex.coord_one q).symm.trans (congrFun hq 1),
      (TetraVertex.coord_two q).symm.trans (congrFun hq 2),
      (TetraVertex.coord_three q).symm.trans (congrFun hq 3)⟩
  rcases coord_eq hbot with ⟨hbotb, hbotc, hbotd⟩
  rcases coord_eq htop with ⟨htopb, htopc, htopd⟩
  rcases coord_eq hxp with ⟨hxpb, hxpc, hxpd⟩
  rcases coord_eq hxm with ⟨hxmb, hxmc, hxmd⟩
  rcases coord_eq hyp with ⟨hypb, hypc, hypd⟩
  rcases coord_eq hym with ⟨hymb, hymc, hymd⟩
  refine ⟨(p.b : ℤ) + p.d + 1, (p.c : ℤ) + p.d + 1, (p.b : ℤ) + p.c + 1,
    by omega, by have := p.sum_eq; omega, by omega, by have := p.sum_eq; omega,
    ⟨p.b + p.c + p.d + 1, by ring⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, hbotb, hbotc, hbotd, Prod.mk.injEq]; omega
  · simp only [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, htopb, htopc, htopd, Prod.mk.injEq]; omega
  · simp only [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, hxpb, hxpc, hxpd, Prod.mk.injEq]; omega
  · simp only [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, hxmb, hxmc, hxmd, Prod.mk.injEq]; omega
  · simp only [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, hypb, hypc, hypd, Prod.mk.injEq]; omega
  · simp only [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, hymb, hymc, hymd, Prod.mk.injEq]; omega

/-- Under `TetraVertex.toSpaceTime`, an upward unit tetrahedron with base `p ∈ Δ³_{n-1}` maps to
`(x, y, t)`, `(x + 1, y, t + 1)`, `(x, y + 1, t + 1)`, `(x + 1, y + 1, t)` in `Lₙ`. -/
theorem IsUpTetrahedron.toSpaceTime_eq {n : ℕ} {v : Fin 4 → TetraVertex n}
    (hu : IsUpTetrahedron v) :
    ∃ x y t : ℤ,
      (((v 0).toSpaceTime.x.val : ℤ), ((v 0).toSpaceTime.y.val : ℤ), (v 0).toSpaceTime.t) =
        (x, y, t) ∧
      (((v 1).toSpaceTime.x.val : ℤ), ((v 1).toSpaceTime.y.val : ℤ), (v 1).toSpaceTime.t) =
        (x + 1, y, t + 1) ∧
      (((v 2).toSpaceTime.x.val : ℤ), ((v 2).toSpaceTime.y.val : ℤ), (v 2).toSpaceTime.t) =
        (x, y + 1, t + 1) ∧
      (((v 3).toSpaceTime.x.val : ℤ), ((v 3).toSpaceTime.y.val : ℤ), (v 3).toSpaceTime.t) =
        (x + 1, y + 1, t) := by
  obtain ⟨m, p, rfl, hv⟩ := hu
  have hb (i : Fin 4) : (v i).b = p.b + if i = 1 then 1 else 0 := by simpa using hv i 1
  have hc (i : Fin 4) : (v i).c = p.c + if i = 2 then 1 else 0 := by simpa using hv i 2
  have hd (i : Fin 4) : (v i).d = p.d + if i = 3 then 1 else 0 := by simpa using hv i 3
  refine ⟨(p.b : ℤ) + p.d, (p.c : ℤ) + p.d, (p.b : ℤ) + p.c, ?_, ?_, ?_, ?_⟩
  · simp [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, hb, hc, hd]
  · simp [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, hb, hc, hd]; omega
  · simp [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, hb, hc, hd]; omega
  · simp [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, hb, hc, hd]; omega

/-- Under `TetraVertex.toSpaceTime`, a downward unit tetrahedron with base `p ∈ Δ³_{n-3}` maps to
`(x + 2, y + 2, t + 2)`, `(x + 1, y + 2, t + 1)`, `(x + 2, y + 1, t + 1)`, `(x + 1, y + 1, t + 2)`
in `Lₙ`. -/
theorem IsDownTetrahedron.toSpaceTime_eq {n : ℕ} {v : Fin 4 → TetraVertex n}
    (hdn : IsDownTetrahedron v) :
    ∃ x y t : ℤ,
      (((v 0).toSpaceTime.x.val : ℤ), ((v 0).toSpaceTime.y.val : ℤ), (v 0).toSpaceTime.t) =
        (x + 2, y + 2, t + 2) ∧
      (((v 1).toSpaceTime.x.val : ℤ), ((v 1).toSpaceTime.y.val : ℤ), (v 1).toSpaceTime.t) =
        (x + 1, y + 2, t + 1) ∧
      (((v 2).toSpaceTime.x.val : ℤ), ((v 2).toSpaceTime.y.val : ℤ), (v 2).toSpaceTime.t) =
        (x + 2, y + 1, t + 1) ∧
      (((v 3).toSpaceTime.x.val : ℤ), ((v 3).toSpaceTime.y.val : ℤ), (v 3).toSpaceTime.t) =
        (x + 1, y + 1, t + 2) := by
  obtain ⟨m, p, rfl, hv⟩ := hdn
  have hb (i : Fin 4) : (v i).b = p.b + if i = 1 then 0 else 1 := by simpa using hv i 1
  have hc (i : Fin 4) : (v i).c = p.c + if i = 2 then 0 else 1 := by simpa using hv i 2
  have hd (i : Fin 4) : (v i).d = p.d + if i = 3 then 0 else 1 := by simpa using hv i 3
  refine ⟨(p.b : ℤ) + p.d, (p.c : ℤ) + p.d, (p.b : ℤ) + p.c, ?_, ?_, ?_, ?_⟩ <;>
    (simp [TetraVertex.toSpaceTime_x_val, TetraVertex.toSpaceTime_y_val,
      TetraVertex.toSpaceTime_t, hb, hc, hd]; omega)

/-- At `n = 1`, `Δ³₁` itself is an upward unit tetrahedron. -/
theorem exists_isUpTetrahedron_one : ∃ v : Fin 4 → TetraVertex 1, IsUpTetrahedron v := by
  refine ⟨![⟨1, 0, 0, 0, rfl⟩, ⟨0, 1, 0, 0, rfl⟩, ⟨0, 0, 1, 0, rfl⟩, ⟨0, 0, 0, 1, rfl⟩],
    0, default, rfl, ?_⟩
  intro i j; fin_cases i <;> fin_cases j <;> rfl

/-- At `n = 2`, `Δ³₂` contains a central unit octahedron. -/
theorem exists_isUnitOctahedron_two :
    ∃ bot top xp xm yp ym : TetraVertex 2, IsUnitOctahedron bot top xp xm yp ym :=
  ⟨⟨1, 0, 0, 1, rfl⟩, ⟨0, 1, 1, 0, rfl⟩, ⟨0, 1, 0, 1, rfl⟩, ⟨1, 0, 1, 0, rfl⟩,
    ⟨0, 0, 1, 1, rfl⟩, ⟨1, 1, 0, 0, rfl⟩, 0, default, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At `n = 3`, `Δ³₃` contains an interior downward unit tetrahedron. -/
theorem exists_isDownTetrahedron_three : ∃ v : Fin 4 → TetraVertex 3, IsDownTetrahedron v := by
  refine ⟨![⟨0, 1, 1, 1, rfl⟩, ⟨1, 0, 1, 1, rfl⟩, ⟨1, 1, 0, 1, rfl⟩, ⟨1, 1, 1, 0, rfl⟩],
    0, default, rfl, ?_⟩
  intro i j; fin_cases i <;> fin_cases j <;> rfl

/-! ### Grid adjacency, walls, and sections in the 2-skeleton -/

/-- Horizontal or vertical unit adjacency in `[0, n]²`. -/
def GridAdj {n : ℕ} (x₁ y₁ x₂ y₂ : Fin (n + 1)) : Prop :=
  ((x₁.val : ℤ) - x₂.val).natAbs + ((y₁.val : ℤ) - y₂.val).natAbs = 1

theorem gridAdj_def {n : ℕ} (x₁ y₁ x₂ y₂ : Fin (n + 1)) :
    GridAdj x₁ y₁ x₂ y₂ ↔
      ((x₁.val : ℤ) - x₂.val).natAbs + ((y₁.val : ℤ) - y₂.val).natAbs = 1 := by
  unfold GridAdj; rfl

instance {n : ℕ} (x₁ y₁ x₂ y₂ : Fin (n + 1)) : Decidable (GridAdj x₁ y₁ x₂ y₂) :=
  decidable_of_iff _ (gridAdj_def x₁ y₁ x₂ y₂).symm

theorem GridAdj.symm {n : ℕ} {x₁ y₁ x₂ y₂ : Fin (n + 1)} (h : GridAdj x₁ y₁ x₂ y₂) :
    GridAdj x₂ y₂ x₁ y₁ := by
  rw [gridAdj_def] at h ⊢; omega

/-- A grid point `(x, y) ∈ [0, n]²` lies on one of the four boundary walls. -/
def IsWall {n : ℕ} (x y : Fin (n + 1)) : Prop :=
  x.val = 0 ∨ x.val = n ∨ y.val = 0 ∨ y.val = n

theorem isWall_def {n : ℕ} (x y : Fin (n + 1)) :
    IsWall x y ↔ x.val = 0 ∨ x.val = n ∨ y.val = 0 ∨ y.val = n := by
  unfold IsWall; rfl

instance {n : ℕ} (x y : Fin (n + 1)) : Decidable (IsWall x y) :=
  decidable_of_iff _ (isWall_def x y).symm

theorem not_isWall_iff {n : ℕ} {x y : Fin (n + 1)} :
    ¬ IsWall x y ↔ 0 < x.val ∧ x.val < n ∧ 0 < y.val ∧ y.val < n := by
  have := x.isLt; have := y.isLt; rw [isWall_def]; omega

/-- A **section** in the 2-skeleton of `Lₙ`: a height function `τ : [0, n]² → ℤ` meeting each
vertical line at a point `(x, y, τ x y) ∈ Lₙ` and changing by `±1` across every unit grid edge. -/
structure Section (n : ℕ) where
  /-- Height on `[0, n]²`. -/
  height : Fin (n + 1) → Fin (n + 1) → ℤ
  /-- Every point `(x, y, height x y)` lies in the parity lattice `Lₙ`. -/
  even_sum' : ∀ x y : Fin (n + 1), Even ((x.val : ℤ) + y.val + height x y)
  /-- Unit grid steps change height by `±1` so edges lie in the 2-skeleton. -/
  slope_eq_one' : ∀ {x₁ y₁ x₂ y₂ : Fin (n + 1)},
    GridAdj x₁ y₁ x₂ y₂ → (height x₁ y₁ - height x₂ y₂).natAbs = 1

namespace Section

variable {n : ℕ}

instance instFunLike : FunLike (Section n) (Fin (n + 1)) (Fin (n + 1) → ℤ) where
  coe := Section.height
  coe_injective τ₁ τ₂ h := by cases τ₁; cases τ₂; congr

@[simp] theorem height_eq_coe (τ : Section n) : τ.height = ⇑τ := rfl

@[ext] theorem ext {τ₁ τ₂ : Section n} (h : ∀ x y, τ₁ x y = τ₂ x y) : τ₁ = τ₂ :=
  DFunLike.ext τ₁ τ₂ fun x => funext (h x)

instance : DecidableEq (Section n) := fun τ₁ τ₂ =>
  decidable_of_iff (∀ x y, τ₁ x y = τ₂ x y) ⟨ext, fun h x y => by rw [h]⟩

@[simp] theorem mk_apply (f : Fin (n + 1) → Fin (n + 1) → ℤ) (he hs) (x y : Fin (n + 1)) :
    (⟨f, he, hs⟩ : Section n) x y = f x y := rfl

theorem even_sum (τ : Section n) (x y : Fin (n + 1)) : Even ((x.val : ℤ) + y.val + τ x y) :=
  τ.even_sum' x y

theorem slope_eq_one (τ : Section n) {x₁ y₁ x₂ y₂ : Fin (n + 1)} (hadj : GridAdj x₁ y₁ x₂ y₂) :
    (τ x₁ y₁ - τ x₂ y₂).natAbs = 1 :=
  τ.slope_eq_one' hadj

theorem abs_sub_eq_one (τ : Section n) {x₁ y₁ x₂ y₂ : Fin (n + 1)} (hadj : GridAdj x₁ y₁ x₂ y₂) :
    |τ x₁ y₁ - τ x₂ y₂| = 1 := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast τ.slope_eq_one hadj

/-- Construct a `Section n` from parity and the 1-Lipschitz bound `|f x₁ y₁ - f x₂ y₂| ≤ 1`:
parity rules out `0`, forcing exact unit slope. -/
def ofDistLeOne (f : Fin (n + 1) → Fin (n + 1) → ℤ)
    (heven : ∀ x y : Fin (n + 1), Even ((x.val : ℤ) + y.val + f x y))
    (hlip : ∀ {x₁ y₁ x₂ y₂ : Fin (n + 1)},
      GridAdj x₁ y₁ x₂ y₂ → |f x₁ y₁ - f x₂ y₂| ≤ 1) : Section n where
  height := f
  even_sum' := heven
  slope_eq_one' {x₁ y₁ x₂ y₂} hadj := by
    obtain ⟨k₁, hk₁⟩ := heven x₁ y₁
    obtain ⟨k₂, hk₂⟩ := heven x₂ y₂
    have hle := hlip hadj
    rw [Int.abs_eq_natAbs] at hle
    rw [gridAdj_def] at hadj
    omega

@[simp] theorem ofDistLeOne_apply (f : Fin (n + 1) → Fin (n + 1) → ℤ) (heven hlip)
    (x y : Fin (n + 1)) : ofDistLeOne f heven hlip x y = f x y := by
  unfold ofDistLeOne; rfl

/-- The point `(x, y, τ x y) ∈ Lₙ` on the graph of `τ` above `(x, y)`. -/
def point (τ : Section n) (x y : Fin (n + 1)) : SpaceTimePoint n :=
  ⟨x, y, τ x y, τ.even_sum x y⟩

@[simp] theorem point_x (τ : Section n) (x y : Fin (n + 1)) : (τ.point x y).x = x := by
  unfold point; rfl
@[simp] theorem point_y (τ : Section n) (x y : Fin (n + 1)) : (τ.point x y).y = y := by
  unfold point; rfl
@[simp] theorem point_t (τ : Section n) (x y : Fin (n + 1)) : (τ.point x y).t = τ x y := by
  unfold point; rfl

/-- Every vertical line `{(x, y)} × ℤ` meets the graph of `τ` in the unique point `τ.point x y`. -/
theorem eq_point_iff (τ : Section n) {p : SpaceTimePoint n} {x y : Fin (n + 1)} :
    (p.x = x ∧ p.y = y ∧ p.t = τ p.x p.y) ↔ p = τ.point x y := by
  constructor
  · rintro ⟨rfl, rfl, ht⟩; ext <;> simp [ht]
  · rintro rfl; simp

/-- Time-reversed section `(x, y) ↦ -τ x y`. -/
def timeRev (τ : Section n) : Section n where
  height x y := -τ x y
  even_sum' x y := (τ.point x y).timeRev.even_sum
  slope_eq_one' {x₁ y₁ x₂ y₂} hadj := by
    have := τ.slope_eq_one hadj; omega

@[simp] theorem timeRev_apply (τ : Section n) (x y : Fin (n + 1)) :
    τ.timeRev x y = -τ x y := by unfold timeRev; rfl

@[simp] theorem timeRev_timeRev (τ : Section n) : τ.timeRev.timeRev = τ := by
  ext x y; simp

instance : PartialOrder (Section n) where
  le τ₁ τ₂ := ∀ x y, τ₁ x y ≤ τ₂ x y
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ x y := (h₁ x y).trans (h₂ x y)
  le_antisymm _ _ h₁ h₂ := ext fun x y => le_antisymm (h₁ x y) (h₂ x y)

theorem le_def {τ₁ τ₂ : Section n} : τ₁ ≤ τ₂ ↔ ∀ x y, τ₁ x y ≤ τ₂ x y := Iff.rfl

instance (τ₁ τ₂ : Section n) : Decidable (τ₁ ≤ τ₂) :=
  decidable_of_iff (∀ x y, τ₁ x y ≤ τ₂ x y) le_def.symm

@[simp] theorem timeRev_le_timeRev {τ₁ τ₂ : Section n} :
    τ₁.timeRev ≤ τ₂.timeRev ↔ τ₂ ≤ τ₁ := by
  simp [le_def]

/-- Pointwise maximum of two sections. -/
protected def sup (τ₁ τ₂ : Section n) : Section n :=
  ofDistLeOne (fun x y => max (τ₁ x y) (τ₂ x y))
    (fun x y => by
      rcases le_total (τ₁ x y) (τ₂ x y) with h | h
      · rw [max_eq_right h]; exact τ₂.even_sum x y
      · rw [max_eq_left h]; exact τ₁.even_sum x y)
    (fun {x₁ y₁ x₂ y₂} hadj => by
      have h₁ := τ₁.slope_eq_one hadj
      have h₂ := τ₂.slope_eq_one hadj
      rw [Int.abs_eq_natAbs]; omega)

/-- Pointwise minimum of two sections. -/
protected def inf (τ₁ τ₂ : Section n) : Section n :=
  ofDistLeOne (fun x y => min (τ₁ x y) (τ₂ x y))
    (fun x y => by
      rcases le_total (τ₁ x y) (τ₂ x y) with h | h
      · rw [min_eq_left h]; exact τ₁.even_sum x y
      · rw [min_eq_right h]; exact τ₂.even_sum x y)
    (fun {x₁ y₁ x₂ y₂} hadj => by
      have h₁ := τ₁.slope_eq_one hadj
      have h₂ := τ₂.slope_eq_one hadj
      rw [Int.abs_eq_natAbs]; omega)

instance : Lattice (Section n) where
  sup := Section.sup
  le_sup_left τ₁ τ₂ := by rw [le_def]; intro x y; unfold Section.sup; simp
  le_sup_right τ₁ τ₂ := by rw [le_def]; intro x y; unfold Section.sup; simp
  sup_le τ₁ τ₂ τ₃ h₁ h₂ := by
    rw [le_def] at h₁ h₂ ⊢; intro x y; unfold Section.sup; simp [h₁ x y, h₂ x y]
  inf := Section.inf
  inf_le_left τ₁ τ₂ := by rw [le_def]; intro x y; unfold Section.inf; simp
  inf_le_right τ₁ τ₂ := by rw [le_def]; intro x y; unfold Section.inf; simp
  le_inf τ₁ τ₂ τ₃ h₁ h₂ := by
    rw [le_def] at h₁ h₂ ⊢; intro x y; unfold Section.inf; simp [h₁ x y, h₂ x y]

@[simp] theorem sup_apply (τ₁ τ₂ : Section n) (x y : Fin (n + 1)) :
    (τ₁ ⊔ τ₂) x y = max (τ₁ x y) (τ₂ x y) := by
  -- Reduce the `Lattice` `⊔` projection to `Section.sup` before unfolding.
  change Section.sup τ₁ τ₂ x y = _
  unfold Section.sup
  exact ofDistLeOne_apply _ _ _ x y

@[simp] theorem inf_apply (τ₁ τ₂ : Section n) (x y : Fin (n + 1)) :
    (τ₁ ⊓ τ₂) x y = min (τ₁ x y) (τ₂ x y) := by
  -- Reduce the `Lattice` `⊓` projection to `Section.inf` before unfolding.
  change Section.inf τ₁ τ₂ x y = _
  unfold Section.inf
  exact ofDistLeOne_apply _ _ _ x y

end Section

/-- The lower associator section `S(x, y) = |x - y|`. -/
def lowerSection (n : ℕ) : Section n :=
  Section.ofDistLeOne (fun x y => |(x.val : ℤ) - y.val|)
    (fun x y => by
      rcases le_total (x.val : ℤ) y.val with h | h
      · rw [abs_of_nonpos (by omega)]; exact ⟨y.val, by ring⟩
      · rw [abs_of_nonneg (by omega)]; exact ⟨x.val, by ring⟩)
    (fun {x₁ y₁ x₂ y₂} hadj => by
      rw [gridAdj_def] at hadj; simp only [Int.abs_eq_natAbs]; omega)

@[simp] theorem lowerSection_apply (n : ℕ) (x y : Fin (n + 1)) :
    lowerSection n x y = |(x.val : ℤ) - y.val| := by
  unfold lowerSection; exact Section.ofDistLeOne_apply _ _ _ x y

/-- The upper associator section `S'(x, y) = n - |n - x - y|`. -/
def upperSection (n : ℕ) : Section n :=
  Section.ofDistLeOne (fun x y => (n : ℤ) - |(n : ℤ) - x.val - y.val|)
    (fun x y => by
      rcases le_total ((n : ℤ) - x.val - y.val) 0 with h | h
      · rw [abs_of_nonpos h]; exact ⟨n, by ring⟩
      · rw [abs_of_nonneg h]; exact ⟨x.val + y.val, by ring⟩)
    (fun {x₁ y₁ x₂ y₂} hadj => by
      rw [gridAdj_def] at hadj; simp only [Int.abs_eq_natAbs]; omega)

@[simp] theorem upperSection_apply (n : ℕ) (x y : Fin (n + 1)) :
    upperSection n x y = (n : ℤ) - |(n : ℤ) - x.val - y.val| := by
  unfold upperSection; exact Section.ofDistLeOne_apply _ _ _ x y

theorem lowerSection_le_upperSection (n : ℕ) : lowerSection n ≤ upperSection n := by
  rw [Section.le_def]; intro x y
  have := x.isLt; have := y.isLt
  simp only [lowerSection_apply, upperSection_apply, Int.abs_eq_natAbs]; omega

theorem isAssociator_iff_between {n : ℕ} (p : SpaceTimePoint n) :
    p.IsAssociator ↔ lowerSection n p.x p.y ≤ p.t ∧ p.t ≤ upperSection n p.x p.y := by
  rw [SpaceTimePoint.isAssociator_def]
  simp only [lowerSection_apply, upperSection_apply]

/-- `S(x, y) = S'(x, y)` precisely on the four boundary walls of `[0, n]²`. -/
theorem lowerSection_eq_upperSection_iff {n : ℕ} (x y : Fin (n + 1)) :
    lowerSection n x y = upperSection n x y ↔ IsWall x y := by
  have := x.isLt; have := y.isLt
  rw [isWall_def]
  simp only [lowerSection_apply, upperSection_apply, Int.abs_eq_natAbs]; omega

@[simp] theorem lowerSection_zero_eq_upperSection_zero : lowerSection 0 = upperSection 0 := by
  ext x y; fin_cases x; fin_cases y; simp

/-- Every associator point above a boundary wall already lies on both `S` and `S'`. -/
theorem eq_lowerSection_of_isAssociator_of_isWall {n : ℕ} {p : SpaceTimePoint n}
    (hp : p.IsAssociator) (hw : IsWall p.x p.y) :
    p.t = lowerSection n p.x p.y ∧ p.t = upperSection n p.x p.y := by
  rw [isAssociator_iff_between] at hp
  have heq := (lowerSection_eq_upperSection_iff p.x p.y).mpr hw
  exact ⟨le_antisymm (hp.2.trans heq.symm.le) hp.1, le_antisymm hp.2 (heq ▸ hp.1)⟩

/-- Any associator point strictly above `S` lies strictly in the interior `(0, n)²`. -/
theorem not_isWall_of_isAssociator_of_lt {n : ℕ} {p : SpaceTimePoint n}
    (hp : p.IsAssociator) (hlt : lowerSection n p.x p.y < p.t) : ¬ IsWall p.x p.y := fun hw =>
  hlt.ne (eq_lowerSection_of_isAssociator_of_isWall hp hw).1.symm

end TauCeti.Hive.Octahedron
