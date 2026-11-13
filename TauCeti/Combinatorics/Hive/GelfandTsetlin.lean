/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Weight
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The hive-to-Gelfand–Tsetlin difference map and its reconstruction

In the product chart `Vertex.ofChart n i j hij hj = ⟨n - j, j - i, i, _⟩` (`0 ≤ i ≤ j ≤ n`, with
inverse `p ↦ (p.z, n - p.x)`), a normalized integer hive `h : IntegerHive n` with clockwise
boundary `productBoundary lam μ γ = ![lam.1, μ.1, γ.dual.1]` satisfies

* `h(0, j) = ∑_{r < j} λ_r` along `A → B` (`s = 0`),
* `h(i, n) = |λ| + ∑_{r < i} μ_r` along `B → C` (`s = 1`), and
* `h(j, j) = ∑_{r < j} γ_r` along `C → A` (`s = 2`),

with `h(0, 0) = 0` at `A = (n, 0, 0)`. Every unit rhombus in `Vertex n` belongs, up to exchanging
opposite acute or obtuse corners, to one of three families in this chart
(`isRhombusConcave_iff_ofChart`):

1. `h(i + 1, j) + h(i, j + 1) ≤ h(i, j) + h(i + 1, j + 1)` (`0 ≤ i < j < n`),
2. `h(i, j) + h(i + 2, j + 1) ≤ h(i + 1, j) + h(i + 1, j + 1)` (`0 ≤ i < j < n`),
3. `h(i, j) + h(i + 1, j + 2) ≤ h(i, j + 1) + h(i + 1, j + 1)` (`0 ≤ i ≤ j`, `j + 2 ≤ n`).

Taking directional first differences `P i j = h(i + 1, j) - h(i, j)` on the informative cells
`0 ≤ i < j ≤ n` (and `0` elsewhere) turns the first two families into the Gelfand–Tsetlin
interlacing inequalities `P i j ≤ P i (j + 1)` and `P (i + 1) (j + 1) ≤ P i j`, assembling a
signed Gelfand–Tsetlin pattern `h.toGTPattern : GTPattern n` with top row `μ` and torus weight
`γ - λ`. Summing back from side `0` recovers every hive value via the completion formula

`gtCompletion lam P i j = gtBoundaryPrefix lam.1 j + ∑ k ∈ Finset.range i, P k j`

(`apply_eq_gtCompletion`), and a pattern `P` with top row `μ` and weight `γ - λ` comes from a hive
with boundary `productBoundary lam μ γ` if and only if `gtCompletion lam P` satisfies the third
rhombus family (`IsGTCompletable lam P`, `fixedIntegerHiveEquivGTPattern`, `gt_reconstruction_iff`).

Rotating twice (`h ↦ h.rotate.rotate`, which adds the constant gauge offset `∑ r, ν.1 r` in chart
coordinates) identifies hives of cyclic boundary `![lam.1, μ.1, ν.1]` with hives of boundary
`productBoundary ν lam μ.dual`, yielding the quasi-hive characterization with top row `lam` and
weight `μ.dual - ν` (`cyclicFixedIntegerHiveEquivGTPattern`). When the side-`0` weight satisfies
the uniform input gap `μ₀ - μₙ₋₁ ≤ λᵣ - λᵣ₊₁` for all `r`, the third rhombus family holds
automatically (`gt_completion_of_uniform_input_gap`), so the difference map becomes an equivalence
onto the entire weight-`(γ - λ)` Gelfand–Tsetlin fibre over `μ` (`stableGTPatternEquiv`,
`exists_stable_gt_equiv`). Outside the stable range, rank-`2` and rank-`3` examples show that the
remaining rhombus inequalities strictly cut down the weight fibre.

## Main definitions

* `TauCeti.Hive.Vertex.ofChart`: product chart `(i, j) ↦ ⟨n - j, j - i, i⟩` on `Vertex n`.
* `TauCeti.Hive.gtBoundaryPrefix`: leading partial sum `∑_{r < j} l r` of `l : Fin n → R`.
* `TauCeti.Hive.toGTPattern`, `TauCeti.Hive.toGTPatternAddMonoidHom`: directional difference map
  `IntegerHive n →+ GTPattern n`.
* `TauCeti.Hive.gtCompletion`, `TauCeti.Hive.IsGTCompletable`, `TauCeti.Hive.ofGTPattern`: chart
  completion, the remaining rhombus predicate, and hive reconstruction from `(lam, P)`.
* `TauCeti.Hive.integerHiveEquivGTPattern`, `TauCeti.Hive.fixedIntegerHiveEquivGTPattern`:
  global and fixed-boundary hive–pattern equivalences.
* `TauCeti.Hive.rotateRotateEquiv`, `TauCeti.Hive.toCyclicGTPattern`,
  `TauCeti.Hive.cyclicFixedIntegerHiveEquivGTPattern`: cyclic `(λ, μ, ν)` rotation/gauge conversion
  and quasi-hive equivalence.
* `TauCeti.Hive.stableGTPatternEquiv`: full weight-fibre equivalence under a uniform input gap.

## Main results

* `TauCeti.Hive.isRhombusConcave_iff_ofChart`: decomposition of `IsRhombusConcave` into the two
  Gelfand–Tsetlin rhombus families and the remaining family.
* `TauCeti.Hive.topRow_toGTPattern`, `TauCeti.Hive.weight_toGTPattern`,
  `TauCeti.Hive.apply_eq_gtCompletion`: top row, weight, and chart inversion for `toGTPattern`.
* `TauCeti.Hive.isGTCompletable_iff_sum_sub_le`, `TauCeti.Hive.gt_reconstruction_iff`: explicit
  difference-sum form of `IsGTCompletable` and fixed-boundary reconstruction criterion.
* `TauCeti.Hive.gt_completion_of_uniform_input_gap`, `TauCeti.Hive.exists_stable_gt_equiv`:
  automatic completion and full fibre equivalence in the stable range.
* `TauCeti.Hive.isGTCompletable_two_iff`, `TauCeti.Hive.hiveCount_two_productBoundary`,
  `TauCeti.Hive.card_gtPattern_three_adjoint_weight_zero`,
  `TauCeti.Hive.hiveCount_three_zero_adjoint_zero`: low-rank classifications and checks.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §2.
* A. Henriques and J. Kamnitzer, *Crystals and coboundary categories*, Duke Math. J. **132**
  (2006), 191–216, Theorem 7.4.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### Product chart on the triangular lattice and unit-rhombus decomposition -/

namespace Vertex

/-- Product-chart parameterization `(i, j) ↦ (n - j, j - i, i)` of `Vertex n` for `0 ≤ i ≤ j ≤ n`,
with inverse `p ↦ (p.z, n - p.x)`. -/
def ofChart (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) : Vertex n :=
  ⟨n - j, j - i, i, by omega⟩

@[simp] theorem ofChart_x (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    (ofChart n i j hij hj).x = n - j := (rfl)

@[simp] theorem ofChart_y (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    (ofChart n i j hij hj).y = j - i := (rfl)

@[simp] theorem ofChart_z (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    (ofChart n i j hij hj).z = i := (rfl)

@[simp]
theorem ofChart_eq_iff {n i₁ j₁ i₂ j₂ : ℕ} {hi₁ : i₁ ≤ j₁} {hj₁ : j₁ ≤ n}
    {hi₂ : i₂ ≤ j₂} {hj₂ : j₂ ≤ n} :
    ofChart n i₁ j₁ hi₁ hj₁ = ofChart n i₂ j₂ hi₂ hj₂ ↔ i₁ = i₂ ∧ j₁ = j₂ := by
  refine ⟨fun h => ⟨congrArg Vertex.z h, ?_⟩, fun ⟨hi, hj⟩ => by subst hi; subst hj; rfl⟩
  have hx := congrArg Vertex.x h; simp only [ofChart_x] at hx; omega

/-- Every lattice vertex `p : Vertex n` is recovered in the product chart at `(p.z, n - p.x)`. -/
@[simp]
theorem ofChart_z_sub_x {n : ℕ} (p : Vertex n) :
    ofChart n p.z (n - p.x) (by have := p.sum_eq; omega) (Nat.sub_le n p.x) = p := by
  have hp := p.sum_eq; ext <;> simp <;> omega

theorem ofChart_eq_ofYZ (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    ofChart n i j hij hj = ofYZ n (j - i) i (by omega) := by
  ext <;> simp; omega

@[simp] theorem ofChart_zero_zero (n : ℕ) : ofChart n 0 0 le_rfl (Nat.zero_le n) = cornerA n := by
  ext <;> simp

/-- Setting `i = 0` gives the `j`-th vertex along side `A → B` (`s = 0`). -/
theorem ofChart_zero_left (n j : ℕ) (hj : j ≤ n) :
    ofChart n 0 j (Nat.zero_le j) hj = edgePoint n 0 ⟨j, by omega⟩ := by ext <;> simp

/-- Setting `j = n` gives the `i`-th vertex along side `B → C` (`s = 1`). -/
theorem ofChart_right (n i : ℕ) (hi : i ≤ n) :
    ofChart n i n hi le_rfl = edgePoint n 1 ⟨i, by omega⟩ := by ext <;> simp

/-- Setting `i = j` gives the `(n - j)`-th vertex along side `C → A` (`s = 2`). -/
theorem ofChart_self (n j : ℕ) (hj : j ≤ n) :
    ofChart n j j le_rfl hj = edgePoint n 2 ⟨n - j, by omega⟩ := by ext <;> simp; omega

/-- Rotating `(n - j, j - i, i)` clockwise twice gives `(j - i, i, n - j)`. -/
theorem rotate_rotate_ofChart (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    (ofChart n i j hij hj).rotate.rotate = ⟨j - i, i, n - j, by omega⟩ := by ext <;> simp

end Vertex

section RhombusFamilies

/-- First Gelfand–Tsetlin unit-rhombus family (`0 ≤ i < j < n`), with obtuse corners `(i, j)` and
`(i + 1, j + 1)` and acute corners `(i + 1, j)` and `(i, j + 1)`. -/
theorem isRhombus_ofChart_gtLeft {n i j : ℕ} (hij : i < j) (hj : j < n) :
    IsRhombus (Vertex.ofChart n i j hij.le hj.le)
      (Vertex.ofChart n (i + 1) j hij hj.le)
      (Vertex.ofChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hj)
      (Vertex.ofChart n i (j + 1) (by omega) hj) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hy00 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy10 : ((j - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  have hy11 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy01 : ((j + 1 - i : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  refine ⟨by simp, by simp; omega, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.ofChart_x, Vertex.ofChart_y, Vertex.ofChart_z, hx0, hx1, hy00, hy10, hy11,
      hy01, Nat.cast_add, Nat.cast_one]
    ring

/-- Second Gelfand–Tsetlin unit-rhombus family (`0 ≤ i < j < n`), with obtuse corners `(i + 1, j)`
and `(i + 1, j + 1)` and acute corners `(i, j)` and `(i + 2, j + 1)`. -/
theorem isRhombus_ofChart_gtRight {n i j : ℕ} (hij : i < j) (hj : j < n) :
    IsRhombus (Vertex.ofChart n (i + 1) j hij hj.le)
      (Vertex.ofChart n i j hij.le hj.le)
      (Vertex.ofChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hj)
      (Vertex.ofChart n (i + 2) (j + 1) (Nat.succ_le_succ hij) hj) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hy10 : ((j - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  have hy00 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy11 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy21 : ((j + 1 - (i + 2) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  refine ⟨by simp, by simp; omega, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.ofChart_x, Vertex.ofChart_y, Vertex.ofChart_z, hx0, hx1, hy10, hy00, hy11,
      hy21, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    ring

/-- Third (remaining) unit-rhombus family (`0 ≤ i ≤ j`, `j + 2 ≤ n`), with obtuse corners
`(i, j + 1)` and `(i + 1, j + 1)` and acute corners `(i, j)` and `(i + 1, j + 2)`. -/
theorem isRhombus_ofChart_rem {n i j : ℕ} (hij : i ≤ j) (hj : j + 2 ≤ n) :
    IsRhombus (Vertex.ofChart n i (j + 1) (by omega) (by omega))
      (Vertex.ofChart n i j hij (by omega))
      (Vertex.ofChart n (i + 1) (j + 1) (Nat.succ_le_succ hij) (by omega))
      (Vertex.ofChart n (i + 1) (j + 2) (by omega) hj) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hx2 : ((n - (j + 2) : ℕ) : ℤ) = (n : ℤ) - j - 2 := by omega
  have hy01 : ((j + 1 - i : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  have hy00 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy11 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy12 : ((j + 2 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  refine ⟨by simp; omega, by simp; omega, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.ofChart_x, Vertex.ofChart_y, Vertex.ofChart_z, hx0, hx1, hx2, hy01, hy00,
      hy11, hy12, Nat.cast_add, Nat.cast_one]
    ring

private theorem coord_diff_bounds_of_sqDist_two {n : ℕ} {p q : Vertex n} (h : p.sqDist q = 2) :
    (-1 ≤ (p.x : ℤ) - q.x ∧ (p.x : ℤ) - q.x ≤ 1) ∧
      (-1 ≤ (p.y : ℤ) - q.y ∧ (p.y : ℤ) - q.y ≤ 1) ∧
      (-1 ≤ (p.z : ℤ) - q.z ∧ (p.z : ℤ) - q.z ≤ 1) := by
  rw [Vertex.sqDist_def] at h
  exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

private theorem long_diag_cases_of_sqDist_six {n : ℕ} {b d : Vertex n} (h : b.sqDist d = 6) :
    ((d.x : ℤ) - b.x = -1 ∧ (d.y : ℤ) - b.y = 2 ∧ (d.z : ℤ) - b.z = -1) ∨
      ((d.x : ℤ) - b.x = 1 ∧ (d.y : ℤ) - b.y = -2 ∧ (d.z : ℤ) - b.z = 1) ∨
      ((d.x : ℤ) - b.x = -1 ∧ (d.y : ℤ) - b.y = -1 ∧ (d.z : ℤ) - b.z = 2) ∨
      ((d.x : ℤ) - b.x = 1 ∧ (d.y : ℤ) - b.y = 1 ∧ (d.z : ℤ) - b.z = -2) ∨
      ((d.x : ℤ) - b.x = -2 ∧ (d.y : ℤ) - b.y = 1 ∧ (d.z : ℤ) - b.z = 1) ∨
      ((d.x : ℤ) - b.x = 2 ∧ (d.y : ℤ) - b.y = -1 ∧ (d.z : ℤ) - b.z = -1) := by
  rw [Vertex.sqDist_comm, Vertex.sqDist_def] at h
  set δx : ℤ := (d.x : ℤ) - b.x
  set δy : ℤ := (d.y : ℤ) - b.y
  set δz : ℤ := (d.z : ℤ) - b.z
  have hsum : δx + δy + δz = 0 := by have := b.sum_eq; have := d.sum_eq; omega
  have hx : -2 ≤ δx ∧ δx ≤ 2 := ⟨by nlinarith, by nlinarith⟩
  have hy : -2 ≤ δy ∧ δy ≤ 2 := ⟨by nlinarith, by nlinarith⟩
  (rcases (by omega : δx = -2 ∨ δx = -1 ∨ δx = 0 ∨ δx = 1 ∨ δx = 2) with
      hdx | hdx | hdx | hdx | hdx <;>
    rcases (by omega : δy = -2 ∨ δy = -1 ∨ δy = 0 ∨ δy = 1 ∨ δy = 2) with
      hdy | hdy | hdy | hdy | hdy) <;>
    (have hdz : δz = -(δx + δy) := by omega
     norm_num [hdx, hdy, hdz] at h) <;>
    omega

private theorem eq_ofChart_of_z_x {n i j : ℕ} {p : Vertex n} {hij : i ≤ j} {hj : j ≤ n}
    (hz : p.z = i) (hx : p.x + j = n) :
    p = Vertex.ofChart n i j hij hj := by
  have hp := p.sum_eq; ext <;> simp <;> omega

private theorem le_of_isRhombus_diag_y {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    {f : Vertex n → R}
    (hgtL : ∀ i j (hij : i < j) (hj : j < n),
      f (Vertex.ofChart n (i + 1) j hij hj.le) + f (Vertex.ofChart n i (j + 1) (by omega) hj) ≤
        f (Vertex.ofChart n i j hij.le hj.le) +
          f (Vertex.ofChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hj))
    {a b c d : Vertex n} (hr : IsRhombus a b c d)
    (hdx : (d.x : ℤ) - b.x = -1) (hdy : (d.y : ℤ) - b.y = 2) (hdz : (d.z : ℤ) - b.z = -1) :
    f b + f d ≤ f a + f c := by
  have := coord_diff_bounds_of_sqDist_two (Vertex.sqDist_comm a b ▸ hr.side_ab)
  have := coord_diff_bounds_of_sqDist_two (Vertex.sqDist_comm d a ▸ hr.side_da)
  have := a.sum_eq; have := b.sum_eq; have := d.sum_eq
  have := hr.midpoint_x; have := hr.midpoint_z
  have hij : b.z - 1 < n - b.x := by omega
  have hj : n - b.x < n := by omega
  have hb_eq : b = Vertex.ofChart n (b.z - 1 + 1) (n - b.x) hij hj.le :=
    eq_ofChart_of_z_x (by omega) (by omega)
  have hd_eq : d = Vertex.ofChart n (b.z - 1) (n - b.x + 1) (by omega) hj :=
    eq_ofChart_of_z_x (by omega) (by omega)
  have : (a.y : ℤ) - b.y = 1 := by omega
  rcases (by omega : ((a.x : ℤ) - b.x = 0 ∧ (a.z : ℤ) - b.z = -1) ∨
      ((a.x : ℤ) - b.x = -1 ∧ (a.z : ℤ) - b.z = 0)) with ⟨_, _⟩ | ⟨_, _⟩
  · have ha_eq : a = Vertex.ofChart n (b.z - 1) (n - b.x) hij.le hj.le :=
      eq_ofChart_of_z_x (by omega) (by omega)
    have hc_eq : c = Vertex.ofChart n (b.z - 1 + 1) (n - b.x + 1) (Nat.succ_le_succ hij.le) hj :=
      eq_ofChart_of_z_x (by omega) (by omega)
    exact (congrArg₂ (f · + f ·) hb_eq hd_eq).trans_le <|
      (hgtL (b.z - 1) (n - b.x) hij hj).trans_eq (congrArg₂ (f · + f ·) ha_eq.symm hc_eq.symm)
  · have ha_eq : a = Vertex.ofChart n (b.z - 1 + 1) (n - b.x + 1) (Nat.succ_le_succ hij.le) hj :=
      eq_ofChart_of_z_x (by omega) (by omega)
    have hc_eq : c = Vertex.ofChart n (b.z - 1) (n - b.x) hij.le hj.le :=
      eq_ofChart_of_z_x (by omega) (by omega)
    exact (congrArg₂ (f · + f ·) hb_eq hd_eq).trans_le <|
      (hgtL (b.z - 1) (n - b.x) hij hj).trans_eq <|
        (congrArg₂ (f · + f ·) hc_eq.symm ha_eq.symm).trans (add_comm _ _)

private theorem le_of_isRhombus_diag_z {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    {f : Vertex n → R}
    (hgtR : ∀ i j (hij : i < j) (hj : j < n),
      f (Vertex.ofChart n i j hij.le hj.le) +
        f (Vertex.ofChart n (i + 2) (j + 1) (Nat.succ_le_succ hij) hj) ≤
        f (Vertex.ofChart n (i + 1) j hij hj.le) +
          f (Vertex.ofChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hj))
    {a b c d : Vertex n} (hr : IsRhombus a b c d)
    (hdx : (d.x : ℤ) - b.x = -1) (hdy : (d.y : ℤ) - b.y = -1) (hdz : (d.z : ℤ) - b.z = 2) :
    f b + f d ≤ f a + f c := by
  have := coord_diff_bounds_of_sqDist_two (Vertex.sqDist_comm a b ▸ hr.side_ab)
  have := coord_diff_bounds_of_sqDist_two (Vertex.sqDist_comm d a ▸ hr.side_da)
  have := a.sum_eq; have := b.sum_eq; have := d.sum_eq
  have := hr.midpoint_x; have := hr.midpoint_z
  have hij : b.z < n - b.x := by omega
  have hj : n - b.x < n := by omega
  have hb_eq : b = Vertex.ofChart n b.z (n - b.x) hij.le hj.le :=
    eq_ofChart_of_z_x rfl (by omega)
  have hd_eq : d = Vertex.ofChart n (b.z + 2) (n - b.x + 1) (Nat.succ_le_succ hij) hj :=
    eq_ofChart_of_z_x (by omega) (by omega)
  have : (a.z : ℤ) - b.z = 1 := by omega
  rcases (by omega : ((a.x : ℤ) - b.x = 0 ∧ (a.y : ℤ) - b.y = -1) ∨
      ((a.x : ℤ) - b.x = -1 ∧ (a.y : ℤ) - b.y = 0)) with ⟨_, _⟩ | ⟨_, _⟩
  · have ha_eq : a = Vertex.ofChart n (b.z + 1) (n - b.x) hij hj.le :=
      eq_ofChart_of_z_x (by omega) (by omega)
    have hc_eq : c = Vertex.ofChart n (b.z + 1) (n - b.x + 1) (Nat.succ_le_succ hij.le) hj :=
      eq_ofChart_of_z_x (by omega) (by omega)
    exact (congrArg₂ (f · + f ·) hb_eq hd_eq).trans_le <|
      (hgtR b.z (n - b.x) hij hj).trans_eq (congrArg₂ (f · + f ·) ha_eq.symm hc_eq.symm)
  · have ha_eq : a = Vertex.ofChart n (b.z + 1) (n - b.x + 1) (Nat.succ_le_succ hij.le) hj :=
      eq_ofChart_of_z_x (by omega) (by omega)
    have hc_eq : c = Vertex.ofChart n (b.z + 1) (n - b.x) hij hj.le :=
      eq_ofChart_of_z_x (by omega) (by omega)
    exact (congrArg₂ (f · + f ·) hb_eq hd_eq).trans_le <|
      (hgtR b.z (n - b.x) hij hj).trans_eq <|
        (congrArg₂ (f · + f ·) hc_eq.symm ha_eq.symm).trans (add_comm _ _)

private theorem le_of_isRhombus_diag_x {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    {f : Vertex n → R}
    (hrem : ∀ i j (hij : i ≤ j) (hj : j + 2 ≤ n),
      f (Vertex.ofChart n i j hij (by omega)) + f (Vertex.ofChart n (i + 1) (j + 2) (by omega) hj) ≤
        f (Vertex.ofChart n i (j + 1) (by omega) (by omega)) +
          f (Vertex.ofChart n (i + 1) (j + 1) (Nat.succ_le_succ hij) (by omega)))
    {a b c d : Vertex n} (hr : IsRhombus a b c d)
    (hdx : (d.x : ℤ) - b.x = -2) (hdy : (d.y : ℤ) - b.y = 1) (hdz : (d.z : ℤ) - b.z = 1) :
    f b + f d ≤ f a + f c := by
  have := coord_diff_bounds_of_sqDist_two (Vertex.sqDist_comm a b ▸ hr.side_ab)
  have := coord_diff_bounds_of_sqDist_two (Vertex.sqDist_comm d a ▸ hr.side_da)
  have := a.sum_eq; have := b.sum_eq; have := d.sum_eq
  have := hr.midpoint_x; have := hr.midpoint_z
  have hij : b.z ≤ n - b.x := by omega
  have hj : n - b.x + 2 ≤ n := by omega
  have hb_eq : b = Vertex.ofChart n b.z (n - b.x) hij (by omega) :=
    eq_ofChart_of_z_x rfl (by omega)
  have hd_eq : d = Vertex.ofChart n (b.z + 1) (n - b.x + 2) (by omega) hj :=
    eq_ofChart_of_z_x (by omega) (by omega)
  have : (a.x : ℤ) - b.x = -1 := by omega
  rcases (by omega : ((a.y : ℤ) - b.y = 1 ∧ (a.z : ℤ) - b.z = 0) ∨
      ((a.y : ℤ) - b.y = 0 ∧ (a.z : ℤ) - b.z = 1)) with ⟨_, _⟩ | ⟨_, _⟩
  · have ha_eq : a = Vertex.ofChart n b.z (n - b.x + 1) (by omega) (by omega) :=
      eq_ofChart_of_z_x (by omega) (by omega)
    have hc_eq : c = Vertex.ofChart n (b.z + 1) (n - b.x + 1) (Nat.succ_le_succ hij) (by omega) :=
      eq_ofChart_of_z_x (by omega) (by omega)
    exact (congrArg₂ (f · + f ·) hb_eq hd_eq).trans_le <|
      (hrem b.z (n - b.x) hij hj).trans_eq (congrArg₂ (f · + f ·) ha_eq.symm hc_eq.symm)
  · have ha_eq : a = Vertex.ofChart n (b.z + 1) (n - b.x + 1) (Nat.succ_le_succ hij) (by omega) :=
      eq_ofChart_of_z_x (by omega) (by omega)
    have hc_eq : c = Vertex.ofChart n b.z (n - b.x + 1) (by omega) (by omega) :=
      eq_ofChart_of_z_x (by omega) (by omega)
    exact (congrArg₂ (f · + f ·) hb_eq hd_eq).trans_le <|
      (hrem b.z (n - b.x) hij hj).trans_eq <|
        (congrArg₂ (f · + f ·) hc_eq.symm ha_eq.symm).trans (add_comm _ _)

/-- **Product-chart characterization of rhombus concavity**: a lattice function `f : Vertex n → R`
is rhombus-concave if and only if it satisfies the two Gelfand–Tsetlin rhombus families and the
remaining rhombus family in `Vertex.ofChart`. -/
theorem isRhombusConcave_iff_ofChart {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    (f : Vertex n → R) :
    IsRhombusConcave f ↔
      (∀ i j (hij : i < j) (hj : j < n),
        f (Vertex.ofChart n (i + 1) j hij hj.le) +
          f (Vertex.ofChart n i (j + 1) (by omega) hj) ≤
          f (Vertex.ofChart n i j hij.le hj.le) +
            f (Vertex.ofChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hj)) ∧
      (∀ i j (hij : i < j) (hj : j < n),
        f (Vertex.ofChart n i j hij.le hj.le) +
          f (Vertex.ofChart n (i + 2) (j + 1) (Nat.succ_le_succ hij) hj) ≤
          f (Vertex.ofChart n (i + 1) j hij hj.le) +
            f (Vertex.ofChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hj)) ∧
      (∀ i j (hij : i ≤ j) (hj : j + 2 ≤ n),
        f (Vertex.ofChart n i j hij (by omega)) +
          f (Vertex.ofChart n (i + 1) (j + 2) (by omega) hj) ≤
          f (Vertex.ofChart n i (j + 1) (by omega) (by omega)) +
            f (Vertex.ofChart n (i + 1) (j + 1) (Nat.succ_le_succ hij) (by omega))) := by
  rw [isRhombusConcave_def]
  refine ⟨fun hf => ⟨fun i j hij hj => hf (isRhombus_ofChart_gtLeft hij hj),
    fun i j hij hj => hf (isRhombus_ofChart_gtRight hij hj),
    fun i j hij hj => hf (isRhombus_ofChart_rem hij hj)⟩, ?_⟩
  rintro ⟨hgtL, hgtR, hrem⟩ a b c d hr
  rcases long_diag_cases_of_sqDist_six hr.long with
    ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · exact le_of_isRhombus_diag_y hgtL hr hx hy hz
  · rw [add_comm (f b) (f d)]
    exact le_of_isRhombus_diag_y hgtL hr.reverse (by omega) (by omega) (by omega)
  · exact le_of_isRhombus_diag_z hgtR hr hx hy hz
  · rw [add_comm (f b) (f d)]
    exact le_of_isRhombus_diag_z hgtR hr.reverse (by omega) (by omega) (by omega)
  · exact le_of_isRhombus_diag_x hrem hr hx hy hz
  · rw [add_comm (f b) (f d)]
    exact le_of_isRhombus_diag_x hrem hr.reverse (by omega) (by omega) (by omega)

end RhombusFamilies

/-! ### Partial boundary sums and chart boundary values -/

section BoundaryPrefix

/-- Leading partial sum `∑_{r < j} l r` of a boundary sequence `l : Fin n → R`. -/
def gtBoundaryPrefix {n : ℕ} {R : Type*} [AddCommMonoid R] (l : Fin n → R) (j : ℕ) : R :=
  ∑ r : Fin n, if r.val < j then l r else 0

theorem gtBoundaryPrefix_def {n : ℕ} {R : Type*} [AddCommMonoid R] (l : Fin n → R) (j : ℕ) :
    gtBoundaryPrefix l j = ∑ r : Fin n, if r.val < j then l r else 0 :=
  (rfl)

theorem gtBoundaryPrefix_eq_sum_filter {n : ℕ} {R : Type*} [AddCommMonoid R]
    (l : Fin n → R) (j : ℕ) :
    gtBoundaryPrefix l j = ∑ r : Fin n with r.val < j, l r :=
  (Finset.sum_filter _ _).symm

@[simp]
theorem gtBoundaryPrefix_zero {n : ℕ} {R : Type*} [AddCommMonoid R] (l : Fin n → R) :
    gtBoundaryPrefix l 0 = 0 := by
  simp [gtBoundaryPrefix_def]

@[simp]
theorem gtBoundaryPrefix_succ {n : ℕ} {R : Type*} [AddCommMonoid R] (l : Fin n → R)
    {j : ℕ} (hj : j < n) :
    gtBoundaryPrefix l (j + 1) = gtBoundaryPrefix l j + l ⟨j, hj⟩ := by
  rw [gtBoundaryPrefix_eq_sum_filter, gtBoundaryPrefix_eq_sum_filter]
  have hsplit : ({r : Fin n | r.val < j + 1} : Finset (Fin n)) =
      insert ⟨j, hj⟩ ({r : Fin n | r.val < j} : Finset (Fin n)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnotMem : (⟨j, hj⟩ : Fin n) ∉ ({r : Fin n | r.val < j} : Finset (Fin n)) := by simp
  rw [hsplit, Finset.sum_insert hnotMem, add_comm]

@[simp]
theorem gtBoundaryPrefix_of_le {n : ℕ} {R : Type*} [AddCommMonoid R] (l : Fin n → R)
    {j : ℕ} (hj : n ≤ j) :
    gtBoundaryPrefix l j = ∑ r : Fin n, l r := by
  rw [gtBoundaryPrefix_def]
  exact Finset.sum_congr rfl fun r _ => ite_eq_left (r.isLt.trans_le hj)

@[simp]
theorem gtBoundaryPrefix_zero_seq {n : ℕ} {R : Type*} [AddCommMonoid R] (j : ℕ) :
    gtBoundaryPrefix (0 : Fin n → R) j = 0 := by
  simp [gtBoundaryPrefix_def]

theorem gtBoundaryPrefix_add {n : ℕ} {R : Type*} [AddCommMonoid R] (l₁ l₂ : Fin n → R) (j : ℕ) :
    gtBoundaryPrefix (l₁ + l₂) j = gtBoundaryPrefix l₁ j + gtBoundaryPrefix l₂ j := by
  simp only [gtBoundaryPrefix_eq_sum_filter, Pi.add_apply, Finset.sum_add_distrib]

theorem gtBoundaryPrefix_sub {n : ℕ} {R : Type*} [AddCommGroup R] (l₁ l₂ : Fin n → R) (j : ℕ) :
    gtBoundaryPrefix (l₁ - l₂) j = gtBoundaryPrefix l₁ j - gtBoundaryPrefix l₂ j := by
  simp only [gtBoundaryPrefix_eq_sum_filter, Pi.sub_apply, Finset.sum_sub_distrib]

/-- Along `A → B` (`i = 0`), `h(0, j)` equals `gtBoundaryPrefix (h.boundary 0) j`. -/
theorem apply_ofChart_zero_left {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    (h : Hive n R) {j : ℕ} (hj : j ≤ n) :
    h (Vertex.ofChart n 0 j (Nat.zero_le j) hj) = gtBoundaryPrefix (h.boundary 0) j := by
  rw [Vertex.ofChart_zero_left, h.apply_edgePoint_zero, gtBoundaryPrefix_eq_sum_filter]

/-- Along `B → C` (`j = n`), `h(i, n)` equals `(∑ r, h.boundary 0 r) + gtBoundaryPrefix _ i`. -/
theorem apply_ofChart_right {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    (h : Hive n R) {i : ℕ} (hi : i ≤ n) :
    h (Vertex.ofChart n i n hi le_rfl) =
      (∑ r : Fin n, h.boundary 0 r) + gtBoundaryPrefix (h.boundary 1) i := by
  rw [Vertex.ofChart_right, h.apply_edgePoint_one, gtBoundaryPrefix_eq_sum_filter]

/-- Along `C → A` (`i = j`), `h(j, j)` equals `gtBoundaryPrefix (h.boundaryWeight 2).dual.1 j`. -/
theorem apply_ofChart_self {n : ℕ} (h : IntegerHive n) {j : ℕ} (hj : j ≤ n) :
    h (Vertex.ofChart n j j le_rfl hj) = gtBoundaryPrefix (h.boundaryWeight 2).dual.1 j := by
  rw [Vertex.ofChart_self, h.apply_edgePoint_two, Fin.val_mk, Finset.sum_filter,
    gtBoundaryPrefix_def, ← Finset.sum_neg_distrib]
  refine (Equiv.sum_comp Fin.revPerm
    (fun k : Fin n => -(if n - j ≤ k.val then h.boundary 2 k else 0))).symm.trans ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Fin.revPerm_apply, Fin.val_rev, DominantWeight.dual_apply, coe_boundaryWeight]
  by_cases hr : r.val < j
  · have hge : n - j ≤ n - (r.val + 1) := by omega
    rw [ite_eq_left hge, ite_eq_left hr]
  · have hnge : ¬ n - j ≤ n - (r.val + 1) := by have := r.isLt; omega
    rw [ite_eq_right hnge, ite_eq_right hr, neg_zero]

theorem apply_ofChart_zero_left_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) {j : ℕ} (hj : j ≤ n) :
    h (Vertex.ofChart n 0 j (Nat.zero_le j) hj) = gtBoundaryPrefix lam.1 j := by
  rw [h.apply_ofChart_zero_left hj, hb, productBoundary_zero]

theorem apply_ofChart_right_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) {i : ℕ} (hi : i ≤ n) :
    h (Vertex.ofChart n i n hi le_rfl) = (∑ r : Fin n, lam.1 r) + gtBoundaryPrefix μ.1 i := by
  rw [h.apply_ofChart_right hi, hb, productBoundary_zero, productBoundary_one]

theorem apply_ofChart_self_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) {j : ℕ} (hj : j ≤ n) :
    h (Vertex.ofChart n j j le_rfl hj) = gtBoundaryPrefix γ.1 j := by
  have hb2 : h.boundaryWeight 2 = γ.dual := Subtype.ext (by simp [coe_boundaryWeight, hb])
  rw [h.apply_ofChart_self hj, hb2, DominantWeight.dual_dual]

end BoundaryPrefix

/-! ### Directional finite-difference map and chart completion -/

section DifferenceAndCompletion

variable {n : ℕ}

/-- Directional finite-difference Gelfand–Tsetlin pattern of an integer hive `h`: in the product
chart, `h.toGTPattern i j = h(i + 1, j) - h(i, j)` on the informative cells `0 ≤ i < j ≤ n`, and
`0` outside. -/
def toGTPattern (h : IntegerHive n) : GTPattern n where
  entry i j :=
    if hij : i < j then
      if hj : j ≤ n then
        h (Vertex.ofChart n (i + 1) j hij hj) - h (Vertex.ofChart n i j hij.le hj)
      else 0
    else 0
  zeros' {i j} hout := by
    rcases hout with hnj | hji
    · by_cases hij : i < j
      · simp [hij, Nat.not_le.mpr hnj]
      · simp [hij]
    · simp [Nat.not_lt.mpr hji]
  interlacing' {i j} hij hj := by
    have hj1 : j + 1 ≤ n := hj
    have hij1 : i < j + 1 := by omega
    have hij2 : i + 1 < j + 1 := Nat.succ_lt_succ hij
    simp only [dite_eq_left hij, dite_eq_left hj.le, dite_eq_left hij1, dite_eq_left hj1,
      dite_eq_left hij2]
    have hleft := h.le_of_isRhombus (isRhombus_ofChart_gtLeft hij hj)
    have hright := h.le_of_isRhombus (isRhombus_ofChart_gtRight hij hj)
    exact ⟨by linarith, by linarith⟩

theorem toGTPattern_apply (h : IntegerHive n) (i j : ℕ) :
    h.toGTPattern i j =
      if hij : i < j then
        if hj : j ≤ n then
          h (Vertex.ofChart n (i + 1) j hij hj) - h (Vertex.ofChart n i j hij.le hj)
        else 0
      else 0 :=
  (rfl)

@[simp]
theorem toGTPattern_apply_of_lt_of_le (h : IntegerHive n) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    h.toGTPattern i j =
      h (Vertex.ofChart n (i + 1) j hij hj) - h (Vertex.ofChart n i j hij.le hj) := by
  rw [toGTPattern_apply, dite_eq_left hij, dite_eq_left hj]

@[simp]
theorem toGTPattern_zero : (0 : IntegerHive n).toGTPattern = 0 := by
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · simp [toGTPattern_apply_of_lt_of_le _ h.1 h.2, GTPattern.zero_apply]
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.zero_apply]

@[simp]
theorem toGTPattern_add (h₁ h₂ : IntegerHive n) :
    (h₁ + h₂).toGTPattern = h₁.toGTPattern + h₂.toGTPattern := by
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · simp only [toGTPattern_apply_of_lt_of_le _ h.1 h.2, add_apply, GTPattern.add_apply]
    abel
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.add_apply,
      GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega), add_zero]

@[simp]
theorem toGTPattern_nsmul (k : ℕ) (h : IntegerHive n) :
    (k • h).toGTPattern = k • h.toGTPattern := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · simp only [toGTPattern_apply_of_lt_of_le _ hij.1 hij.2, nsmul_apply, GTPattern.nsmul_apply,
      nsmul_eq_mul]
    ring
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.nsmul_apply,
      GTPattern.entry_eq_zero _ (by omega), smul_zero]

/-- `Hive.toGTPattern` bundled as an additive monoid homomorphism `IntegerHive n →+ GTPattern n`. -/
def toGTPatternAddMonoidHom : IntegerHive n →+ GTPattern n where
  toFun := toGTPattern
  map_zero' := toGTPattern_zero
  map_add' := toGTPattern_add

@[simp]
theorem toGTPatternAddMonoidHom_apply (h : IntegerHive n) :
    toGTPatternAddMonoidHom h = h.toGTPattern :=
  (rfl)

/-- The top row of `h.toGTPattern` is the side-`1` (`B → C`) boundary of `h`. -/
@[simp]
theorem topRow_toGTPattern (h : IntegerHive n) : h.toGTPattern.topRow = h.boundary 1 := by
  ext i
  rw [GTPattern.topRow_apply, h.toGTPattern_apply_of_lt_of_le i.isLt le_rfl,
    Vertex.ofChart_right, Vertex.ofChart_right, boundary_apply]
  rfl

@[simp]
theorem topWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.topWeight = h.boundaryWeight 1 :=
  Subtype.ext (by simp)

/-- Summing the first `i ≤ j` entries of row `j ≤ n` of `h.toGTPattern` telescopes to
`h(i, j) - h(0, j)`. -/
theorem sum_range_toGTPattern (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    (∑ k ∈ Finset.range i, h.toGTPattern k j) =
      h (Vertex.ofChart n i j hij hj) - h (Vertex.ofChart n 0 j (Nat.zero_le j) hj) := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), h.toGTPattern_apply_of_lt_of_le hij hj]
    abel

/-- Row `j ≤ n` of `h.toGTPattern` sums to
`gtBoundaryPrefix (h.boundaryWeight 2).dual.1 j - gtBoundaryPrefix (h.boundary 0) j`. -/
theorem rowSum_toGTPattern (h : IntegerHive n) {j : ℕ} (hj : j ≤ n) :
    h.toGTPattern.rowSum j =
      gtBoundaryPrefix (h.boundaryWeight 2).dual.1 j - gtBoundaryPrefix (h.boundary 0) j := by
  rw [GTPattern.rowSum_def, h.sum_range_toGTPattern le_rfl hj, h.apply_ofChart_self hj,
    h.apply_ofChart_zero_left hj]

/-- The torus weight of `h.toGTPattern` is `(h.boundaryWeight 2).dual.1 - h.boundary 0`. -/
@[simp]
theorem weight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.weight = (h.boundaryWeight 2).dual.1 - h.boundary 0 := by
  ext r
  rw [GTPattern.weight_apply, h.rowSum_toGTPattern r.isLt, h.rowSum_toGTPattern r.isLt.le,
    gtBoundaryPrefix_succ _ r.isLt, gtBoundaryPrefix_succ _ r.isLt, Pi.sub_apply]
  abel

theorem topRow_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) : h.toGTPattern.topRow = μ.1 := by
  rw [h.topRow_toGTPattern, hb, productBoundary_one]

theorem weight_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) : h.toGTPattern.weight = γ.1 - lam.1 := by
  have hb2 : h.boundaryWeight 2 = γ.dual := Subtype.ext (by simp [coe_boundaryWeight, hb])
  rw [h.weight_toGTPattern, hb2, DominantWeight.dual_dual, hb, productBoundary_zero]

/-- Inverse chart formula `gtBoundaryPrefix lam.1 j + ∑ k ∈ Finset.range i, P k j` reconstructing
the hive value at `(i, j)` (`0 ≤ i ≤ j ≤ n`) from the side-`0` dominant weight `lam` and a
Gelfand–Tsetlin pattern `P`. -/
def gtCompletion (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) : ℤ :=
  gtBoundaryPrefix lam.1 j + ∑ k ∈ Finset.range i, P k j

theorem gtCompletion_def (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) :
    gtCompletion lam P i j = gtBoundaryPrefix lam.1 j + ∑ k ∈ Finset.range i, P k j :=
  (rfl)

@[simp]
theorem gtCompletion_zero_left (lam : DominantWeight n) (P : GTPattern n) (j : ℕ) :
    gtCompletion lam P 0 j = gtBoundaryPrefix lam.1 j := by
  simp [gtCompletion_def]

theorem gtCompletion_succ_left (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) :
    gtCompletion lam P (i + 1) j = gtCompletion lam P i j + P i j := by
  rw [gtCompletion_def, gtCompletion_def, Finset.sum_range_succ, add_assoc]

theorem gtCompletion_self (lam : DominantWeight n) (P : GTPattern n) (j : ℕ) :
    gtCompletion lam P j j = gtBoundaryPrefix lam.1 j + P.rowSum j := by
  rw [gtCompletion_def, GTPattern.rowSum_def]

theorem gtCompletion_self_of_weight {lam : DominantWeight n} {P : GTPattern n} {g : Fin n → ℤ}
    (hw : P.weight = g - lam.1) {j : ℕ} (hj : j ≤ n) :
    gtCompletion lam P j j = gtBoundaryPrefix g j := by
  rw [gtCompletion_self, ← P.sum_weight_lt hj, ← gtBoundaryPrefix_eq_sum_filter, hw,
    gtBoundaryPrefix_sub, add_sub_cancel]

theorem gtCompletion_right (lam : DominantWeight n) (P : GTPattern n) {i : ℕ} (hi : i ≤ n) :
    gtCompletion lam P i n = (∑ r : Fin n, lam.1 r) + gtBoundaryPrefix P.topRow i := by
  rw [gtCompletion_def, gtBoundaryPrefix_of_le lam.1 le_rfl]
  congr 1
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), gtBoundaryPrefix_succ _ hi, GTPattern.topRow_apply]

/-- Every hive value in the product chart is recovered from `h.boundaryWeight 0` and
`h.toGTPattern` via `gtCompletion`. -/
theorem apply_ofChart_eq_gtCompletion (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    h (Vertex.ofChart n i j hij hj) = gtCompletion (h.boundaryWeight 0) h.toGTPattern i j := by
  rw [gtCompletion_def, coe_boundaryWeight, ← h.apply_ofChart_zero_left hj,
    h.sum_range_toGTPattern hij hj, add_sub_cancel]

/-- **Chart inversion formula**: every integer hive `h` is recovered at `p : Vertex n` as
`gtCompletion (h.boundaryWeight 0) h.toGTPattern p.z (n - p.x)`. -/
theorem apply_eq_gtCompletion (h : IntegerHive n) (p : Vertex n) :
    h p = gtCompletion (h.boundaryWeight 0) h.toGTPattern p.z (n - p.x) := by
  have hp := h.apply_ofChart_eq_gtCompletion
    (i := p.z) (j := n - p.x) (by have := p.sum_eq; omega) (Nat.sub_le n p.x)
  rwa [Vertex.ofChart_z_sub_x] at hp

theorem apply_eq_gtCompletion_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (p : Vertex n) :
    h p = gtCompletion lam h.toGTPattern p.z (n - p.x) := by
  have hb0 : h.boundaryWeight 0 = lam := Subtype.ext (by simp [coe_boundaryWeight, hb])
  rw [h.apply_eq_gtCompletion p, hb0]

/-- A Gelfand–Tsetlin pattern `P` is **hive-completable** over the side-`0` dominant weight `lam`
when `gtCompletion lam P` satisfies the third (remaining) unit-rhombus family in the product
chart. -/
def IsGTCompletable (lam : DominantWeight n) (P : GTPattern n) : Prop :=
  ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
    gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
      gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1)

theorem isGTCompletable_def (lam : DominantWeight n) (P : GTPattern n) :
    IsGTCompletable lam P ↔
      ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
        gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
          gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1) :=
  Iff.rfl

theorem isGTCompletable_iff_fin (lam : DominantWeight n) (P : GTPattern n) :
    IsGTCompletable lam P ↔
      ∀ i j : Fin n, i.val ≤ j.val → j.val + 2 ≤ n →
        gtCompletion lam P i.val j.val + gtCompletion lam P (i.val + 1) (j.val + 2) ≤
          gtCompletion lam P i.val (j.val + 1) + gtCompletion lam P (i.val + 1) (j.val + 1) :=
  ⟨fun h i j hij hj => h i.val j.val hij hj,
    fun h i j hij hj => h ⟨i, by omega⟩ ⟨j, by omega⟩ hij hj⟩

/-- `IsGTCompletable lam P` is decidable by bounded quantification over `i, j : Fin n`. -/
instance instDecidableIsGTCompletable (lam : DominantWeight n) (P : GTPattern n) :
    Decidable (IsGTCompletable lam P) :=
  decidable_of_iff _ (isGTCompletable_iff_fin lam P).symm

/-- Single-cell reformulation of the remaining rhombus inequality for `j + 2 ≤ n` in terms of
row-to-row differences of `P` and the gap `lam.1 ⟨j, _⟩ - lam.1 ⟨j + 1, _⟩`. -/
theorem gtCompletion_rem_iff (lam : DominantWeight n) (P : GTPattern n) {i j : ℕ}
    (hj : j + 2 ≤ n) :
    gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
      gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1) ↔
      (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
        (lam.1 ⟨j, by omega⟩ - lam.1 ⟨j + 1, by omega⟩) +
          ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) := by
  have hd1 : gtCompletion lam P i (j + 1) - gtCompletion lam P i j =
      lam.1 ⟨j, by omega⟩ + ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) := by
    rw [gtCompletion_def, gtCompletion_def, gtBoundaryPrefix_succ lam.1 (by omega),
      Finset.sum_sub_distrib]
    abel
  have hd2 : gtCompletion lam P (i + 1) (j + 2) - gtCompletion lam P (i + 1) (j + 1) =
      lam.1 ⟨j + 1, by omega⟩ + ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1)) := by
    rw [gtCompletion_def, gtCompletion_def, gtBoundaryPrefix_succ lam.1 (by omega),
      Finset.sum_sub_distrib]
    abel
  constructor <;> intro h <;> linarith

/-- **Difference-sum characterization of `IsGTCompletable`**. -/
theorem isGTCompletable_iff_sum_sub_le (lam : DominantWeight n) (P : GTPattern n) :
    IsGTCompletable lam P ↔
      ∀ i j : ℕ, i ≤ j → (hj : j + 2 ≤ n) →
        (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
          (lam.1 ⟨j, by omega⟩ - lam.1 ⟨j + 1, by omega⟩) +
            ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
  ⟨fun h i j hij hj => (gtCompletion_rem_iff lam P hj).mp (h i j hij hj),
    fun h i j hij hj => (gtCompletion_rem_iff lam P hj).mpr (h i j hij hj)⟩

theorem isGTCompletable_toGTPattern (h : IntegerHive n) :
    IsGTCompletable (h.boundaryWeight 0) h.toGTPattern := by
  intro i j hij hj
  simp only [← h.apply_ofChart_eq_gtCompletion hij (by omega),
    ← h.apply_ofChart_eq_gtCompletion (by omega : i + 1 ≤ j + 2) hj,
    ← h.apply_ofChart_eq_gtCompletion (by omega : i ≤ j + 1) (by omega),
    ← h.apply_ofChart_eq_gtCompletion (Nat.succ_le_succ hij) (by omega)]
  exact h.le_of_isRhombus (isRhombus_ofChart_rem hij hj)

end DifferenceAndCompletion

/-! ### Hive reconstruction and object equivalences -/

section Reconstruction

variable {n : ℕ}

/-- Reconstruct a normalized integer hive from a side-`0` dominant weight `lam` and a
hive-completable Gelfand–Tsetlin pattern `P`. -/
def ofGTPattern (lam : DominantWeight n) (P : GTPattern n) (hP : IsGTCompletable lam P) :
    IntegerHive n where
  value p := gtCompletion lam P p.z (n - p.x)
  value_cornerA' := by simp
  le_of_isRhombus' {a b c d} hr := by
    refine (isRhombusConcave_def (fun p : Vertex n => gtCompletion lam P p.z (n - p.x))).mp ?_ hr
    rw [isRhombusConcave_iff_ofChart]
    have hchart (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
        gtCompletion lam P (Vertex.ofChart n i j hij hj).z
          (n - (Vertex.ofChart n i j hij hj).x) = gtCompletion lam P i j := by
      simp [Nat.sub_sub_self hj]
    refine ⟨fun i j hij hj => ?_, fun i j hij hj => ?_, fun i j hij hj => ?_⟩
    · simp only [hchart]
      rw [gtCompletion_succ_left, gtCompletion_succ_left]
      linarith [P.entry_le_entry_succ_row hij hj]
    · simp only [hchart]
      rw [gtCompletion_succ_left lam P (i + 1) (j + 1), gtCompletion_succ_left lam P i j]
      linarith [P.entry_succ_succ_le_entry (i := i) hj]
    · simp only [hchart]
      exact hP i j hij hj

@[simp] theorem ofGTPattern_apply (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) (p : Vertex n) :
    ofGTPattern lam P hP p = gtCompletion lam P p.z (n - p.x) := (rfl)

theorem ofGTPattern_ofChart (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    ofGTPattern lam P hP (Vertex.ofChart n i j hij hj) = gtCompletion lam P i j := by
  simp [Nat.sub_sub_self hj]

@[simp]
theorem toGTPattern_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).toGTPattern = P := by
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · rw [toGTPattern_apply_of_lt_of_le _ h.1 h.2, ofGTPattern_ofChart, ofGTPattern_ofChart,
      gtCompletion_succ_left, add_sub_cancel_left]
  · exact GTPattern.entry_eq_zero _ (by omega) |>.trans (P.entry_eq_zero (by omega)).symm

@[simp]
theorem boundary_zero_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundary 0 = lam.1 := by
  ext r
  have hs : Vertex.edgePoint n 0 r.succ =
      Vertex.ofChart n 0 (r.val + 1) (Nat.zero_le _) r.isLt := by ext <;> simp
  have hc : Vertex.edgePoint n 0 r.castSucc =
      Vertex.ofChart n 0 r.val (Nat.zero_le _) r.isLt.le := by ext <;> simp
  rw [boundary_apply, hs, hc, ofGTPattern_ofChart, ofGTPattern_ofChart,
    gtCompletion_zero_left, gtCompletion_zero_left, gtBoundaryPrefix_succ lam.1 r.isLt,
    add_sub_cancel_left]

@[simp] theorem boundaryWeight_zero_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundaryWeight 0 = lam := Subtype.ext (by simp)

@[simp] theorem boundary_one_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundary 1 = P.topRow := by
  rw [← topRow_toGTPattern, toGTPattern_ofGTPattern]

@[simp] theorem boundaryWeight_one_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundaryWeight 1 = P.topWeight := Subtype.ext (by simp)

theorem dual_boundaryWeight_two_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    ((ofGTPattern lam P hP).boundaryWeight 2).dual.1 = lam.1 + P.weight := by
  have hw := weight_toGTPattern (ofGTPattern lam P hP)
  rw [toGTPattern_ofGTPattern, boundary_zero_ofGTPattern] at hw
  ext r
  have hr := congrFun hw r
  simp only [Pi.sub_apply, Pi.add_apply] at hr ⊢
  linarith

/-- Whenever `P` is hive-completable over `lam`, `lam.1 + P.weight` is automatically antitone
(dominant), as the dual of side `2` of `ofGTPattern lam P hP`. -/
theorem antitone_add_weight_of_isGTCompletable {lam : DominantWeight n} {P : GTPattern n}
    (hP : IsGTCompletable lam P) :
    Antitone (lam.1 + P.weight) :=
  dual_boundaryWeight_two_ofGTPattern lam P hP ▸ ((ofGTPattern lam P hP).boundaryWeight 2).dual.2

@[simp]
theorem boundary_two_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) (r : Fin n) :
    (ofGTPattern lam P hP).boundary 2 r = -(lam.1 r.rev + P.weight r.rev) := by
  have hd := congrFun (dual_boundaryWeight_two_ofGTPattern lam P hP) r.rev
  simp only [DominantWeight.dual_apply, coe_boundaryWeight, Fin.rev_rev, Pi.add_apply] at hd
  linarith

theorem boundary_ofGTPattern_eq_productBoundary {lam μ γ : DominantWeight n} {P : GTPattern n}
    (hTop : P.topRow = μ.1) (hWeight : P.weight = γ.1 - lam.1) (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundary = productBoundary lam μ γ := by
  ext s r
  fin_cases s
  · simp
  · rw [Fin.mk_one, boundary_one_ofGTPattern, hTop, productBoundary_one]
  · simp [hWeight]

@[simp] theorem ofGTPattern_toGTPattern (h : IntegerHive n) :
    ofGTPattern (h.boundaryWeight 0) h.toGTPattern h.isGTCompletable_toGTPattern = h := by
  ext p; exact (h.apply_eq_gtCompletion p).symm

/-- Global equivalence between normalized integer hives of size `n` and pairs `(lam, P)` of a
dominant weight and a hive-completable Gelfand–Tsetlin pattern. -/
def integerHiveEquivGTPattern (n : ℕ) :
    IntegerHive n ≃ {lp : DominantWeight n × GTPattern n // IsGTCompletable lp.1 lp.2} where
  toFun h := ⟨(h.boundaryWeight 0, h.toGTPattern), h.isGTCompletable_toGTPattern⟩
  invFun lp := ofGTPattern lp.1.1 lp.1.2 lp.2
  left_inv h := h.ofGTPattern_toGTPattern
  right_inv lp := Subtype.ext <| Prod.ext
    (boundaryWeight_zero_ofGTPattern lp.1.1 lp.1.2 lp.2)
    (toGTPattern_ofGTPattern lp.1.1 lp.1.2 lp.2)

@[simp] theorem integerHiveEquivGTPattern_apply_coe (h : IntegerHive n) :
    (integerHiveEquivGTPattern n h).1 = (h.boundaryWeight 0, h.toGTPattern) := (rfl)

@[simp] theorem integerHiveEquivGTPattern_symm_apply
    (lp : {lp : DominantWeight n × GTPattern n // IsGTCompletable lp.1 lp.2}) :
    (integerHiveEquivGTPattern n).symm lp = ofGTPattern lp.1.1 lp.1.2 lp.2 := (rfl)

/-- **Fixed-boundary hive–pattern equivalence**: integer hives with boundary
`productBoundary lam μ γ` correspond bijectively to Gelfand–Tsetlin patterns `P` with top row `μ`,
weight `γ - λ`, and `IsGTCompletable lam P`. -/
def fixedIntegerHiveEquivGTPattern (lam μ γ : DominantWeight n) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧ IsGTCompletable lam P} where
  toFun h := ⟨h.1.toGTPattern, topRow_toGTPattern_of_productBoundary h.2,
    weight_toGTPattern_of_productBoundary h.2, by
      have hb0 : h.1.boundaryWeight 0 = lam := Subtype.ext (by simp [coe_boundaryWeight, h.2])
      exact hb0.subst (motive := fun l => IsGTCompletable l h.1.toGTPattern)
        h.1.isGTCompletable_toGTPattern⟩
  invFun P := ⟨ofGTPattern lam P.1 P.2.2.2,
    boundary_ofGTPattern_eq_productBoundary P.2.1 P.2.2.1 P.2.2.2⟩
  left_inv h := Subtype.ext <| ext fun p =>
    (apply_eq_gtCompletion_of_productBoundary h.2 p).symm
  right_inv P := Subtype.ext (toGTPattern_ofGTPattern lam P.1 P.2.2.2)

@[simp] theorem fixedIntegerHiveEquivGTPattern_apply_coe (lam μ γ : DominantWeight n)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPattern lam μ γ h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem fixedIntegerHiveEquivGTPattern_symm_apply_coe (lam μ γ : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧ IsGTCompletable lam P}) :
    ((fixedIntegerHiveEquivGTPattern lam μ γ).symm P).1 = ofGTPattern lam P.1 P.2.2.2 := (rfl)

theorem hiveCount_productBoundary_eq_card_gtPattern (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card
        {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧ IsGTCompletable lam P} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivGTPattern lam μ γ)

/-- **Gelfand–Tsetlin reconstruction criterion**: a pattern `P` with top row `μ` and weight
`γ - λ` is the difference pattern of a hive with boundary `productBoundary lam μ γ` (realized via
`gtCompletion lam P`) if and only if the remaining rhombus family holds on `gtCompletion lam P`. -/
theorem gt_reconstruction_iff (lam μ γ : DominantWeight n) (P : GTPattern n)
    (hTop : P.topRow = μ.1) (hWeight : P.weight = γ.1 - lam.1) :
    (∃ h : FixedIntegerHive (productBoundary lam μ γ),
      ∀ v : Vertex n, h.1 v = gtCompletion lam P v.z (n - v.x)) ↔
      ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
        gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
          gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1) := by
  refine ⟨fun ⟨h, hv⟩ i j hij hj => ?_, fun hrem =>
    ⟨(fixedIntegerHiveEquivGTPattern lam μ γ).symm ⟨P, hTop, hWeight, hrem⟩, fun _ => rfl⟩⟩
  have hr := h.1.le_of_isRhombus (isRhombus_ofChart_rem hij hj)
  have hchart (i' j' : ℕ) (hi' : i' ≤ j') (hj' : j' ≤ n) :
      h.1 (Vertex.ofChart n i' j' hi' hj') = gtCompletion lam P i' j' := by
    rw [hv, Vertex.ofChart_z, Vertex.ofChart_x, Nat.sub_sub_self hj']
  rwa [hchart i j hij (by omega), hchart (i + 1) (j + 2) (by omega) hj,
    hchart i (j + 1) (by omega) (by omega),
    hchart (i + 1) (j + 1) (Nat.succ_le_succ hij) (by omega)] at hr

end Reconstruction

/-! ### Cyclic `(λ, μ, ν)` orientation and Henriques–Kamnitzer quasi-hive conversion -/

section CyclicOrientation

variable {n : ℕ}

/-- Two clockwise rotations evaluate `h` at `p.rotate.rotate`, re-normalized by subtracting the
value at `C = (0, 0, n) = (cornerA n).rotate.rotate`. -/
theorem rotate_rotate_apply {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (h : Hive n R) (p : Vertex n) :
    h.rotate.rotate p = h p.rotate.rotate - h (Vertex.cornerA n).rotate.rotate := by
  simp only [rotate_apply]
  abel

/-- Explicit rotation and gauge conversion from cyclic boundary `![lam.1, μ.1, ν.1]` to the product
chart: `h.rotate.rotate` shifts `h ⟨j - i, i, n - j, _⟩` by the constant `+ ∑ r, ν.1 r`. -/
theorem rotate_rotate_ofChart_of_cyclicBoundary {lam μ ν : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = ![lam.1, μ.1, ν.1]) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    h.rotate.rotate (Vertex.ofChart n i j hij hj) =
      h ⟨j - i, i, n - j, by omega⟩ + ∑ r : Fin n, ν.1 r := by
  have hC : (Vertex.cornerA n).rotate.rotate = Vertex.edgePoint n 2 0 := by ext <;> simp
  have hall : ({r : Fin n | 0 ≤ r.val} : Finset (Fin n)) = Finset.univ := by ext r; simp
  rw [h.rotate_rotate_apply, Vertex.rotate_rotate_ofChart, hC, h.apply_edgePoint_two 0,
    Fin.val_zero, hall, hb]
  simp [sub_neg_eq_add]

/-- Rotating twice identifies integer hives of clockwise cyclic boundary `![lam.1, μ.1, ν.1]` with
integer hives of product boundary `productBoundary ν lam μ.dual`. -/
def rotateRotateEquiv (lam μ ν : DominantWeight n) :
    FixedIntegerHive ![lam.1, μ.1, ν.1] ≃ FixedIntegerHive (productBoundary ν lam μ.dual) where
  toFun h := ⟨h.1.rotate.rotate, by
    ext s r
    fin_cases s <;> simp [boundary_rotate, h.2]⟩
  invFun k := ⟨k.1.rotate, by
    ext s r
    fin_cases s <;> simp [boundary_rotate, k.2]⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)

@[simp] theorem rotateRotateEquiv_apply_coe (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive ![lam.1, μ.1, ν.1]) :
    (rotateRotateEquiv lam μ ν h).1 = h.1.rotate.rotate := (rfl)

@[simp] theorem rotateRotateEquiv_symm_apply_coe (lam μ ν : DominantWeight n)
    (k : FixedIntegerHive (productBoundary ν lam μ.dual)) :
    ((rotateRotateEquiv lam μ ν).symm k).1 = k.1.rotate := (rfl)

/-- Directional difference pattern attached to a hive in the cyclic `(λ, μ, ν)` orientation:
`h.toCyclicGTPattern = h.rotate.rotate.toGTPattern`. -/
def toCyclicGTPattern (h : IntegerHive n) : GTPattern n :=
  h.rotate.rotate.toGTPattern

theorem toCyclicGTPattern_def (h : IntegerHive n) :
    h.toCyclicGTPattern = h.rotate.rotate.toGTPattern := (rfl)

/-- The constant gauge offset cancels in `toCyclicGTPattern`, giving the direct lattice difference
`h ⟨j - (i + 1), i + 1, n - j, _⟩ - h ⟨j - i, i, n - j, _⟩` for `0 ≤ i < j ≤ n`. -/
@[simp]
theorem toCyclicGTPattern_apply_of_lt_of_le (h : IntegerHive n) {i j : ℕ} (hij : i < j)
    (hj : j ≤ n) :
    h.toCyclicGTPattern i j =
      h ⟨j - (i + 1), i + 1, n - j, by omega⟩ - h ⟨j - i, i, n - j, by omega⟩ := by
  rw [toCyclicGTPattern_def, toGTPattern_apply_of_lt_of_le _ hij hj, rotate_rotate_apply,
    rotate_rotate_apply, Vertex.rotate_rotate_ofChart, Vertex.rotate_rotate_ofChart]
  abel

@[simp] theorem topRow_toCyclicGTPattern (h : IntegerHive n) :
    h.toCyclicGTPattern.topRow = h.boundary 0 := by
  simp [toCyclicGTPattern_def, boundary_rotate]

@[simp] theorem weight_toCyclicGTPattern (h : IntegerHive n) :
    h.toCyclicGTPattern.weight = (h.boundaryWeight 1).dual.1 - h.boundary 2 := by
  simp [toCyclicGTPattern_def, boundary_rotate, boundaryWeight_rotate]

/-- **Cyclic quasi-hive equivalence (Henriques–Kamnitzer, Theorem 7.4)**: integer hives with
clockwise cyclic boundary `![lam.1, μ.1, ν.1]` correspond bijectively to Gelfand–Tsetlin patterns
with top row `lam.1`, torus weight `μ.dual.1 - ν.1`, and `IsGTCompletable ν P`. -/
def cyclicFixedIntegerHiveEquivGTPattern (lam μ ν : DominantWeight n) :
    FixedIntegerHive ![lam.1, μ.1, ν.1] ≃
      {P : GTPattern n // P.topRow = lam.1 ∧ P.weight = μ.dual.1 - ν.1 ∧ IsGTCompletable ν P} :=
  (rotateRotateEquiv lam μ ν).trans (fixedIntegerHiveEquivGTPattern ν lam μ.dual)

@[simp] theorem cyclicFixedIntegerHiveEquivGTPattern_apply_coe (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive ![lam.1, μ.1, ν.1]) :
    (cyclicFixedIntegerHiveEquivGTPattern lam μ ν h).1 = h.1.toCyclicGTPattern := (rfl)

@[simp] theorem cyclicFixedIntegerHiveEquivGTPattern_symm_apply_coe (lam μ ν : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = lam.1 ∧ P.weight = μ.dual.1 - ν.1 ∧ IsGTCompletable ν P}) :
    ((cyclicFixedIntegerHiveEquivGTPattern lam μ ν).symm P).1 =
      (ofGTPattern ν P.1 P.2.2.2).rotate := (rfl)

end CyclicOrientation

/-! ### Uniform input gap and stable Gelfand–Tsetlin fibre equivalence -/

section UniformInputGap

/-- **Uniform input gap**: when `μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ` for
every `r : Fin n`, the remaining rhombus family holds automatically on `gtCompletion lam P` for
every Gelfand–Tsetlin pattern `P` with top row `μ`. -/
theorem gt_completion_of_uniform_input_gap {n : ℕ} (lam μ : DominantWeight (n + 1))
    (P : GTPattern (n + 1)) (hTop : P.topRow = μ.1)
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    ∀ i j : ℕ, i ≤ j → j + 2 ≤ n + 1 →
      gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
        gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1) := by
  intro i j hij hj
  rw [gtCompletion_rem_iff lam P hj]
  have hnn : 0 ≤ ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
    Finset.sum_nonneg fun k hk => sub_nonneg.mpr <|
      P.entry_le_entry_succ_row (by have := Finset.mem_range.mp hk; omega) (by omega)
  have htele : (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
      P 0 (j + 2) - P (i + 1) (j + 2) := by
    calc (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1)))
        ≤ ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P (k + 1) (j + 2)) :=
          Finset.sum_le_sum fun k _ => sub_le_sub_left (P.entry_succ_succ_le_entry (by omega)) _
      _ = P 0 (j + 2) - P (i + 1) (j + 2) := Finset.sum_range_sub' (fun k => P k (j + 2)) (i + 1)
  have hhi : P 0 (j + 2) ≤ μ.1 0 := hTop ▸ (P.entry_mem_Icc (Nat.zero_lt_succ (j + 1)) hj).2
  have hlo : μ.1 (Fin.last n) ≤ P (i + 1) (j + 2) :=
    hTop ▸ (P.entry_mem_Icc (Nat.succ_lt_succ (Nat.lt_succ_of_le hij)) hj).1
  have hg := hGap ⟨j, by omega⟩
  simp only [Fin.castSucc_mk, Fin.succ_mk] at hg
  linarith

theorem isGTCompletable_of_uniform_input_gap {n : ℕ} {lam μ : DominantWeight (n + 1)}
    {P : GTPattern (n + 1)} (hTop : P.topRow = μ.1)
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    IsGTCompletable lam P :=
  gt_completion_of_uniform_input_gap lam μ P hTop hGap

/-- Under the uniform input gap on `lam`, fixed-boundary integer hives with boundary
`productBoundary lam μ γ` are equivalent to the entire weight-`(γ - λ)` Gelfand–Tsetlin fibre over
`μ`. -/
def stableGTPatternEquiv {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans
    (Equiv.subtypeEquivRight fun P =>
      ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩,
        fun ⟨ht, hw⟩ => ⟨ht, hw, gt_completion_of_uniform_input_gap lam μ P ht hGap⟩⟩)

@[simp] theorem stableGTPatternEquiv_apply_coe {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (stableGTPatternEquiv lam μ γ hGap h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem stableGTPatternEquiv_symm_apply {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (P : {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1}) (v : Vertex (n + 1)) :
    ((stableGTPatternEquiv lam μ γ hGap).symm P).1 v =
      gtCompletion lam P.1 v.z (n + 1 - v.x) := (rfl)

theorem hiveCount_eq_card_gtPattern_of_uniform_input_gap {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (stableGTPatternEquiv lam μ γ hGap)

/-- In the stable range, the difference map gives an equivalence onto the full weight-`(γ - λ)`
Gelfand–Tsetlin fibre over `μ` with `gtCompletion` as inverse chart formula. -/
theorem exists_stable_gt_equiv {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    ∃ e : FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1},
      ∀ h v, h.1 v = gtCompletion lam (e h).1 v.z (n + 1 - v.x) :=
  ⟨stableGTPatternEquiv lam μ γ hGap,
    fun h v => apply_eq_gtCompletion_of_productBoundary h.2 v⟩

end UniformInputGap

/-! ### Low-rank equivalences and concrete checks (`n = 0, 1, 2, 3`) -/

section LowRankAndChecks

/-- For `n ≤ 1`, there are no `j` with `j + 2 ≤ n`, so `IsGTCompletable` holds vacuously. -/
theorem isGTCompletable_of_le_one {n : ℕ} (hn : n ≤ 1) (lam : DominantWeight n) (P : GTPattern n) :
    IsGTCompletable lam P :=
  fun _ _ _ hj => absurd hj (by omega)

/-- At `n = 0`, the unique empty hive corresponds unconditionally to the unique empty pattern. -/
def fixedIntegerHiveEquivGTPatternZero (lam μ γ : DominantWeight 0) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern 0 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans
    (Equiv.subtypeEquivRight fun P =>
      ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩,
        fun ⟨ht, hw⟩ => ⟨ht, hw, isGTCompletable_of_le_one (Nat.zero_le 1) lam P⟩⟩)

@[simp] theorem fixedIntegerHiveEquivGTPatternZero_apply_coe (lam μ γ : DominantWeight 0)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPatternZero lam μ γ h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem fixedIntegerHiveEquivGTPatternZero_symm_apply_coe (lam μ γ : DominantWeight 0)
    (P : {P : GTPattern 0 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1}) :
    ((fixedIntegerHiveEquivGTPatternZero lam μ γ).symm P).1 =
      ofGTPattern lam P.1 (isGTCompletable_of_le_one (Nat.zero_le 1) lam P.1) := (rfl)

/-- At `n = 1`, fixed-boundary hives correspond unconditionally to patterns of top row `μ` and
weight `γ - λ`. -/
def fixedIntegerHiveEquivGTPatternOne (lam μ γ : DominantWeight 1) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern 1 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans
    (Equiv.subtypeEquivRight fun P =>
      ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩,
        fun ⟨ht, hw⟩ => ⟨ht, hw, isGTCompletable_of_le_one le_rfl lam P⟩⟩)

@[simp] theorem fixedIntegerHiveEquivGTPatternOne_apply_coe (lam μ γ : DominantWeight 1)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPatternOne lam μ γ h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem fixedIntegerHiveEquivGTPatternOne_symm_apply_coe (lam μ γ : DominantWeight 1)
    (P : {P : GTPattern 1 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1}) :
    ((fixedIntegerHiveEquivGTPatternOne lam μ γ).symm P).1 =
      ofGTPattern lam P.1 (isGTCompletable_of_le_one le_rfl lam P.1) := (rfl)

/-- At `n = 1`, `hiveCount (productBoundary lam μ γ)` is `1` when `lam.1 0 + μ.1 0 = γ.1 0` and
`0` otherwise. -/
theorem hiveCount_one_productBoundary (lam μ γ : DominantWeight 1) :
    hiveCount (productBoundary lam μ γ) = if lam.1 0 + μ.1 0 = γ.1 0 then 1 else 0 := by
  rw [← natCard_fixedIntegerHive, Nat.card_congr (fixedIntegerHiveEquivGTPatternOne lam μ γ)]
  let P₀ : {P : GTPattern 1 // P.topRow = μ.1} := default
  have hw₀ : P₀.1.weight 0 = μ.1 0 := by
    have hsum := P₀.1.sum_weight
    simp only [Fin.sum_univ_one, P₀.2] at hsum
    exact hsum
  have : Subsingleton {P : GTPattern 1 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} :=
    ⟨fun P Q => Subtype.ext <| Subtype.mk.inj <|
      Subsingleton.elim (⟨P.1, P.2.1⟩ : {R : GTPattern 1 // R.topRow = μ.1}) ⟨Q.1, Q.2.1⟩⟩
  split_ifs with hsum
  · have : Unique {P : GTPattern 1 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} :=
      uniqueOfSubsingleton ⟨P₀.1, P₀.2, funext fun r => by
        rw [Subsingleton.elim r 0, hw₀, Pi.sub_apply]; omega⟩
    exact Nat.card_unique
  · refine Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨Q, hQtop, hQw⟩ => hsum ?_⟩)
    have hQeq : Q = P₀.1 := congrArg Subtype.val
      (Subsingleton.elim (⟨Q, hQtop⟩ : {P : GTPattern 1 // P.topRow = μ.1}) P₀)
    have hr := congrFun hQw 0
    rw [hQeq, hw₀, Pi.sub_apply] at hr
    omega

/-- **Rank-`2` remaining rhombus criterion**: for a pattern `P : GTPattern 2` with top row `μ` and
weight `γ - λ`, `IsGTCompletable lam P` reduces to the single inequality
`lam.1 1 + μ.1 0 ≤ γ.1 0`. -/
theorem isGTCompletable_two_iff (lam μ γ : DominantWeight 2) (P : GTPattern 2)
    (hTop : P.topRow = μ.1) (hWeight : P.weight = γ.1 - lam.1) :
    IsGTCompletable lam P ↔ lam.1 1 + μ.1 0 ≤ γ.1 0 := by
  rw [isGTCompletable_def]
  have hP02 : P 0 2 = μ.1 0 := by simpa [GTPattern.topRow_apply] using congrFun hTop 0
  have h00 : gtCompletion lam P 0 0 + gtCompletion lam P 1 2 ≤
      gtCompletion lam P 0 1 + gtCompletion lam P 1 1 ↔ lam.1 1 + μ.1 0 ≤ γ.1 0 := by
    have h12 : gtCompletion lam P 1 2 = lam.1 0 + lam.1 1 + μ.1 0 := by
      rw [gtCompletion_def, gtBoundaryPrefix_of_le lam.1 le_rfl, Fin.sum_univ_two,
        Finset.sum_range_one, hP02]
    have h01 : gtCompletion lam P 0 1 = lam.1 0 := by
      rw [gtCompletion_zero_left, gtBoundaryPrefix_succ lam.1 (by decide), gtBoundaryPrefix_zero,
        zero_add]; rfl
    have h11 : gtCompletion lam P 1 1 = γ.1 0 := by
      rw [gtCompletion_self_of_weight hWeight (by decide), gtBoundaryPrefix_succ γ.1 (by decide),
        gtBoundaryPrefix_zero, zero_add]; rfl
    rw [gtCompletion_zero_left, gtBoundaryPrefix_zero, h12, h01, h11]; omega
  refine ⟨fun h => h00.mp (h 0 0 le_rfl le_rfl), fun h i j hij hj => ?_⟩
  obtain rfl : j = 0 := by omega
  obtain rfl : i = 0 := by omega
  exact h00.mpr h

/-- Two rank-`2` patterns with the same top row and weight are equal. -/
theorem eq_of_topRow_eq_of_weight_eq_two {P Q : GTPattern 2} (ht : P.topRow = Q.topRow)
    (hw : P.weight = Q.weight) : P = Q := by
  ext i j
  by_cases hij : i < j ∧ j ≤ 2
  · obtain ⟨hlt, hle⟩ := hij
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hP1 : P.weight 0 = P 0 1 := by simp [GTPattern.weight_apply, GTPattern.rowSum_def]
      have hQ1 : Q.weight 0 = Q 0 1 := by simp [GTPattern.weight_apply, GTPattern.rowSum_def]
      linarith [congrFun hw 0]
    · simpa [GTPattern.topRow_apply] using congrFun ht 0
    · simpa [GTPattern.topRow_apply] using congrFun ht 1
  · rw [P.entry_eq_zero (by omega), Q.entry_eq_zero (by omega)]

/-- Cardinality of a rank-`2` Gelfand–Tsetlin weight fibre over a dominant top row `μ`. -/
theorem card_gtPattern_two_topRow_weight (μ : DominantWeight 2) (w : Fin 2 → ℤ) :
    Nat.card {P : GTPattern 2 // P.topRow = μ.1 ∧ P.weight = w} =
      if w 0 + w 1 = μ.1 0 + μ.1 1 ∧ μ.1 1 ≤ w 0 ∧ w 0 ≤ μ.1 0 then 1 else 0 := by
  have : Subsingleton {P : GTPattern 2 // P.topRow = μ.1 ∧ P.weight = w} :=
    ⟨fun P Q => Subtype.ext (eq_of_topRow_eq_of_weight_eq_two (P.2.1.trans Q.2.1.symm)
      (P.2.2.trans Q.2.2.symm))⟩
  split_ifs with hcond
  · obtain ⟨hsum, hlo, hhi⟩ := hcond
    let Q₁ : GTPattern 1 := GTPattern.equivOne.symm ![w 0]
    have hQ₁ : Q₁.topRow = ![w 0] :=
      (GTPattern.equivOne_apply Q₁).symm.trans (GTPattern.equivOne.apply_symm_apply ![w 0])
    have hint : Interlaces μ.1 Q₁.topRow :=
      interlaces_iff.mpr fun i => by rw [Subsingleton.elim i 0, hQ₁]; exact ⟨hhi, hlo⟩
    let P : GTPattern 2 := Q₁.extend μ.1 hint
    have hPtop : P.topRow = μ.1 := GTPattern.topRow_extend Q₁ μ.1 hint
    have hPw0 : P.weight 0 = w 0 := by
      have h0 : P.weight 0 = Q₁.weight 0 := GTPattern.weight_extend_castSucc Q₁ μ.1 hint 0
      have hs := Q₁.sum_weight
      simp only [Fin.sum_univ_one, hQ₁, Matrix.cons_val_zero] at hs
      exact h0.trans hs
    have hPw1 : P.weight 1 = w 1 := by
      have hs := P.sum_weight
      simp only [Fin.sum_univ_two, hPtop, hPw0] at hs
      omega
    have hPw : P.weight = w := by ext r; fin_cases r; exacts [hPw0, hPw1]
    have : Unique {Q : GTPattern 2 // Q.topRow = μ.1 ∧ Q.weight = w} :=
      uniqueOfSubsingleton ⟨P, hPtop, hPw⟩
    exact Nat.card_unique
  · refine Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨P, hPt, hPw⟩ => hcond ?_⟩)
    have hsum : w 0 + w 1 = μ.1 0 + μ.1 1 := by
      have hs := P.sum_weight; simp only [hPw, hPt, Fin.sum_univ_two] at hs; exact hs
    have hmem := P.weight_mem_Icc 0
    rw [hPw, hPt] at hmem
    exact ⟨hsum, hmem.1, hmem.2⟩

/-- **Closed-form `GL₂` Clebsch–Gordan formula for `hiveCount`**: at rank `2`,
`hiveCount (productBoundary lam μ γ)` equals `1` when `|λ| + |μ| = |γ|` and
`max (λ₀ + μ₁) (λ₁ + μ₀) ≤ γ₀ ≤ λ₀ + μ₀`, and `0` otherwise. -/
theorem hiveCount_two_productBoundary (lam μ γ : DominantWeight 2) :
    hiveCount (productBoundary lam μ γ) =
      if (lam.1 0 + lam.1 1) + (μ.1 0 + μ.1 1) = γ.1 0 + γ.1 1 ∧
          max (lam.1 0 + μ.1 1) (lam.1 1 + μ.1 0) ≤ γ.1 0 ∧ γ.1 0 ≤ lam.1 0 + μ.1 0
        then 1 else 0 := by
  rw [hiveCount_productBoundary_eq_card_gtPattern]
  have heq :
      Nat.card
        {P : GTPattern 2 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧ IsGTCompletable lam P} =
      if lam.1 1 + μ.1 0 ≤ γ.1 0 then
        Nat.card {P : GTPattern 2 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1}
      else 0 := by
    split_ifs with hrem
    · exact Nat.card_congr (Equiv.subtypeEquivRight fun P =>
        ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩,
          fun ⟨ht, hw⟩ => ⟨ht, hw, (isGTCompletable_two_iff lam μ γ P ht hw).mpr hrem⟩⟩)
    · refine Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨P, ht, hw, hc⟩ =>
        hrem ((isGTCompletable_two_iff lam μ γ P ht hw).mp hc)⟩)
  rw [heq, card_gtPattern_two_topRow_weight μ (γ.1 - lam.1)]
  simp only [Pi.sub_apply, max_le_iff]
  split_ifs <;> omega

/-- Rank-`2` check outside the stable range: for `λ = (0, 0)`, `μ = (2, 0)`, and `γ = (1, 1)`, the
Gelfand–Tsetlin weight-`(1, 1)` fibre over `μ` has cardinality `1`, whereas `hiveCount` is `0`
because `λ₁ + μ₀ = 2 ≤ 1 = γ₀` fails (while `γ = (2, 0)` has `hiveCount = 1`). -/
theorem rank_two_unstable_check :
    let lam : DominantWeight 2 := 0
    let μ : DominantWeight 2 := ⟨![2, 0], by decide⟩
    let γ_bad : DominantWeight 2 := ⟨![1, 1], by decide⟩
    let γ_good : DominantWeight 2 := ⟨![2, 0], by decide⟩
    Nat.card {P : GTPattern 2 // P.topRow = μ.1 ∧ P.weight = γ_bad.1 - lam.1} = 1 ∧
      hiveCount (productBoundary lam μ γ_bad) = 0 ∧
      hiveCount (productBoundary lam μ γ_good) = 1 := by
  dsimp only
  refine ⟨(card_gtPattern_two_topRow_weight ⟨![2, 0], by decide⟩ _).trans ?_, ?_, ?_⟩
  · simp only [Pi.sub_apply, DominantWeight.zero_apply]; decide
  · rw [hiveCount_two_productBoundary]; simp only [DominantWeight.zero_apply, max_le_iff]; decide
  · rw [hiveCount_two_productBoundary]; simp only [DominantWeight.zero_apply, max_le_iff]; decide

/-- Rank-`2` check in the stable range: for `λ = μ = (2, 0)`, the uniform input gap holds and each
of `γ = (4, 0)`, `(3, 1)`, `(2, 2)` has `hiveCount = 1`. -/
theorem rank_two_stable_clebsch_gordan_check :
    let lam : DominantWeight 2 := ⟨![2, 0], by decide⟩
    let μ : DominantWeight 2 := ⟨![2, 0], by decide⟩
    (∀ r : Fin 1, μ.1 0 - μ.1 (Fin.last 1) ≤ lam.1 r.castSucc - lam.1 r.succ) ∧
      hiveCount (productBoundary lam μ ⟨![4, 0], by decide⟩) = 1 ∧
      hiveCount (productBoundary lam μ ⟨![3, 1], by decide⟩) = 1 ∧
      hiveCount (productBoundary lam μ ⟨![2, 2], by decide⟩) = 1 := by
  dsimp only
  refine ⟨by decide, ?_, ?_, ?_⟩ <;> rw [hiveCount_two_productBoundary] <;> decide

private def adjointZeroPattern (b : Bool) : GTPattern 3 where
  entry i j :=
    match i, j with
    | 0, 3 => 1
    | 2, 3 => -1
    | 0, 2 => if b then 1 else 0
    | 1, 2 => if b then -1 else 0
    | _, _ => 0
  zeros' {i j} hout := by
    match i, j with
    | 0, 3 | 2, 3 | 0, 2 | 1, 2 => omega
    | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 1, 3 | 2, 0 | 2, 1 | 2, 2 => rfl
    | i + 3, _ => rfl
    | 0, j + 4 | 1, j + 4 | 2, j + 4 => rfl
  interlacing' {i j} hij hj := by
    have : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases b <;> decide

@[simp]
private theorem adjointZeroPattern_apply (b : Bool) (i j : ℕ) :
    adjointZeroPattern b i j =
      match i, j with
      | 0, 3 => 1
      | 2, 3 => -1
      | 0, 2 => if b then 1 else 0
      | 1, 2 => if b then -1 else 0
      | _, _ => 0 := by
  rw [← congrFun₂ (GTPattern.entry_eq_coe (P := adjointZeroPattern b)) i j]
  rfl

private theorem adjointZeroPattern_topRow (b : Bool) :
    (adjointZeroPattern b).topRow = ![1, 0, -1] := by
  ext i; fin_cases i <;> simp [GTPattern.topRow_apply]

private theorem adjointZeroPattern_weight (b : Bool) :
    (adjointZeroPattern b).weight = 0 := by
  ext r; fin_cases r <;> cases b <;>
    simp [GTPattern.weight_apply, GTPattern.rowSum_def, Finset.sum_range_succ]

/-- Explicit bijection between the weight-`0` Gelfand–Tsetlin fibre over the rational `SL₃` adjoint
top row `(1, 0, -1)` and `Bool`, corresponding to the two middle rows `(0, 0)` and `(1, -1)`. -/
def gtPatternThreeAdjointZeroEquiv :
    {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.weight = 0} ≃ Bool where
  toFun P := decide (P.1 0 2 = 1)
  invFun b := ⟨adjointZeroPattern b, adjointZeroPattern_topRow b, adjointZeroPattern_weight b⟩
  left_inv := by
    rintro ⟨P, hTop, hW⟩
    have h03 : P 0 3 = 1 := by simpa [GTPattern.topRow_apply] using congrFun hTop 0
    have h13 : P 1 3 = 0 := by simpa [GTPattern.topRow_apply] using congrFun hTop 1
    have h23 : P 2 3 = -1 := by simpa [GTPattern.topRow_apply] using congrFun hTop 2
    have h01 : P 0 1 = 0 := by
      simpa [GTPattern.weight_apply, GTPattern.rowSum_def] using congrFun hW 0
    have hrow2 : P 0 2 + P 1 2 = 0 := by
      simpa [GTPattern.weight_apply, GTPattern.rowSum_def, Finset.sum_range_succ, h01] using
        congrFun hW 1
    have h02_lo : 0 ≤ P 0 2 := by
      simpa [h13] using P.entry_succ_succ_le_entry (i := 0) (j := 2) (by decide)
    have h02_hi : P 0 2 ≤ 1 := by
      simpa [h03] using P.entry_le_entry_succ_row (i := 0) (j := 2) (by decide) (by decide)
    apply Subtype.ext
    ext i j
    dsimp only
    rcases (by omega : P 0 2 = 0 ∨ P 0 2 = 1) with h02 | h02
    · rw [h02]
      by_cases hij : i < j ∧ j ≤ 3
      · (rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨
            (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3)) with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [h01, h02, h03, h13, h23]); omega
      · have hf : decide ((0 : ℤ) = 1) = false := by decide
        rw [hf, (adjointZeroPattern false).entry_eq_zero (by omega), P.entry_eq_zero (by omega)]
    · rw [h02]
      by_cases hij : i < j ∧ j ≤ 3
      · (rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨
            (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3)) with
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [h01, h02, h03, h13, h23]); omega
      · have ht : decide ((1 : ℤ) = 1) = true := by decide
        rw [ht, (adjointZeroPattern true).entry_eq_zero (by omega), P.entry_eq_zero (by omega)]
  right_inv b := by cases b <;> simp

@[simp] theorem gtPatternThreeAdjointZeroEquiv_apply
    (P : {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.weight = 0}) :
    gtPatternThreeAdjointZeroEquiv P = decide (P.1 0 2 = 1) := (rfl)

@[simp] theorem gtPatternThreeAdjointZeroEquiv_symm_apply (b : Bool) (i j : ℕ) :
    (gtPatternThreeAdjointZeroEquiv.symm b).1 i j =
      match i, j with
      | 0, 3 => 1
      | 2, 3 => -1
      | 0, 2 => if b then 1 else 0
      | 1, 2 => if b then -1 else 0
      | _, _ => 0 :=
  adjointZeroPattern_apply b i j

/-- Rank-`3` check: the weight-`0` Gelfand–Tsetlin fibre over the `SL₃` adjoint weight `(1, 0, -1)`
has cardinality `2` (the `2`-dimensional zero weight space of `𝔰𝔩₃`). -/
theorem card_gtPattern_three_adjoint_weight_zero :
    Nat.card {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.weight = 0} = 2 := by
  simp [Nat.card_congr gtPatternThreeAdjointZeroEquiv]

/-- Rank-`3` check: although the weight-`0` Gelfand–Tsetlin fibre over `μ = (1, 0, -1)` has two
patterns, neither satisfies `IsGTCompletable 0 P`, so
`hiveCount (productBoundary 0 ⟨![1, 0, -1], _⟩ 0) = 0`. -/
theorem hiveCount_three_zero_adjoint_zero :
    hiveCount (productBoundary (0 : DominantWeight 3) ⟨![1, 0, -1], by decide⟩ 0) = 0 := by
  rw [hiveCount_eq_zero_iff]
  refine ⟨fun h => ?_⟩
  obtain ⟨P, hTop, hW, hComp⟩ := fixedIntegerHiveEquivGTPattern 0 ⟨![1, 0, -1], by decide⟩ 0 h
  have hzero : (0 : DominantWeight 3).1 = 0 := by ext; simp
  have h00 := hComp 0 0 le_rfl (by decide)
  have h01 := hComp 0 1 (Nat.zero_le 1) le_rfl
  have h03 : P 0 3 = 1 := by simpa [GTPattern.topRow_apply] using congrFun hTop 0
  have hP01 : P 0 1 = 0 := by
    simpa [GTPattern.weight_apply, GTPattern.rowSum_def, hzero] using congrFun hW 0
  simp only [gtCompletion_def, hzero, gtBoundaryPrefix_zero_seq, zero_add, Nat.reduceAdd,
    Finset.sum_range_zero, Finset.sum_range_one, h03, hP01] at h00 h01
  omega

end LowRankAndChecks

end TauCeti.Hive
