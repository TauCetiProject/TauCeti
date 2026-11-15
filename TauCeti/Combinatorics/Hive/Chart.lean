/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.PartialSum
public import TauCeti.Combinatorics.Hive.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The product chart on the triangular lattice and its three unit-rhombus families

In tensor-product conventions, a lattice point of the size-`n` hive triangle `Hive.Vertex n` is
conveniently indexed by a pair `(i, j)` with `0 ≤ i ≤ j ≤ n` via
`Hive.Vertex.ofChart n i j : (i, j) ↦ (n - j, j - i, i)`. The three clockwise boundary sides
`A → B`, `B → C`, and `C → A` become the edges `i = 0`, `j = n`, and `i = j`, so on a hive with
boundary `productBoundary λ μ γ = (λ, μ, γ*)` the boundary values are `h(0, j) = ∑_{r < j} λ_r`,
`h(i, n) = |λ| + ∑_{r < i} μ_r`, and `h(j, j) = ∑_{r < j} γ_r`.

Every unit rhombus in `Hive.Vertex n` belongs, up to swapping opposite corners, to one of three
two-index families in `(i, j)` coordinates (`isRhombus_ofChart_one`, `isRhombus_ofChart_two`,
`isRhombus_ofChart_three`), giving an exact characterization of `Hive.IsRhombusConcave` over any
preordered abelian group (`isRhombusConcave_iff_ofChart`). Two clockwise rotations convert the
symmetric cyclic boundary `cyclicBoundary λ μ ν = (λ, μ, ν)` into `productBoundary ν λ μ*`.

## Main definitions

* `TauCeti.Hive.Vertex.ofChart`: the product chart `(i, j) ↦ (n - j, j - i, i)` for `i ≤ j ≤ n`.
* `TauCeti.Hive.cyclicBoundary`: the clockwise cyclic boundary `(λ, μ, ν)` for invariant triples.

## Main results

* `TauCeti.Hive.isRhombus_ofChart_one`, `TauCeti.Hive.isRhombus_ofChart_two`,
  `TauCeti.Hive.isRhombus_ofChart_three`: the three unit-rhombus families in `(i, j)` coordinates.
* `TauCeti.Hive.isRhombusConcave_iff_ofChart`: characterization of rhombus concavity by the three
  product-chart inequality families.
* `TauCeti.Hive.apply_ofChart_zero`, `TauCeti.Hive.apply_ofChart_last`,
  `TauCeti.Hive.apply_ofChart_diag`, `TauCeti.Hive.apply_ofChart_diag_of_productBoundary`:
  hive values along the three boundary sides in the product chart.
* `TauCeti.Hive.boundary_rotate_rotate_of_cyclicBoundary`: rotation conversion from cyclic boundary
  `(λ, μ, ν)` to `productBoundary ν λ μ*`.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. Henriques and J. Kamnitzer, *Crystals and coboundary categories*, Duke Math. J. **132**
  (2006), 191–216, §7.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

namespace Vertex

/-- Construct the lattice vertex `(n - j, j - i, i)` from product-chart coordinates `0 ≤ i ≤ j ≤ n`.
-/
def ofChart (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) : Vertex n :=
  ⟨n - j, j - i, i, by omega⟩

@[simp] theorem ofChart_x (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (ofChart n i j hij hjn).x = n - j := (rfl)

@[simp] theorem ofChart_y (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (ofChart n i j hij hjn).y = j - i := (rfl)

@[simp] theorem ofChart_z (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (ofChart n i j hij hjn).z = i := (rfl)

/-- `Vertex.ofChart` is `Vertex.ofYZ` at `y = j - i` and `z = i`. -/
theorem ofChart_eq_ofYZ (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    ofChart n i j hij hjn = ofYZ n (j - i) i (by omega) := by
  ext <;> simp; omega

@[simp] theorem ofChart_eq_iff {n i₁ j₁ i₂ j₂ : ℕ} {h₁ : i₁ ≤ j₁} {h₁' : j₁ ≤ n}
    {h₂ : i₂ ≤ j₂} {h₂' : j₂ ≤ n} :
    ofChart n i₁ j₁ h₁ h₁' = ofChart n i₂ j₂ h₂ h₂' ↔ i₁ = i₂ ∧ j₁ = j₂ := by
  refine ⟨fun h => ?_, fun ⟨hi, hj⟩ => by subst hi; subst hj; rfl⟩
  have hz : i₁ = i₂ := congrArg Vertex.z h
  have hx : n - j₁ = n - j₂ := congrArg Vertex.x h
  exact ⟨hz, by omega⟩

/-- Every vertex `p : Vertex n` is recovered in the product chart at `i = p.z`, `j = n - p.x`. -/
@[simp] theorem ofChart_z_sub_x {n : ℕ} (p : Vertex n) :
    ofChart n p.z (n - p.x) (by have := p.sum_eq; omega) (Nat.sub_le n p.x) = p := by
  have hp := p.sum_eq
  ext <;> simp <;> omega

@[simp] theorem ofChart_zero_zero (n : ℕ) :
    ofChart n 0 0 (Nat.zero_le 0) (Nat.zero_le n) = cornerA n := by
  ext <;> simp

/-- Setting `i = 0` in the product chart gives the `j`-th vertex along side `A → B`. -/
theorem ofChart_zero_left (n j : ℕ) (hjn : j ≤ n) :
    ofChart n 0 j (Nat.zero_le j) hjn = edgePoint n 0 ⟨j, by omega⟩ := by
  ext <;> simp

/-- Setting `j = n` in the product chart gives the `i`-th vertex along side `B → C`. -/
theorem ofChart_last_right (n i : ℕ) (hin : i ≤ n) :
    ofChart n i n hin le_rfl = edgePoint n 1 ⟨i, by omega⟩ := by
  ext <;> simp

/-- Setting `i = j` in the product chart gives the `(n - j)`-th vertex along side `C → A`. -/
theorem ofChart_diag (n j : ℕ) (hjn : j ≤ n) :
    ofChart n j j le_rfl hjn = edgePoint n 2 ⟨n - j, by omega⟩ := by
  ext <;> simp; omega

end Vertex

/-! ### The three unit-rhombus families in the product chart -/

section RhombusChart

/-- First unit-rhombus family in `(i, j)` coordinates (`0 ≤ i < j < n`), with obtuse corners
`(i, j)` and `(i + 1, j + 1)` and acute corners `(i, j + 1)` and `(i + 1, j)`. -/
theorem isRhombus_ofChart_one {n i j : ℕ} (hij : i < j) (hjn : j < n) :
    IsRhombus
      (Vertex.ofChart n i j (by omega) (by omega))
      (Vertex.ofChart n i (j + 1) (by omega) (by omega))
      (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega))
      (Vertex.ofChart n (i + 1) j (by omega) (by omega)) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hy00 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy01 : ((j + 1 - i : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  have hy11 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy10 : ((j - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  refine ⟨by simp; omega, by simp; omega, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.ofChart_x, Vertex.ofChart_y, Vertex.ofChart_z,
      hx0, hx1, hy00, hy01, hy11, hy10, Nat.cast_add, Nat.cast_one]
    ring

/-- Second unit-rhombus family in `(i, j)` coordinates (`0 ≤ i < j < n`), with obtuse corners
`(i + 1, j)` and `(i + 1, j + 1)` and acute corners `(i, j)` and `(i + 2, j + 1)`. -/
theorem isRhombus_ofChart_two {n i j : ℕ} (hij : i < j) (hjn : j < n) :
    IsRhombus
      (Vertex.ofChart n (i + 1) j (by omega) (by omega))
      (Vertex.ofChart n i j (by omega) (by omega))
      (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega))
      (Vertex.ofChart n (i + 2) (j + 1) (by omega) (by omega)) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hy00 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy10 : ((j - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  have hy11 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy21 : ((j + 1 - (i + 2) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  refine ⟨by simp, by simp; omega, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.ofChart_x, Vertex.ofChart_y, Vertex.ofChart_z,
      hx0, hx1, hy00, hy10, hy11, hy21, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring

/-- Third unit-rhombus family in `(i, j)` coordinates (`0 ≤ i ≤ j`, `j + 2 ≤ n`), with obtuse
corners `(i, j + 1)` and `(i + 1, j + 1)` and acute corners `(i, j)` and `(i + 1, j + 2)`. -/
theorem isRhombus_ofChart_three {n i j : ℕ} (hij : i ≤ j) (hjn : j + 2 ≤ n) :
    IsRhombus
      (Vertex.ofChart n i (j + 1) (by omega) (by omega))
      (Vertex.ofChart n i j (by omega) (by omega))
      (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega))
      (Vertex.ofChart n (i + 1) (j + 2) (by omega) (by omega)) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hx2 : ((n - (j + 2) : ℕ) : ℤ) = (n : ℤ) - j - 2 := by omega
  have hy00 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy01 : ((j + 1 - i : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  have hy11 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy12 : ((j + 2 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  refine ⟨by simp; omega, by simp; omega, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.ofChart_x, Vertex.ofChart_y, Vertex.ofChart_z,
      hx0, hx1, hx2, hy00, hy01, hy11, hy12, Nat.cast_add, Nat.cast_one]
    ring

/-- Every side of a unit rhombus changes each barycentric coordinate by `-1`, `0`, or `1`. -/
private theorem coord_sub_mem_Icc_of_sqDist_eq_two {n : ℕ} {p q : Vertex n}
    (h : p.sqDist q = 2) :
    (-1 ≤ (p.x : ℤ) - q.x ∧ (p.x : ℤ) - q.x ≤ 1) ∧
      (-1 ≤ (p.y : ℤ) - q.y ∧ (p.y : ℤ) - q.y ≤ 1) ∧
      (-1 ≤ (p.z : ℤ) - q.z ∧ (p.z : ℤ) - q.z ≤ 1) := by
  rw [Vertex.sqDist_def] at h
  refine ⟨?_, ?_, ?_⟩
  · simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (a := (p.x : ℤ) - q.x) (b := 2)
      (by decide)).mpr (by linarith [sq_nonneg ((p.y : ℤ) - q.y), sq_nonneg ((p.z : ℤ) - q.z)])
  · simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (a := (p.y : ℤ) - q.y) (b := 2)
      (by decide)).mpr (by linarith [sq_nonneg ((p.x : ℤ) - q.x), sq_nonneg ((p.z : ℤ) - q.z)])
  · simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (a := (p.z : ℤ) - q.z) (b := 2)
      (by decide)).mpr (by linarith [sq_nonneg ((p.x : ℤ) - q.x), sq_nonneg ((p.y : ℤ) - q.y)])

/-- Long-diagonal coordinate differences of a unit rhombus have at least one coordinate equal to
`±2` (since three squares in `{0, 1, 4}` summing to `6` cannot all be `≤ 1`). -/
private theorem long_diag_cases_of_isRhombus {n : ℕ} {a b c d : Vertex n}
    (hr : IsRhombus a b c d) :
    ((d.y : ℤ) - b.y = -2 ∨ (d.y : ℤ) - b.y = 2) ∨
      ((d.z : ℤ) - b.z = 2 ∨ (d.z : ℤ) - b.z = -2) ∨
      ((d.x : ℤ) - b.x = -2 ∨ (d.x : ℤ) - b.x = 2) := by
  obtain ⟨hax, hay, haz⟩ := coord_sub_mem_Icc_of_sqDist_eq_two hr.side_ab
  obtain ⟨hcx, hcy, hcz⟩ := coord_sub_mem_Icc_of_sqDist_eq_two
    (Vertex.sqDist_comm b c ▸ hr.side_bc)
  have hmx := hr.midpoint_x; have hmy := hr.midpoint_y; have hmz := hr.midpoint_z
  have hlong := hr.long
  rw [Vertex.sqDist_comm, Vertex.sqDist_def] at hlong
  have hsq : ∀ u : ℤ, -2 ≤ u → u ≤ 2 → u ^ 2 ≤ 1 ∨ (u = -2 ∨ u = 2) := by
    intro u hlo hhi
    rcases (by omega : u = -2 ∨ u = -1 ∨ u = 0 ∨ u = 1 ∨ u = 2) with
      rfl | rfl | rfl | rfl | rfl <;> decide
  rcases hsq ((d.x : ℤ) - b.x) (by omega) (by omega) with hx | hx
  · rcases hsq ((d.y : ℤ) - b.y) (by omega) (by omega) with hy | hy
    · rcases hsq ((d.z : ℤ) - b.z) (by omega) (by omega) with hz | hz
      · omega
      · exact Or.inr (Or.inl hz.symm)
    · exact Or.inl hy
  · exact Or.inr (Or.inr hx)

private theorem le_of_isRhombus_dy_neg_two {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    {f : Vertex n → R}
    (h₁ : ∀ i j (hij : i < j) (hjn : j < n),
      f (Vertex.ofChart n i (j + 1) (by omega) (by omega)) +
          f (Vertex.ofChart n (i + 1) j (by omega) (by omega)) ≤
        f (Vertex.ofChart n i j (by omega) (by omega)) +
          f (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega)))
    {a b c d : Vertex n} (hr : IsRhombus a b c d) (hdy : (d.y : ℤ) - b.y = -2) :
    f b + f d ≤ f a + f c := by
  obtain ⟨_, _, haz⟩ := coord_sub_mem_Icc_of_sqDist_eq_two hr.side_ab
  obtain ⟨_, _, hcz⟩ := coord_sub_mem_Icc_of_sqDist_eq_two
    (Vertex.sqDist_comm b c ▸ hr.side_bc)
  have hsum_b := b.sum_eq; have hsum_d := d.sum_eq
  have hsum_a := a.sum_eq; have hsum_c := c.sum_eq
  have hmx := hr.midpoint_x; have hmy := hr.midpoint_y; have hmz := hr.midpoint_z
  have hlong := hr.long; rw [Vertex.sqDist_comm, Vertex.sqDist_def, hdy] at hlong
  have hxdz : ((d.x : ℤ) - b.x) + ((d.z : ℤ) - b.z) = 2 := by omega
  have hsq : ((d.x : ℤ) - b.x - 1) ^ 2 + ((d.z : ℤ) - b.z - 1) ^ 2 = 0 := by
    linear_combination hlong - 2 * hxdz
  have hdx : (d.x : ℤ) - b.x = 1 := by
    linarith [sq_eq_zero_iff.mp (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _) |>.mp hsq).1]
  have hdz : (d.z : ℤ) - b.z = 1 := by
    linarith [sq_eq_zero_iff.mp (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _) |>.mp hsq).2]
  set i := b.z
  set j := n - b.x - 1
  have hij : i < j := by omega
  have hjn : j < n := by omega
  have hstep := h₁ i j hij hjn
  have hb_eq : Vertex.ofChart n i (j + 1) (by omega) (by omega) = b := by
    ext <;> simp [i, j] <;> omega
  have hd_eq : Vertex.ofChart n (i + 1) j (by omega) (by omega) = d := by
    ext <;> simp [i, j] <;> omega
  rcases (by omega : a.x = b.x + 1 ∧ c.x = b.x ∨ a.x = b.x ∧ c.x = b.x + 1) with
    ⟨hax', hcx'⟩ | ⟨hax', hcx'⟩
  · have ha_eq : Vertex.ofChart n i j (by omega) (by omega) = a := by ext <;> simp [i, j] <;> omega
    have hc_eq : Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega) = c := by
      ext <;> simp [i, j] <;> omega
    rwa [hb_eq, hd_eq, ha_eq, hc_eq] at hstep
  · have ha_eq : Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega) = a := by
      ext <;> simp [i, j] <;> omega
    have hc_eq : Vertex.ofChart n i j (by omega) (by omega) = c := by ext <;> simp [i, j] <;> omega
    rw [hb_eq, hd_eq, hc_eq, ha_eq, add_comm (f c) (f a)] at hstep
    exact hstep

private theorem le_of_isRhombus_dz_two {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    {f : Vertex n → R}
    (h₂ : ∀ i j (hij : i < j) (hjn : j < n),
      f (Vertex.ofChart n i j (by omega) (by omega)) +
          f (Vertex.ofChart n (i + 2) (j + 1) (by omega) (by omega)) ≤
        f (Vertex.ofChart n (i + 1) j (by omega) (by omega)) +
          f (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega)))
    {a b c d : Vertex n} (hr : IsRhombus a b c d) (hdz : (d.z : ℤ) - b.z = 2) :
    f b + f d ≤ f a + f c := by
  obtain ⟨hax, _, haz⟩ := coord_sub_mem_Icc_of_sqDist_eq_two hr.side_ab
  obtain ⟨hcx, _, hcz⟩ := coord_sub_mem_Icc_of_sqDist_eq_two
    (Vertex.sqDist_comm b c ▸ hr.side_bc)
  have hsum_b := b.sum_eq; have hsum_d := d.sum_eq
  have hsum_a := a.sum_eq; have hsum_c := c.sum_eq
  have hmx := hr.midpoint_x; have hmy := hr.midpoint_y; have hmz := hr.midpoint_z
  have hlong := hr.long; rw [Vertex.sqDist_comm, Vertex.sqDist_def, hdz] at hlong
  have hxdy : ((d.x : ℤ) - b.x) + ((d.y : ℤ) - b.y) = -2 := by omega
  have hsq : ((d.x : ℤ) - b.x + 1) ^ 2 + ((d.y : ℤ) - b.y + 1) ^ 2 = 0 := by
    linear_combination hlong + 2 * hxdy
  have hdx : (d.x : ℤ) - b.x = -1 := by
    linarith [sq_eq_zero_iff.mp (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _) |>.mp hsq).1]
  set i := b.z
  set j := n - b.x
  have hij : i < j := by omega
  have hjn : j < n := by omega
  have hstep := h₂ i j hij hjn
  have hb_eq : Vertex.ofChart n i j (by omega) (by omega) = b := by ext <;> simp [i, j]
  have hd_eq : Vertex.ofChart n (i + 2) (j + 1) (by omega) (by omega) = d := by
    ext <;> simp [i, j] <;> omega
  rcases (by omega : a.x = b.x ∧ c.x + 1 = b.x ∨ a.x + 1 = b.x ∧ c.x = b.x) with
    ⟨hax', hcx'⟩ | ⟨hax', hcx'⟩
  · have ha_eq : Vertex.ofChart n (i + 1) j (by omega) (by omega) = a := by
      ext <;> simp [i, j] <;> omega
    have hc_eq : Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega) = c := by
      ext <;> simp [i, j] <;> omega
    rwa [hb_eq, hd_eq, ha_eq, hc_eq] at hstep
  · have ha_eq : Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega) = a := by
      ext <;> simp [i, j] <;> omega
    have hc_eq : Vertex.ofChart n (i + 1) j (by omega) (by omega) = c := by
      ext <;> simp [i, j] <;> omega
    rw [hb_eq, hd_eq, hc_eq, ha_eq, add_comm (f c) (f a)] at hstep
    exact hstep

private theorem le_of_isRhombus_dx_neg_two {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    {f : Vertex n → R}
    (h₃ : ∀ i j (hij : i ≤ j) (hjn : j + 2 ≤ n),
      f (Vertex.ofChart n i j (by omega) (by omega)) +
          f (Vertex.ofChart n (i + 1) (j + 2) (by omega) (by omega)) ≤
        f (Vertex.ofChart n i (j + 1) (by omega) (by omega)) +
          f (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega)))
    {a b c d : Vertex n} (hr : IsRhombus a b c d) (hdx : (d.x : ℤ) - b.x = -2) :
    f b + f d ≤ f a + f c := by
  obtain ⟨hax, _, haz⟩ := coord_sub_mem_Icc_of_sqDist_eq_two hr.side_ab
  obtain ⟨hcx, _, hcz⟩ := coord_sub_mem_Icc_of_sqDist_eq_two
    (Vertex.sqDist_comm b c ▸ hr.side_bc)
  have hsum_b := b.sum_eq; have hsum_d := d.sum_eq
  have hsum_a := a.sum_eq; have hsum_c := c.sum_eq
  have hmx := hr.midpoint_x; have hmy := hr.midpoint_y; have hmz := hr.midpoint_z
  have hlong := hr.long; rw [Vertex.sqDist_comm, Vertex.sqDist_def, hdx] at hlong
  have hydz : ((d.y : ℤ) - b.y) + ((d.z : ℤ) - b.z) = 2 := by omega
  have hsq : ((d.y : ℤ) - b.y - 1) ^ 2 + ((d.z : ℤ) - b.z - 1) ^ 2 = 0 := by
    linear_combination hlong - 2 * hydz
  have hdy : (d.y : ℤ) - b.y = 1 := by
    linarith [sq_eq_zero_iff.mp (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _) |>.mp hsq).1]
  have hdz : (d.z : ℤ) - b.z = 1 := by
    linarith [sq_eq_zero_iff.mp (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _) |>.mp hsq).2]
  set i := b.z
  set j := n - b.x
  have hij : i ≤ j := by omega
  have hjn : j + 2 ≤ n := by omega
  have hstep := h₃ i j hij hjn
  have hb_eq : Vertex.ofChart n i j hij (by omega) = b := by ext <;> simp [i, j]
  have hd_eq : Vertex.ofChart n (i + 1) (j + 2) (by omega) hjn = d := by
    ext <;> simp [i, j] <;> omega
  rcases (by omega : a.z = b.z ∧ c.z = b.z + 1 ∨ a.z = b.z + 1 ∧ c.z = b.z) with
    ⟨haz', hcz'⟩ | ⟨haz', hcz'⟩
  · have ha_eq : Vertex.ofChart n i (j + 1) (by omega) (by omega) = a := by
      ext <;> simp [i, j] <;> omega
    have hc_eq : Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega) = c := by
      ext <;> simp [i, j] <;> omega
    rwa [hb_eq, hd_eq, ha_eq, hc_eq] at hstep
  · have ha_eq : Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega) = a := by
      ext <;> simp [i, j] <;> omega
    have hc_eq : Vertex.ofChart n i (j + 1) (by omega) (by omega) = c := by
      ext <;> simp [i, j] <;> omega
    rw [hb_eq, hd_eq, hc_eq, ha_eq, add_comm (f c) (f a)] at hstep
    exact hstep

/-- **Product-chart characterization of rhombus concavity**: a lattice function `f : Vertex n → R`
is rhombus-concave if and only if it satisfies the three product-chart rhombus inequality families.
-/
theorem isRhombusConcave_iff_ofChart {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    (f : Vertex n → R) :
    IsRhombusConcave f ↔
      (∀ i j (hij : i < j) (hjn : j < n),
        f (Vertex.ofChart n i (j + 1) (by omega) (by omega)) +
            f (Vertex.ofChart n (i + 1) j (by omega) (by omega)) ≤
          f (Vertex.ofChart n i j (by omega) (by omega)) +
            f (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega))) ∧
      (∀ i j (hij : i < j) (hjn : j < n),
        f (Vertex.ofChart n i j (by omega) (by omega)) +
            f (Vertex.ofChart n (i + 2) (j + 1) (by omega) (by omega)) ≤
          f (Vertex.ofChart n (i + 1) j (by omega) (by omega)) +
            f (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega))) ∧
      (∀ i j (hij : i ≤ j) (hjn : j + 2 ≤ n),
        f (Vertex.ofChart n i j (by omega) (by omega)) +
            f (Vertex.ofChart n (i + 1) (j + 2) (by omega) (by omega)) ≤
          f (Vertex.ofChart n i (j + 1) (by omega) (by omega)) +
            f (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega))) := by
  rw [isRhombusConcave_def]
  refine ⟨fun hf => ⟨fun i j hij hjn => hf (isRhombus_ofChart_one hij hjn),
    fun i j hij hjn => hf (isRhombus_ofChart_two hij hjn),
    fun i j hij hjn => hf (isRhombus_ofChart_three hij hjn)⟩, ?_⟩
  rintro ⟨h₁, h₂, h₃⟩ a b c d hr
  rcases long_diag_cases_of_isRhombus hr with (hdy | hdy) | (hdz | hdz) | (hdx | hdx)
  · exact le_of_isRhombus_dy_neg_two h₁ hr hdy
  · rw [add_comm (f b) (f d)]
    exact le_of_isRhombus_dy_neg_two h₁ hr.reverse (by omega)
  · exact le_of_isRhombus_dz_two h₂ hr hdz
  · rw [add_comm (f b) (f d)]
    exact le_of_isRhombus_dz_two h₂ hr.reverse (by omega)
  · exact le_of_isRhombus_dx_neg_two h₃ hr hdx
  · rw [add_comm (f b) (f d)]
    exact le_of_isRhombus_dx_neg_two h₃ hr.reverse (by omega)

end RhombusChart

/-! ### Boundary values in the product chart and cyclic boundary conversion -/

section BoundaryChart

variable {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]

/-- Along `i = 0`, `h(0, j)` is `prefixSum j (h.boundary 0)`. -/
theorem apply_ofChart_zero (h : Hive n R) {j : ℕ} (hjn : j ≤ n) :
    h (Vertex.ofChart n 0 j (Nat.zero_le j) hjn) = prefixSum j (h.boundary 0) := by
  rw [Vertex.ofChart_zero_left, h.apply_edgePoint_zero, prefixSum_def]

/-- Along `j = n`, `h(i, n)` is the total sum of side `0` plus `prefixSum i (h.boundary 1)`. -/
theorem apply_ofChart_last (h : Hive n R) {i : ℕ} (hin : i ≤ n) :
    h (Vertex.ofChart n i n hin le_rfl) =
      (∑ r : Fin n, h.boundary 0 r) + prefixSum i (h.boundary 1) := by
  rw [Vertex.ofChart_last_right, h.apply_edgePoint_one, prefixSum_def]

/-- Along the diagonal `i = j`, `h(j, j)` is minus the suffix sum of `h.boundary 2`. -/
theorem apply_ofChart_diag (h : Hive n R) {j : ℕ} (hjn : j ≤ n) :
    h (Vertex.ofChart n j j le_rfl hjn) =
      -∑ r : Fin n with n - j ≤ r.val, h.boundary 2 r := by
  rw [Vertex.ofChart_diag, h.apply_edgePoint_two]

/-- For an integer hive, `h(j, j)` is `prefixSum j (h.boundaryWeight 2).dual.1`. -/
theorem apply_ofChart_diag_of_boundaryWeight (h : IntegerHive n) {j : ℕ} (hjn : j ≤ n) :
    h (Vertex.ofChart n j j le_rfl hjn) = prefixSum j (h.boundaryWeight 2).dual.1 := by
  rw [apply_ofChart_diag, prefixSum_def, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_neg_distrib]
  refine (Equiv.sum_comp Fin.revPerm
      (fun r : Fin n => -(if n - j ≤ r.val then h.boundary 2 r else 0))).symm.trans ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Fin.revPerm_apply, Fin.val_rev, DominantWeight.dual_apply, coe_boundaryWeight]
  by_cases hr : r.val < j
  · have hge : n - j ≤ n - (r.val + 1) := by omega
    rw [ite_eq_left hge, ite_eq_left hr]
  · have hnge : ¬ n - j ≤ n - (r.val + 1) := by omega
    rw [ite_eq_right hnge, ite_eq_right hr, neg_zero]

/-- On `productBoundary lam μ γ`, the diagonal value `h(j, j)` is `prefixSum j γ.1`. -/
theorem apply_ofChart_diag_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) {j : ℕ} (hjn : j ≤ n) :
    h (Vertex.ofChart n j j le_rfl hjn) = prefixSum j γ.1 := by
  have hw : h.boundaryWeight 2 = γ.dual := Subtype.ext (by simp [coe_boundaryWeight, hb])
  rw [apply_ofChart_diag_of_boundaryWeight h hjn, hw, DominantWeight.dual_dual]

/-- The symmetric clockwise cyclic boundary `(λ, μ, ν)` indexing `GL n`-invariants in
`V_λ ⊗ V_μ ⊗ V_ν`. -/
def cyclicBoundary (lam μ ν : DominantWeight n) : Fin 3 → Fin n → ℤ := ![lam.1, μ.1, ν.1]

@[simp] theorem cyclicBoundary_zero (lam μ ν : DominantWeight n) :
    cyclicBoundary lam μ ν 0 = lam.1 := (rfl)

@[simp] theorem cyclicBoundary_one (lam μ ν : DominantWeight n) :
    cyclicBoundary lam μ ν 1 = μ.1 := (rfl)

@[simp] theorem cyclicBoundary_two (lam μ ν : DominantWeight n) :
    cyclicBoundary lam μ ν 2 = ν.1 := (rfl)

theorem productBoundary_eq_cyclicBoundary (lam μ γ : DominantWeight n) :
    productBoundary lam μ γ = cyclicBoundary lam μ γ.dual := by
  ext s i; fin_cases s <;> simp

theorem cyclicBoundary_eq_productBoundary (lam μ ν : DominantWeight n) :
    cyclicBoundary lam μ ν = productBoundary lam μ ν.dual := by
  ext s i; fin_cases s <;> simp

/-- Two clockwise rotations convert `cyclicBoundary lam μ ν` into `productBoundary ν lam μ.dual`. -/
theorem boundary_rotate_rotate_of_cyclicBoundary {lam μ ν : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = cyclicBoundary lam μ ν) :
    h.rotate.rotate.boundary = productBoundary ν lam μ.dual := by
  ext s i; fin_cases s <;> simp [hb]

/-- One clockwise rotation converts `productBoundary ν lam μ.dual` back into
`cyclicBoundary lam μ ν`. -/
theorem boundary_rotate_of_productBoundary_dual {lam μ ν : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary ν lam μ.dual) :
    h.rotate.boundary = cyclicBoundary lam μ ν := by
  ext s i; fin_cases s <;> simp [hb]

end BoundaryChart

end TauCeti.Hive
