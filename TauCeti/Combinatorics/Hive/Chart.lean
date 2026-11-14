/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The product chart and determinant-shift equivalences on hives

Two coordinate tools connect the symmetric barycentric definition of hives to tableaux and
Gelfand–Tsetlin patterns:

1. **Determinant-shift equivalences** (`TauCeti.Hive.fixedIntegerHiveShiftEquiv`,
   `TauCeti.Hive.hiveCount_productBoundary_shift`): adding the slack-free normalized affine hive
   `Hive.affine n a (a + b)` translates a clockwise product boundary `(lam, μ, γ*)` to
   `(lam.shift a, μ.shift b, (γ.shift (a + b))*)`, giving an explicit equivalence of fixed-boundary
   integer hive fibres and invariance of `hiveCount` under simultaneous determinant shifts.
2. **The `(i, j)` product chart** (`TauCeti.Hive.Vertex.ofChart`,
   `TauCeti.Hive.isRhombusConcave_iff_ofChart`): reindexing `Vertex n` by
   `(i, j) ↦ (n - j, j - i, i)` for `0 ≤ i ≤ j ≤ n` places the partial sums of `λ`, `μ`, and `γ`
   along `i = 0`, `j = n`, and `i = j`, and decomposes `IsRhombusConcave` into the three unit
   rhombus families (horizontal strips, elementary grid cells, and vertical strips).

## Main definitions

* `TauCeti.Hive.fixedIntegerHiveShiftEquiv`: equivalence of fixed-boundary integer hive fibres
  under simultaneous determinant shifts `(lam, μ, γ) ↦ (lam.shift a, μ.shift b, γ.shift (a + b))`.
* `TauCeti.Hive.Vertex.ofChart`: the `(i, j)` chart `(i, j) ↦ (n - j, j - i, i)` on `Vertex n`.

## Main results

* `TauCeti.Hive.productBoundary_shift`, `TauCeti.Hive.hiveCount_productBoundary_shift`,
  `TauCeti.Hive.hiveCount_productBoundary_shift_left`,
  `TauCeti.Hive.hiveCount_productBoundary_shift_right`: behaviour of `productBoundary` and
  `hiveCount` under determinant shifts.
* `TauCeti.Hive.isRhombusConcave_iff_ofChart`: equivalence between `IsRhombusConcave` and the
  horizontal, elementary-cell, and vertical chart inequalities.
* `TauCeti.Hive.apply_ofChart_zero_left`, `TauCeti.Hive.apply_ofChart_right`,
  `TauCeti.Hive.apply_ofChart_diag`: boundary partial-sum formulas in chart coordinates.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. S. Buch, *The saturation conjecture (after A. Knutson and T. Tao)*, Enseign. Math. (2) **46**
  (2000), 43–60, Appendix A.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### Affine hive addition and determinant-shift equivalences -/

section Shift

variable {n : ℕ}

/-- The normalized affine hive with zero slopes is the zero hive. -/
@[simp] theorem affine_zero {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (n : ℕ) : affine n (0 : R) 0 = 0 := by
  ext p
  simp

/-- Slope parameters of normalized affine hives add homomorphically. -/
@[simp] theorem affine_add {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    (n : ℕ) (β₁ γ₁ β₂ γ₂ : R) :
    affine n (β₁ + β₂) (γ₁ + γ₂) = affine n β₁ γ₁ + affine n β₂ γ₂ := by
  ext p
  simp only [affine_apply, add_apply, nsmul_add]
  abel

/-- Shifting `λ` by `a`, `μ` by `b`, and `γ` by `a + b` adds the boundary of
`affine n a (a + b)` to `productBoundary lam μ γ`. -/
theorem productBoundary_shift (lam μ γ : DominantWeight n) (a b : ℤ) :
    productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)) =
      productBoundary lam μ γ + (affine n a (a + b)).boundary := by
  ext s i
  fin_cases s <;> simp [productBoundary_zero, productBoundary_one, productBoundary_two]

/-- Adding `affine n a (a + b)` to an integer hive with boundary `(lam, μ, γ*)` shifts its boundary
to `(lam.shift a, μ.shift b, (γ.shift (a + b))*)`. -/
theorem boundary_add_affine_eq_productBoundary_shift {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) (a b : ℤ) :
    (h + affine n a (a + b)).boundary =
      productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)) := by
  rw [boundary_add, hb, productBoundary_shift]

/-- Equivalence of fixed-boundary integer hive fibres induced by simultaneous determinant shifts
`lam ↦ lam.shift a`, `μ ↦ μ.shift b`, `γ ↦ γ.shift (a + b)`. -/
def fixedIntegerHiveShiftEquiv (lam μ γ : DominantWeight n) (a b : ℤ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))) where
  toFun h := ⟨h.1 + affine n a (a + b), boundary_add_affine_eq_productBoundary_shift h.2 a b⟩
  invFun h := ⟨h.1 + affine n (-a) (-(a + b)), by
    have hb := boundary_add_affine_eq_productBoundary_shift h.2 (-a) (-b)
    have hneg : -a + -b = -(a + b) := by omega
    have hab : (a + b) + (-a + -b) = 0 := by omega
    simpa only [hneg, DominantWeight.shift_shift, hab, add_neg_cancel,
      DominantWeight.shift_zero] using hb⟩
  left_inv h := Subtype.ext <| by
    dsimp only
    rw [add_assoc, ← affine_add, add_neg_cancel, add_neg_cancel, affine_zero, add_zero]
  right_inv h := Subtype.ext <| by
    dsimp only
    rw [add_assoc, ← affine_add, neg_add_cancel, neg_add_cancel, affine_zero, add_zero]

/-- Shifting a fixed-boundary hive adds `affine n a (a + b)` to the underlying hive. -/
@[simp] theorem coe_fixedIntegerHiveShiftEquiv_apply (lam μ γ : DominantWeight n) (a b : ℤ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    ((fixedIntegerHiveShiftEquiv lam μ γ a b h).1 : IntegerHive n) = h.1 + affine n a (a + b) :=
  (rfl)

/-- Unshifting a fixed-boundary hive adds `affine n (-a) (-(a + b))` to the underlying hive. -/
@[simp] theorem coe_fixedIntegerHiveShiftEquiv_symm_apply (lam μ γ : DominantWeight n) (a b : ℤ)
    (h : FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)))) :
    (((fixedIntegerHiveShiftEquiv lam μ γ a b).symm h).1 : IntegerHive n) =
      h.1 + affine n (-a) (-(a + b)) :=
  (rfl)

/-- Simultaneous determinant shifts of the input weights shift the output weight by their sum
without changing `hiveCount`. -/
theorem hiveCount_productBoundary_shift (lam μ γ : DominantWeight n) (a b : ℤ) :
    hiveCount (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))) =
      hiveCount (productBoundary lam μ γ) := by
  rw [← card_fixedIntegerHive, ← card_fixedIntegerHive]
  exact (Fintype.card_congr (fixedIntegerHiveShiftEquiv lam μ γ a b)).symm

/-- Shifting the first input weight and the output weight by the same integer preserves
`hiveCount`. -/
@[simp] theorem hiveCount_productBoundary_shift_left (lam μ γ : DominantWeight n) (a : ℤ) :
    hiveCount (productBoundary (lam.shift a) μ (γ.shift a)) =
      hiveCount (productBoundary lam μ γ) := by
  simpa using hiveCount_productBoundary_shift lam μ γ a 0

/-- Shifting the second input weight and the output weight by the same integer preserves
`hiveCount`. -/
@[simp] theorem hiveCount_productBoundary_shift_right (lam μ γ : DominantWeight n) (b : ℤ) :
    hiveCount (productBoundary lam (μ.shift b) (γ.shift b)) =
      hiveCount (productBoundary lam μ γ) := by
  simpa using hiveCount_productBoundary_shift lam μ γ 0 b

end Shift

/-! ### The `(i, j)` product chart and its three unit-rhombus families -/

namespace Vertex

/-- The `(i, j)` product chart `(i, j) ↦ (n - j, j - i, i)` on `Vertex n` for `0 ≤ i ≤ j ≤ n`. -/
def ofChart (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) : Vertex n :=
  ofYZ n (j - i) i (by omega)

/-- The `x`-coordinate of `ofChart n i j` is `n - j`. -/
@[simp] theorem ofChart_x (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (ofChart n i j hij hjn).x = n - j := by
  simp only [ofChart, ofYZ_x]
  omega

/-- The `y`-coordinate of `ofChart n i j` is `j - i`. -/
@[simp] theorem ofChart_y (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (ofChart n i j hij hjn).y = j - i :=
  ofYZ_y n (j - i) i _

/-- The `z`-coordinate of `ofChart n i j` is `i`. -/
@[simp] theorem ofChart_z (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (ofChart n i j hij hjn).z = i :=
  ofYZ_z n (j - i) i _

/-- `ofChart n` is injective in `(i, j)`. -/
@[simp] theorem ofChart_eq_iff {n i₁ j₁ i₂ j₂ : ℕ} {hi₁ : i₁ ≤ j₁} {hj₁ : j₁ ≤ n}
    {hi₂ : i₂ ≤ j₂} {hj₂ : j₂ ≤ n} :
    ofChart n i₁ j₁ hi₁ hj₁ = ofChart n i₂ j₂ hi₂ hj₂ ↔ i₁ = i₂ ∧ j₁ = j₂ := by
  refine ⟨fun h => ?_, fun ⟨hi, hj⟩ => by subst hi; subst hj; rfl⟩
  have hz : i₁ = i₂ := by simpa using congrArg Vertex.z h
  have hy : j₁ - i₁ = j₂ - i₂ := by simpa using congrArg Vertex.y h
  omega

/-- Every lattice vertex `p : Vertex n` is `ofChart n p.z (n - p.x)`. -/
@[simp] theorem ofChart_z_sub_x {n : ℕ} (p : Vertex n) :
    ofChart n p.z (n - p.x) (by have := p.sum_eq; omega) (Nat.sub_le n p.x) = p := by
  have := p.sum_eq
  ext <;> simp <;> omega

/-- The origin `(0, 0)` of the product chart is `cornerA n`. -/
@[simp] theorem ofChart_zero_zero (n : ℕ) :
    ofChart n 0 0 le_rfl (Nat.zero_le n) = cornerA n := by
  ext <;> simp

/-- Along `i = 0`, `ofChart n 0 j` traverses side `0` (`A → B`). -/
theorem ofChart_zero_left (n j : ℕ) (hj : j ≤ n) :
    ofChart n 0 j (Nat.zero_le j) hj = edgePoint n 0 ⟨j, by omega⟩ := by
  ext <;> simp

/-- Along `j = n`, `ofChart n i n` traverses side `1` (`B → C`). -/
theorem ofChart_right (n i : ℕ) (hi : i ≤ n) :
    ofChart n i n hi le_rfl = edgePoint n 1 ⟨i, by omega⟩ := by
  ext <;> simp

/-- Along the diagonal `i = j`, `ofChart n j j` is the `(n - j)`-th vertex of side `2` (`C → A`). -/
theorem ofChart_diag (n j : ℕ) (hj : j ≤ n) :
    ofChart n j j le_rfl hj = edgePoint n 2 ⟨n - j, by omega⟩ := by
  ext <;> simp
  omega

end Vertex

section ChartRhombi

/-- Horizontal-strip unit rhombus in `(i, j)` coordinates (`0 ≤ i ≤ j`, `j + 2 ≤ n`), with obtuse
corners `(i, j + 1), (i + 1, j + 1)` and acute corners `(i, j), (i + 1, j + 2)`. -/
theorem isRhombus_ofChart_horiz {n i j : ℕ} (hij : i ≤ j) (hjn : j + 2 ≤ n) :
    IsRhombus
      (Vertex.ofChart n i (j + 1) (by omega) (by omega))
      (Vertex.ofChart n i j hij (by omega))
      (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega))
      (Vertex.ofChart n (i + 1) (j + 2) (by omega) hjn) := by
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

/-- Elementary `(i, j)` grid cell unit rhombus (`0 ≤ i < j < n`), with obtuse corners
`(i, j), (i + 1, j + 1)` and acute corners `(i + 1, j), (i, j + 1)`. -/
theorem isRhombus_ofChart_cell {n i j : ℕ} (hij : i < j) (hjn : j < n) :
    IsRhombus
      (Vertex.ofChart n i j hij.le hjn.le)
      (Vertex.ofChart n (i + 1) j hij hjn.le)
      (Vertex.ofChart n (i + 1) (j + 1) (by omega) hjn)
      (Vertex.ofChart n i (j + 1) (by omega) hjn) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hy00 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy10 : ((j - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  have hy11 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy01 : ((j + 1 - i : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  refine ⟨by simp, by simp; omega, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.ofChart_x, Vertex.ofChart_y, Vertex.ofChart_z,
      hx0, hx1, hy00, hy10, hy11, hy01, Nat.cast_add, Nat.cast_one]
    ring

/-- Vertical-strip unit rhombus in `(i, j)` coordinates (`0 ≤ i < j < n`), with obtuse corners
`(i + 1, j), (i + 1, j + 1)` and acute corners `(i, j), (i + 2, j + 1)`. -/
theorem isRhombus_ofChart_vert {n i j : ℕ} (hij : i < j) (hjn : j < n) :
    IsRhombus
      (Vertex.ofChart n (i + 1) j hij hjn.le)
      (Vertex.ofChart n i j hij.le hjn.le)
      (Vertex.ofChart n (i + 1) (j + 1) (by omega) hjn)
      (Vertex.ofChart n (i + 2) (j + 1) (by omega) hjn) := by
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

private theorem unit_chart_step {u v : ℤ} (h : (-v) ^ 2 + (v - u) ^ 2 + u ^ 2 = 2) :
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
      (u = 0 ∧ v = -1) ∨ (u = -1 ∧ v = -1) ∨ (u = -1 ∧ v = 0) := by
  have hu : -1 ≤ u ∧ u ≤ 1 := by
    simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (b := 2) (by decide)).mpr
      (by linarith [sq_nonneg (-v), sq_nonneg (v - u)])
  have hv : -1 ≤ v ∧ v ≤ 1 := by
    simpa [abs_le] using (Int.abs_le_sqrt_iff_sq_le (a := v) (b := 2) (by decide)).mpr
      (by linarith [sq_nonneg (v - u), sq_nonneg u])
  rcases (by omega : u = -1 ∨ u = 0 ∨ u = 1) with rfl | rfl | rfl <;>
    rcases (by omega : v = -1 ∨ v = 0 ∨ v = 1) with rfl | rfl | rfl <;>
    (norm_num at h) <;> norm_num

private theorem unit_chart_pair_oriented {u v u' v' : ℤ}
    (hab : (-v) ^ 2 + (v - u) ^ 2 + u ^ 2 = 2)
    (hbc : (-v') ^ 2 + (v' - u') ^ 2 + u' ^ 2 = 2)
    (hac : (v' - v) ^ 2 + ((v - u) - (v' - u')) ^ 2 + (u - u') ^ 2 = 2)
    (hsum : 0 ≤ u + u') (hord : u < u' ∨ u = u' ∧ v ≤ v') :
    (u = 0 ∧ v = 1 ∧ u' = 1 ∧ v' = 1) ∨
      (u = 0 ∧ v = -1 ∧ u' = 1 ∧ v' = 0) ∨
      (u = 1 ∧ v = 0 ∧ u' = 1 ∧ v' = 1) := by
  rcases unit_chart_step hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases unit_chart_step hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    omega

private theorem chart_steps_of_isRhombus_oriented {n : ℕ} {a b c d : Vertex n}
    (hr : IsRhombus a b c d) (hbz : b.z ≤ d.z)
    (hord : a.z < c.z ∨ a.z = c.z ∧ c.x ≤ a.x) :
    ((a.z : ℤ) - b.z = 0 ∧ (b.x : ℤ) - a.x = 1 ∧ (c.z : ℤ) - b.z = 1 ∧ (b.x : ℤ) - c.x = 1) ∨
      ((a.z : ℤ) - b.z = 0 ∧ (b.x : ℤ) - a.x = -1 ∧ (c.z : ℤ) - b.z = 1 ∧ (b.x : ℤ) - c.x = 0) ∨
      ((a.z : ℤ) - b.z = 1 ∧ (b.x : ℤ) - a.x = 0 ∧ (c.z : ℤ) - b.z = 1 ∧ (b.x : ℤ) - c.x = 1) := by
  have := a.sum_eq; have := b.sum_eq; have := c.sum_eq; have := d.sum_eq
  have := hr.midpoint_z
  have hab : (-((b.x : ℤ) - a.x)) ^ 2 + (((b.x : ℤ) - a.x) - ((a.z : ℤ) - b.z)) ^ 2 +
      ((a.z : ℤ) - b.z) ^ 2 = 2 := by
    have hay : (a.y : ℤ) - b.y = ((b.x : ℤ) - a.x) - ((a.z : ℤ) - b.z) := by omega
    have hs := hr.side_ab; rw [Vertex.sqDist_def] at hs; rw [← hay]; linarith
  have hbc : (-((b.x : ℤ) - c.x)) ^ 2 + (((b.x : ℤ) - c.x) - ((c.z : ℤ) - b.z)) ^ 2 +
      ((c.z : ℤ) - b.z) ^ 2 = 2 := by
    have hcy : (c.y : ℤ) - b.y = ((b.x : ℤ) - c.x) - ((c.z : ℤ) - b.z) := by omega
    have hs := hr.side_bc; rw [Vertex.sqDist_comm, Vertex.sqDist_def] at hs; rw [← hcy]; linarith
  have hac : (((b.x : ℤ) - c.x) - ((b.x : ℤ) - a.x)) ^ 2 +
      ((((b.x : ℤ) - a.x) - ((a.z : ℤ) - b.z)) -
        (((b.x : ℤ) - c.x) - ((c.z : ℤ) - b.z))) ^ 2 +
      (((a.z : ℤ) - b.z) - ((c.z : ℤ) - b.z)) ^ 2 = 2 := by
    have hax : (a.x : ℤ) - c.x = ((b.x : ℤ) - c.x) - ((b.x : ℤ) - a.x) := by omega
    have hac_y : (a.y : ℤ) - c.y =
        (((b.x : ℤ) - a.x) - ((a.z : ℤ) - b.z)) - (((b.x : ℤ) - c.x) - ((c.z : ℤ) - b.z)) := by
      omega
    have haz : (a.z : ℤ) - c.z = ((a.z : ℤ) - b.z) - ((c.z : ℤ) - b.z) := by omega
    have hs := hr.short; rw [Vertex.sqDist_def] at hs; rw [← hax, ← hac_y, ← haz]; exact hs
  exact unit_chart_pair_oriented hab hbc hac (by omega) (by omega)

private theorem le_of_isRhombus_oriented {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    {f : Vertex n → R}
    (hH : ∀ i j (hij : i ≤ j) (hjn : j + 2 ≤ n),
      f (Vertex.ofChart n i j hij (by omega)) +
          f (Vertex.ofChart n (i + 1) (j + 2) (by omega) hjn) ≤
        f (Vertex.ofChart n i (j + 1) (by omega) (by omega)) +
          f (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega)))
    (hC : ∀ i j (hij : i < j) (hjn : j < n),
      f (Vertex.ofChart n (i + 1) j hij hjn.le) +
          f (Vertex.ofChart n i (j + 1) (by omega) hjn) ≤
        f (Vertex.ofChart n i j hij.le hjn.le) +
          f (Vertex.ofChart n (i + 1) (j + 1) (by omega) hjn))
    (hV : ∀ i j (hij : i < j) (hjn : j < n),
      f (Vertex.ofChart n i j hij.le hjn.le) +
          f (Vertex.ofChart n (i + 2) (j + 1) (by omega) hjn) ≤
        f (Vertex.ofChart n (i + 1) j hij hjn.le) +
          f (Vertex.ofChart n (i + 1) (j + 1) (by omega) hjn))
    {a b c d : Vertex n} (hr : IsRhombus a b c d) (hbz : b.z ≤ d.z)
    (hord : a.z < c.z ∨ a.z = c.z ∧ c.x ≤ a.x) :
    f b + f d ≤ f a + f c := by
  have := a.sum_eq; have := b.sum_eq; have := c.sum_eq; have := d.sum_eq
  have := hr.midpoint_x; have := hr.midpoint_y; have := hr.midpoint_z
  rcases chart_steps_of_isRhombus_oriented hr hbz hord with
    ⟨hu, hv, hu', hv'⟩ | ⟨hu, hv, hu', hv'⟩ | ⟨hu, hv, hu', hv'⟩
  · have hij : b.z ≤ n - b.x := by omega
    have hjn : (n - b.x) + 2 ≤ n := by omega
    have hb_eq : b = Vertex.ofChart n b.z (n - b.x) hij (by omega) := by simp
    have hd_eq : d = Vertex.ofChart n (b.z + 1) ((n - b.x) + 2) (by omega) hjn := by
      ext <;> simp <;> omega
    have ha_eq : a = Vertex.ofChart n b.z ((n - b.x) + 1) (by omega) (by omega) := by
      ext <;> simp <;> omega
    have hc_eq : c = Vertex.ofChart n (b.z + 1) ((n - b.x) + 1) (by omega) (by omega) := by
      ext <;> simp <;> omega
    rw [congrArg f hb_eq, congrArg f hd_eq, congrArg f ha_eq, congrArg f hc_eq]
    exact hH b.z (n - b.x) hij hjn
  · have hij : b.z < n - d.x := by omega
    have hjn : n - d.x < n := by omega
    have hb_eq : b = Vertex.ofChart n b.z ((n - d.x) + 1) (by omega) hjn := by
      ext <;> simp <;> omega
    have hd_eq : d = Vertex.ofChart n (b.z + 1) (n - d.x) hij hjn.le := by ext <;> simp <;> omega
    have ha_eq : a = Vertex.ofChart n b.z (n - d.x) hij.le hjn.le := by ext <;> simp <;> omega
    have hc_eq : c = Vertex.ofChart n (b.z + 1) ((n - d.x) + 1) (by omega) hjn := by
      ext <;> simp <;> omega
    rw [congrArg f hb_eq, congrArg f hd_eq, congrArg f ha_eq, congrArg f hc_eq, add_comm]
    exact hC b.z (n - d.x) hij hjn
  · have hij : b.z < n - b.x := by omega
    have hjn : n - b.x < n := by omega
    have hb_eq : b = Vertex.ofChart n b.z (n - b.x) hij.le hjn.le := by simp
    have hd_eq : d = Vertex.ofChart n (b.z + 2) ((n - b.x) + 1) (by omega) hjn := by
      ext <;> simp <;> omega
    have ha_eq : a = Vertex.ofChart n (b.z + 1) (n - b.x) hij hjn.le := by ext <;> simp <;> omega
    have hc_eq : c = Vertex.ofChart n (b.z + 1) ((n - b.x) + 1) (by omega) hjn := by
      ext <;> simp <;> omega
    rw [congrArg f hb_eq, congrArg f hd_eq, congrArg f ha_eq, congrArg f hc_eq]
    exact hV b.z (n - b.x) hij hjn

/-- **Rhombus concavity in the `(i, j)` chart**: a lattice function is rhombus-concave if and only
if it satisfies the horizontal, elementary-cell, and vertical unit-rhombus inequalities in
`Vertex.ofChart` coordinates. -/
theorem isRhombusConcave_iff_ofChart {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    (f : Vertex n → R) :
    IsRhombusConcave f ↔
      (∀ i j (hij : i ≤ j) (hjn : j + 2 ≤ n),
        f (Vertex.ofChart n i j hij (by omega)) +
            f (Vertex.ofChart n (i + 1) (j + 2) (by omega) hjn) ≤
          f (Vertex.ofChart n i (j + 1) (by omega) (by omega)) +
            f (Vertex.ofChart n (i + 1) (j + 1) (by omega) (by omega))) ∧
      (∀ i j (hij : i < j) (hjn : j < n),
        f (Vertex.ofChart n (i + 1) j hij hjn.le) +
            f (Vertex.ofChart n i (j + 1) (by omega) hjn) ≤
          f (Vertex.ofChart n i j hij.le hjn.le) +
            f (Vertex.ofChart n (i + 1) (j + 1) (by omega) hjn)) ∧
      (∀ i j (hij : i < j) (hjn : j < n),
        f (Vertex.ofChart n i j hij.le hjn.le) +
            f (Vertex.ofChart n (i + 2) (j + 1) (by omega) hjn) ≤
          f (Vertex.ofChart n (i + 1) j hij hjn.le) +
            f (Vertex.ofChart n (i + 1) (j + 1) (by omega) hjn)) := by
  rw [isRhombusConcave_def]
  refine ⟨fun hf => ⟨fun i j hij hjn => hf (isRhombus_ofChart_horiz hij hjn),
      fun i j hij hjn => hf (isRhombus_ofChart_cell hij hjn),
      fun i j hij hjn => hf (isRhombus_ofChart_vert hij hjn)⟩, ?_⟩
  rintro ⟨hH, hC, hV⟩
  have hbz_all {a b c d : Vertex n} (hr : IsRhombus a b c d) (hbz : b.z ≤ d.z) :
      f b + f d ≤ f a + f c := by
    rcases lt_trichotomy a.z c.z with hlt | heq | hgt
    · exact le_of_isRhombus_oriented hH hC hV hr hbz (Or.inl hlt)
    · rcases le_total c.x a.x with hcx | hax
      · exact le_of_isRhombus_oriented hH hC hV hr hbz (Or.inr ⟨heq, hcx⟩)
      · rw [add_comm (f a) (f c)]
        exact le_of_isRhombus_oriented hH hC hV hr.swap_opposite.reverse hbz
          (Or.inr ⟨heq.symm, hax⟩)
    · rw [add_comm (f a) (f c)]
      exact le_of_isRhombus_oriented hH hC hV hr.swap_opposite.reverse hbz (Or.inl hgt)
  intro a b c d hr
  rcases le_total b.z d.z with hbz | hdz
  · exact hbz_all hr hbz
  · rw [add_comm (f b) (f d)]
    exact hbz_all hr.reverse hdz

/-- Boundary values of an integer hive with `productBoundary lam μ γ` along `i = 0`. -/
theorem apply_ofChart_zero_left {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (j : ℕ) (hj : j ≤ n) :
    h (Vertex.ofChart n 0 j (Nat.zero_le j) hj) = ∑ r : Fin n with r.val < j, lam.1 r := by
  rw [Vertex.ofChart_zero_left, h.apply_edgePoint_zero, hb, productBoundary_zero]

/-- Boundary values of an integer hive with `productBoundary lam μ γ` along `j = n`. -/
theorem apply_ofChart_right {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (i : ℕ) (hi : i ≤ n) :
    h (Vertex.ofChart n i n hi le_rfl) =
      (∑ r : Fin n, lam.1 r) + ∑ l : Fin n with l.val < i, μ.1 l := by
  rw [Vertex.ofChart_right, h.apply_edgePoint_one, hb, productBoundary_zero, productBoundary_one]

/-- Boundary values of an integer hive with `productBoundary lam μ γ` along `i = j`. -/
theorem apply_ofChart_diag {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (j : ℕ) (hj : j ≤ n) :
    h (Vertex.ofChart n j j le_rfl hj) = ∑ r : Fin n with r.val < j, γ.1 r := by
  rw [Vertex.ofChart_diag, h.apply_edgePoint_two, hb, productBoundary_two]
  simp only [DominantWeight.dual_apply, Finset.sum_neg_distrib, neg_neg, Finset.sum_filter]
  refine (Finset.sum_congr rfl fun k _ => ?_).trans
    (Equiv.sum_comp Fin.revPerm fun r : Fin n => if r.val < j then γ.1 r else 0)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  by_cases hk : n - j ≤ k.val
  · simp [hk, show n - (k.val + 1) < j by omega]
  · simp [hk, show ¬ n - (k.val + 1) < j by omega]

end ChartRhombi

end TauCeti.Hive
