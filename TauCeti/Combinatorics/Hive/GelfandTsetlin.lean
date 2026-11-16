/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Count
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Weight
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The hive-to-Gelfand–Tsetlin difference map and its reconstruction

In the product chart `(i, j) ↦ (n - j, j - i, i)` (`0 ≤ i ≤ j ≤ n`) on the size-`n` triangular
lattice `TauCeti.Hive.Vertex n`, a normalized integer hive `h` with boundary
`productBoundary l m g = (l, m, g*)` takes the boundary values

* `h(0, j) = prefixSum j l`,
* `h(j, j) = prefixSum j g`,
* `h(i, n) = (∑ r, l r) + prefixSum i m`,

with `h(0, 0) = 0`. Taking vertical forward differences `P i j = h(i + 1, j) - h(i, j)` on the
informative cells `0 ≤ i < j ≤ n` defines a signed Gelfand–Tsetlin pattern `h.toGTPattern`
(`TauCeti.Hive.toGTPattern`): two of the three unit-rhombus orientations in `Δₙ` become the two
Gelfand–Tsetlin interlacing inequalities `P i j ≤ P i (j + 1)` and `P (i + 1) (j + 1) ≤ P i j`,
while the boundary values identify `h.toGTPattern.topRow = m` and `h.toGTPattern.rowWeight = g - l`.

Summing those vertical differences from the bottom edge `i = 0` recovers every hive value via the
chart completion

`gtCompletion l P i j = prefixSum j l + ∑ k ∈ range i, P k j`.

Classifying all unit rhombi of `Δₙ` up to three-fold rotation shows that `gtCompletion l P` defines
a hive with boundary `productBoundary l m g` if and only if `P.topRow = m`, `P.rowWeight = g - l`,
and the third unit-rhombus orientation holds (`TauCeti.Hive.gt_reconstruction_iff`), giving an
explicit equivalence `TauCeti.Hive.fixedHiveEquivGTPattern` between `FixedIntegerHive` and the
rhombus-constrained Gelfand–Tsetlin fibre. Counterclockwise rotation `h ↦ h.rotate.rotate` converts
the cyclic boundary `(λ, μ, ν)` into `productBoundary ν λ μ*`, yielding the quasi-hive comparison
onto patterns of top row `λ` and torus weight `μ* - ν` (`TauCeti.Hive.cyclicHiveEquivGTPattern`).

When the first input weight `l` satisfies the uniform gap `m 0 - m (last n) ≤ l r - l (r + 1)` for
all `r`, the third rhombus family holds automatically on every pattern over `m`
(`TauCeti.Hive.gt_completion_of_uniform_input_gap`), so the difference and completion maps identify
the hive fibre with the entire weight-`(g - l)` Gelfand–Tsetlin fibre over `m`
(`TauCeti.Hive.stableGTEquiv`, `TauCeti.Hive.exists_stable_gt_equiv`).

## Main definitions

* `TauCeti.Hive.gtVertex`, `TauCeti.Hive.gtChartEquiv`: the product chart
  `(i, j) ↦ (n - j, j - i, i)` on `Vertex n`.
* `TauCeti.Hive.toGTPattern`, `TauCeti.Hive.toGTPatternAddMonoidHom`: vertical difference map from
  `IntegerHive n` to `GTPattern n`.
* `TauCeti.Hive.gtCompletion`, `TauCeti.Hive.gtRemainingRhombus`: inverse chart completion and the
  remaining unit-rhombus inequality family.
* `TauCeti.Hive.fixedHiveEquivGTPattern`: equivalence between fixed-boundary integer hives and the
  constrained Gelfand–Tsetlin fibre.
* `TauCeti.Hive.cyclicToProductEquiv`, `TauCeti.Hive.toCyclicGTPattern`,
  `TauCeti.Hive.cyclicHiveEquivGTPattern`: cyclic-orientation conversion with top row `λ` and
  weight `μ* - ν`.
* `TauCeti.Hive.stableGTEquiv`: stable equivalence onto the full weight fibre under the uniform
  input gap.

## Main results

* `TauCeti.Hive.IsRhombus.x_eq_or_y_eq_or_z_eq`, `TauCeti.Hive.isRhombusConcave_iff_gtVertex`:
  short-diagonal coordinate equality and characterization of rhombus concavity by the three
  product-chart families.
* `TauCeti.Hive.gt_reconstruction_iff`: necessary and sufficient condition for `gtCompletion` to
  reconstruct a fixed-boundary integer hive.
* `TauCeti.Hive.gt_completion_of_uniform_input_gap`, `TauCeti.Hive.exists_stable_gt_equiv`.
* `TauCeti.Hive.gtRemainingRhombus_two_iff` and low-rank worked examples in ranks `0`, `1`, `2`,
  and `3`.

## References

* A. Henriques and J. Kamnitzer, *Crystals and coboundary categories*, Duke Math. J. **132**
  (2006), 191–266, §7, Theorem 7.4.
* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### The product chart `(i, j) ↦ (n - j, j - i, i)` -/

section Chart

variable {n : ℕ}

/-- The product-chart lattice vertex `(i, j) ↦ (n - j, j - i, i)` in `Δₙ` for `0 ≤ i ≤ j ≤ n`. -/
def gtVertex (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) : Vertex n :=
  ⟨n - j, j - i, i, by omega⟩

@[simp]
theorem gtVertex_x (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (gtVertex n i j hij hjn).x = n - j := (rfl)

@[simp]
theorem gtVertex_y (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (gtVertex n i j hij hjn).y = j - i := (rfl)

@[simp]
theorem gtVertex_z (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (gtVertex n i j hij hjn).z = i := (rfl)

theorem gtVertex_eq_ofYZ (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    gtVertex n i j hij hjn = Vertex.ofYZ n (j - i) i (by omega) := by
  ext <;> simp; omega

@[simp]
theorem gtVertex_eq_iff {i₁ j₁ i₂ j₂ : ℕ} {hi₁ : i₁ ≤ j₁} {hj₁ : j₁ ≤ n}
    {hi₂ : i₂ ≤ j₂} {hj₂ : j₂ ≤ n} :
    gtVertex n i₁ j₁ hi₁ hj₁ = gtVertex n i₂ j₂ hi₂ hj₂ ↔ i₁ = i₂ ∧ j₁ = j₂ := by
  refine ⟨fun h => ⟨congrArg Vertex.z h, ?_⟩, fun ⟨hi, hj⟩ => by subst hi; subst hj; rfl⟩
  have hx := congrArg Vertex.x h
  simp only [gtVertex_x] at hx
  omega

/-- Every vertex `p : Vertex n` has `p.z ≤ n - p.x` and `n - p.x ≤ n`, and is recovered by
`gtVertex n p.z (n - p.x)`. -/
@[simp]
theorem gtVertex_z_sub_x (p : Vertex n) :
    gtVertex n p.z (n - p.x) (by have := p.sum_eq; omega) (Nat.sub_le n p.x) = p := by
  have := p.sum_eq
  ext <;> simp <;> omega

/-- Equivalence between the triangular index set `{ (i, j) // i ≤ j ∧ j ≤ n }` and `Vertex n`. -/
def gtChartEquiv (n : ℕ) : {ij : ℕ × ℕ // ij.1 ≤ ij.2 ∧ ij.2 ≤ n} ≃ Vertex n where
  toFun ij := gtVertex n ij.1.1 ij.1.2 ij.2.1 ij.2.2
  invFun p := ⟨(p.z, n - p.x), ⟨by have := p.sum_eq; omega, Nat.sub_le n p.x⟩⟩
  left_inv ij := by
    apply Subtype.ext
    ext
    · simp
    · simp only [gtVertex_x]
      have := ij.2.2
      omega
  right_inv := gtVertex_z_sub_x

@[simp]
theorem gtChartEquiv_apply (ij : {ij : ℕ × ℕ // ij.1 ≤ ij.2 ∧ ij.2 ≤ n}) :
    gtChartEquiv n ij = gtVertex n ij.1.1 ij.1.2 ij.2.1 ij.2.2 := (rfl)

@[simp]
theorem gtChartEquiv_symm_apply_coe (p : Vertex n) :
    ((gtChartEquiv n).symm p).1 = (p.z, n - p.x) := (rfl)

@[simp]
theorem gtVertex_zero_zero (n : ℕ) :
    gtVertex n 0 0 le_rfl (Nat.zero_le n) = Vertex.cornerA n := by
  ext <;> simp

theorem gtVertex_zero_left (n j : ℕ) (hjn : j ≤ n) :
    gtVertex n 0 j (Nat.zero_le j) hjn = Vertex.edgePoint n 0 ⟨j, Nat.lt_succ_of_le hjn⟩ := by
  ext <;> simp

theorem gtVertex_self (n j : ℕ) (hjn : j ≤ n) :
    gtVertex n j j le_rfl hjn = Vertex.edgePoint n 2 ⟨n - j, by omega⟩ := by
  ext <;> simp; omega

theorem gtVertex_top (n i : ℕ) (hin : i ≤ n) :
    gtVertex n i n hin le_rfl = Vertex.edgePoint n 1 ⟨i, Nat.lt_succ_of_le hin⟩ := by
  ext <;> simp

/-- Along the bottom chart edge `i = 0`, a hive takes the prefix sums of side `0`. -/
theorem apply_gtVertex_zero_left {R : Type*} [AddCommGroup R] [PartialOrder R]
    (h : Hive n R) {j : ℕ} (hjn : j ≤ n) :
    h (gtVertex n 0 j (Nat.zero_le j) hjn) = prefixSum j (h.boundary 0) := by
  rw [gtVertex_zero_left, h.apply_edgePoint_zero, prefixSum_def]

/-- Along the right chart edge `j = n`, a hive takes
`(∑ r, h.boundary 0 r) + prefixSum i (h.boundary 1)`. -/
theorem apply_gtVertex_top {R : Type*} [AddCommGroup R] [PartialOrder R]
    (h : Hive n R) {i : ℕ} (hin : i ≤ n) :
    h (gtVertex n i n hin le_rfl) =
      (∑ r : Fin n, h.boundary 0 r) + prefixSum i (h.boundary 1) := by
  rw [gtVertex_top, h.apply_edgePoint_one, prefixSum_def]

/-- Along the diagonal chart edge `i = j`, an integer hive takes the prefix sums of
`(h.boundaryWeight 2).dual`. -/
theorem apply_gtVertex_self (h : IntegerHive n) {j : ℕ} (hjn : j ≤ n) :
    h (gtVertex n j j le_rfl hjn) = prefixSum j (h.boundaryWeight 2).dual.1 := by
  rw [gtVertex_self, h.apply_edgePoint_two, prefixSum_def, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_neg_distrib]
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev, DominantWeight.dual_apply, coe_boundaryWeight]
  by_cases hr : r.val < j
  · have hr' : n - j ≤ n - (r.val + 1) := by omega
    simp [hr, hr']
  · have hr' : ¬ n - j ≤ n - (r.val + 1) := by omega
    simp [hr, hr']

end Chart

/-! ### Unit-rhombus classification in the product chart -/

section RhombusClassification

variable {n : ℕ}

/-- First Gelfand–Tsetlin rhombus family in the `(i, j)` chart (`0 ≤ i < j < n`): obtuse corners
`(i, j)` and `(i + 1, j + 1)`, acute corners `(i + 1, j)` and `(i, j + 1)`. -/
theorem isRhombus_gtVertex_first {i j : ℕ} (hij : i < j) (hjn : j < n) :
    IsRhombus
      (gtVertex n i j hij.le hjn.le)
      (gtVertex n (i + 1) j hij hjn.le)
      (gtVertex n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn)
      (gtVertex n i (j + 1) (hij.le.trans (Nat.le_succ j)) hjn) := by
  have hr :=
    (isRhombus_ofYZ_step (n := n) (y := i) (z := n - (j + 1)) (by omega)).rotate.swap_opposite
  convert hr using 1 <;> (ext <;> simp <;> omega)

/-- Second Gelfand–Tsetlin rhombus family in the `(i, j)` chart (`0 ≤ i < j < n`): obtuse corners
`(i + 1, j)` and `(i + 1, j + 1)`, acute corners `(i, j)` and `(i + 2, j + 1)`. -/
theorem isRhombus_gtVertex_second {i j : ℕ} (hij : i < j) (hjn : j < n) :
    IsRhombus
      (gtVertex n (i + 1) j hij hjn.le)
      (gtVertex n i j hij.le hjn.le)
      (gtVertex n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn)
      (gtVertex n (i + 2) (j + 1) (Nat.succ_le_succ hij) hjn) := by
  have hr := (isRhombus_ofYZ_step (n := n) (y := n - (j + 1)) (z := j - (i + 1))
    (by omega)).rotate.rotate.reverse
  convert hr using 1 <;> (ext <;> simp <;> omega)

/-- Third (remaining) rhombus family in the `(i, j)` chart (`0 ≤ i ≤ j`, `j + 2 ≤ n`): obtuse
corners `(i, j + 1)` and `(i + 1, j + 1)`, acute corners `(i, j)` and `(i + 1, j + 2)`. -/
theorem isRhombus_gtVertex_third {i j : ℕ} (hij : i ≤ j) (hjn : j + 2 ≤ n) :
    IsRhombus
      (gtVertex n i (j + 1) (hij.trans (Nat.le_succ j)) (by omega))
      (gtVertex n i j hij (by omega))
      (gtVertex n (i + 1) (j + 1) (Nat.succ_le_succ hij) (by omega))
      (gtVertex n (i + 1) (j + 2) (by omega) hjn) := by
  have hr := isRhombus_ofYZ_step (n := n) (y := j - i) (z := i) (by omega)
  convert hr using 1 <;> (ext <;> simp <;> omega)

private theorem neg_one_le_and_le_one_of_sq_le_two {u : ℤ} (hu : u ^ 2 ≤ 2) :
    -1 ≤ u ∧ u ≤ 1 := by
  constructor <;> (by_contra! h; nlinarith)

/-- Every unit rhombus has equal `x`, equal `y`, or equal `z` coordinates along its short
diagonal. -/
theorem IsRhombus.x_eq_or_y_eq_or_z_eq {a b c d : Vertex n} (hr : IsRhombus a b c d) :
    a.x = c.x ∨ a.y = c.y ∨ a.z = c.z := by
  have hs := hr.short
  rw [Vertex.sqDist_def] at hs
  have hsum : (a.x : ℤ) + a.y + a.z = (c.x : ℤ) + c.y + c.z := by
    have := a.sum_eq; have := c.sum_eq; omega
  have hdx := neg_one_le_and_le_one_of_sq_le_two (u := (a.x : ℤ) - c.x)
    (by linarith [sq_nonneg ((a.y : ℤ) - c.y), sq_nonneg ((a.z : ℤ) - c.z)])
  have hdy := neg_one_le_and_le_one_of_sq_le_two (u := (a.y : ℤ) - c.y)
    (by linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.z : ℤ) - c.z)])
  have hdz := neg_one_le_and_le_one_of_sq_le_two (u := (a.z : ℤ) - c.z)
    (by linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.y : ℤ) - c.y)])
  omega

/-- Classify a unit rhombus whose short diagonal has `a.x = c.x` and `c.y + 1 = a.y`: it is an
elementary `(y, z)`-step cell up to reversing the two acute corners. -/
private theorem eq_ofYZ_step_of_isRhombus_of_x_eq {a b c d : Vertex n} (hr : IsRhombus a b c d)
    (hx : a.x = c.x) (hy : c.y + 1 = a.y) :
    ∃ (u v : ℕ) (huv : (u + 1) + (v + 1) ≤ n),
      a = Vertex.ofYZ n (u + 1) v (Nat.le_of_succ_le huv) ∧
      c = Vertex.ofYZ n u (v + 1) (by omega) ∧
      ((b = Vertex.ofYZ n u v (by omega) ∧ d = Vertex.ofYZ n (u + 1) (v + 1) huv) ∨
        (b = Vertex.ofYZ n (u + 1) (v + 1) huv ∧ d = Vertex.ofYZ n u v (by omega))) := by
  have ha := a.sum_eq; have hb := b.sum_eq; have hc := c.sum_eq; have hd := d.sum_eq
  have hz : a.z + 1 = c.z := by omega
  have hx' : (a.x : ℤ) = c.x := by exact_mod_cast hx
  have hy' : (c.y : ℤ) + 1 = a.y := by exact_mod_cast hy
  have hz' : (a.z : ℤ) + 1 = c.z := by exact_mod_cast hz
  have hab := hr.side_ab; have hbc := hr.side_bc
  rw [Vertex.sqDist_def] at hab; rw [Vertex.sqDist_comm, Vertex.sqDist_def] at hbc
  set t : ℤ := (b.z : ℤ) - a.z
  have hby : (b.y : ℤ) = c.y + t := by
    have hdiff : ((a.x : ℤ) - b.x) ^ 2 + ((a.y : ℤ) - b.y) ^ 2 + ((a.z : ℤ) - b.z) ^ 2 -
        (((c.x : ℤ) - b.x) ^ 2 + ((c.y : ℤ) - b.y) ^ 2 + ((c.z : ℤ) - b.z) ^ 2) = 0 := by omega
    rw [hx', ← hy', ← hz'] at hdiff
    linarith
  have hbx : (b.x : ℤ) = a.x + 1 - 2 * t := by omega
  have ht2 : t * (t - 1) = 0 := by
    have hbz : (a.z : ℤ) + t = b.z := add_sub_cancel _ _
    have hq : ((a.x : ℤ) - (a.x + 1 - 2 * t)) ^ 2 + ((c.y + 1 : ℤ) - (c.y + t)) ^ 2 +
        ((a.z : ℤ) - (a.z + t)) ^ 2 = 2 := by
      rw [← hbx, ← hby, hbz, hy']
      exact hab
    have hq6 : (6 : ℤ) * (t * (t - 1)) = 0 := by linear_combination hq
    exact (mul_eq_zero.mp hq6).resolve_left (by decide)
  have hmx := hr.midpoint_x; have hmy := hr.midpoint_y
  rcases mul_eq_zero.mp ht2 with ht0 | ht1
  · refine ⟨c.y, a.z, by omega, by ext <;> simp <;> omega, by ext <;> simp <;> omega,
      Or.inl ⟨by ext <;> simp <;> omega, by ext <;> simp <;> omega⟩⟩
  · refine ⟨c.y, a.z, by omega, by ext <;> simp <;> omega, by ext <;> simp <;> omega,
      Or.inr ⟨by ext <;> simp <;> omega, by ext <;> simp <;> omega⟩⟩

/-- When `a.x = c.x` on a unit rhombus `(a, b, c, d)`, `f b + f d ≤ f a + f c` follows from the
elementary `(y, z)`-step inequalities. -/
private theorem le_of_x_eq_of_ofYZ_step {R : Type*} [AddCommSemigroup R] [LE R]
    {f : Vertex n → R}
    (hstep : ∀ (u v : ℕ) (huv : (u + 1) + (v + 1) ≤ n),
      f (Vertex.ofYZ n u v (by omega)) + f (Vertex.ofYZ n (u + 1) (v + 1) huv) ≤
        f (Vertex.ofYZ n (u + 1) v (Nat.le_of_succ_le huv)) +
          f (Vertex.ofYZ n u (v + 1) (by omega)))
    {a b c d : Vertex n} (hr : IsRhombus a b c d) (hx : a.x = c.x) :
    f b + f d ≤ f a + f c := by
  have hs := hr.short; rw [Vertex.sqDist_def] at hs
  have ha := a.sum_eq; have hc := c.sum_eq
  have hdy : c.y + 1 = a.y ∨ a.y + 1 = c.y := by
    have hsq : ((a.y : ℤ) - c.y) ^ 2 + ((a.z : ℤ) - c.z) ^ 2 = 2 := by
      rw [hx] at hs; linarith
    have hbnd := neg_one_le_and_le_one_of_sq_le_two (u := (a.y : ℤ) - c.y)
      (by linarith [sq_nonneg ((a.z : ℤ) - c.z)])
    have hne : a.y ≠ c.y := fun hy0 => by
      have hz0 : a.z = c.z := by omega
      rw [hy0, hz0] at hsq
      linarith
    omega
  rcases hdy with hy | hy
  · obtain ⟨u, v, huv, ha', hc', ⟨hb', hd'⟩ | ⟨hb', hd'⟩⟩ :=
      eq_ofYZ_step_of_isRhombus_of_x_eq hr hx hy
    · rw [ha', hc', hb', hd']
      exact hstep u v huv
    · rw [ha', hc', hb', hd', add_comm (f (Vertex.ofYZ n (u + 1) (v + 1) huv))]
      exact hstep u v huv
  · obtain ⟨u, v, huv, hc', ha', ⟨hd', hb'⟩ | ⟨hd', hb'⟩⟩ :=
      eq_ofYZ_step_of_isRhombus_of_x_eq hr.swap_opposite hx.symm hy
    · rw [ha', hc', hb', hd', add_comm (f (Vertex.ofYZ n (u + 1) (v + 1) huv)),
        add_comm (f (Vertex.ofYZ n u (v + 1) _))]
      exact hstep u v huv
    · rw [ha', hc', hb', hd', add_comm (f (Vertex.ofYZ n u (v + 1) _))]
      exact hstep u v huv

/-- **Product-chart characterization of rhombus concavity**: a lattice function `f : Vertex n → R`
is rhombus-concave if and only if it satisfies the three `(i, j)`-chart rhombus families. -/
theorem isRhombusConcave_iff_gtVertex {R : Type*} [AddCommGroup R] [Preorder R]
    (f : Vertex n → R) :
    IsRhombusConcave f ↔
      (∀ (i j : ℕ) (hij : i < j) (hjn : j < n),
        f (gtVertex n (i + 1) j hij hjn.le) +
          f (gtVertex n i (j + 1) (hij.le.trans (Nat.le_succ j)) hjn) ≤
          f (gtVertex n i j hij.le hjn.le) +
            f (gtVertex n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn)) ∧
      (∀ (i j : ℕ) (hij : i < j) (hjn : j < n),
        f (gtVertex n i j hij.le hjn.le) +
          f (gtVertex n (i + 2) (j + 1) (Nat.succ_le_succ hij) hjn) ≤
          f (gtVertex n (i + 1) j hij hjn.le) +
            f (gtVertex n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn)) ∧
      (∀ (i j : ℕ) (hij : i ≤ j) (hjn : j + 2 ≤ n),
        f (gtVertex n i j hij (by omega)) +
          f (gtVertex n (i + 1) (j + 2) (by omega) hjn) ≤
          f (gtVertex n i (j + 1) (hij.trans (Nat.le_succ j)) (by omega)) +
            f (gtVertex n (i + 1) (j + 1) (Nat.succ_le_succ hij) (by omega))) := by
  rw [isRhombusConcave_def]
  refine ⟨fun hf => ⟨fun i j hij hjn => hf (isRhombus_gtVertex_first hij hjn),
    fun i j hij hjn => hf (isRhombus_gtVertex_second hij hjn),
    fun i j hij hjn => hf (isRhombus_gtVertex_third hij hjn)⟩, ?_⟩
  rintro ⟨h₁, h₂, h₃⟩ a b c d hr
  rcases hr.x_eq_or_y_eq_or_z_eq with hx | hy | hz
  · refine le_of_x_eq_of_ofYZ_step (fun u v huv => ?_) hr hx
    have h := h₃ v (u + v) (Nat.le_add_left v u) (by omega)
    convert h using 3 <;> (ext <;> simp <;> omega)
  · have hrot := le_of_x_eq_of_ofYZ_step (f := fun p => f p.rotate) (fun u v huv => ?_)
      hr.rotate.rotate (by simpa using hy)
    · simpa only [Vertex.rotate_rotate_rotate] using hrot
    · have h := h₁ u (n - (v + 1)) (by omega) (by omega)
      rw [add_comm (f (gtVertex n (u + 1) (n - (v + 1)) _ _)),
        add_comm (f (gtVertex n u (n - (v + 1)) _ _))] at h
      convert h using 3 <;> (ext <;> simp <;> omega)
  · have hrot := le_of_x_eq_of_ofYZ_step (f := fun p => f p.rotate.rotate) (fun u v huv => ?_)
      hr.rotate (by simpa using hz)
    · simpa only [Vertex.rotate_rotate_rotate] using hrot
    · have h := h₂ (n - (u + 1) - (v + 1)) (n - (u + 1)) (by omega) (by omega)
      rw [add_comm (f (gtVertex n (n - (u + 1) - (v + 1)) (n - (u + 1)) _ _))] at h
      convert h using 3 <;> (ext <;> simp <;> omega)

end RhombusClassification

/-! ### Forward vertical difference map `toGTPattern` -/

section DifferenceMap

variable {n : ℕ}

/-- The signed Gelfand–Tsetlin pattern attached to an integer hive by vertical forward differences
`P i j = h(i + 1, j) - h(i, j)` on the informative cells `0 ≤ i < j ≤ n`. -/
def toGTPattern (h : IntegerHive n) : GTPattern n where
  entry i j :=
    if hij : i < j ∧ j ≤ n then
      h (gtVertex n (i + 1) j hij.1 hij.2) - h (gtVertex n i j hij.1.le hij.2)
    else 0
  zeros' hz := dite_eq_right_iff.mpr fun hij => absurd hij (by omega)
  interlacing' {i j} hij hjn := by
    have hlow : i < j ∧ j ≤ n := ⟨hij, hjn.le⟩
    have hul : i < j + 1 ∧ j + 1 ≤ n := ⟨hij.trans (Nat.lt_succ_self j), hjn⟩
    have hur : i + 1 < j + 1 ∧ j + 1 ≤ n := ⟨Nat.succ_lt_succ hij, hjn⟩
    simp only [hlow, hul, hur, and_self, ↓reduceDIte]
    have hr₁ := h.le_of_isRhombus (isRhombus_gtVertex_first hij hjn)
    have hr₂ := h.le_of_isRhombus (isRhombus_gtVertex_second hij hjn)
    exact ⟨by linarith, by linarith⟩

theorem toGTPattern_apply (h : IntegerHive n) (i j : ℕ) :
    h.toGTPattern i j =
      if hij : i < j ∧ j ≤ n then
        h (gtVertex n (i + 1) j hij.1 hij.2) - h (gtVertex n i j hij.1.le hij.2)
      else 0 := (rfl)

/-- On an informative cell `i < j ≤ n`, `h.toGTPattern i j = h(i + 1, j) - h(i, j)`. -/
@[simp]
theorem toGTPattern_apply_of_lt_of_le (h : IntegerHive n) {i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    h.toGTPattern i j =
      h (gtVertex n (i + 1) j hij hjn) - h (gtVertex n i j hij.le hjn) := by
  simp [toGTPattern_apply, hij, hjn]

@[simp]
theorem toGTPattern_zero : (0 : IntegerHive n).toGTPattern = 0 := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · rw [toGTPattern_apply_of_lt_of_le 0 hij.1 hij.2, zero_apply, zero_apply, sub_self,
      GTPattern.zero_apply]
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.zero_apply]

@[simp]
theorem toGTPattern_add (h₁ h₂ : IntegerHive n) :
    (h₁ + h₂).toGTPattern = h₁.toGTPattern + h₂.toGTPattern := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · simp only [toGTPattern_apply_of_lt_of_le _ hij.1 hij.2, add_apply, GTPattern.add_apply]
    abel
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.add_apply,
      GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega), add_zero]

/-- `TauCeti.Hive.toGTPattern` bundled as an additive monoid homomorphism. -/
def toGTPatternAddMonoidHom (n : ℕ) : IntegerHive n →+ GTPattern n where
  toFun := toGTPattern
  map_zero' := toGTPattern_zero
  map_add' := toGTPattern_add

@[simp]
theorem toGTPatternAddMonoidHom_apply (h : IntegerHive n) :
    toGTPatternAddMonoidHom n h = h.toGTPattern := (rfl)

/-- The top row of `h.toGTPattern` is side `1` of `h.boundary`. -/
@[simp]
theorem topRow_toGTPattern (h : IntegerHive n) : h.toGTPattern.topRow = h.boundary 1 := by
  ext i
  rw [GTPattern.topRow_apply, toGTPattern_apply_of_lt_of_le h i.isLt le_rfl,
    gtVertex_top n (i.val + 1) i.isLt, gtVertex_top n i.val i.isLt.le, h.boundary_apply]
  rfl

/-- The top dominant weight of `h.toGTPattern` is `h.boundaryWeight 1`. -/
@[simp]
theorem topWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.topWeight = h.boundaryWeight 1 :=
  Subtype.ext (by rw [GTPattern.topWeight_coe, topRow_toGTPattern, coe_boundaryWeight])

/-- Vertical partial sums of `h.toGTPattern` telescope to `h(i, j) - h(0, j)`. -/
theorem sum_range_toGTPattern (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    (∑ k ∈ Finset.range i, h.toGTPattern k j) =
      h (gtVertex n i j hij hjn) - h (gtVertex n 0 j (Nat.zero_le j) hjn) := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hij),
      toGTPattern_apply_of_lt_of_le h hij hjn]
    abel

/-- Row `j ≤ n` of `h.toGTPattern` sums to `h(j, j) - h(0, j)`. -/
theorem rowSum_toGTPattern (h : IntegerHive n) {j : ℕ} (hjn : j ≤ n) :
    h.toGTPattern.rowSum j =
      prefixSum j (h.boundaryWeight 2).dual.1 - prefixSum j (h.boundary 0) := by
  rw [GTPattern.rowSum_def, sum_range_toGTPattern h le_rfl hjn, apply_gtVertex_self h hjn,
    apply_gtVertex_zero_left h hjn]

/-- The torus weight of `h.toGTPattern` is `(h.boundaryWeight 2).dual - h.boundary 0`. -/
@[simp]
theorem rowWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.rowWeight = (h.boundaryWeight 2).dual.1 - h.boundary 0 := by
  ext r
  rw [GTPattern.rowWeight_apply, rowSum_toGTPattern h r.isLt, rowSum_toGTPattern h r.isLt.le,
    prefixSum_succ r.isLt, prefixSum_succ r.isLt, Pi.sub_apply]
  abel

/-- On `productBoundary l m g`, `h.toGTPattern` has top row `m` and torus weight `g - l`. -/
theorem topRow_and_rowWeight_toGTPattern_of_productBoundary {l m g : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary l m g) :
    h.toGTPattern.topRow = m.1 ∧ h.toGTPattern.rowWeight = g.1 - l.1 := by
  have hb2 : h.boundaryWeight 2 = g.dual := Subtype.ext (by simp [coe_boundaryWeight, hb])
  exact ⟨by simp [hb], by simp [hb2, hb]⟩

end DifferenceMap

/-! ### Inverse chart completion and `gt_reconstruction_iff` -/

section Reconstruction

variable {n : ℕ}

/-- The **product-chart completion** `h(i, j) = prefixSum j l + ∑_{k < i} P k j` reconstructing
lattice values from a bottom-edge sequence `l : Fin n → ℤ` and a pattern `P : GTPattern n`. -/
def gtCompletion (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) : ℤ :=
  prefixSum j l + ∑ k ∈ Finset.range i, P k j

theorem gtCompletion_def (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P i j = prefixSum j l + ∑ k ∈ Finset.range i, P k j := (rfl)

@[simp]
theorem gtCompletion_zero_left (l : Fin n → ℤ) (P : GTPattern n) (j : ℕ) :
    gtCompletion l P 0 j = prefixSum j l := by
  simp [gtCompletion]

theorem gtCompletion_zero_zero (l : Fin n → ℤ) (P : GTPattern n) :
    gtCompletion l P 0 0 = 0 := by
  simp [gtCompletion]

theorem gtCompletion_self (l : Fin n → ℤ) (P : GTPattern n) (j : ℕ) :
    gtCompletion l P j j = prefixSum j l + P.rowSum j := by
  rw [gtCompletion_def, GTPattern.rowSum_def]

@[simp]
theorem gtCompletion_succ_left_sub (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P (i + 1) j - gtCompletion l P i j = P i j := by
  simp only [gtCompletion_def, Finset.sum_range_succ]
  abel

/-- **Left-inverse chart law**: completing `(h.boundary 0, h.toGTPattern)` at `(i, j)` recovers
`h (gtVertex n i j hij hjn)`. -/
@[simp]
theorem gtCompletion_toGTPattern_gtVertex (h : IntegerHive n) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    gtCompletion (h.boundary 0) h.toGTPattern i j = h (gtVertex n i j hij hjn) := by
  rw [gtCompletion_def, sum_range_toGTPattern h hij hjn, apply_gtVertex_zero_left h hjn]
  abel

/-- Evaluating `gtCompletion (h.boundary 0) h.toGTPattern` at `(v.z, n - v.x)` recovers `h v` at
every vertex `v : Vertex n`. -/
@[simp]
theorem gtCompletion_toGTPattern (h : IntegerHive n) (v : Vertex n) :
    gtCompletion (h.boundary 0) h.toGTPattern v.z (n - v.x) = h v := by
  have hv := gtCompletion_toGTPattern_gtVertex h
    (i := v.z) (j := n - v.x) (by have := v.sum_eq; omega) (Nat.sub_le n v.x)
  rwa [gtVertex_z_sub_x] at hv

/-- The explicit difference-sum form of the third unit-rhombus family for `gtCompletion l P`:
for all `0 ≤ i ≤ j` with `j + 2 ≤ n`,
`∑_{k ≤ i} (P k (j + 2) - P k (j + 1)) ≤ l_j - l_{j + 1} + ∑_{k < i} (P k (j + 1) - P k j)`. -/
def gtRemainingRhombus (l : Fin n → ℤ) (P : GTPattern n) : Prop :=
  ∀ (i j : ℕ), i ≤ j → (hjn : j + 2 ≤ n) →
    (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
      l ⟨j, by omega⟩ - l ⟨j + 1, by omega⟩ + ∑ k ∈ Finset.range i, (P k (j + 1) - P k j)

theorem gtRemainingRhombus_def (l : Fin n → ℤ) (P : GTPattern n) :
    gtRemainingRhombus l P ↔
      ∀ (i j : ℕ), i ≤ j → (hjn : j + 2 ≤ n) →
        (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
          l ⟨j, by omega⟩ - l ⟨j + 1, by omega⟩ +
            ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
  Iff.rfl

/-- Equivalence between the third chart-rhombus inequality on `gtCompletion l P` and the explicit
difference-sum inequality at a single `(i, j)` with `j + 2 ≤ n`. -/
theorem gtCompletion_third_rhombus_iff (l : Fin n → ℤ) (P : GTPattern n)
    {i j : ℕ} (hjn : j + 2 ≤ n) :
    gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
      gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) ↔
    (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
      l ⟨j, by omega⟩ - l ⟨j + 1, by omega⟩ + ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) := by
  simp only [gtCompletion_def, Finset.sum_sub_distrib]
  have hj2 : j + 2 = (j + 1) + 1 := rfl
  rw [hj2, prefixSum_succ (by omega : j + 1 < n) l, prefixSum_succ (by omega : j < n) l]
  omega

/-- `gtRemainingRhombus l P` is equivalent to the third chart-rhombus family on `gtCompletion l P`.
-/
theorem gtRemainingRhombus_iff_gtCompletion_le (l : Fin n → ℤ) (P : GTPattern n) :
    gtRemainingRhombus l P ↔
      ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
        gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
          gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) :=
  forall₄_congr fun _ _ _ hjn => (gtCompletion_third_rhombus_iff l P hjn).symm

/-- Every hive's difference pattern satisfies `gtRemainingRhombus (h.boundary 0)`. -/
theorem gtRemainingRhombus_toGTPattern (h : IntegerHive n) :
    gtRemainingRhombus (h.boundary 0) h.toGTPattern := by
  rw [gtRemainingRhombus_iff_gtCompletion_le]
  intro i j hij hjn
  rw [gtCompletion_toGTPattern_gtVertex h hij (by omega),
    gtCompletion_toGTPattern_gtVertex h (by omega : i + 1 ≤ j + 2) hjn,
    gtCompletion_toGTPattern_gtVertex h (hij.trans (Nat.le_succ j)) (by omega),
    gtCompletion_toGTPattern_gtVertex h (Nat.succ_le_succ hij) (by omega)]
  exact h.le_of_isRhombus (isRhombus_gtVertex_third hij hjn)

/-- `gtCompletion l P` pulled back along `(v.z, n - v.x)` is rhombus-concave iff
`gtRemainingRhombus l P` holds: the first two chart families are automatic from `P`'s interlacing.
-/
theorem isRhombusConcave_gtCompletion_iff (l : Fin n → ℤ) (P : GTPattern n) :
    IsRhombusConcave (fun v : Vertex n => gtCompletion l P v.z (n - v.x)) ↔
      gtRemainingRhombus l P := by
  rw [isRhombusConcave_iff_gtVertex, gtRemainingRhombus_iff_gtCompletion_le]
  have heval (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
      gtCompletion l P (gtVertex n i j hij hjn).z (n - (gtVertex n i j hij hjn).x) =
        gtCompletion l P i j := by
    simp only [gtVertex_z, gtVertex_x, Nat.sub_sub_self hjn]
  refine ⟨fun ⟨_, _, h₃⟩ i j hij hjn => ?_, fun hrem => ⟨?_, ?_, ?_⟩⟩
  · have h := h₃ i j hij hjn
    simpa only [heval] using h
  · intro i j hij hjn
    simp only [heval]
    have hle := P.entry_le_entry_succ_row hij hjn
    have hd₁ := gtCompletion_succ_left_sub l P i j
    have hd₂ := gtCompletion_succ_left_sub l P i (j + 1)
    linarith
  · intro i j hij hjn
    simp only [heval]
    have hle := P.entry_succ_succ_le_entry (i := i) hjn
    have hd₁ := gtCompletion_succ_left_sub l P i j
    have hd₂ := gtCompletion_succ_left_sub l P (i + 1) (j + 1)
    linarith
  · intro i j hij hjn
    simp only [heval]
    exact hrem i j hij hjn

/-- Clockwise boundary of the lattice function `v ↦ gtCompletion l P v.z (n - v.x)`. -/
theorem boundaryLinear_gtCompletion (l : Fin n → ℤ) (P : GTPattern n) :
    boundaryLinear ℤ n ℤ (fun v : Vertex n => gtCompletion l P v.z (n - v.x)) =
      ![l, P.topRow, fun r => -(l r.rev + P.rowWeight r.rev)] := by
  ext s r
  fin_cases s
  · simp only [boundaryLinear_apply, Fin.zero_eta, Vertex.edgePoint_zero_z, Vertex.edgePoint_zero_x,
      gtCompletion_zero_left, Fin.val_succ, Fin.val_castSucc, Matrix.cons_val_zero]
    rw [Nat.sub_sub_self r.isLt, Nat.sub_sub_self r.isLt.le, prefixSum_succ r.isLt, Fin.eta]
    abel
  · simp only [boundaryLinear_apply, Fin.mk_one, Vertex.edgePoint_one_z, Vertex.edgePoint_one_x,
      Nat.sub_zero, Fin.val_succ, Fin.val_castSucc, gtCompletion_succ_left_sub,
      Matrix.cons_val_one, Matrix.cons_val_zero, GTPattern.topRow_apply]
  · simp only [boundaryLinear_apply, Fin.reduceFinMk, Vertex.edgePoint_two_z,
      Vertex.edgePoint_two_x, gtCompletion_self, Fin.val_succ, Fin.val_castSucc,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, GTPattern.rowWeight_apply]
    have hrev1 : n - r.val = r.rev.val + 1 := by simp only [Fin.val_rev]; omega
    have hrev0 : n - (r.val + 1) = r.rev.val := by simp only [Fin.val_rev]
    rw [hrev1, hrev0, prefixSum_succ r.rev.isLt, Fin.eta]
    abel

/-- Reconstruct a normalized integer hive from `(l, P)` under `gtRemainingRhombus l P`. -/
def hiveOfGTPattern (l : Fin n → ℤ) (P : GTPattern n) (hrem : gtRemainingRhombus l P) :
    IntegerHive n where
  value v := gtCompletion l P v.z (n - v.x)
  value_cornerA' := by simp
  le_of_isRhombus' hr :=
    (isRhombusConcave_def _).mp ((isRhombusConcave_gtCompletion_iff l P).mpr hrem) hr

@[simp]
theorem hiveOfGTPattern_apply (l : Fin n → ℤ) (P : GTPattern n)
    (hrem : gtRemainingRhombus l P) (v : Vertex n) :
    hiveOfGTPattern l P hrem v = gtCompletion l P v.z (n - v.x) := by
  rw [← value_eq_coe]; rfl

theorem boundary_hiveOfGTPattern (l : Fin n → ℤ) (P : GTPattern n)
    (hrem : gtRemainingRhombus l P) :
    (hiveOfGTPattern l P hrem).boundary =
      ![l, P.topRow, fun r => -(l r.rev + P.rowWeight r.rev)] := by
  rw [← boundaryLinear_gtCompletion l P]
  ext s r
  simp [boundary_apply]

/-- **Right-inverse difference law**: taking vertical differences of `hiveOfGTPattern l P hrem`
recovers `P`. -/
@[simp]
theorem toGTPattern_hiveOfGTPattern (l : Fin n → ℤ) (P : GTPattern n)
    (hrem : gtRemainingRhombus l P) :
    (hiveOfGTPattern l P hrem).toGTPattern = P := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · rw [toGTPattern_apply_of_lt_of_le _ hij.1 hij.2, hiveOfGTPattern_apply, hiveOfGTPattern_apply]
    simp only [gtVertex_z, gtVertex_x, Nat.sub_sub_self hij.2, gtCompletion_succ_left_sub]
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega)]

/-- **Equivalence between fixed-boundary integer hives and the constrained Gelfand–Tsetlin fibre**:
hives with boundary `productBoundary l m g` correspond bijectively via `toGTPattern` and
`hiveOfGTPattern` to Gelfand–Tsetlin patterns `P` with top row `m`, torus weight `g - l`, and
`gtRemainingRhombus l P`. -/
def fixedHiveEquivGTPattern (l m g : DominantWeight n) :
    FixedIntegerHive (productBoundary l m g) ≃
      {P : GTPattern n //
        P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1 ∧ gtRemainingRhombus l.1 P} where
  toFun h := ⟨h.1.toGTPattern,
    (topRow_and_rowWeight_toGTPattern_of_productBoundary h.2).1,
    (topRow_and_rowWeight_toGTPattern_of_productBoundary h.2).2, by
      have hb0 : h.1.boundary 0 = l.1 := by rw [h.2, productBoundary_zero]
      exact hb0 ▸ gtRemainingRhombus_toGTPattern h.1⟩
  invFun P := ⟨hiveOfGTPattern l.1 P.1 P.2.2.2, by
    rw [boundary_hiveOfGTPattern, P.2.1, P.2.2.1]
    ext s r
    fin_cases s <;> simp⟩
  left_inv h := by
    apply Subtype.ext
    ext v
    dsimp only
    have hb0 : h.1.boundary 0 = l.1 := by rw [h.2, productBoundary_zero]
    rw [hiveOfGTPattern_apply, ← hb0, gtCompletion_toGTPattern]
  right_inv P := Subtype.ext (toGTPattern_hiveOfGTPattern l.1 P.1 P.2.2.2)

@[simp]
theorem fixedHiveEquivGTPattern_apply_coe (l m g : DominantWeight n)
    (h : FixedIntegerHive (productBoundary l m g)) :
    (fixedHiveEquivGTPattern l m g h).1 = h.1.toGTPattern := (rfl)

@[simp]
theorem fixedHiveEquivGTPattern_symm_apply_coe (l m g : DominantWeight n)
    (P : {P : GTPattern n //
      P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1 ∧ gtRemainingRhombus l.1 P})
    (v : Vertex n) :
    ((fixedHiveEquivGTPattern l m g).symm P).1 v = gtCompletion l.1 P.1 v.z (n - v.x) :=
  hiveOfGTPattern_apply l.1 P.1 P.2.2.2 v

/-- **Gelfand–Tsetlin hive reconstruction criterion**: for a pattern `P` with top row `m` and
torus weight `g - l`, a hive with boundary `productBoundary l m g` whose values are the chart
completion `gtCompletion l P` exists if and only if the remaining rhombus family holds on
`gtCompletion l P`. -/
theorem gt_reconstruction_iff (l m g : DominantWeight n) (P : GTPattern n)
    (hTop : P.topRow = m.1) (hWeight : P.rowWeight = g.1 - l.1) :
    (∃ h : FixedIntegerHive (productBoundary l m g),
      ∀ v : Vertex n, h.1 v = gtCompletion l.1 P v.z (n - v.x)) ↔
    ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
      gtCompletion l.1 P i j + gtCompletion l.1 P (i + 1) (j + 2) ≤
        gtCompletion l.1 P i (j + 1) + gtCompletion l.1 P (i + 1) (j + 1) := by
  rw [← gtRemainingRhombus_iff_gtCompletion_le]
  refine ⟨fun ⟨h, hv⟩ => ?_, fun hrem =>
    ⟨(fixedHiveEquivGTPattern l m g).symm ⟨P, hTop, hWeight, hrem⟩,
      fixedHiveEquivGTPattern_symm_apply_coe l m g ⟨P, hTop, hWeight, hrem⟩⟩⟩
  have hconc : IsRhombusConcave (fun v : Vertex n => gtCompletion l.1 P v.z (n - v.x)) := by
    have heq : (fun v : Vertex n => gtCompletion l.1 P v.z (n - v.x)) = ⇑h.1 :=
      funext fun v => (hv v).symm
    rw [heq]
    exact h.1.isRhombusConcave
  exact (isRhombusConcave_gtCompletion_iff l.1 P).mp hconc

end Reconstruction

/-! ### Cyclic-orientation conversion (`(λ, μ, ν)` to `productBoundary ν λ μ*`) -/

section CyclicOrientation

variable {n : ℕ}

/-- Evaluating `h.rotate.rotate` subtracts the value at `C = (0, 0, n)` from `h p.rotate.rotate`. -/
theorem rotate_rotate_apply {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (h : Hive n R) (p : Vertex n) :
    h.rotate.rotate p = h p.rotate.rotate - h (Vertex.cornerA n).rotate.rotate := by
  simp only [rotate_apply]
  abel

/-- Rotating twice shifts boundary sides by `2` in `Fin 3`. -/
theorem boundary_rotate_rotate {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (h : Hive n R) (s : Fin 3) :
    h.rotate.rotate.boundary s = h.boundary (s + 2) := by
  rw [boundary_rotate, boundary_rotate, add_assoc]
  rfl

/-- Counterclockwise rotation `h ↦ h.rotate.rotate` converts the cyclic boundary `(λ, μ, ν)` into
`productBoundary ν λ μ*`. -/
theorem boundary_rotate_rotate_eq_productBoundary_iff (lam μ ν : DominantWeight n)
    (h : IntegerHive n) :
    h.boundary = ![lam.1, μ.1, ν.1] ↔
      h.rotate.rotate.boundary = productBoundary ν lam μ.dual := by
  constructor
  · intro hb
    ext s r
    fin_cases s <;> simp [hb]
  · intro hb
    ext s r
    have hrot := congrFun (congrFun hb (s + 1)) r
    fin_cases s <;> simpa using hrot

/-- **Cyclic-to-product hive equivalence**: counterclockwise rotation identifies normalized integer
hives of cyclic boundary `(λ, μ, ν)` with those of boundary `productBoundary ν λ μ*`. -/
def cyclicToProductEquiv (lam μ ν : DominantWeight n) :
    FixedIntegerHive ![lam.1, μ.1, ν.1] ≃
      FixedIntegerHive (productBoundary ν lam μ.dual) where
  toFun h := ⟨h.1.rotate.rotate, (boundary_rotate_rotate_eq_productBoundary_iff lam μ ν h.1).mp h.2⟩
  invFun k := ⟨k.1.rotate,
    (boundary_rotate_rotate_eq_productBoundary_iff lam μ ν k.1.rotate).mpr
      (by simpa only [rotate_rotate_rotate] using k.2)⟩
  left_inv h := Subtype.ext (rotate_rotate_rotate h.1)
  right_inv k := Subtype.ext (rotate_rotate_rotate k.1)

@[simp]
theorem cyclicToProductEquiv_apply_coe (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive ![lam.1, μ.1, ν.1]) :
    (cyclicToProductEquiv lam μ ν h).1 = h.1.rotate.rotate := (rfl)

@[simp]
theorem cyclicToProductEquiv_symm_apply_coe (lam μ ν : DominantWeight n)
    (k : FixedIntegerHive (productBoundary ν lam μ.dual)) :
    ((cyclicToProductEquiv lam μ ν).symm k).1 = k.1.rotate := (rfl)

/-- The Gelfand–Tsetlin pattern in the Henriques–Kamnitzer cyclic orientation, obtained by applying
`toGTPattern` after counterclockwise rotation `h ↦ h.rotate.rotate`. -/
def toCyclicGTPattern (h : IntegerHive n) : GTPattern n :=
  h.rotate.rotate.toGTPattern

@[simp]
theorem topRow_toCyclicGTPattern (h : IntegerHive n) :
    h.toCyclicGTPattern.topRow = h.boundary 0 := by
  simp [toCyclicGTPattern]

@[simp]
theorem rowWeight_toCyclicGTPattern (h : IntegerHive n) :
    h.toCyclicGTPattern.rowWeight = (h.boundaryWeight 1).dual.1 - h.boundary 2 := by
  simp [toCyclicGTPattern]

/-- **Cyclic-orientation hive-to-pattern equivalence**: integer hives with cyclic boundary
`(λ, μ, ν)` correspond bijectively to Gelfand–Tsetlin patterns `P` of top row `λ` and torus weight
`μ* - ν` satisfying `gtRemainingRhombus ν P`. -/
def cyclicHiveEquivGTPattern (lam μ ν : DominantWeight n) :
    FixedIntegerHive ![lam.1, μ.1, ν.1] ≃
      {P : GTPattern n //
        P.topRow = lam.1 ∧ P.rowWeight = μ.dual.1 - ν.1 ∧ gtRemainingRhombus ν.1 P} :=
  (cyclicToProductEquiv lam μ ν).trans (fixedHiveEquivGTPattern ν lam μ.dual)

@[simp]
theorem cyclicHiveEquivGTPattern_apply_coe (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive ![lam.1, μ.1, ν.1]) :
    (cyclicHiveEquivGTPattern lam μ ν h).1 = h.1.toCyclicGTPattern := (rfl)

end CyclicOrientation

/-! ### Uniform input-gap sufficiency and the stable hive-to-pattern equivalence -/

section StableRegime

private theorem thirdRhombus_defect_le_of_le {n : ℕ} (P : GTPattern (n + 1))
    {i j : ℕ} (hij : i ≤ j) (hjn : j + 2 ≤ n + 1) :
    (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) -
      (∑ k ∈ Finset.range i, (P k (j + 1) - P k j)) ≤
      P.topRow 0 - P.topRow (Fin.last n) := by
  have hrhs : 0 ≤ ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
    Finset.sum_nonneg fun k hk => sub_nonneg.mpr
      (P.entry_le_entry_succ_row (lt_of_lt_of_le (Finset.mem_range.mp hk) hij) (by omega))
  have hlhs : (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
      P 0 (j + 2) - P (i + 1) (j + 2) := by
    rw [← Finset.sum_range_sub' (fun k => P k (j + 2)) (i + 1)]
    exact Finset.sum_le_sum fun k _ => sub_le_sub_left
      (P.entry_succ_succ_le_entry (i := k) (j := j + 1) (by omega)) _
  have htop : P 0 (j + 2) ≤ P.topRow 0 := (P.entry_mem_Icc (by omega) hjn).2
  have hbot : P.topRow (Fin.last n) ≤ P (i + 1) (j + 2) := by
    simpa [Fin.last] using (P.entry_mem_Icc (i := i + 1) (j := j + 2) (by omega) hjn).1
  linarith

private theorem thirdRhombus_defect_le_of_gt {n : ℕ} (P : GTPattern (n + 1))
    {i j : ℕ} (hij : j + 1 ≤ i) (hjn : j + 2 ≤ n + 1) :
    (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) -
      (∑ k ∈ Finset.range i, (P k (j + 1) - P k j)) ≤
      P.topRow 0 - P.topRow (Fin.last n) := by
  have htrim₁ : (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) =
      (∑ k ∈ Finset.range (j + 2), P k (j + 2)) - ∑ k ∈ Finset.range (j + 1), P k (j + 1) := by
    rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hij)), Finset.sum_sub_distrib,
      Finset.sum_range_succ (fun k => P k (j + 1)) (j + 1), P.entry_eq_zero_of_le le_rfl, add_zero]
    intro k _ hkj
    simp only [Finset.mem_range, not_lt] at hkj
    rw [P.entry_eq_zero_of_le hkj, P.entry_eq_zero_of_le (by omega), sub_self]
  have htrim₂ : (∑ k ∈ Finset.range i, (P k (j + 1) - P k j)) =
      (∑ k ∈ Finset.range (j + 1), P k (j + 1)) - ∑ k ∈ Finset.range j, P k j := by
    rw [← Finset.sum_subset (Finset.range_mono hij), Finset.sum_sub_distrib,
      Finset.sum_range_succ (fun k => P k j) j, P.entry_eq_zero_of_le le_rfl, add_zero]
    intro k _ hkj
    simp only [Finset.mem_range, not_lt] at hkj
    rw [P.entry_eq_zero_of_le hkj, P.entry_eq_zero_of_le (by omega), sub_self]
  have hub : (∑ k ∈ Finset.range (j + 2), P k (j + 2)) -
      (∑ k ∈ Finset.range (j + 1), P k (j + 1)) ≤ P 0 (j + 2) := by
    rw [Finset.sum_range_succ' (fun k => P k (j + 2)) (j + 1)]
    have hle : (∑ k ∈ Finset.range (j + 1), P (k + 1) (j + 2)) ≤
        ∑ k ∈ Finset.range (j + 1), P k (j + 1) :=
      Finset.sum_le_sum fun k _ => P.entry_succ_succ_le_entry (i := k) (j := j + 1) (by omega)
    linarith
  have hlb : P j (j + 1) ≤ (∑ k ∈ Finset.range (j + 1), P k (j + 1)) -
      ∑ k ∈ Finset.range j, P k j := by
    rw [Finset.sum_range_succ (fun k => P k (j + 1)) j]
    have hle : (∑ k ∈ Finset.range j, P k j) ≤ ∑ k ∈ Finset.range j, P k (j + 1) :=
      Finset.sum_le_sum fun k hk =>
        P.entry_le_entry_succ_row (Finset.mem_range.mp hk) (by omega)
    linarith
  have htop : P 0 (j + 2) ≤ P.topRow 0 := (P.entry_mem_Icc (by omega) hjn).2
  have hbot : P.topRow (Fin.last n) ≤ P j (j + 1) := by
    simpa [Fin.last] using (P.entry_mem_Icc (i := j) (j := j + 1) (by omega) (by omega)).1
  linarith

/-- **Pattern bound on the third-rhombus defect**: for every signed Gelfand–Tsetlin pattern `P` on
`n + 1` rows, every `j` with `j + 2 ≤ n + 1`, and every `i : ℕ`, the net row-step increment across
columns `j, j + 1, j + 2` is at most the top-row spread `P.topRow 0 - P.topRow (Fin.last n)`. -/
theorem thirdRhombus_defect_le {n : ℕ} (P : GTPattern (n + 1)) {j : ℕ} (hjn : j + 2 ≤ n + 1)
    (i : ℕ) :
    (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) -
      (∑ k ∈ Finset.range i, (P k (j + 1) - P k j)) ≤
      P.topRow 0 - P.topRow (Fin.last n) := by
  rcases le_or_gt i j with hij | hij
  · exact thirdRhombus_defect_le_of_le P hij hjn
  · exact thirdRhombus_defect_le_of_gt P hij hjn

/-- **Uniform input-gap sufficiency**: when every adjacent gap `l_r - l_{r + 1}` of `l` is at least
the spread `P.topRow 0 - P.topRow (Fin.last n)`, the third chart-rhombus inequality holds on
`gtCompletion l P` for every `j` with `j + 2 ≤ n + 1` and every `i : ℕ`. -/
theorem gt_completion_of_uniform_input_gap {n : ℕ} (l : Fin (n + 1) → ℤ) (P : GTPattern (n + 1))
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ l r.castSucc - l r.succ)
    {j : ℕ} (hjn : j + 2 ≤ n + 1) (i : ℕ) :
    gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
      gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) := by
  rw [gtCompletion_third_rhombus_iff l P hjn]
  have hdef := thirdRhombus_defect_le P hjn i
  have hg := hGap ⟨j, by omega⟩
  simp only [Fin.castSucc_mk, Fin.succ_mk] at hg
  linarith

/-- Under the uniform input gap, `gtRemainingRhombus l P` holds automatically. -/
theorem gtRemainingRhombus_of_uniform_input_gap {n : ℕ} (l : Fin (n + 1) → ℤ)
    (P : GTPattern (n + 1))
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ l r.castSucc - l r.succ) :
    gtRemainingRhombus l P :=
  (gtRemainingRhombus_iff_gtCompletion_le l P).mpr fun i _ _ hjn =>
    gt_completion_of_uniform_input_gap l P hGap hjn i

/-- **Stable hive-to-pattern equivalence**: when `l` has adjacent coordinate gaps at least
`m 0 - m (last n)`, the difference and completion maps identify `FixedIntegerHive` on
`productBoundary l m g` with the full Gelfand–Tsetlin weight fibre of top row `m` and weight
`g - l`. -/
def stableGTEquiv {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ l.1 r.castSucc - l.1 r.succ) :
    FixedIntegerHive (productBoundary l m g) ≃
      {P : GTPattern (n + 1) // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1} :=
  (fixedHiveEquivGTPattern l m g).trans
    { toFun P := ⟨P.1, P.2.1, P.2.2.1⟩
      invFun P := ⟨P.1, P.2.1, P.2.2,
        gtRemainingRhombus_of_uniform_input_gap l.1 P.1 (by rwa [P.2.1])⟩
      left_inv _ := rfl
      right_inv _ := rfl }

@[simp]
theorem stableGTEquiv_apply_coe {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ l.1 r.castSucc - l.1 r.succ)
    (h : FixedIntegerHive (productBoundary l m g)) :
    (stableGTEquiv l m g hGap h).1 = h.1.toGTPattern := (rfl)

@[simp]
theorem stableGTEquiv_symm_apply_coe {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ l.1 r.castSucc - l.1 r.succ)
    (P : {P : GTPattern (n + 1) // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1})
    (v : Vertex (n + 1)) :
    ((stableGTEquiv l m g hGap).symm P).1 v = gtCompletion l.1 P.1 v.z (n + 1 - v.x) :=
  fixedHiveEquivGTPattern_symm_apply_coe l m g
    ⟨P.1, P.2.1, P.2.2, gtRemainingRhombus_of_uniform_input_gap l.1 P.1 (by rwa [P.2.1])⟩ v

/-- Existence form of `TauCeti.Hive.stableGTEquiv`: under the uniform input gap, there is a
bijection `e` from `FixedIntegerHive (productBoundary l m g)` to patterns of top row `m` and weight
`g - l` whose chart completion recovers every hive vertex value. -/
theorem exists_stable_gt_equiv {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ l.1 r.castSucc - l.1 r.succ) :
    ∃ e : FixedIntegerHive (productBoundary l m g) ≃
        {P : GTPattern (n + 1) // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1},
      ∀ h v, h.1 v = gtCompletion l.1 (e h).1 v.z (n + 1 - v.x) :=
  ⟨stableGTEquiv l m g hGap, fun h v => by
    have hb0 : h.1.boundary 0 = l.1 := by rw [h.2, productBoundary_zero]
    rw [stableGTEquiv_apply_coe, ← hb0, gtCompletion_toGTPattern]⟩

/-- Under the uniform input gap, `hiveCount (productBoundary l m g)` equals the cardinality of the
Gelfand–Tsetlin weight fibre of top row `m` and weight `g - l`. -/
theorem hiveCount_eq_card_gtPattern_of_uniform_input_gap {n : ℕ}
    (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ l.1 r.castSucc - l.1 r.succ) :
    hiveCount (productBoundary l m g) =
      Nat.card {P : GTPattern (n + 1) // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (stableGTEquiv l m g hGap)

end StableRegime

/-! ### Low-rank specializations (`n = 0, 1, 2`) and worked examples -/

section LowRankAndExamples

/-- At rank `0`, `gtRemainingRhombus` is vacuous (`j + 2 ≤ 0` is impossible). -/
@[simp]
theorem gtRemainingRhombus_zero (l : Fin 0 → ℤ) (P : GTPattern 0) : gtRemainingRhombus l P :=
  fun _ _ _ hjn => absurd hjn (by omega)

/-- At rank `1`, `gtRemainingRhombus` is vacuous (`j + 2 ≤ 1` is impossible). -/
@[simp]
theorem gtRemainingRhombus_one (l : Fin 1 → ℤ) (P : GTPattern 1) : gtRemainingRhombus l P :=
  fun _ _ _ hjn => absurd hjn (by omega)

/-- At rank `0`, `FixedIntegerHive` is unconditionally equivalent to the Gelfand–Tsetlin weight
fibre. -/
def fixedHiveEquivGTPatternZero (l m g : DominantWeight 0) :
    FixedIntegerHive (productBoundary l m g) ≃
      {P : GTPattern 0 // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1} :=
  (fixedHiveEquivGTPattern l m g).trans
    { toFun P := ⟨P.1, P.2.1, P.2.2.1⟩
      invFun P := ⟨P.1, P.2.1, P.2.2, gtRemainingRhombus_zero l.1 P.1⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-- At rank `1`, `FixedIntegerHive` is unconditionally equivalent to the Gelfand–Tsetlin weight
fibre. -/
def fixedHiveEquivGTPatternOne (l m g : DominantWeight 1) :
    FixedIntegerHive (productBoundary l m g) ≃
      {P : GTPattern 1 // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1} :=
  (fixedHiveEquivGTPattern l m g).trans
    { toFun P := ⟨P.1, P.2.1, P.2.2.1⟩
      invFun P := ⟨P.1, P.2.1, P.2.2, gtRemainingRhombus_one l.1 P.1⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-- **Rank-`2` remaining-rhombus criterion**: for `n = 2`, the third rhombus family reduces to the
single index `(i, j) = (0, 0)`, giving `P.topRow 0 - P.rowWeight 0 ≤ l 0 - l 1`. -/
theorem gtRemainingRhombus_two_iff (l : Fin 2 → ℤ) (P : GTPattern 2) :
    gtRemainingRhombus l P ↔ P.topRow 0 - P.rowWeight 0 ≤ l 0 - l 1 := by
  rw [gtRemainingRhombus_def]
  constructor
  · intro h
    have h0 := h 0 0 le_rfl le_rfl
    simpa [GTPattern.topRow_apply, GTPattern.rowWeight_apply, GTPattern.rowSum_def] using h0
  · intro h i j hij hjn
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
    simpa [GTPattern.topRow_apply, GTPattern.rowWeight_apply, GTPattern.rowSum_def] using h

/-- On a rank-`2` pattern with `P.topRow = m` and `P.rowWeight = g - l`, `gtRemainingRhombus l P` is
equivalent to the boundary inequality `l 1 + m 0 ≤ g 0`. -/
theorem gtRemainingRhombus_two_iff_of_topRow_of_rowWeight {l m g : Fin 2 → ℤ} {P : GTPattern 2}
    (hTop : P.topRow = m) (hWeight : P.rowWeight = g - l) :
    gtRemainingRhombus l P ↔ l 1 + m 0 ≤ g 0 := by
  rw [gtRemainingRhombus_two_iff, hTop, hWeight, Pi.sub_apply]
  omega

/-- Every rank-`2` Gelfand–Tsetlin weight fibre has at most one pattern, since `P.topRow` fixes row
`2` and `P.rowWeight 0` fixes row `1`. -/
instance subsingleton_gtPattern_two (m w : Fin 2 → ℤ) :
    Subsingleton {P : GTPattern 2 // P.topRow = m ∧ P.rowWeight = w} where
  allEq P₁ P₂ := Subtype.ext <| GTPattern.ext fun i j => by
    rcases (by omega :
        (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (2 < j ∨ j ≤ i)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · have h0 := congrFun (P₁.2.2.trans P₂.2.2.symm) 0
      simpa [GTPattern.rowWeight_apply, GTPattern.rowSum_def] using h0
    · simpa [GTPattern.topRow_apply] using congrFun (P₁.2.1.trans P₂.2.1.symm) 0
    · simpa [GTPattern.topRow_apply] using congrFun (P₁.2.1.trans P₂.2.1.symm) 1
    · rw [P₁.1.entry_eq_zero h, P₂.1.entry_eq_zero h]

/-- Feasibility and cardinality of a rank-`2` Gelfand–Tsetlin weight fibre: it has cardinality `1`
if and only if `m 1 ≤ w 0 ≤ m 0` and `w 0 + w 1 = m 0 + m 1`. -/
theorem card_gtPattern_two_eq_one_iff (m w : Fin 2 → ℤ) :
    Nat.card {P : GTPattern 2 // P.topRow = m ∧ P.rowWeight = w} = 1 ↔
      m 1 ≤ w 0 ∧ w 0 ≤ m 0 ∧ w 0 + w 1 = m 0 + m 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨fun ⟨_, ⟨⟨P, hTop, hW⟩⟩⟩ => ?_, fun ⟨hlo, hhi, hsum⟩ => ⟨inferInstance, ⟨?_⟩⟩⟩
  · have hw0 : w 0 = P 0 1 := by
      have := congrFun hW.symm 0
      simpa [GTPattern.rowWeight_apply, GTPattern.rowSum_def] using this
    have hm0 : m 0 = P 0 2 := by simpa [GTPattern.topRow_apply] using (congrFun hTop 0).symm
    have hm1 : m 1 = P 1 2 := by simpa [GTPattern.topRow_apply] using (congrFun hTop 1).symm
    have hle1 : P 0 1 ≤ P 0 2 := P.entry_le_entry_succ_row (by decide) (by decide)
    have hle2 : P 1 2 ≤ P 0 1 := P.entry_succ_succ_le_entry (i := 0) (j := 1) (by decide)
    have htot := P.sum_rowWeight
    rw [hTop, hW] at htot
    simp only [Fin.sum_univ_two] at htot
    omega
  · let Q : GTPattern 1 := GTPattern.const 1 (w 0)
    have hint : Interlaces m Q.topRow := interlaces_iff.mpr fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      simp [Q, hhi, hlo]
    refine ⟨Q.extend m hint, GTPattern.topRow_extend Q m hint, ?_⟩
    ext ⟨r, hr⟩
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · exact (GTPattern.rowWeight_extend_castSucc Q m hint 0).trans
        (congrFun (GTPattern.rowWeight_const (w 0)) 0)
    · have hQ : ∑ i, Q.topRow i = w 0 := by simp [Q]
      have hm : ∑ i, m i = m 0 + m 1 := Fin.sum_univ_two m
      have hlast : (Q.extend m hint).rowWeight ⟨1, hr⟩ = (∑ i, m i) - ∑ i, Q.topRow i :=
        GTPattern.rowWeight_extend_last Q m hint
      have hw1 : w ⟨1, hr⟩ = w 1 := rfl
      linarith [hsum]

/-- Closed-form criterion for `hiveCount (productBoundary l m g) = 1` in rank `2`. -/
theorem hiveCount_productBoundary_two_eq_one_iff (l m g : DominantWeight 2) :
    hiveCount (productBoundary l m g) = 1 ↔
      m.1 1 ≤ g.1 0 - l.1 0 ∧ g.1 0 - l.1 0 ≤ m.1 0 ∧
        l.1 1 + m.1 0 ≤ g.1 0 ∧ g.1 0 + g.1 1 = l.1 0 + l.1 1 + m.1 0 + m.1 1 := by
  rw [← natCard_fixedIntegerHive, Nat.card_congr (fixedHiveEquivGTPattern l m g)]
  by_cases hrem : l.1 1 + m.1 0 ≤ g.1 0
  · have heq : {P : GTPattern 2 //
        P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1 ∧ gtRemainingRhombus l.1 P} ≃
        {P : GTPattern 2 // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1} :=
      { toFun P := ⟨P.1, P.2.1, P.2.2.1⟩
        invFun P := ⟨P.1, P.2.1, P.2.2,
          (gtRemainingRhombus_two_iff_of_topRow_of_rowWeight P.2.1 P.2.2).mpr hrem⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [Nat.card_congr heq, card_gtPattern_two_eq_one_iff]
    simp only [Pi.sub_apply, hrem, true_and]
    omega
  · refine ⟨fun hc => ?_, fun h => absurd h.2.2.1 hrem⟩
    obtain ⟨_, ⟨⟨P, hTop, hW, hr⟩⟩⟩ := Nat.card_eq_one_iff_unique.mp hc
    exact absurd ((gtRemainingRhombus_two_iff_of_topRow_of_rowWeight hTop hW).mp hr) hrem

/-- Worked check (`n = 2`, `λ = (0, 0)`, `μ = (2, 0)`): at `γ = (2, 0)` both the hive fibre and the
pattern weight fibre have cardinality `1`, whereas at `γ = (1, 1)` the pattern weight fibre still
has cardinality `1` (`P 0 1 = 1`) while `l 1 + m 0 ≤ g 0` (`2 ≤ 1`) fails so `hiveCount = 0`. -/
theorem worked_two_zero_zero_two_zero :
    hiveCount
      (productBoundary ⟨![0, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩) = 1 ∧
    Nat.card {P : GTPattern 2 // P.topRow = ![2, 0] ∧ P.rowWeight = ![2, 0]} = 1 ∧
    hiveCount
      (productBoundary ⟨![0, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![1, 1], by decide⟩) = 0 ∧
    Nat.card {P : GTPattern 2 // P.topRow = ![2, 0] ∧ P.rowWeight = ![1, 1]} = 1 := by
  refine ⟨(hiveCount_productBoundary_two_eq_one_iff _ _ _).mpr (by decide),
    (card_gtPattern_two_eq_one_iff _ _).mpr (by decide), ?_,
    (card_gtPattern_two_eq_one_iff _ _).mpr (by decide)⟩
  have hle := hiveCount_le_one_two
    (productBoundary ⟨![0, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![1, 1], by decide⟩)
  have hne : hiveCount
      (productBoundary ⟨![0, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![1, 1], by decide⟩) ≠ 1 := by
    rw [ne_eq, hiveCount_productBoundary_two_eq_one_iff]
    decide
  omega

/-- Worked check (`n = 2`, `λ = μ = (2, 0)`): all three Clebsch–Gordan summands
`γ = (4, 0), (3, 1), (2, 2)` occur with `hiveCount = 1`. -/
theorem worked_two_sym_two_sym_two :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![4, 0], by decide⟩) = 1 ∧
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![3, 1], by decide⟩) = 1 ∧
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![2, 2], by decide⟩) = 1 :=
  ⟨(hiveCount_productBoundary_two_eq_one_iff _ _ _).mpr (by decide),
    (hiveCount_productBoundary_two_eq_one_iff _ _ _).mpr (by decide),
    (hiveCount_productBoundary_two_eq_one_iff _ _ _).mpr (by decide)⟩

/-- Explicit entry formula for the two rank-`3` patterns of top row `(1, 0, -1)` and torus weight
`0`: middle row `(0, 0)` for `false` and `(1, -1)` for `true`, with bottom entry `0`. -/
private def adjointZeroWeightRaw (b : Bool) : GTPattern 3 where
  entry
    | 0, 2 => if b then 1 else 0
    | 1, 2 => if b then -1 else 0
    | 0, 3 => 1
    | 1, 3 => 0
    | 2, 3 => -1
    | _, _ => 0
  zeros' {i j} h := by
    match i, j with
    | 0, 2 | 1, 2 | 0, 3 | 1, 3 | 2, 3 => omega
    | 0, 0 | 0, 1 | 0, _ + 4 | 1, 0 | 1, 1 | 1, _ + 4
    | 2, 0 | 2, 1 | 2, 2 | 2, _ + 4 | _ + 3, _ => rfl
  interlacing' {i j} hij hjn := by
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases b <;> decide

private def adjointZeroWeightPattern (b : Bool) :
    {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.rowWeight = 0} :=
  ⟨adjointZeroWeightRaw b,
    by
      ext i
      fin_cases i <;>
        simp [GTPattern.topRow_apply, adjointZeroWeightRaw, ← GTPattern.entry_eq_coe],
    by ext r; fin_cases r <;> cases b <;>
      simp [GTPattern.rowWeight_apply, GTPattern.rowSum_def, Finset.sum_range_succ,
        adjointZeroWeightRaw, ← GTPattern.entry_eq_coe]⟩

/-- Equivalence between `Bool` and the two rank-`3` patterns of top row `(1, 0, -1)` and torus
weight `(0, 0, 0)` (middle row `(0, 0)` for `false`, `(1, -1)` for `true`). -/
private def adjointZeroWeightEquivBool :
    {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.rowWeight = 0} ≃ Bool where
  toFun P := decide (P.1 0 2 = 1)
  invFun := adjointZeroWeightPattern
  left_inv := by
    rintro ⟨P, hTop, hW⟩
    have hp03 : P 0 3 = 1 := by simpa [GTPattern.topRow_apply] using congrFun hTop 0
    have hp13 : P 1 3 = 0 := by simpa [GTPattern.topRow_apply] using congrFun hTop 1
    have hp23 : P 2 3 = -1 := by simpa [GTPattern.topRow_apply] using congrFun hTop 2
    have hp01 : P 0 1 = 0 := by
      simpa [GTPattern.rowWeight_apply, GTPattern.rowSum_def] using congrFun hW 0
    have hp12 : P.entry 1 2 = -P 0 2 := by
      have hw1 := congrFun hW 1
      simp only [GTPattern.rowWeight_apply, GTPattern.rowSum_def, Fin.val_one,
        Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hp01, sub_zero,
        Pi.zero_apply] at hw1
      rw [GTPattern.entry_eq_coe]
      linarith
    have hhi : P 0 2 ≤ P 0 3 := P.entry_le_entry_succ_row (by decide) (by decide)
    have hlo : P 1 3 ≤ P 0 2 := P.entry_succ_succ_le_entry (i := 0) (j := 2) (by decide)
    have h02 : P 0 2 = 0 ∨ P 0 2 = 1 := by omega
    apply Subtype.ext
    ext i j
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨
        (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) ∨ (3 < j ∨ j ≤ i)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · rcases h02 with ha | ha <;>
        simp [adjointZeroWeightPattern, adjointZeroWeightRaw, ← GTPattern.entry_eq_coe, ha, hp01]
    · rcases h02 with ha | ha <;>
        simp [adjointZeroWeightPattern, adjointZeroWeightRaw, ← GTPattern.entry_eq_coe, ha]
    · rcases h02 with ha | ha <;>
        simp [adjointZeroWeightPattern, adjointZeroWeightRaw, ← GTPattern.entry_eq_coe, ha, hp12]
    · rcases h02 with ha | ha <;>
        simp [adjointZeroWeightPattern, adjointZeroWeightRaw, ← GTPattern.entry_eq_coe, ha, hp03]
    · rcases h02 with ha | ha <;>
        simp [adjointZeroWeightPattern, adjointZeroWeightRaw, ← GTPattern.entry_eq_coe, ha, hp13]
    · rcases h02 with ha | ha <;>
        simp [adjointZeroWeightPattern, adjointZeroWeightRaw, ← GTPattern.entry_eq_coe, ha, hp23]
    · rw [P.entry_eq_zero h, (adjointZeroWeightPattern _).1.entry_eq_zero h]
  right_inv b := by
    cases b <;> simp [adjointZeroWeightPattern, adjointZeroWeightRaw, ← GTPattern.entry_eq_coe]

/-- Worked check (`n = 3`, `λ = (0, 0, 0)`, `μ = (1, 0, -1)`, `γ = (0, 0, 0)`): the zero-weight
space of the trace-free adjoint representation has `2` Gelfand–Tsetlin patterns, while the third
rhombus family eliminates both so `hiveCount = 0`. -/
theorem worked_three_adjoint_zero_weight :
    Nat.card {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.rowWeight = 0} = 2 ∧
    hiveCount
      (productBoundary
        ⟨![0, 0, 0], by decide⟩ ⟨![1, 0, -1], by decide⟩ ⟨![0, 0, 0], by decide⟩) = 0 := by
  refine ⟨by rw [Nat.card_congr adjointZeroWeightEquivBool, Nat.card_eq_fintype_card,
    Fintype.card_bool], ?_⟩
  rw [hiveCount_eq_zero_iff]
  refine ⟨fun ⟨h, hb⟩ => ?_⟩
  obtain ⟨hTop, hW⟩ := topRow_and_rowWeight_toGTPattern_of_productBoundary hb
  have hb0 : h.boundary 0 = ![0, 0, 0] := by rw [hb, productBoundary_zero]
  have hrem := hb0 ▸ gtRemainingRhombus_toGTPattern h
  have hr0 := hrem 0 0 le_rfl (by decide)
  have hr1 := hrem 0 1 (Nat.zero_le 1) (by decide)
  have hp03 : h.toGTPattern 0 3 = 1 := by simpa [GTPattern.topRow_apply] using congrFun hTop 0
  have hp01 : h.toGTPattern 0 1 = 0 := by
    simpa [GTPattern.rowWeight_apply, GTPattern.rowSum_def] using congrFun hW 0
  simp [hp03, hp01] at hr0 hr1
  omega

end LowRankAndExamples

end TauCeti.Hive
