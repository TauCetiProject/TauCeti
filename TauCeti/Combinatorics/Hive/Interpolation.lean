/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Basic
public import TauCeti.Combinatorics.Hive.UnitTriangle
public import TauCeti.Topology.PL.Map
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Simplicial hive interpolation and zero-sum triangle gradients

Given a real-valued function `f : Vertex n → ℝ` on the size-`n` triangular lattice, simplicial
interpolation on each of the `n²` unit equilateral triangles (`TauCeti.Hive.UnitTriangle n`)
extends `f` to a continuous piecewise-affine function `interpolate f` on the continuous barycentric
simplex `barycentricSimplex n` (and via `planarInterpolate f` to the Euclidean triangle
`planarSimplex n ⊆ ℝ²`).

On each unit triangle `T`, `interpolate f` agrees with the continuous affine map
`triangleAffine f T = ∑ i, f (T.vertex i) • T.weight i`. Its directional derivatives along the
three clockwise perimeter directions `(-1, 1, 0)`, `(0, -1, 1)`, `(1, 0, -1)` form the zero-sum
triple `triangleGradient f T`, defined combinatorially over any additive abelian group so that
`ℤ`, `ℚ`, and `ℝ` share a single gradient API. Across the `i`-th edge of any downward unit
triangle `down s` and its upward neighbour `adjacentUp s i`, the `(i + 1)`-coordinate of
`triangleGradient` is constant while the `i`-th coordinate jumps by the unit-rhombus slack.

## Main definitions

* `TauCeti.Hive.adjacentUp`, `TauCeti.Hive.adjacentCell`: upward neighbour across side `i` of a
  downward unit triangle and their convex union rhombus cell.
* `TauCeti.Hive.triangleGradient`: zero-sum triple of edge slopes of a unit triangle over any
  `AddCommGroup`.
* `TauCeti.Hive.triangleAffine`, `TauCeti.Hive.interpolate`, `TauCeti.Hive.planarInterpolate`:
  simplicial affine pieces and continuous piecewise-affine interpolation in barycentric and planar
  coordinates.

## Main results

* `TauCeti.Hive.triangleGradient_adjacentUp_add_one`,
  `TauCeti.Hive.triangleGradient_adjacentUp_sub_down_self`: edge-constant coordinate and slack jump
  of `triangleGradient` across shared edges.
* `TauCeti.Hive.triangleAffine_contLinear_unitStepVec`: directional derivatives of `triangleAffine`
  along clockwise unit-step vectors equal `triangleGradient`.
* `TauCeti.Hive.isPiecewiseAffineOn_interpolate`, `TauCeti.Hive.continuousOn_interpolate`,
  `TauCeti.Hive.isPiecewiseAffineOn_planarInterpolate`.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §2 and
  Appendix 2, Proposition 4.
-/

public section

open Set
open scoped BigOperators

namespace TauCeti.Hive

/-! ### Adjacent unit triangles, interior unit rhombi, and zero-sum triangle gradients -/

/-- The upward unit triangle sharing the `i`-th edge of the downward triangle `down s`. -/
def adjacentUp {m : ℕ} (s : Vertex m) (i : Fin 3) : UnitTriangle (m + 2) :=
  UnitTriangle.up (s.add (unitCorner i))

@[simp] theorem weight_adjacentUp_apply {m : ℕ} (s : Vertex m) (i j : Fin 3) (x : Fin 3 → ℝ) :
    (adjacentUp s i).weight j x = x j - ((s.coord j : ℝ) + if i = j then 1 else 0) := by
  simp [adjacentUp]

theorem adjacentUp_vertex_add_one {m : ℕ} (s : Vertex m) (i : Fin 3) :
    (adjacentUp s i).vertex (i + 1) = (UnitTriangle.down s).vertex (i + 2) :=
  Vertex.ext_coord fun j => by
    rw [adjacentUp, UnitTriangle.vertex_coord_up, UnitTriangle.vertex_coord_down, Vertex.coord_add]
    fin_cases i <;> fin_cases j <;> simp

theorem adjacentUp_vertex_add_two {m : ℕ} (s : Vertex m) (i : Fin 3) :
    (adjacentUp s i).vertex (i + 2) = (UnitTriangle.down s).vertex (i + 1) :=
  Vertex.ext_coord fun j => by
    rw [adjacentUp, UnitTriangle.vertex_coord_up, UnitTriangle.vertex_coord_down, Vertex.coord_add]
    fin_cases i <;> fin_cases j <;> simp

/-- The upward triangle `adjacentUp s i` and the downward triangle `down s` form a unit rhombus
with obtuse corners on their shared edge and acute corners `(adjacentUp s i).vertex i` and
`(down s).vertex i`. -/
theorem isRhombus_adjacent {m : ℕ} (s : Vertex m) (i : Fin 3) :
    IsRhombus ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
      ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  fin_cases i
  · convert isRhombus_at_cornerA.add s using 1 <;>
      exact Vertex.ext_coord fun j => by
        simp only [adjacentUp, UnitTriangle.vertex_coord_up, UnitTriangle.vertex_coord_down,
          Vertex.coord_add]
        fin_cases j <;> simp
  · convert isRhombus_at_cornerA.rotate.add s using 1 <;>
      exact Vertex.ext_coord fun j => by
        simp only [adjacentUp, UnitTriangle.vertex_coord_up, UnitTriangle.vertex_coord_down,
          Vertex.coord_add]
        fin_cases j <;> simp
  · convert isRhombus_at_cornerA.rotate.rotate.add s using 1 <;>
      exact Vertex.ext_coord fun j => by
        simp only [adjacentUp, UnitTriangle.vertex_coord_up, UnitTriangle.vertex_coord_down,
          Vertex.coord_add]
        fin_cases j <;> simp

/-- The union of the cells of `adjacentUp s i` and `down s`, a continuous unit rhombus inside
`barycentricSimplex (m + 2)`. -/
def adjacentCell {m : ℕ} (s : Vertex m) (i : Fin 3) : Set (Fin 3 → ℝ) :=
  (adjacentUp s i).cell ∪ (UnitTriangle.down s).cell

@[simp] theorem mem_adjacentCell_iff {m : ℕ} {s : Vertex m} {i : Fin 3} {x : Fin 3 → ℝ} :
    x ∈ adjacentCell s i ↔ x ∈ (adjacentUp s i).cell ∨ x ∈ (UnitTriangle.down s).cell := Iff.rfl

instance {m : ℕ} : Inhabited (UnitTriangle (m + 1)) := ⟨UnitTriangle.up (Vertex.cornerA m)⟩

/-- `adjacentCell s i` is cut out inside `barycentricSimplex (m + 2)` by bounding the two
coordinates other than `i` to `[s_{i+1}, s_{i+1} + 1]` and `[s_{i+2}, s_{i+2} + 1]`. -/
theorem adjacentCell_eq {m : ℕ} (s : Vertex m) (i : Fin 3) :
    adjacentCell s i =
      {x ∈ barycentricSimplex (m + 2) |
        (s.coord (i + 1) : ℝ) ≤ x (i + 1) ∧ x (i + 1) ≤ (s.coord (i + 1) : ℝ) + 1 ∧
        (s.coord (i + 2) : ℝ) ≤ x (i + 2) ∧ x (i + 2) ≤ (s.coord (i + 2) : ℝ) + 1} := by
  ext x
  simp only [adjacentCell, mem_union, UnitTriangle.mem_cell_iff, mem_ofPred_eq]
  have hs : (s.x : ℝ) + s.y + s.z = m := by exact_mod_cast s.sum_eq
  constructor
  · rintro (⟨hx, hw⟩ | ⟨hx, hw⟩)
    · have hsum : x 0 + x 1 + x 2 = (m : ℝ) + 2 := by
        simpa [Fin.sum_univ_three, add_assoc] using (mem_barycentricSimplex_iff.mp hx).2
      have h0 := hw 0; have h1 := hw 1; have h2 := hw 2
      simp only [adjacentUp, UnitTriangle.weight_up_apply, Vertex.coord_add] at h0 h1 h2
      refine ⟨hx, ?_, ?_, ?_, ?_⟩ <;>
        (fin_cases i <;> simp at h0 h1 h2 ⊢ <;> linarith [hs, hsum])
    · have hsum : x 0 + x 1 + x 2 = (m : ℝ) + 2 := by
        simpa [Fin.sum_univ_three, add_assoc] using (mem_barycentricSimplex_iff.mp hx).2
      have h0 := hw 0; have h1 := hw 1; have h2 := hw 2
      simp only [UnitTriangle.weight_down_apply] at h0 h1 h2
      refine ⟨hx, ?_, ?_, ?_, ?_⟩ <;>
        (fin_cases i <;> simp at h0 h1 h2 ⊢ <;> linarith [hs, hsum])
  · rintro ⟨hx, h1_lo, h1_hi, h2_lo, h2_hi⟩
    have hsum : x 0 + x 1 + x 2 = (m : ℝ) + 2 := by
      simpa [Fin.sum_univ_three, add_assoc] using (mem_barycentricSimplex_iff.mp hx).2
    rcases le_total ((s.coord i : ℝ) + 1) (x i) with hhi | hlo
    · left
      refine ⟨hx, fun k => ?_⟩
      simp only [adjacentUp, UnitTriangle.weight_up_apply, Vertex.coord_add]
      fin_cases i <;> fin_cases k <;>
        simp at h1_lo h1_hi h2_lo h2_hi hhi ⊢ <;> linarith [hs, hsum]
    · right
      refine ⟨hx, fun k => ?_⟩
      simp only [UnitTriangle.weight_down_apply]
      fin_cases i <;> fin_cases k <;>
        simp at h1_lo h1_hi h2_lo h2_hi hlo ⊢ <;> linarith [hs, hsum]

theorem isConvexPolyhedron_adjacentCell {m : ℕ} (s : Vertex m) (i : Fin 3) :
    IsConvexPolyhedron (adjacentCell s i) := by
  let c1 : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ (Fin 3 → ℝ) (s.coord (i + 1) : ℝ)
  let c2 : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ (Fin 3 → ℝ) (s.coord (i + 2) : ℝ)
  let one : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ (Fin 3 → ℝ) 1
  let g : Fin 4 → ((Fin 3 → ℝ) →ᴬ[ℝ] ℝ) :=
    ![c1 - coordAffine (i + 1), coordAffine (i + 1) - (c1 + one),
      c2 - coordAffine (i + 2), coordAffine (i + 2) - (c2 + one)]
  have heq : adjacentCell s i = barycentricSimplex (m + 2) ∩ {x | ∀ j, g j x ≤ 0} := by
    rw [adjacentCell_eq]
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, g,
      c1, c2, one, Matrix.cons_val_zero, Matrix.cons_val_succ, ContinuousAffineMap.sub_apply,
      ContinuousAffineMap.add_apply, coordAffine_apply, ContinuousAffineMap.coe_const,
      Function.const_apply]
    exact and_congr_right' ⟨fun ⟨_, _, _, _⟩ =>
        ⟨by linarith, by linarith, by linarith, by linarith⟩,
      fun ⟨_, _, _, _⟩ => ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  rw [heq]
  exact (isConvexPolyhedron_barycentricSimplex (m + 2)).inter (isConvexPolyhedron_setOf_forall g)

theorem convex_adjacentCell {m : ℕ} (s : Vertex m) (i : Fin 3) : Convex ℝ (adjacentCell s i) :=
  (isConvexPolyhedron_adjacentCell s i).convex

/-- The zero-sum triple of clockwise unit-step edge slopes of `f : Vertex n → R` on a unit triangle
`T : UnitTriangle n` along directions `A → B` (`s = 0`), `B → C` (`s = 1`), and `C → A` (`s = 2`).
-/
def triangleGradient {n : ℕ} {R : Type*} [AddCommGroup R] (f : Vertex n → R) :
    UnitTriangle n → Fin 3 → R
  | .up base, s => f ((UnitTriangle.up base).vertex (s + 1)) - f ((UnitTriangle.up base).vertex s)
  | .down base, s =>
      f ((UnitTriangle.down base).vertex s) - f ((UnitTriangle.down base).vertex (s + 1))

@[simp] theorem triangleGradient_up {m : ℕ} {R : Type*} [AddCommGroup R] (f : Vertex (m + 1) → R)
    (base : Vertex m) (s : Fin 3) :
    triangleGradient f (UnitTriangle.up base) s =
      f ((UnitTriangle.up base).vertex (s + 1)) - f ((UnitTriangle.up base).vertex s) := (rfl)

@[simp] theorem triangleGradient_down {m : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex (m + 2) → R) (base : Vertex m) (s : Fin 3) :
    triangleGradient f (UnitTriangle.down base) s =
      f ((UnitTriangle.down base).vertex s) - f ((UnitTriangle.down base).vertex (s + 1)) := (rfl)

@[simp] theorem sum_triangleGradient {n : ℕ} {R : Type*} [AddCommGroup R] (f : Vertex n → R)
    (T : UnitTriangle n) : ∑ s : Fin 3, triangleGradient f T s = 0 := by
  have h11 : (1 : Fin 3) + 1 = 2 := rfl
  have h21 : (2 : Fin 3) + 1 = 0 := rfl
  cases T <;>
    simp only [Fin.sum_univ_three, triangleGradient_up, triangleGradient_down, zero_add, h11,
      h21] <;> abel

@[simp] theorem triangleGradient_zero {n : ℕ} {R : Type*} [AddCommGroup R] (T : UnitTriangle n)
    (s : Fin 3) : triangleGradient (0 : Vertex n → R) T s = 0 := by
  cases T <;> simp

theorem triangleGradient_add {n : ℕ} {R : Type*} [AddCommGroup R] (f g : Vertex n → R)
    (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (f + g) T s = triangleGradient f T s + triangleGradient g T s := by
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, Pi.add_apply] <;> abel

theorem triangleGradient_smul {n : ℕ} {S R : Type*} [Semiring S] [AddCommGroup R] [Module S R]
    (c : S) (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (c • f) T s = c • triangleGradient f T s := by
  cases T <;> simp [smul_sub]

/-- Across the shared `i`-th edge of `down s` and `adjacentUp s i`, the `(i + 1)`-coordinate of
`triangleGradient` is constant. -/
theorem triangleGradient_adjacentUp_add_one {m : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i : Fin 3) :
    triangleGradient f (adjacentUp s i) (i + 1) =
      triangleGradient f (UnitTriangle.down s) (i + 1) := by
  have h12 : i + 1 + 1 = i + 2 := by fin_cases i <;> rfl
  have hup : triangleGradient f (adjacentUp s i) (i + 1) =
      f ((adjacentUp s i).vertex (i + 1 + 1)) - f ((adjacentUp s i).vertex (i + 1)) := rfl
  rw [hup, triangleGradient_down, h12, adjacentUp_vertex_add_two, adjacentUp_vertex_add_one]

/-- Across the shared `i`-th edge of `down s` and `adjacentUp s i`, the `i`-th coordinate of
`triangleGradient` jumps by the unit-rhombus slack. -/
theorem triangleGradient_adjacentUp_sub_down_self {m : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i : Fin 3) :
    triangleGradient f (adjacentUp s i) i - triangleGradient f (UnitTriangle.down s) i =
      rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  have hup : triangleGradient f (adjacentUp s i) i =
      f ((adjacentUp s i).vertex (i + 1)) - f ((adjacentUp s i).vertex i) := rfl
  rw [hup, triangleGradient_down, rhombusSlack_def, adjacentUp_vertex_add_one]
  abel

/-- Across the shared `i`-th edge of `down s` and `adjacentUp s i`, the `(i + 2)`-th coordinate of
`triangleGradient` jumps by minus the unit-rhombus slack. -/
theorem triangleGradient_adjacentUp_sub_down_add_two {m : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i : Fin 3) :
    triangleGradient f (adjacentUp s i) (i + 2) -
        triangleGradient f (UnitTriangle.down s) (i + 2) =
      -rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  have h21 : i + 2 + 1 = i := by fin_cases i <;> rfl
  have hup : triangleGradient f (adjacentUp s i) (i + 2) =
      f ((adjacentUp s i).vertex (i + 2 + 1)) - f ((adjacentUp s i).vertex (i + 2)) := rfl
  rw [hup, triangleGradient_down, h21, rhombusSlack_def, adjacentUp_vertex_add_two]
  abel

/-- At size `1`, the zero-sum gradient of the unique unit triangle equals the clockwise boundary
`(λ₁, μ₁, ν₁)` of the hive. -/
theorem triangleGradient_up_cornerA_zero {R : Type*} [AddCommGroup R] [PartialOrder R]
    (h : Hive 1 R) (s : Fin 3) :
    triangleGradient h (UnitTriangle.up (Vertex.cornerA 0)) s = h.boundary s 0 := by
  fin_cases s <;>
    · rw [triangleGradient_up, boundary_apply]
      congr 2 <;> ext <;> simp

/-! ### Simplicial affine pieces and continuous piecewise-affine interpolation -/

/-- The continuous affine extension of `f : Vertex n → ℝ` on a unit triangle `T : UnitTriangle n`.
-/
noncomputable def triangleAffine {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n) :
    (Fin 3 → ℝ) →ᴬ[ℝ] ℝ :=
  f (T.vertex 0) • T.weight 0 + f (T.vertex 1) • T.weight 1 + f (T.vertex 2) • T.weight 2

theorem triangleAffine_apply {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine f T x = ∑ i : Fin 3, f (T.vertex i) * T.weight i x := by
  simp [triangleAffine, Fin.sum_univ_three, add_assoc]

@[simp] theorem triangleAffine_vertex {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n)
    (i : Fin 3) : triangleAffine f T (T.vertex i).barycentric = f (T.vertex i) := by
  rw [triangleAffine_apply]
  fin_cases i <;> simp

/-- The `s`-th clockwise perimeter unit-step vector in `Fin 3 → ℝ`: `(-1, 1, 0)`, `(0, -1, 1)`,
`(1, 0, -1)`. -/
def unitStepVec : Fin 3 → (Fin 3 → ℝ)
  | ⟨0, _⟩ => ![-1, 1, 0]
  | ⟨1, _⟩ => ![0, -1, 1]
  | ⟨2, _⟩ => ![1, 0, -1]

@[simp] theorem sum_unitStepVec (s : Fin 3) : ∑ i : Fin 3, unitStepVec s i = 0 := by
  fin_cases s <;> simp [unitStepVec, Fin.sum_univ_three]

/-- The directional derivative of `triangleAffine f T` along `unitStepVec s` equals the
combinatorial edge slope `triangleGradient f T s`. -/
@[simp] theorem triangleAffine_contLinear_unitStepVec {n : ℕ} (f : Vertex n → ℝ)
    (T : UnitTriangle n) (s : Fin 3) :
    (triangleAffine f T).contLinear (unitStepVec s) = triangleGradient f T s := by
  cases T <;> fin_cases s <;> simp [triangleAffine, unitStepVec] <;> ring

/-- `triangleAffine f T` preserves three-point affine combinations with unit weight sum. -/
theorem triangleAffine_combo {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n)
    {w : Fin 3 → ℝ} (hw : ∑ i, w i = 1) (v : Fin 3 → Fin 3 → ℝ) :
    triangleAffine f T (∑ i, w i • v i) = ∑ i, w i * triangleAffine f T (v i) := by
  have hw' : w 0 + w 1 + w 2 = 1 := by simpa [Fin.sum_univ_three, add_assoc] using hw
  have hweight (j : Fin 3) :
      T.weight j (∑ i, w i • v i) = ∑ i, w i * T.weight j (v i) := by
    cases T with
    | up base =>
      simp only [UnitTriangle.weight_up_apply, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      linear_combination (base.coord j : ℝ) * hw'
    | down base =>
      simp only [UnitTriangle.weight_down_apply, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      linear_combination -((base.coord j : ℝ) + 1) * hw'
  simp_rw [triangleAffine_apply, hweight]
  simp only [Fin.sum_univ_three]
  ring

/-- Two unit triangles whose cells both contain `x` assign the same affine value at `x`. -/
theorem triangleAffine_eq_of_mem_cell {n : ℕ} (f : Vertex n → ℝ) {T₁ T₂ : UnitTriangle n}
    {x : Fin 3 → ℝ} (hx₁ : x ∈ T₁.cell) (hx₂ : x ∈ T₂.cell) :
    triangleAffine f T₁ x = triangleAffine f T₂ x := by
  have hx_sum : ∑ i, x i = (n : ℝ) :=
    (mem_barycentricSimplex_iff.mp (T₁.cell_subset_barycentricSimplex hx₁)).2
  conv_rhs => rw [← T₁.sum_weight_smul_vertex hx_sum]
  rw [triangleAffine_combo f T₂ (T₁.sum_weight hx_sum), triangleAffine_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_lt_of_le (T₁.weight_nonneg hx₁ i) with h0 | hpos
  · simp [← h0]
  · obtain ⟨j, hj⟩ := T₁.mem_range_vertex_of_weight_pos hx₁ hx₂ hpos
    rw [← hj, triangleAffine_vertex]
    ring

/-- Continuous piecewise-affine simplicial extension of `f : Vertex n → ℝ` to `Fin 3 → ℝ`.
On `barycentricSimplex n` it agrees with `triangleAffine f T` on every cell `T.cell`; outside the
union of cells (and for `n = 0`) it takes the fallback value `f (cornerA n)`. -/
noncomputable def interpolate {n : ℕ} (f : Vertex n → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  open Classical in
  if h : ∃ T : UnitTriangle n, x ∈ T.cell then triangleAffine f h.choose x
  else f (Vertex.cornerA n)

theorem interpolate_eq_triangleAffine {n : ℕ} (f : Vertex n → ℝ) {T : UnitTriangle n}
    {x : Fin 3 → ℝ} (hx : x ∈ T.cell) :
    interpolate f x = triangleAffine f T x := by
  rw [interpolate]
  split_ifs with hex
  · exact triangleAffine_eq_of_mem_cell f hex.choose_spec hx
  · exact False.elim (hex ⟨T, hx⟩)

@[simp] theorem interpolate_zero_rank (f : Vertex 0 → ℝ) (x : Fin 3 → ℝ) :
    interpolate f x = f (Vertex.cornerA 0) := by
  simp [interpolate]

/-- `interpolate f` extends `f` from the lattice vertices `Vertex n` via `Vertex.barycentric`. -/
@[simp] theorem interpolate_barycentric {n : ℕ} (f : Vertex n → ℝ) (p : Vertex n) :
    interpolate f p.barycentric = f p := by
  rcases n with _ | m
  · rw [interpolate_zero_rank, Subsingleton.elim p (Vertex.cornerA 0)]
  · have hmem : p.barycentric ∈ ⋃ T : UnitTriangle (m + 1), T.cell := by
      rw [UnitTriangle.iUnion_cell_eq_barycentricSimplex]
      exact barycentric_mem_barycentricSimplex p
    obtain ⟨T, hT⟩ := mem_iUnion.mp hmem
    obtain ⟨i, rfl⟩ := UnitTriangle.mem_range_vertex_of_barycentric_mem_cell hT
    rw [interpolate_eq_triangleAffine f hT, triangleAffine_vertex]

/-- Along any unit lattice edge `(a, c)`, `interpolate f` is affine on `[0, 1]`. -/
theorem interpolate_lineMap_of_isUnitEdge {n : ℕ} (f : Vertex n → ℝ) {a c : Vertex n}
    (h : IsUnitEdge a c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    interpolate f (AffineMap.lineMap a.barycentric c.barycentric t) =
      (1 - t) * f a + t * f c := by
  obtain ⟨T, ha, hc⟩ := exists_cell_of_isUnitEdge h
  have hmem : AffineMap.lineMap a.barycentric c.barycentric t ∈ T.cell := by
    rw [AffineMap.lineMap_apply_module]
    exact T.convex_cell ha hc (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  rw [interpolate_eq_triangleAffine f hmem, AffineMap.lineMap_apply_module]
  have hsum : ∑ i : Fin 3, (![1 - t, t, 0] : Fin 3 → ℝ) i = 1 := by
    simp [Fin.sum_univ_three]
  have hpt : (1 - t) • a.barycentric + t • c.barycentric =
      ∑ i : Fin 3, (![1 - t, t, 0] : Fin 3 → ℝ) i •
        (![a.barycentric, c.barycentric, 0] : Fin 3 → Fin 3 → ℝ) i := by
    ext k; simp [Fin.sum_univ_three]
  rw [hpt, triangleAffine_combo f T hsum]
  obtain ⟨ia, rfl⟩ := UnitTriangle.mem_range_vertex_of_barycentric_mem_cell ha
  obtain ⟨ic, rfl⟩ := UnitTriangle.mem_range_vertex_of_barycentric_mem_cell hc
  simp [Fin.sum_univ_three]

/-- `interpolate f` is piecewise affine on `barycentricSimplex n`. -/
theorem isPiecewiseAffineOn_interpolate {n : ℕ} (f : Vertex n → ℝ) :
    IsPiecewiseAffineOn (interpolate f) (barycentricSimplex n) := by
  rcases n with _ | m
  · refine (isPiecewiseAffineOn_continuousAffineMap
      (ContinuousAffineMap.const ℝ (Fin 3 → ℝ) (f (Vertex.cornerA 0)))
      (barycentricSimplex 0)).congr fun x _ => ?_
    simp
  · refine isPiecewiseAffineOn_of_finite (ι := UnitTriangle (m + 1))
      (C := UnitTriangle.cell) (A := triangleAffine f)
      (fun T => T.isConvexPolyhedron_cell)
      (by rw [UnitTriangle.iUnion_cell_eq_barycentricSimplex]) fun T x hx => ?_
    exact interpolate_eq_triangleAffine f hx.2

theorem isPLOn_interpolate {n : ℕ} (f : Vertex n → ℝ) :
    IsPLOn (interpolate f) (barycentricSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).isPLOn

theorem continuousOn_interpolate {n : ℕ} (f : Vertex n → ℝ) :
    ContinuousOn (interpolate f) (barycentricSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).continuousOn

theorem interpolate_add {n : ℕ} (f g : Vertex n → ℝ) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex n) :
    interpolate (f + g) x = interpolate f x + interpolate g x := by
  rcases n with _ | m
  · simp
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex m).symm ▸ hx)
    simp only [interpolate_eq_triangleAffine _ hT, triangleAffine_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => add_mul _ _ _

theorem interpolate_smul {n : ℕ} (c : ℝ) (f : Vertex n → ℝ) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex n) :
    interpolate (c • f) x = c * interpolate f x := by
  rcases n with _ | m
  · simp
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex m).symm ▸ hx)
    simp only [interpolate_eq_triangleAffine _ hT, triangleAffine_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

theorem interpolate_barycentricLinear {n : ℕ} (c₀ α β γ : ℝ) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex n) :
    interpolate (barycentricLinear (n := n) c₀ α β γ) x =
      c₀ + x 0 * α + x 1 * β + x 2 * γ := by
  rcases n with _ | m
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx
    subst hx; simp
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex m).symm ▸ hx)
    have hx_sum : ∑ i, x i = ((m + 1 : ℕ) : ℝ) := (mem_barycentricSimplex_iff.mp hx).2
    rw [interpolate_eq_triangleAffine _ hT, triangleAffine_apply]
    have hsw := T.sum_weight hx_sum
    have hcomb := T.sum_weight_smul_vertex hx_sum
    have hc0 := congrFun hcomb 0; have hc1 := congrFun hcomb 1; have hc2 := congrFun hcomb 2
    simp only [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Vertex.barycentric_apply, Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two,
      barycentricLinear_apply, nsmul_eq_mul] at hsw hc0 hc1 hc2 ⊢
    linear_combination c₀ * hsw + α * hc0 + β * hc1 + γ * hc2

theorem interpolate_add_barycentricLinear {n : ℕ} (f : Vertex n → ℝ) (c₀ α β γ : ℝ)
    {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex n) :
    interpolate (f + barycentricLinear (n := n) c₀ α β γ) x =
      interpolate f x + (c₀ + x 0 * α + x 1 * β + x 2 * γ) := by
  rw [interpolate_add _ _ hx, interpolate_barycentricLinear _ _ _ _ hx]

/-- Compatibility of `interpolate` with restriction to a translated subtriangle `h.subtriangle p`.
-/
theorem interpolate_subtriangle {m k : ℕ} (h : RealHive (m + k)) (p : Vertex m) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex k) :
    interpolate (h.subtriangle p) x =
      interpolate h (p.barycentric + x) - h (p.add (Vertex.cornerA k)) := by
  rcases k with _ | k'
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx
    subst hx
    have hpA : p.add (Vertex.cornerA 0) = p := by ext <;> simp
    simp [hpA]
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex k').symm ▸ hx)
    have hTp : p.barycentric + x ∈ (T.addLeft p).cell :=
      (T.addLeft p).mem_cell_iff.mpr
        ⟨add_mem_barycentricSimplex (barycentric_mem_barycentricSimplex p) hx, fun i => by
          rw [UnitTriangle.weight_addLeft_apply]; exact T.weight_nonneg hT i⟩
    have hx_sum : ∑ i, x i = ((k' + 1 : ℕ) : ℝ) := (mem_barycentricSimplex_iff.mp hx).2
    rw [interpolate_eq_triangleAffine _ hT, interpolate_eq_triangleAffine _ hTp,
      triangleAffine_apply, triangleAffine_apply]
    have hsw := T.sum_weight hx_sum
    simp only [subtriangle_apply, UnitTriangle.vertex_addLeft, UnitTriangle.weight_addLeft_apply,
      sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsw, mul_one]

/-- Continuous piecewise-affine simplicial extension of `f : Vertex n → ℝ` in the Euclidean plane
`EuclideanSpace ℝ (Fin 2)`, defined by pulling `interpolate f` back along `planeInvAffine n`. -/
noncomputable def planarInterpolate {n : ℕ} (f : Vertex n → ℝ)
    (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  interpolate f (planeInvAffine n u)

theorem planarInterpolate_def {n : ℕ} (f : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate f u = interpolate f (planeInvAffine n u) := (rfl)

@[simp] theorem planarInterpolate_plane {n : ℕ} (f : Vertex n → ℝ) (p : Vertex n) :
    planarInterpolate f p.plane = f p := by
  simp [planarInterpolate]

theorem planarInterpolate_planeLinear {n : ℕ} (f : Vertex n → ℝ) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) :
    planarInterpolate f (planeLinear x) = interpolate f x := by
  rw [planarInterpolate, planeInvAffine_planeLinear hx]

theorem isPiecewiseAffineOn_planarInterpolate {n : ℕ} (f : Vertex n → ℝ) :
    IsPiecewiseAffineOn (planarInterpolate f) (planarSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).comp
    (isPiecewiseAffineOn_continuousAffineMap (planeInvAffine n) (planarSimplex n))
    fun _ hu => mem_planarSimplex_iff.mp hu

theorem isPLOn_planarInterpolate {n : ℕ} (f : Vertex n → ℝ) :
    IsPLOn (planarInterpolate f) (planarSimplex n) :=
  (isPiecewiseAffineOn_planarInterpolate f).isPLOn

theorem continuousOn_planarInterpolate {n : ℕ} (f : Vertex n → ℝ) :
    ContinuousOn (planarInterpolate f) (planarSimplex n) :=
  (isPiecewiseAffineOn_planarInterpolate f).continuousOn

end TauCeti.Hive
