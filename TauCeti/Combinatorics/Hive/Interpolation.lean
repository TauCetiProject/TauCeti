/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Basic
public import TauCeti.Combinatorics.Hive.UnitTriangle
public import TauCeti.Topology.PL.Map
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Simplicial hive interpolation and zero-sum triangle gradients

Given `f : Vertex n → ℝ` on the size-`n` triangular lattice, simplicial interpolation on each of
the `n²` unit equilateral triangles (`TauCeti.Hive.UnitTriangle n`) extends `f` to a continuous
piecewise-affine function `interpolate f` on `barycentricSimplex n` (and via `planarInterpolate f`
to the Euclidean triangle `planarSimplex n ⊆ ℝ²`).

On each unit triangle `T`, `interpolate f` agrees with the continuous affine map
`triangleAffine f T = ∑ i, f (T.vertex i) • T.weight i`. Its directional derivatives along the
three clockwise perimeter directions `(-1, 1, 0)`, `(0, -1, 1)`, `(1, 0, -1)` form the zero-sum
triple `triangleGradient f T`, defined combinatorially over any additive abelian group so that `ℤ`,
`ℚ`, and `ℝ` share a single gradient API. Across the shared edge of any downward unit triangle
`down s` opposite `(down s).vertex i` and its upward neighbour `adjacentUp s i`, the
`(i + 1)`-coordinate of `triangleGradient` is constant while the `i`-th coordinate jumps by the
unit-rhombus slack.

## Main definitions

* `TauCeti.Hive.triangleGradient`: zero-sum triple of edge slopes of a unit triangle over any
  `AddCommGroup`.
* `TauCeti.Hive.triangleAffine`, `TauCeti.Hive.interpolate`, `TauCeti.Hive.planarInterpolate`:
  simplicial affine pieces and simplicial extensions (continuous and piecewise affine on
  `barycentricSimplex n` and `planarSimplex n`, respectively).

## Main results

* `TauCeti.Hive.triangleGradient_adjacentUp_add_one`,
  `TauCeti.Hive.triangleGradient_adjacentUp_sub_down_self`,
  `TauCeti.Hive.triangleGradient_up_edgePoint`, `TauCeti.Hive.isRhombusConcave_iff_adjacent`.
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

/-! ### Zero-sum triangle gradients and adjacent-rhombus concavity -/

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
  have h11 : (1 : Fin 3) + 1 = 2 := rfl; have h21 : (2 : Fin 3) + 1 = 0 := rfl
  cases T <;> simp only [Fin.sum_univ_three, triangleGradient_up, triangleGradient_down, zero_add,
    h11, h21] <;> abel

@[simp] theorem triangleGradient_zero {n : ℕ} {R : Type*} [AddCommGroup R] (T : UnitTriangle n)
    (s : Fin 3) : triangleGradient (0 : Vertex n → R) T s = 0 := by cases T <;> simp
theorem triangleGradient_add {n : ℕ} {R : Type*} [AddCommGroup R] (f g : Vertex n → R)
    (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (f + g) T s = triangleGradient f T s + triangleGradient g T s := by
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, Pi.add_apply] <;> abel
theorem triangleGradient_smul {n : ℕ} {S R : Type*} [Semiring S] [AddCommGroup R] [Module S R]
    (c : S) (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (c • f) T s = c • triangleGradient f T s := by cases T <;> simp [smul_sub]
@[simp] theorem triangleGradient_adjacentUp {m : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i j : Fin 3) :
    triangleGradient f (adjacentUp s i) j =
      f ((adjacentUp s i).vertex (j + 1)) - f ((adjacentUp s i).vertex j) := by
  rw [adjacentUp_def, triangleGradient_up, ← adjacentUp_def]

/-- Across the shared edge of `down s` and `adjacentUp s i` opposite `(down s).vertex i`, the
`(i + 1)`-coordinate of `triangleGradient` is constant. -/
theorem triangleGradient_adjacentUp_add_one {m : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i : Fin 3) :
    triangleGradient f (adjacentUp s i) (i + 1) =
      triangleGradient f (UnitTriangle.down s) (i + 1) := by
  have hi : i + 1 + 1 = i + 2 := by fin_cases i <;> rfl
  rw [triangleGradient_adjacentUp, triangleGradient_down, hi,
    adjacentUp_vertex_add_two, adjacentUp_vertex_add_one]

/-- Across the shared edge of `down s` and `adjacentUp s i` opposite `(down s).vertex i`, the
`i`-th coordinate of `triangleGradient` jumps by the unit-rhombus slack. -/
theorem triangleGradient_adjacentUp_sub_down_self {m : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i : Fin 3) :
    triangleGradient f (adjacentUp s i) i - triangleGradient f (UnitTriangle.down s) i =
      rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  rw [triangleGradient_adjacentUp, triangleGradient_down, rhombusSlack_def,
    adjacentUp_vertex_add_one]; abel

/-- Across the shared edge of `down s` and `adjacentUp s i` opposite `(down s).vertex i`, the
`(i + 2)`-th coordinate of `triangleGradient` jumps by minus the unit-rhombus slack. -/
theorem triangleGradient_adjacentUp_sub_down_add_two {m : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i : Fin 3) :
    triangleGradient f (adjacentUp s i) (i + 2) -
        triangleGradient f (UnitTriangle.down s) (i + 2) =
      -rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  have hi : i + 2 + 1 = i := by fin_cases i <;> rfl
  rw [triangleGradient_adjacentUp, triangleGradient_down, hi, rhombusSlack_def,
    adjacentUp_vertex_add_two]; abel

/-- At size `m + 2`, rhombus concavity over any ordered additive abelian group is completely
determined by the unit rhombi `isRhombus_adjacent s i` across shared interior unit edges. -/
theorem isRhombusConcave_iff_adjacent {m : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (f : Vertex (m + 2) → R) :
    IsRhombusConcave f ↔ ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  rw [isRhombusConcave_iff_rhombusSlack_nonneg]
  refine ⟨fun hf s i => hf (isRhombus_adjacent s i), fun hadj a b c d hr => ?_⟩
  obtain ⟨s, i, hac, hbd⟩ := hr.exists_adjacentUp
  have h1 : f a + f c =
      f ((UnitTriangle.down s).vertex (i + 2)) + f ((UnitTriangle.down s).vertex (i + 1)) := by
    rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [rfl; exact add_comm _ _]
  have h2 : f b + f d =
      f ((adjacentUp s i).vertex i) + f ((UnitTriangle.down s).vertex i) := by
    rcases hbd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [rfl; exact add_comm _ _]
  rw [rhombusSlack_def, h1, h2, ← rhombusSlack_def]; exact hadj s i

/-- Along side `s` of the perimeter, the `s`-th coordinate of `triangleGradient f` on the upward
perimeter triangle `up (edgePoint m s i)` equals `boundaryLinear ℤ (m + 1) R f s i`. -/
theorem triangleGradient_up_edgePoint {m : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex (m + 1) → R) (s : Fin 3) (i : Fin (m + 1)) :
    triangleGradient f (UnitTriangle.up (Vertex.edgePoint m s i)) s =
      boundaryLinear ℤ (m + 1) R f s i := by
  have hi := i.isLt
  fin_cases s <;> rw [triangleGradient_up, boundaryLinear_apply] <;> congr 2 <;> ext <;> simp
  all_goals omega

/-- At size `1`, the zero-sum gradient of the unique unit triangle equals the clockwise boundary
`(λ₁, μ₁, ν₁)` of `f`. -/
theorem triangleGradient_up_cornerA_zero {R : Type*} [AddCommGroup R]
    (f : Vertex 1 → R) (s : Fin 3) :
    triangleGradient f (UnitTriangle.up (Vertex.cornerA 0)) s = boundaryLinear ℤ 1 R f s 0 := by
  rw [Subsingleton.elim (Vertex.cornerA 0) (Vertex.edgePoint 0 s 0), triangleGradient_up_edgePoint]

/-! ### Simplicial affine pieces and continuous piecewise-affine interpolation -/

/-- Continuous affine extension of `f : Vertex n → ℝ` on a unit triangle `T : UnitTriangle n`. -/
noncomputable def triangleAffine {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n) :
    (Fin 3 → ℝ) →ᴬ[ℝ] ℝ :=
  f (T.vertex 0) • T.weight 0 + f (T.vertex 1) • T.weight 1 + f (T.vertex 2) • T.weight 2

theorem triangleAffine_apply {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine f T x = ∑ i : Fin 3, f (T.vertex i) * T.weight i x := by
  simp [triangleAffine, Fin.sum_univ_three, add_assoc]
@[simp] theorem triangleAffine_vertex {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n)
    (i : Fin 3) : triangleAffine f T (T.vertex i).barycentric = f (T.vertex i) := by
  rw [triangleAffine_apply]; fin_cases i <;> simp

/-- The `s`-th clockwise perimeter unit-step vector in `Fin 3 → ℝ`: `(-1, 1, 0)`, `(0, -1, 1)`,
`(1, 0, -1)`. -/
def unitStepVec : Fin 3 → (Fin 3 → ℝ)
  | ⟨0, _⟩ => ![-1, 1, 0] | ⟨1, _⟩ => ![0, -1, 1] | ⟨2, _⟩ => ![1, 0, -1]

@[simp] theorem unitStepVec_apply (s k : Fin 3) :
    unitStepVec s k = (if k = s + 1 then 1 else 0) - (if k = s then 1 else 0) := by
  fin_cases s <;> fin_cases k <;> simp [unitStepVec]
theorem sum_unitStepVec (s : Fin 3) : ∑ i : Fin 3, unitStepVec s i = 0 := by simp

/-- The directional derivative of `triangleAffine f T` along `unitStepVec s` equals the
combinatorial edge slope `triangleGradient f T s`. -/
@[simp] theorem triangleAffine_contLinear_unitStepVec {n : ℕ} (f : Vertex n → ℝ)
    (T : UnitTriangle n) (s : Fin 3) :
    (triangleAffine f T).contLinear (unitStepVec s) = triangleGradient f T s := by
  cases T <;> fin_cases s <;> simp [triangleAffine] <;> ring

/-- `triangleAffine f T` preserves three-point affine combinations with unit weight sum. -/
theorem triangleAffine_combo {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n)
    {w : Fin 3 → ℝ} (hw : ∑ i, w i = 1) (v : Fin 3 → Fin 3 → ℝ) :
    triangleAffine f T (∑ i, w i • v i) = ∑ i, w i * triangleAffine f T (v i) := by
  rw [← Finset.univ.affineCombination_eq_linear_combination v w hw,
    ← ContinuousAffineMap.coe_toAffineMap, Finset.univ.map_affineCombination v w hw,
    Finset.univ.affineCombination_eq_linear_combination _ w hw]
  simp [smul_eq_mul]

/-- Two unit triangles whose cells both contain `x` assign the same affine value at `x`. -/
theorem triangleAffine_eq_of_mem_cell {n : ℕ} (f : Vertex n → ℝ) {T₁ T₂ : UnitTriangle n}
    {x : Fin 3 → ℝ} (hx₁ : x ∈ T₁.cell) (hx₂ : x ∈ T₂.cell) :
    triangleAffine f T₁ x = triangleAffine f T₂ x := by
  have hx_sum := (mem_barycentricSimplex_iff.mp (T₁.cell_subset_barycentricSimplex hx₁)).2
  conv_rhs => rw [← T₁.sum_weight_smul_vertex hx_sum]
  rw [triangleAffine_combo f T₂ (T₁.sum_weight hx_sum), triangleAffine_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_lt_of_le (T₁.weight_nonneg hx₁ i) with h0 | hpos
  · simp [← h0]
  · obtain ⟨j, hj⟩ := T₁.mem_range_vertex_of_weight_pos hx₁ hx₂ hpos
    rw [← hj, triangleAffine_vertex, mul_comm]

/-- Simplicial extension of `f : Vertex n → ℝ` to `Fin 3 → ℝ` that is continuous and piecewise
affine on `barycentricSimplex n`. On `barycentricSimplex n` it agrees with `triangleAffine f T` on
every cell `T.cell`; outside the union of cells (and for `n = 0`) it takes the fallback value
`f (cornerA n)`. -/
noncomputable def interpolate {n : ℕ} (f : Vertex n → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  open Classical in
  if h : ∃ T : UnitTriangle n, x ∈ T.cell then triangleAffine f h.choose x
  else f (Vertex.cornerA n)

theorem interpolate_eq_triangleAffine {n : ℕ} (f : Vertex n → ℝ) {T : UnitTriangle n}
    {x : Fin 3 → ℝ} (hx : x ∈ T.cell) : interpolate f x = triangleAffine f T x := by
  rw [interpolate]; split_ifs with hex
  · exact triangleAffine_eq_of_mem_cell f hex.choose_spec hx
  · exact (hex ⟨T, hx⟩).elim

/-- Outside `barycentricSimplex n`, `interpolate f` takes the fallback value `f (cornerA n)`. -/
theorem interpolate_of_notMem_barycentricSimplex {n : ℕ} (f : Vertex n → ℝ) {x : Fin 3 → ℝ}
    (hx : x ∉ barycentricSimplex n) : interpolate f x = f (Vertex.cornerA n) := by
  rw [interpolate]; split_ifs with h <;>
    [exact (hx (h.choose.cell_subset_barycentricSimplex h.choose_spec)).elim; rfl]
@[simp] theorem interpolate_zero_rank (f : Vertex 0 → ℝ) (x : Fin 3 → ℝ) :
    interpolate f x = f (Vertex.cornerA 0) := by simp [interpolate]

/-- `interpolate f` extends `f` from the lattice vertices `Vertex n` via `Vertex.barycentric`. -/
@[simp] theorem interpolate_barycentric {n : ℕ} (f : Vertex n → ℝ) (p : Vertex n) :
    interpolate f p.barycentric = f p := by
  rcases n with _ | m
  · rw [interpolate_zero_rank, Subsingleton.elim p (Vertex.cornerA 0)]
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex m).symm ▸
      barycentric_mem_barycentricSimplex p)
    obtain ⟨i, rfl⟩ := UnitTriangle.mem_range_vertex_of_barycentric_mem_cell hT
    rw [interpolate_eq_triangleAffine f hT, triangleAffine_vertex]

/-- Along any unit lattice edge `(a, c)`, `interpolate f` is affine on `[0, 1]`. -/
theorem interpolate_lineMap_of_isUnitEdge {n : ℕ} (f : Vertex n → ℝ) {a c : Vertex n}
    (h : IsUnitEdge a c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    interpolate f (AffineMap.lineMap a.barycentric c.barycentric t) = (1 - t) * f a + t * f c := by
  obtain ⟨T, ha, hc⟩ := exists_cell_of_isUnitEdge h
  obtain ⟨ia, rfl⟩ := UnitTriangle.mem_range_vertex_of_barycentric_mem_cell ha
  obtain ⟨ic, rfl⟩ := UnitTriangle.mem_range_vertex_of_barycentric_mem_cell hc
  rw [interpolate_eq_triangleAffine f (T.convex_cell.lineMap_mem ha hc ht),
    (triangleAffine f T).apply_lineMap, triangleAffine_vertex, triangleAffine_vertex,
    AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]

/-- `interpolate f` is piecewise affine on `barycentricSimplex n` (outside which it uses the
constant fallback `f (cornerA n)`). -/
theorem isPiecewiseAffineOn_interpolate {n : ℕ} (f : Vertex n → ℝ) :
    IsPiecewiseAffineOn (interpolate f) (barycentricSimplex n) := by
  rcases n with _ | m
  · exact (isPiecewiseAffineOn_continuousAffineMap
      (ContinuousAffineMap.const ℝ _ (f (Vertex.cornerA 0))) _).congr fun _ _ => by simp
  · exact isPiecewiseAffineOn_of_finite (C := UnitTriangle.cell) (A := triangleAffine f)
      (fun T => T.isConvexPolyhedron_cell) (by rw [UnitTriangle.iUnion_cell_eq_barycentricSimplex])
      fun _ _ hx => interpolate_eq_triangleAffine f hx.2

/-- `interpolate f` is piecewise linear (`IsPLOn`) on `barycentricSimplex n`. -/
theorem isPLOn_interpolate {n : ℕ} (f : Vertex n → ℝ) :
    IsPLOn (interpolate f) (barycentricSimplex n) := (isPiecewiseAffineOn_interpolate f).isPLOn

/-- `interpolate f` is continuous on `barycentricSimplex n` (outside which it uses the constant
fallback `f (cornerA n)`). -/
theorem continuousOn_interpolate {n : ℕ} (f : Vertex n → ℝ) :
    ContinuousOn (interpolate f) (barycentricSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).continuousOn

theorem interpolate_add {n : ℕ} (f g : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate (f + g) x = interpolate f x + interpolate g x := by
  rw [interpolate, interpolate, interpolate]; split_ifs with h
  · simp only [triangleAffine_apply, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => add_mul _ _ _
  · rfl
theorem interpolate_smul {n : ℕ} (c : ℝ) (f : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate (c • f) x = c * interpolate f x := by
  rw [interpolate, interpolate]; split_ifs with h
  · simp only [triangleAffine_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
  · rfl
@[simp] theorem interpolate_zero {n : ℕ} (x : Fin 3 → ℝ) :
    interpolate (0 : Vertex n → ℝ) x = 0 := by simpa using interpolate_smul 0 (0 : Vertex n → ℝ) x
@[simp] theorem interpolate_const {n : ℕ} (c : ℝ) (x : Fin 3 → ℝ) :
    interpolate (fun _ : Vertex n => c) x = c := by
  rw [interpolate]; split_ifs with h
  · have hs := h.choose.cell_subset_barycentricSimplex h.choose_spec
    rw [triangleAffine_apply, ← Finset.mul_sum,
      h.choose.sum_weight (mem_barycentricSimplex_iff.mp hs).2, mul_one]
  · rfl

theorem interpolate_barycentricLinear {n : ℕ} (c₀ α β γ : ℝ) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex n) :
    interpolate (barycentricLinear (n := n) c₀ α β γ) x = c₀ + x 0 * α + x 1 * β + x 2 * γ := by
  rcases n with _ | m
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx; subst hx; simp
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex m).symm ▸ hx)
    rw [interpolate_eq_triangleAffine _ hT, triangleAffine_apply]
    have hxs := (mem_barycentricSimplex_iff.mp hx).2
    have hsw := T.sum_weight hxs; have hcomb := T.sum_weight_smul_vertex hxs
    have hc0 := congrFun hcomb 0; have hc1 := congrFun hcomb 1; have hc2 := congrFun hcomb 2
    simp only [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Vertex.barycentric_apply, Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two,
      barycentricLinear_apply, nsmul_eq_mul] at hsw hc0 hc1 hc2 ⊢
    linear_combination c₀ * hsw + α * hc0 + β * hc1 + γ * hc2

theorem interpolate_add_barycentricLinear {n : ℕ} (f : Vertex n → ℝ) (c₀ α β γ : ℝ)
    {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex n) :
    interpolate (f + barycentricLinear (n := n) c₀ α β γ) x =
      interpolate f x + (c₀ + x 0 * α + x 1 * β + x 2 * γ) := by
  rw [interpolate_add, interpolate_barycentricLinear _ _ _ _ hx]

/-- Compatibility of `interpolate` with lattice translation by `p : Vertex m`. -/
theorem interpolate_comp_add {m k : ℕ} (f : Vertex (m + k) → ℝ) (p : Vertex m) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex k) :
    interpolate (fun q : Vertex k => f (p.add q)) x = interpolate f (p.barycentric + x) := by
  rcases k with _ | k'
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx; subst hx; simp
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex k').symm ▸ hx)
    have hTp : p.barycentric + x ∈ (T.addLeft p).cell := UnitTriangle.mem_cell_iff.mpr
      ⟨add_mem_barycentricSimplex (barycentric_mem_barycentricSimplex p) hx, fun i => by
        rw [UnitTriangle.weight_addLeft_apply]; exact T.weight_nonneg hT i⟩
    rw [interpolate_eq_triangleAffine _ hT, interpolate_eq_triangleAffine _ hTp,
      triangleAffine_apply, triangleAffine_apply]
    simp [UnitTriangle.vertex_addLeft, UnitTriangle.weight_addLeft_apply]

/-- Compatibility of `interpolate` with restriction to `h.subtriangle p`. -/
theorem interpolate_subtriangle {m k : ℕ} (h : RealHive (m + k)) (p : Vertex m) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex k) :
    interpolate (h.subtriangle p) x =
      interpolate h (p.barycentric + x) - h (p.add (Vertex.cornerA k)) := by
  have hsub : ⇑(h.subtriangle p) =
      (fun q => h (p.add q)) + fun _ => -h (p.add (Vertex.cornerA k)) :=
    funext fun _ => by simp [sub_eq_add_neg]
  rw [hsub, interpolate_add, interpolate_comp_add h p hx, interpolate_const, sub_eq_add_neg]

/-- Simplicial extension of `f : Vertex n → ℝ` to `EuclideanSpace ℝ (Fin 2)` that is continuous and
piecewise affine on `planarSimplex n`, defined by pulling `interpolate f` back along
`planeInvAffine n`. -/
noncomputable def planarInterpolate {n : ℕ} (f : Vertex n → ℝ)
    (u : EuclideanSpace ℝ (Fin 2)) : ℝ := interpolate f (planeInvAffine n u)

theorem planarInterpolate_def {n : ℕ} (f : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate f u = interpolate f (planeInvAffine n u) := (rfl)
@[simp] theorem planarInterpolate_plane {n : ℕ} (f : Vertex n → ℝ) (p : Vertex n) :
    planarInterpolate f p.plane = f p := by simp [planarInterpolate]
theorem planarInterpolate_planeLinear {n : ℕ} (f : Vertex n → ℝ) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) : planarInterpolate f (planeLinear x) = interpolate f x := by
  rw [planarInterpolate, planeInvAffine_planeLinear hx]

/-- `planarInterpolate f` is piecewise affine on `planarSimplex n` (outside which it uses the
constant fallback `f (cornerA n)`). -/
theorem isPiecewiseAffineOn_planarInterpolate {n : ℕ} (f : Vertex n → ℝ) :
    IsPiecewiseAffineOn (planarInterpolate f) (planarSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).comp
    (isPiecewiseAffineOn_continuousAffineMap (planeInvAffine n) (planarSimplex n))
    fun _ hu => mem_planarSimplex_iff.mp hu

/-- `planarInterpolate f` is piecewise linear (`IsPLOn`) on `planarSimplex n`. -/
theorem isPLOn_planarInterpolate {n : ℕ} (f : Vertex n → ℝ) :
    IsPLOn (planarInterpolate f) (planarSimplex n) :=
  (isPiecewiseAffineOn_planarInterpolate f).isPLOn

/-- `planarInterpolate f` is continuous on `planarSimplex n`. -/
theorem continuousOn_planarInterpolate {n : ℕ} (f : Vertex n → ℝ) :
    ContinuousOn (planarInterpolate f) (planarSimplex n) :=
  (isPiecewiseAffineOn_planarInterpolate f).continuousOn

end TauCeti.Hive
