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
import TauCeti.LinearAlgebra.AffineSpace.AffineMap

/-!
# Simplicial hive interpolation and zero-sum triangle gradients

Simplicial interpolation on the `n²` unit equilateral triangles (`TauCeti.Hive.UnitTriangle n`)
extends `f : Vertex n → ℝ` to a continuous piecewise-affine function `interpolate f` on
`barycentricSimplex n` (and via `planarInterpolate f` to `planarSimplex n ⊆ ℝ²`), agreeing on each
unit triangle `T` with `triangleAffine f T = ∑ i, f (T.vertex i) • T.weight i`. Its directional
derivatives along `(-1, 1, 0)`, `(0, -1, 1)`, `(1, 0, -1)` form the zero-sum triple
`triangleGradient f T` over any additive abelian group; across the shared edge of `down s` and
`adjacentUp s i`, the `(i + 1)`-coordinate is constant while the `i`-th jumps by the rhombus slack.

## Main definitions and results

* `TauCeti.Hive.triangleGradient`, `TauCeti.Hive.triangleAffine`, `TauCeti.Hive.interpolate`,
  `TauCeti.Hive.planarInterpolate`.
* `TauCeti.Hive.triangleGradient_adjacentUp_add_one`,
  `TauCeti.Hive.triangleGradient_adjacentUp_sub_down_self`,
  `TauCeti.Hive.triangleGradient_up_edgePoint`, `TauCeti.Hive.isRhombusConcave_iff_adjacent`.
* `TauCeti.Hive.triangleAffine_contLinear_unitStepVec`,
  `TauCeti.Hive.isPiecewiseAffineOn_interpolate`, `TauCeti.Hive.continuousOn_interpolate`,
  `TauCeti.Hive.isPiecewiseAffineOn_planarInterpolate`.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §2, App. 2.
-/

public section

open Set
open scoped BigOperators

namespace TauCeti.Hive

/-! ### Zero-sum triangle gradients and adjacent-rhombus concavity -/

/-- The zero-sum triple of clockwise unit-step edge slopes of `f : Vertex n → R` on a unit triangle
`T : UnitTriangle n` along `A → B` (`s = 0`), `B → C` (`s = 1`), and `C → A` (`s = 2`). -/
def triangleGradient {n : ℕ} {R : Type*} [AddCommGroup R] (f : Vertex n → R) :
    UnitTriangle n → Fin 3 → R
  | .up b, s => f ((UnitTriangle.up b).vertex (s + 1)) - f ((UnitTriangle.up b).vertex s)
  | .down b, s => f ((UnitTriangle.down b).vertex s) - f ((UnitTriangle.down b).vertex (s + 1))

@[simp] theorem triangleGradient_up {m : ℕ} {R : Type*} [AddCommGroup R] (f : Vertex (m + 1) → R)
    (b : Vertex m) (s : Fin 3) : triangleGradient f (UnitTriangle.up b) s =
      f ((UnitTriangle.up b).vertex (s + 1)) - f ((UnitTriangle.up b).vertex s) := (rfl)
@[simp] theorem triangleGradient_down {m : ℕ} {R : Type*} [AddCommGroup R] (f : Vertex (m + 2) → R)
    (b : Vertex m) (s : Fin 3) : triangleGradient f (UnitTriangle.down b) s =
      f ((UnitTriangle.down b).vertex s) - f ((UnitTriangle.down b).vertex (s + 1)) := (rfl)
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
theorem triangleGradient_neg {n : ℕ} {R : Type*} [AddCommGroup R] (f : Vertex n → R)
    (T : UnitTriangle n) (s : Fin 3) : triangleGradient (-f) T s = -triangleGradient f T s := by
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, Pi.neg_apply] <;> abel
theorem triangleGradient_sub {n : ℕ} {R : Type*} [AddCommGroup R] (f g : Vertex n → R)
    (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (f - g) T s = triangleGradient f T s - triangleGradient g T s := by
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, Pi.sub_apply] <;> abel
theorem triangleGradient_smul {n : ℕ} {S R : Type*} [Semiring S] [AddCommGroup R] [Module S R]
    (c : S) (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (c • f) T s = c • triangleGradient f T s := by cases T <;> simp [smul_sub]
@[simp] theorem triangleGradient_const {n : ℕ} {R : Type*} [AddCommGroup R] (c : R)
    (T : UnitTriangle n) (s : Fin 3) : triangleGradient (fun _ : Vertex n => c) T s = 0 := by
  cases T <;> simp
theorem triangleGradient_comp {n : ℕ} {R S F : Type*} [AddCommGroup R] [AddCommGroup S]
    [FunLike F R S] [AddMonoidHomClass F R S] (φ : F) (f : Vertex n → R) (T : UnitTriangle n)
    (s : Fin 3) : triangleGradient (φ ∘ f) T s = φ (triangleGradient f T s) := by cases T <;> simp
@[simp] theorem triangleGradient_map {n : ℕ} {R S : Type*} [AddCommGroup R] [PartialOrder R]
    [AddCommGroup S] [PartialOrder S] (φ : R →+o S) (h : Hive n R) (T : UnitTriangle n)
    (s : Fin 3) : triangleGradient (h.map φ) T s = φ (triangleGradient h T s) := by cases T <;> simp
@[simp] theorem triangleGradient_ofInt {n : ℕ} (R : Type*) [Ring R] [PartialOrder R]
    [IsOrderedRing R] (h : IntegerHive n) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (ofInt R h) T s = ((triangleGradient h T s : ℤ) : R) := by cases T <;> simp
theorem triangleGradient_barycentricLinear {n : ℕ} {R : Type*} [AddCommGroup R]
    (c₀ α β γ : R) (T : UnitTriangle n) :
    triangleGradient (barycentricLinear c₀ α β γ) T = ![β - α, γ - β, α - γ] := by
  have h {m : ℕ} (p q : Vertex m) :
      barycentricLinear c₀ α β γ p - barycentricLinear c₀ α β γ q =
        (p.x • α - q.x • α) + (p.y • β - q.y • β) + (p.z • γ - q.z • γ) := by
    simp only [barycentricLinear_apply]; abel
  ext s; cases T <;> fin_cases s <;>
    simp [-barycentricLinear_apply, h, add_nsmul, sub_eq_add_neg, add_comm]
@[simp] theorem triangleGradient_affine {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] (β γ : R) (T : UnitTriangle n) :
    triangleGradient (affine n β γ) T = ![β, γ - β, -γ] := by
  simpa [show (⇑(affine n β γ) : Vertex n → R) = barycentricLinear 0 0 β γ from
    funext fun p => by simp] using triangleGradient_barycentricLinear (0 : R) 0 β γ T
theorem triangleGradient_comp_add {m k : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex (m + k) → R) (p : Vertex m) (T : UnitTriangle k) (s : Fin 3) :
    triangleGradient (fun q => f (p.add q)) T s = triangleGradient f (T.addLeft p) s := by
  cases T <;> [rw [triangleGradient_up]; rw [triangleGradient_down]] <;>
    simp only [← UnitTriangle.vertex_addLeft, UnitTriangle.addLeft_up, UnitTriangle.addLeft_down,
      triangleGradient_up, triangleGradient_down]
@[simp] theorem triangleGradient_subtriangle {m k : ℕ} {R : Type*} [AddCommGroup R]
    [PartialOrder R] [IsOrderedAddMonoid R] (h : Hive (m + k) R) (p : Vertex m)
    (T : UnitTriangle k) (s : Fin 3) :
    triangleGradient (h.subtriangle p) T s = triangleGradient h (T.addLeft p) s := by
  have hsub : (⇑(h.subtriangle p) : Vertex k → R) =
      (fun q => h (p.add q)) - fun _ => h (p.add (Vertex.cornerA k)) := funext fun _ => by simp
  rw [hsub, triangleGradient_sub, triangleGradient_comp_add, triangleGradient_const, sub_zero]
theorem triangleGradient_comp_rotate {n : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (fun p => f p.rotate) T s = triangleGradient f T.rotate (s + 1) := by
  cases T <;> [rw [triangleGradient_up]; rw [triangleGradient_down]] <;>
    rw [← UnitTriangle.vertex_rotate, ← UnitTriangle.vertex_rotate] <;> simp
@[simp] theorem triangleGradient_rotate {n : ℕ} {R : Type*} [AddCommGroup R]
    [PartialOrder R] [IsOrderedAddMonoid R] (h : Hive n R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient h.rotate T s = triangleGradient h T.rotate (s + 1) := by
  have hrot : (⇑h.rotate : Vertex n → R) =
      (fun p => h p.rotate) - fun _ => h (Vertex.cornerA n).rotate := funext fun _ => by simp
  rw [hrot, triangleGradient_sub, triangleGradient_comp_rotate, triangleGradient_const, sub_zero]
theorem triangleGradient_comp_reflect {n : ℕ} {R : Type*} [AddCommGroup R]
    (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (fun p => f p.reflect) T s = -triangleGradient f T.reflect s.rev := by
  have hs1 : -(s + 1) = s.rev := by fin_cases s <;> decide
  have hs0 : -s = s.rev + 1 := by fin_cases s <;> decide
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, ← UnitTriangle.vertex_reflect,
    UnitTriangle.reflect_up, UnitTriangle.reflect_down, hs1, hs0] <;> abel
@[simp] theorem triangleGradient_reflect {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    (h : Hive n R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient h.reflect T s = -triangleGradient h T.reflect s.rev := by
  simpa [show (⇑h.reflect : Vertex n → R) = fun p => h p.reflect from funext fun _ => by simp] using
    triangleGradient_comp_reflect h T s
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
  rw [triangleGradient_adjacentUp, triangleGradient_down, (by fin_cases i <;> rfl : i + 1 + 1 =
    i + 2), adjacentUp_vertex_add_two, adjacentUp_vertex_add_one]
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
  rw [triangleGradient_adjacentUp, triangleGradient_down, (by fin_cases i <;> rfl : i + 2 + 1 = i),
    rhombusSlack_def, adjacentUp_vertex_add_two]; abel

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
  have h2 : f b + f d = f ((adjacentUp s i).vertex i) + f ((UnitTriangle.down s).vertex i) := by
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
theorem triangleGradient_up_cornerA_zero {R : Type*} [AddCommGroup R] (f : Vertex 1 → R)
    (s : Fin 3) : triangleGradient f (UnitTriangle.up (Vertex.cornerA 0)) s =
      boundaryLinear ℤ 1 R f s 0 := by
  rw [Subsingleton.elim (Vertex.cornerA 0) (Vertex.edgePoint 0 s 0), triangleGradient_up_edgePoint]

/-! ### Simplicial affine pieces and continuous piecewise-affine interpolation -/

/-- Continuous affine extension of `f : Vertex n → ℝ` on a unit triangle `T : UnitTriangle n`. -/
noncomputable def triangleAffine {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n) :
    (Fin 3 → ℝ) →ᴬ[ℝ] ℝ :=
  f (T.vertex 0) • T.weight 0 + f (T.vertex 1) • T.weight 1 + f (T.vertex 2) • T.weight 2

theorem triangleAffine_def {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n) : triangleAffine f T =
    f (T.vertex 0) • T.weight 0 + f (T.vertex 1) • T.weight 1 + f (T.vertex 2) • T.weight 2 := (rfl)
theorem triangleAffine_apply {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine f T x = ∑ i : Fin 3, f (T.vertex i) * T.weight i x := by
  simp [triangleAffine, Fin.sum_univ_three, add_assoc]
@[simp] theorem triangleAffine_zero {n : ℕ} (T : UnitTriangle n) :
    triangleAffine (0 : Vertex n → ℝ) T = 0 := by ext x; simp [triangleAffine_apply]
theorem triangleAffine_add {n : ℕ} (f g : Vertex n → ℝ) (T : UnitTriangle n) :
    triangleAffine (f + g) T = triangleAffine f T + triangleAffine g T := by
  ext x; simp [triangleAffine_apply, add_mul, Finset.sum_add_distrib]
theorem triangleAffine_smul {n : ℕ} (c : ℝ) (f : Vertex n → ℝ) (T : UnitTriangle n) :
    triangleAffine (c • f) T = c • triangleAffine f T := by
  ext x; simp [triangleAffine_apply, mul_assoc, Finset.mul_sum]
theorem triangleAffine_addLeft {m n : ℕ} (f : Vertex (m + n) → ℝ) (p : Vertex m)
    (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine f (T.addLeft p) (p.barycentric + x) =
      triangleAffine (fun q => f (p.add q)) T x := by
  simp [triangleAffine_apply, UnitTriangle.vertex_addLeft, UnitTriangle.weight_addLeft_apply]
@[simp] theorem triangleAffine_vertex {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n) (i : Fin 3) :
    triangleAffine f T (T.vertex i).barycentric = f (T.vertex i) := by
  rw [triangleAffine_apply]; fin_cases i <;> simp
@[simp] theorem triangleAffine_up_barycentric_add_unitCorner {m : ℕ} (f : Vertex (m + 1) → ℝ)
    (b : Vertex m) (i : Fin 3) :
    triangleAffine f (UnitTriangle.up b) (b.add (unitCorner i)).barycentric =
      f (b.add (unitCorner i)) := by simpa using triangleAffine_vertex f (UnitTriangle.up b) i
@[simp] theorem triangleAffine_down_barycentric_add_oppUnitCorner {m : ℕ} (f : Vertex (m + 2) → ℝ)
    (b : Vertex m) (i : Fin 3) :
    triangleAffine f (UnitTriangle.down b) (b.add (oppUnitCorner i)).barycentric =
      f (b.add (oppUnitCorner i)) := by simpa using triangleAffine_vertex f (UnitTriangle.down b) i

/-- The `s`-th clockwise perimeter unit-step vector `(-1, 1, 0)`, `(0, -1, 1)`, `(1, 0, -1)`. -/
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

/-- Two unit triangles whose cells both contain `x` assign the same affine value at `x`. -/
theorem triangleAffine_eq_of_mem_cell {n : ℕ} (f : Vertex n → ℝ) {T₁ T₂ : UnitTriangle n}
    {x : Fin 3 → ℝ} (hx₁ : x ∈ T₁.cell) (hx₂ : x ∈ T₂.cell) :
    triangleAffine f T₁ x = triangleAffine f T₂ x := by
  have hx_sum := (mem_barycentricSimplex_iff.mp (T₁.cell_subset_barycentricSimplex hx₁)).2
  have hcombo := (triangleAffine f T₂).toAffineMap.apply_sum_smul_of_sum_eq_one Finset.univ
    (T₁.sum_weight hx_sum) fun i => (T₁.vertex i).barycentric
  simp only [ContinuousAffineMap.coe_toAffineMap, smul_eq_mul] at hcombo
  conv_rhs => rw [← T₁.sum_weight_smul_vertex hx_sum, hcombo]
  rw [triangleAffine_apply]; refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_lt_of_le (T₁.weight_nonneg hx₁ i) with h0 | hpos
  · simp [← h0]
  · obtain ⟨j, hj⟩ := T₁.mem_range_vertex_of_weight_pos hx₁ hx₂ hpos
    rw [← hj, triangleAffine_vertex, mul_comm]

/-- Simplicial extension of `f : Vertex n → ℝ` to `Fin 3 → ℝ`, agreeing with `triangleAffine f T`
on each cell `T.cell` of `barycentricSimplex n` and taking fallback value `f (cornerA n)` outside
the union of cells (and for `n = 0`). -/
noncomputable def interpolate {n : ℕ} (f : Vertex n → ℝ) (x : Fin 3 → ℝ) : ℝ := open Classical in
  if h : ∃ T : UnitTriangle n, x ∈ T.cell then triangleAffine f h.choose x else f (Vertex.cornerA n)

theorem interpolate_eq_triangleAffine {n : ℕ} (f : Vertex n → ℝ) {T : UnitTriangle n}
    {x : Fin 3 → ℝ} (hx : x ∈ T.cell) : interpolate f x = triangleAffine f T x := by
  rw [interpolate]; split_ifs with hex <;>
    [exact triangleAffine_eq_of_mem_cell f hex.choose_spec hx; exact (hex ⟨T, hx⟩).elim]
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
/-- `interpolate f` is continuous on `barycentricSimplex n`. -/
theorem continuousOn_interpolate {n : ℕ} (f : Vertex n → ℝ) :
    ContinuousOn (interpolate f) (barycentricSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).continuousOn

theorem interpolate_add {n : ℕ} (f g : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate (f + g) x = interpolate f x + interpolate g x := by
  rw [interpolate, interpolate, interpolate]; split_ifs with h <;> [simp [triangleAffine_add]; rfl]
theorem interpolate_smul {n : ℕ} (c : ℝ) (f : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate (c • f) x = c * interpolate f x := by
  rw [interpolate, interpolate]; split_ifs with h <;> [simp [triangleAffine_smul]; rfl]
@[simp] theorem interpolate_zero {n : ℕ} (x : Fin 3 → ℝ) :
    interpolate (0 : Vertex n → ℝ) x = 0 := by simpa using interpolate_smul 0 (0 : Vertex n → ℝ) x
@[simp] theorem interpolate_const {n : ℕ} (c : ℝ) (x : Fin 3 → ℝ) :
    interpolate (fun _ : Vertex n => c) x = c := by
  rw [interpolate]; split_ifs with h
  · rw [triangleAffine_apply, ← Finset.mul_sum, h.choose.sum_weight
      (mem_barycentricSimplex_iff.mp (h.choose.cell_subset_barycentricSimplex h.choose_spec)).2,
      mul_one]
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
      triangleAffine_addLeft]
/-- Compatibility of `interpolate` with restriction to `h.subtriangle p`. -/
theorem interpolate_subtriangle {m k : ℕ} (h : RealHive (m + k)) (p : Vertex m) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex k) : interpolate (h.subtriangle p) x =
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
/-- Outside `planarSimplex n`, `planarInterpolate f` takes the fallback value `f (cornerA n)`. -/
theorem planarInterpolate_of_notMem_planarSimplex {n : ℕ} (f : Vertex n → ℝ)
    {u : EuclideanSpace ℝ (Fin 2)} (hu : u ∉ planarSimplex n) :
    planarInterpolate f u = f (Vertex.cornerA n) :=
  interpolate_of_notMem_barycentricSimplex f (mt mem_planarSimplex_iff.mpr hu)
@[simp] theorem planarInterpolate_zero_rank (f : Vertex 0 → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate f u = f (Vertex.cornerA 0) := by simp [planarInterpolate]
/-- Along any unit lattice edge `(a, c)`, `planarInterpolate f` is affine on `[0, 1]`. -/
theorem planarInterpolate_lineMap_of_isUnitEdge {n : ℕ} (f : Vertex n → ℝ) {a c : Vertex n}
    (h : IsUnitEdge a c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    planarInterpolate f (AffineMap.lineMap a.plane c.plane t) = (1 - t) * f a + t * f c := by
  rw [planarInterpolate, (planeInvAffine n).apply_lineMap, planeInvAffine_plane,
    planeInvAffine_plane, interpolate_lineMap_of_isUnitEdge f h ht]
theorem planarInterpolate_add {n : ℕ} (f g : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (f + g) u = planarInterpolate f u + planarInterpolate g u :=
  interpolate_add f g (planeInvAffine n u)
theorem planarInterpolate_smul {n : ℕ} (c : ℝ) (f : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (c • f) u = c * planarInterpolate f u :=
  interpolate_smul c f (planeInvAffine n u)
@[simp] theorem planarInterpolate_zero {n : ℕ} (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (0 : Vertex n → ℝ) u = 0 := interpolate_zero (planeInvAffine n u)
@[simp] theorem planarInterpolate_const {n : ℕ} (c : ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (fun _ : Vertex n => c) u = c := interpolate_const c (planeInvAffine n u)
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
