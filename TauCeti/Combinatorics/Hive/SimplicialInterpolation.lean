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
import Mathlib.Tactic.Ring

/-!
# Simplicial hive interpolation and zero-sum triangle gradients

Simplicial interpolation on the `n²` unit equilateral triangles (`TauCeti.Hive.UnitTriangle n`)
extends `f : Vertex n → ℝ` to a continuous piecewise-affine function `interpolate f` on
`barycentricSimplex n` (and via `planarInterpolate f` to `planarSimplex n ⊆ ℝ²`), agreeing on each
unit triangle `T` with `triangleAffine f T = ∑ i, f (T.vertex i) • T.weight i`. Its finite
differences along the outer-perimeter unit steps `(-1, 1, 0)`, `(0, -1, 1)`, `(1, 0, -1)` form
the zero-sum triple `triangleGradient f T` over any additive abelian group (matching the
directional derivatives of `triangleAffine f T` when `R = ℝ`); across the shared edge of `down s`
and `adjacentUp s i`, the `(i + 1)`-coordinate is constant while the `i`-th jumps by the rhombus
slack.

## Main definitions and results

* `TauCeti.Hive.triangleGradient`, `TauCeti.Hive.triangleAffine`, `TauCeti.Hive.interpolate`,
  `TauCeti.Hive.planarInterpolate`.
* `TauCeti.Hive.triangleGradient_adjacentUp_add_one`,
  `TauCeti.Hive.triangleGradient_adjacentUp_sub_down_self`,
  `TauCeti.Hive.triangleGradient_up_edgePoint`, `TauCeti.Hive.isRhombusConcave_iff_adjacent`.
* `TauCeti.Hive.eq_triangleAffine_of_vertex`, `TauCeti.Hive.eqOn_interpolate_of_affineOn_cell`,
  `TauCeti.Hive.eqOn_planarInterpolate_of_affineOn_cell`.
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

variable {n m k : ℕ}

/-! ### Zero-sum triangle gradients and adjacent-rhombus concavity -/

section

variable {R : Type*} [AddCommGroup R]

/-- The zero-sum triple of finite differences of `f : Vertex n → R` on a unit triangle
`T : UnitTriangle n` along the fixed outer-perimeter directions `A → B` (`s = 0`, `(-1, 1, 0)`),
`B → C` (`s = 1`, `(0, -1, 1)`), and `C → A` (`s = 2`, `(1, 0, -1)`). Both upward and downward
vertex cycles `vertex 0 → vertex 1 → vertex 2` run clockwise in the plane: on `up b`, each edge
`vertex s → vertex (s + 1)` matches the `s`-th perimeter direction
(`f (vertex (s + 1)) - f (vertex s)`); on `down b`, each indexed edge `vertex s → vertex (s + 1)`
points opposite to the `s`-th perimeter direction, giving `f (vertex s) - f (vertex (s + 1))`. -/
def triangleGradient (f : Vertex n → R) : UnitTriangle n → Fin 3 → R
  | .up b, s => f ((UnitTriangle.up b).vertex (s + 1)) - f ((UnitTriangle.up b).vertex s)
  | .down b, s => f ((UnitTriangle.down b).vertex s) - f ((UnitTriangle.down b).vertex (s + 1))

@[simp] theorem triangleGradient_up (f : Vertex (m + 1) → R) (b : Vertex m) (s : Fin 3) :
    triangleGradient f (UnitTriangle.up b) s =
      f ((UnitTriangle.up b).vertex (s + 1)) - f ((UnitTriangle.up b).vertex s) := (rfl)
@[simp] theorem triangleGradient_down (f : Vertex (m + 2) → R) (b : Vertex m) (s : Fin 3) :
    triangleGradient f (UnitTriangle.down b) s =
      f ((UnitTriangle.down b).vertex s) - f ((UnitTriangle.down b).vertex (s + 1)) := (rfl)
@[simp] theorem sum_triangleGradient (f : Vertex n → R) (T : UnitTriangle n) :
    ∑ s : Fin 3, triangleGradient f T s = 0 := by
  cases T <;> simp [Fin.sum_univ_three] <;> abel
@[simp] theorem triangleGradient_zero (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (0 : Vertex n → R) T s = 0 := by cases T <;> simp
theorem triangleGradient_add (f g : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (f + g) T s = triangleGradient f T s + triangleGradient g T s := by
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, Pi.add_apply] <;> abel
theorem triangleGradient_neg (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (-f) T s = -triangleGradient f T s := by
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, Pi.neg_apply] <;> abel
theorem triangleGradient_sub (f g : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (f - g) T s = triangleGradient f T s - triangleGradient g T s := by
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, Pi.sub_apply] <;> abel
theorem triangleGradient_smul {S : Type*} [Semiring S] [Module S R] (c : S) (f : Vertex n → R)
    (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (c • f) T s = c • triangleGradient f T s := by cases T <;> simp [smul_sub]
@[simp] theorem triangleGradient_const (c : R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (fun _ : Vertex n => c) T s = 0 := by cases T <;> simp
theorem triangleGradient_comp {S F : Type*} [AddCommGroup S] [FunLike F R S]
    [AddMonoidHomClass F R S] (φ : F) (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (φ ∘ f) T s = φ (triangleGradient f T s) := by cases T <;> simp
@[simp] theorem triangleGradient_map [PartialOrder R] {S : Type*} [AddCommGroup S] [PartialOrder S]
    (φ : R →+o S) (h : Hive n R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (h.map φ) T s = φ (triangleGradient h T s) := by cases T <;> simp
@[simp] theorem triangleGradient_ofInt (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R]
    (h : IntegerHive n) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (ofInt R h) T s = ((triangleGradient h T s : ℤ) : R) := by cases T <;> simp
@[simp high] theorem triangleGradient_barycentricLinear (c₀ α β γ : R) (T : UnitTriangle n) :
    triangleGradient (barycentricLinear c₀ α β γ) T = ![β - α, γ - β, α - γ] := by
  ext s; cases T <;> fin_cases s <;> simp [add_nsmul] <;> abel
@[simp high] theorem triangleGradient_affine [Preorder R] (β γ : R)
    (T : UnitTriangle n) : triangleGradient (affine n β γ) T = ![β, γ - β, -γ] := by
  have hcoe : ⇑(affine n β γ) = barycentricLinear 0 0 β γ := funext fun _ => by simp
  simp [hcoe]
theorem triangleGradient_comp_add (f : Vertex (m + k) → R) (p : Vertex m) (T : UnitTriangle k)
    (s : Fin 3) :
    triangleGradient (fun q => f (p.add q)) T s = triangleGradient f (T.addLeft p) s := by
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, UnitTriangle.addLeft_up,
    UnitTriangle.addLeft_down, ← UnitTriangle.vertex_addLeft]
@[simp] theorem triangleGradient_subtriangle [PartialOrder R] [IsOrderedAddMonoid R]
    (h : Hive (m + k) R) (p : Vertex m) (T : UnitTriangle k) (s : Fin 3) :
    triangleGradient (h.subtriangle p) T s = triangleGradient h (T.addLeft p) s := by
  rw [show ⇑(h.subtriangle p) = (fun q => h (p.add q)) - fun _ => h (p.add (Vertex.cornerA k))
    from funext fun _ => subtriangle_apply _ _ _, triangleGradient_sub,
    triangleGradient_comp_add, triangleGradient_const, sub_zero]
theorem triangleGradient_comp_rotate (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (fun p => f p.rotate) T s = triangleGradient f T.rotate (s + 1) := by
  cases T <;> simp
@[simp] theorem triangleGradient_rotate [PartialOrder R] [IsOrderedAddMonoid R] (h : Hive n R)
    (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient h.rotate T s = triangleGradient h T.rotate (s + 1) := by
  rw [show ⇑h.rotate = (fun p => h p.rotate) - fun _ => h (Vertex.cornerA n).rotate
    from funext fun _ => rotate_apply _ _, triangleGradient_sub, triangleGradient_comp_rotate,
    triangleGradient_const, sub_zero]
theorem triangleGradient_comp_reflect (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient (fun p => f p.reflect) T s = -triangleGradient f T.reflect s.rev := by
  cases T <;> fin_cases s <;> simp [Fin.rev] <;> abel
@[simp] theorem triangleGradient_reflect [PartialOrder R] (h : Hive n R) (T : UnitTriangle n)
    (s : Fin 3) : triangleGradient h.reflect T s = -triangleGradient h T.reflect s.rev := by
  rw [coe_reflect]; exact triangleGradient_comp_reflect h T s
@[simp] theorem triangleGradient_adjacentUp (f : Vertex (m + 2) → R) (s : Vertex m) (i j : Fin 3) :
    triangleGradient f (adjacentUp s i) j =
      f ((adjacentUp s i).vertex (j + 1)) - f ((adjacentUp s i).vertex j) := by
  rw [adjacentUp_def, triangleGradient_up, ← adjacentUp_def]

/-- Across the shared edge of `down s` and `adjacentUp s i` opposite `(down s).vertex i`, the
`(i + 1)`-coordinate of `triangleGradient` is constant. -/
theorem triangleGradient_adjacentUp_add_one (f : Vertex (m + 2) → R) (s : Vertex m) (i : Fin 3) :
    triangleGradient f (adjacentUp s i) (i + 1) =
      triangleGradient f (UnitTriangle.down s) (i + 1) := by
  rw [triangleGradient_adjacentUp, triangleGradient_down, (by fin_cases i <;> rfl : i + 1 + 1 =
    i + 2), vertex_adjacentUp_add_two, vertex_adjacentUp_add_one]
/-- Across the shared edge of `down s` and `adjacentUp s i` opposite `(down s).vertex i`, the
`i`-th coordinate of `triangleGradient` jumps by the unit-rhombus slack. -/
theorem triangleGradient_adjacentUp_sub_down_self (f : Vertex (m + 2) → R) (s : Vertex m)
    (i : Fin 3) :
    triangleGradient f (adjacentUp s i) i - triangleGradient f (UnitTriangle.down s) i =
      rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  rw [triangleGradient_adjacentUp, triangleGradient_down, rhombusSlack_def,
    vertex_adjacentUp_add_one]; abel
/-- Across the shared edge of `down s` and `adjacentUp s i` opposite `(down s).vertex i`, the
`(i + 2)`-th coordinate of `triangleGradient` jumps by minus the unit-rhombus slack. -/
theorem triangleGradient_adjacentUp_sub_down_add_two (f : Vertex (m + 2) → R) (s : Vertex m)
    (i : Fin 3) :
    triangleGradient f (adjacentUp s i) (i + 2) - triangleGradient f (UnitTriangle.down s) (i + 2) =
      -rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  rw [triangleGradient_adjacentUp, triangleGradient_down, (by fin_cases i <;> rfl : i + 2 + 1 = i),
    rhombusSlack_def, vertex_adjacentUp_add_two]; abel

/-- At size `m + 2`, rhombus concavity over any ordered additive abelian group is completely
determined by the unit rhombi `isRhombus_adjacent s i` across shared interior unit edges. -/
theorem isRhombusConcave_iff_adjacent [PartialOrder R] [IsOrderedAddMonoid R]
    (f : Vertex (m + 2) → R) :
    IsRhombusConcave f ↔ ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  rw [isRhombusConcave_iff_rhombusSlack_nonneg]
  refine ⟨fun hf s i => hf (isRhombus_adjacent s i), fun hadj a b c d hr => ?_⟩
  obtain ⟨s, i, hac, hbd⟩ := hr.exists_adjacentUp
  rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hbd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simpa [rhombusSlack_def, add_comm] using hadj s i

/-- Along side `s` of the perimeter, the `s`-th coordinate of `triangleGradient f` on the upward
perimeter triangle `up (edgePoint m s i)` equals `boundaryLinear ℤ (m + 1) R f s i`. -/
theorem triangleGradient_up_edgePoint (f : Vertex (m + 1) → R) (s : Fin 3) (i : Fin (m + 1)) :
    triangleGradient f (UnitTriangle.up (Vertex.edgePoint m s i)) s =
      boundaryLinear ℤ (m + 1) R f s i := by
  fin_cases s <;> rw [triangleGradient_up, boundaryLinear_apply] <;>
    congr 2 <;> ext <;> simp <;> omega
/-- At size `1`, the zero-sum gradient of the unique unit triangle equals the clockwise boundary
`(λ₁, μ₁, ν₁)` of `f`. -/
theorem triangleGradient_up_cornerA_zero (f : Vertex 1 → R) (s : Fin 3) :
    triangleGradient f (UnitTriangle.up (Vertex.cornerA 0)) s = boundaryLinear ℤ 1 R f s 0 := by
  rw [Subsingleton.elim (Vertex.cornerA 0) (Vertex.edgePoint 0 s 0), triangleGradient_up_edgePoint]

end

/-! ### Simplicial affine pieces and continuous piecewise-affine interpolation -/

/-- Continuous affine extension of `f : Vertex n → ℝ` on a unit triangle `T : UnitTriangle n`. -/
noncomputable def triangleAffine (f : Vertex n → ℝ) (T : UnitTriangle n) : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ :=
  f (T.vertex 0) • T.weight 0 + f (T.vertex 1) • T.weight 1 + f (T.vertex 2) • T.weight 2

theorem triangleAffine_def (f : Vertex n → ℝ) (T : UnitTriangle n) : triangleAffine f T =
    f (T.vertex 0) • T.weight 0 + f (T.vertex 1) • T.weight 1 + f (T.vertex 2) • T.weight 2 := (rfl)
theorem triangleAffine_apply (f : Vertex n → ℝ) (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine f T x = ∑ i : Fin 3, f (T.vertex i) * T.weight i x := by
  simp [triangleAffine, Fin.sum_univ_three, add_assoc]
@[simp] theorem triangleAffine_zero (T : UnitTriangle n) :
    triangleAffine (0 : Vertex n → ℝ) T = 0 := by ext x; simp [triangleAffine_apply]
theorem triangleAffine_add (f g : Vertex n → ℝ) (T : UnitTriangle n) :
    triangleAffine (f + g) T = triangleAffine f T + triangleAffine g T := by
  ext x; simp [triangleAffine_apply, add_mul, Finset.sum_add_distrib]
theorem triangleAffine_smul (c : ℝ) (f : Vertex n → ℝ) (T : UnitTriangle n) :
    triangleAffine (c • f) T = c • triangleAffine f T := by
  ext x; simp [triangleAffine_apply, mul_assoc, Finset.mul_sum]
theorem triangleAffine_neg (f : Vertex n → ℝ) (T : UnitTriangle n) :
    triangleAffine (-f) T = -triangleAffine f T := by simpa using triangleAffine_smul (-1 : ℝ) f T
theorem triangleAffine_sub (f g : Vertex n → ℝ) (T : UnitTriangle n) :
    triangleAffine (f - g) T = triangleAffine f T - triangleAffine g T := by
  rw [sub_eq_add_neg, triangleAffine_add, triangleAffine_neg, sub_eq_add_neg]
theorem triangleAffine_const (c : ℝ) (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) : triangleAffine (fun _ : Vertex n => c) T x = c := by
  rw [triangleAffine_apply, ← Finset.mul_sum, T.sum_weight hx, mul_one]
theorem triangleAffine_ofRhombusConcave (f : Vertex n → ℝ) (hf : IsRhombusConcave f)
    (T : UnitTriangle n) {x : Fin 3 → ℝ} (hx : ∑ i, x i = (n : ℝ)) :
    triangleAffine (ofRhombusConcave f hf) T x = triangleAffine f T x - f (Vertex.cornerA n) := by
  rw [show ⇑(ofRhombusConcave f hf) = f - fun _ => f (Vertex.cornerA n)
    from funext fun _ => ofRhombusConcave_apply _ _ _, triangleAffine_sub,
    ContinuousAffineMap.sub_apply, triangleAffine_const _ T hx]
theorem triangleAffine_addLeft (f : Vertex (m + n) → ℝ) (p : Vertex m) (T : UnitTriangle n)
    (x : Fin 3 → ℝ) : triangleAffine f (T.addLeft p) (p.barycentric + x) =
      triangleAffine (fun q => f (p.add q)) T x := by
  simp [triangleAffine_apply, UnitTriangle.vertex_addLeft, UnitTriangle.weight_addLeft_apply]
theorem triangleAffine_subtriangle (h : RealHive (m + k)) (p : Vertex m) (T : UnitTriangle k)
    {x : Fin 3 → ℝ} (hx : ∑ i, x i = (k : ℝ)) : triangleAffine (h.subtriangle p) T x =
      triangleAffine h (T.addLeft p) (p.barycentric + x) - h (p.add (Vertex.cornerA k)) := by
  rw [show ⇑(h.subtriangle p) = (fun q => h (p.add q)) - fun _ => h (p.add (Vertex.cornerA k))
    from funext fun _ => subtriangle_apply _ _ _, triangleAffine_sub,
    ContinuousAffineMap.sub_apply, ← triangleAffine_addLeft, triangleAffine_const _ T hx]
theorem triangleAffine_comp_rotate (f : Vertex n → ℝ) (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine (fun p => f p.rotate) T x = triangleAffine f T.rotate (fun k => x (k - 1)) := by
  simp only [triangleAffine_apply]
  exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 3)) _ _ fun i => by
    simp [UnitTriangle.vertex_rotate, UnitTriangle.weight_rotate_apply]
theorem triangleAffine_rotate (h : RealHive n) (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) : triangleAffine h.rotate T x =
      triangleAffine h T.rotate (fun k => x (k - 1)) - h (Vertex.cornerA n).rotate := by
  rw [show ⇑h.rotate = (fun p => h p.rotate) - fun _ => h (Vertex.cornerA n).rotate
    from funext fun _ => rotate_apply _ _, triangleAffine_sub, ContinuousAffineMap.sub_apply,
    triangleAffine_comp_rotate, triangleAffine_const _ T hx]
theorem triangleAffine_comp_reflect (f : Vertex n → ℝ) (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine (fun p => f p.reflect) T x = triangleAffine f T.reflect (fun k => x (-k)) := by
  simp only [triangleAffine_apply]
  exact Fintype.sum_equiv (Equiv.neg (Fin 3)) _ _ fun i => by
    rw [Equiv.neg_apply, UnitTriangle.vertex_reflect, UnitTriangle.weight_reflect_apply]
theorem triangleAffine_reflect (h : RealHive n) (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine h.reflect T x = triangleAffine h T.reflect (fun k => x (-k)) := by
  rw [coe_reflect]; exact triangleAffine_comp_reflect h T x
@[simp] theorem triangleAffine_vertex (f : Vertex n → ℝ) (T : UnitTriangle n) (i : Fin 3) :
    triangleAffine f T (T.vertex i).barycentric = f (T.vertex i) := by
  rw [triangleAffine_apply]; fin_cases i <;> simp
@[simp] theorem triangleAffine_up_barycentric_add_unitCorner (f : Vertex (m + 1) → ℝ)
    (b : Vertex m) (i : Fin 3) :
    triangleAffine f (UnitTriangle.up b) (b.add (unitCorner i)).barycentric =
      f (b.add (unitCorner i)) := by simpa using triangleAffine_vertex f (UnitTriangle.up b) i
@[simp] theorem triangleAffine_down_barycentric_add_oppUnitCorner (f : Vertex (m + 2) → ℝ)
    (b : Vertex m) (i : Fin 3) :
    triangleAffine f (UnitTriangle.down b) (b.add (oppUnitCorner i)).barycentric =
      f (b.add (oppUnitCorner i)) := by simpa using triangleAffine_vertex f (UnitTriangle.down b) i
/-- Any affine map agreeing with `f` on the vertices of `T` equals `triangleAffine f T` on the
hyperplane `{x | ∑ i, x i = n}`. -/
theorem eq_triangleAffine_of_vertex {f : Vertex n → ℝ} {T : UnitTriangle n}
    {A : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ} (hA : ∀ i, A (T.vertex i).barycentric = f (T.vertex i))
    {x : Fin 3 → ℝ} (hx : ∑ i, x i = (n : ℝ)) : A x = triangleAffine f T x := by
  have hw := T.sum_weight hx
  have h := (Finset.univ.map_affineCombination (fun i => (T.vertex i).barycentric)
    (fun i => T.weight i x) hw A).symm
  simp only [Finset.affineCombination_eq_linear_combination _ _ _ hw,
    T.sum_weight_smul_vertex hx] at h
  rw [← h]
  simp [triangleAffine_apply, hA, mul_comm]
/-- Any affine map agreeing with `f` on the vertices of `T` agrees with `triangleAffine f T` on
`T.cell`. -/
theorem eqOn_triangleAffine_of_vertex {f : Vertex n → ℝ} {T : UnitTriangle n}
    {A : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ} (hA : ∀ i, A (T.vertex i).barycentric = f (T.vertex i)) :
    EqOn A (triangleAffine f T) T.cell := fun _ hx => eq_triangleAffine_of_vertex hA
  (mem_barycentricSimplex_iff.mp (T.cell_subset_barycentricSimplex hx)).2
theorem triangleAffine_barycentricLinear (c₀ α β γ : ℝ) (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) :
    triangleAffine (barycentricLinear c₀ α β γ) T x = c₀ + x 0 * α + x 1 * β + x 2 * γ := by
  let p (i : Fin 3) : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj i).toContinuousAffineMap
  let A := ContinuousAffineMap.const ℝ _ c₀ + α • p 0 + β • p 1 + γ • p 2
  simpa [A, p, mul_comm] using (eq_triangleAffine_of_vertex (A := A.toAffineMap)
    (fun i => by simp [A, p, mul_comm]) hx).symm
theorem triangleAffine_affine (β γ : ℝ) (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) : triangleAffine (affine n β γ) T x = x 1 * β + x 2 * γ := by
  have hcoe : ⇑(affine n β γ) = barycentricLinear 0 0 β γ := funext fun _ => by simp
  simpa [hcoe] using triangleAffine_barycentricLinear (0 : ℝ) 0 β γ T hx

/-- The `s`-th clockwise perimeter unit-step vector `(-1, 1, 0)`, `(0, -1, 1)`, `(1, 0, -1)`. -/
def unitStepVec : Fin 3 → (Fin 3 → ℝ)
  | ⟨0, _⟩ => ![-1, 1, 0] | ⟨1, _⟩ => ![0, -1, 1] | ⟨2, _⟩ => ![1, 0, -1]

@[simp] theorem unitStepVec_apply (s k : Fin 3) :
    unitStepVec s k = (if k = s + 1 then 1 else 0) - (if k = s then 1 else 0) := by
  fin_cases s <;> fin_cases k <;> simp [unitStepVec]
theorem sum_unitStepVec (s : Fin 3) : ∑ i : Fin 3, unitStepVec s i = 0 := by simp

/-- The directional derivative of `triangleAffine f T` along `unitStepVec s` equals the
combinatorial edge slope `triangleGradient f T s`. -/
@[simp] theorem triangleAffine_contLinear_unitStepVec (f : Vertex n → ℝ) (T : UnitTriangle n)
    (s : Fin 3) : (triangleAffine f T).contLinear (unitStepVec s) = triangleGradient f T s := by
  cases T <;> fin_cases s <;> simp [triangleAffine] <;> ring

/-- Two unit triangles whose cells both contain `x` assign the same affine value at `x`. -/
theorem triangleAffine_eq_of_mem_cell (f : Vertex n → ℝ) {T₁ T₂ : UnitTriangle n} {x : Fin 3 → ℝ}
    (hx₁ : x ∈ T₁.cell) (hx₂ : x ∈ T₂.cell) : triangleAffine f T₁ x = triangleAffine f T₂ x := by
  have hx_sum := (mem_barycentricSimplex_iff.mp (T₁.cell_subset_barycentricSimplex hx₁)).2
  have hw := T₁.sum_weight hx_sum
  have haff := (Finset.univ.map_affineCombination (fun i => (T₁.vertex i).barycentric)
    (fun i => T₁.weight i x) hw (triangleAffine f T₂).toAffineMap).symm
  simp only [Finset.affineCombination_eq_linear_combination _ _ _ hw,
    T₁.sum_weight_smul_vertex hx_sum, ContinuousAffineMap.coe_toAffineMap] at haff
  rw [← haff, triangleAffine_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_lt_of_le (T₁.weight_nonneg hx₁ i) with h0 | hpos
  · simp [← h0]
  · obtain ⟨j, hj⟩ := T₁.mem_range_vertex_of_weight_pos hx₁ hx₂ hpos; simp [← hj, mul_comm]

/-- Simplicial extension of `f : Vertex n → ℝ` to `Fin 3 → ℝ`, agreeing with `triangleAffine f T`
on each cell `T.cell` of `barycentricSimplex n` and taking fallback value `f (cornerA n)` outside
the union of cells (and for `n = 0`). -/
noncomputable def interpolate (f : Vertex n → ℝ) (x : Fin 3 → ℝ) : ℝ := open Classical in
  if h : ∃ T : UnitTriangle n, x ∈ T.cell then triangleAffine f h.choose x else f (Vertex.cornerA n)

theorem interpolate_eq_triangleAffine (f : Vertex n → ℝ) {T : UnitTriangle n} {x : Fin 3 → ℝ}
    (hx : x ∈ T.cell) : interpolate f x = triangleAffine f T x := by
  rw [interpolate]; split_ifs with hex <;>
    [exact triangleAffine_eq_of_mem_cell f hex.choose_spec hx; exact (hex ⟨T, hx⟩).elim]
/-- Outside `barycentricSimplex n`, `interpolate f` takes the fallback value `f (cornerA n)`. -/
theorem interpolate_of_notMem_barycentricSimplex (f : Vertex n → ℝ) {x : Fin 3 → ℝ}
    (hx : x ∉ barycentricSimplex n) : interpolate f x = f (Vertex.cornerA n) := by
  rw [interpolate]; split_ifs with h <;>
    [exact (hx (h.choose.cell_subset_barycentricSimplex h.choose_spec)).elim; rfl]
@[simp] theorem interpolate_rank_zero (f : Vertex 0 → ℝ) (x : Fin 3 → ℝ) :
    interpolate f x = f (Vertex.cornerA 0) := by simp [interpolate]
/-- `interpolate f` extends `f` from the lattice vertices `Vertex n` via `Vertex.barycentric`. -/
@[simp] theorem interpolate_barycentric (f : Vertex n → ℝ) (p : Vertex n) :
    interpolate f p.barycentric = f p := by
  rcases n with _ | m
  · rw [interpolate_rank_zero, Subsingleton.elim p (Vertex.cornerA 0)]
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex m).symm ▸
      barycentric_mem_barycentricSimplex p)
    obtain ⟨i, rfl⟩ := UnitTriangle.mem_range_vertex_of_barycentric_mem_cell hT
    rw [interpolate_eq_triangleAffine f hT, triangleAffine_vertex]
/-- Any function that is affine on every unit-triangle cell and agrees with `f` on lattice vertices
equals `interpolate f` on `barycentricSimplex n`. -/
theorem eqOn_interpolate_of_affineOn_cell {f : Vertex n → ℝ} {g : (Fin 3 → ℝ) → ℝ}
    (hg_vert : ∀ p : Vertex n, g p.barycentric = f p)
    (hg_aff : ∀ T : UnitTriangle n, ∃ A : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ, EqOn g A T.cell) :
    EqOn g (interpolate f) (barycentricSimplex n) := fun x hx => by
  rcases n with _ | m
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx
    rw [hx, ← Vertex.barycentric_cornerA_zero, hg_vert, interpolate_rank_zero]
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex m).symm ▸ hx)
    obtain ⟨A, hA⟩ := hg_aff T; rw [hA hT, interpolate_eq_triangleAffine f hT]
    exact eqOn_triangleAffine_of_vertex
      (fun i => (hA (T.barycentric_vertex_mem_cell i)).symm.trans (hg_vert _)) hT
/-- Along any unit lattice edge `(a, c)`, `interpolate f` is affine on `[0, 1]`. -/
theorem interpolate_lineMap_of_isUnitEdge (f : Vertex n → ℝ) {a c : Vertex n} (h : IsUnitEdge a c)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    interpolate f (AffineMap.lineMap a.barycentric c.barycentric t) = (1 - t) * f a + t * f c := by
  obtain ⟨T, ha, hc⟩ := exists_cell_of_isUnitEdge h
  obtain ⟨ia, rfl⟩ := UnitTriangle.mem_range_vertex_of_barycentric_mem_cell ha
  obtain ⟨ic, rfl⟩ := UnitTriangle.mem_range_vertex_of_barycentric_mem_cell hc
  rw [interpolate_eq_triangleAffine f (T.convex_cell.lineMap_mem ha hc ht),
    (triangleAffine f T).apply_lineMap, triangleAffine_vertex, triangleAffine_vertex,
    AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]

/-- `interpolate f` is piecewise affine on `barycentricSimplex n` (outside which it uses the
constant fallback `f (cornerA n)`). -/
theorem isPiecewiseAffineOn_interpolate (f : Vertex n → ℝ) :
    IsPiecewiseAffineOn (interpolate f) (barycentricSimplex n) := by
  rcases n with _ | m
  · exact (isPiecewiseAffineOn_continuousAffineMap
      (ContinuousAffineMap.const ℝ _ (f (Vertex.cornerA 0))) _).congr fun _ _ => by simp
  · exact isPiecewiseAffineOn_of_finite (C := UnitTriangle.cell) (A := triangleAffine f)
      (fun T => T.isConvexPolyhedron_cell) (by rw [UnitTriangle.iUnion_cell_eq_barycentricSimplex])
      fun _ _ hx => interpolate_eq_triangleAffine f hx.2
/-- `interpolate f` is piecewise linear (`IsPLOn`) on `barycentricSimplex n`. -/
theorem isPLOn_interpolate (f : Vertex n → ℝ) : IsPLOn (interpolate f) (barycentricSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).isPLOn
/-- `interpolate f` is continuous on `barycentricSimplex n`. -/
theorem continuousOn_interpolate (f : Vertex n → ℝ) :
    ContinuousOn (interpolate f) (barycentricSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).continuousOn

theorem interpolate_add (f g : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate (f + g) x = interpolate f x + interpolate g x := by
  rw [interpolate, interpolate, interpolate]; split_ifs with h <;> [simp [triangleAffine_add]; rfl]
theorem interpolate_smul (c : ℝ) (f : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate (c • f) x = c * interpolate f x := by
  rw [interpolate, interpolate]; split_ifs with h <;> [simp [triangleAffine_smul]; rfl]
theorem interpolate_neg (f : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate (-f) x = -interpolate f x := by simpa using interpolate_smul (-1 : ℝ) f x
theorem interpolate_sub (f g : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate (f - g) x = interpolate f x - interpolate g x := by
  rw [sub_eq_add_neg, interpolate_add, interpolate_neg, sub_eq_add_neg]
@[simp] theorem interpolate_zero (x : Fin 3 → ℝ) : interpolate (0 : Vertex n → ℝ) x = 0 := by
  simpa using interpolate_smul 0 (0 : Vertex n → ℝ) x
@[simp] theorem interpolate_const (c : ℝ) (x : Fin 3 → ℝ) :
    interpolate (fun _ : Vertex n => c) x = c := by
  rw [interpolate]; split_ifs with h
  · exact triangleAffine_const c h.choose
      (mem_barycentricSimplex_iff.mp (h.choose.cell_subset_barycentricSimplex h.choose_spec)).2
  · rfl
theorem interpolate_ofRhombusConcave (f : Vertex n → ℝ) (hf : IsRhombusConcave f) (x : Fin 3 → ℝ) :
    interpolate (ofRhombusConcave f hf) x = interpolate f x - f (Vertex.cornerA n) := by
  rw [show ⇑(ofRhombusConcave f hf) = f - fun _ => f (Vertex.cornerA n)
    from funext fun _ => ofRhombusConcave_apply _ _ _, interpolate_sub, interpolate_const]
theorem interpolate_barycentricLinear (c₀ α β γ : ℝ) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex n) :
    interpolate (barycentricLinear (n := n) c₀ α β γ) x = c₀ + x 0 * α + x 1 * β + x 2 * γ := by
  rcases n with _ | m
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx; subst hx; simp
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex m).symm ▸ hx)
    rw [interpolate_eq_triangleAffine _ hT,
      triangleAffine_barycentricLinear _ _ _ _ T (mem_barycentricSimplex_iff.mp hx).2]
theorem interpolate_affine (β γ : ℝ) {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex n) :
    interpolate (affine n β γ) x = x 1 * β + x 2 * γ := by
  have hcoe : ⇑(affine n β γ) = barycentricLinear 0 0 β γ := funext fun _ => by simp
  simpa [hcoe] using interpolate_barycentricLinear (n := n) (0 : ℝ) 0 β γ hx
theorem interpolate_add_barycentricLinear (f : Vertex n → ℝ) (c₀ α β γ : ℝ) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex n) : interpolate (f + barycentricLinear (n := n) c₀ α β γ) x =
      interpolate f x + (c₀ + x 0 * α + x 1 * β + x 2 * γ) := by
  rw [interpolate_add, interpolate_barycentricLinear _ _ _ _ hx]
/-- Compatibility of `interpolate` with lattice translation by `p : Vertex m`. -/
theorem interpolate_comp_add (f : Vertex (m + k) → ℝ) (p : Vertex m) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex k) :
    interpolate (fun q : Vertex k => f (p.add q)) x = interpolate f (p.barycentric + x) := by
  rcases k with _ | k'
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx; subst hx; simp
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex k').symm ▸ hx)
    rw [interpolate_eq_triangleAffine _ hT,
      interpolate_eq_triangleAffine _ (UnitTriangle.mem_cell_addLeft_iff.mpr hT),
      triangleAffine_addLeft]
/-- Compatibility of `interpolate` with restriction to `h.subtriangle p`. -/
theorem interpolate_subtriangle (h : RealHive (m + k)) (p : Vertex m) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex k) : interpolate (h.subtriangle p) x =
      interpolate h (p.barycentric + x) - h (p.add (Vertex.cornerA k)) := by
  rw [show ⇑(h.subtriangle p) = (fun q => h (p.add q)) - fun _ => h (p.add (Vertex.cornerA k))
    from funext fun _ => subtriangle_apply _ _ _, interpolate_sub,
    interpolate_comp_add h p hx, interpolate_const]
/-- Compatibility of `interpolate` with clockwise rotation on `barycentricSimplex n`. -/
theorem interpolate_comp_rotate (f : Vertex n → ℝ) {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex n) :
    interpolate (fun p => f p.rotate) x = interpolate f (fun k => x (k - 1)) := by
  rcases n with _ | m
  · rw [interpolate_rank_zero, interpolate_rank_zero,
      Subsingleton.elim (Vertex.cornerA 0).rotate (Vertex.cornerA 0)]
  · obtain ⟨T, hT⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex m).symm ▸ hx)
    rw [interpolate_eq_triangleAffine _ hT,
      interpolate_eq_triangleAffine _ (UnitTriangle.mem_cell_rotate_iff.mpr hT),
      triangleAffine_comp_rotate]
/-- Compatibility of `interpolate` with `Hive.rotate` on `barycentricSimplex n`. -/
theorem interpolate_rotate (h : RealHive n) {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex n) :
    interpolate h.rotate x = interpolate h (fun k => x (k - 1)) - h (Vertex.cornerA n).rotate := by
  rw [show ⇑h.rotate = (fun p => h p.rotate) - fun _ => h (Vertex.cornerA n).rotate
    from funext fun _ => rotate_apply _ _, interpolate_sub, interpolate_comp_rotate h hx,
    interpolate_const]
/-- Compatibility of `interpolate` with reflection fixing `A = (n, 0, 0)`. -/
theorem interpolate_comp_reflect (f : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate (fun p => f p.reflect) x = interpolate f (fun k => x (-k)) := by
  by_cases h : ∃ T : UnitTriangle n, x ∈ T.cell
  · obtain ⟨T, hT⟩ := h
    rw [interpolate_eq_triangleAffine _ hT,
      interpolate_eq_triangleAffine _ (UnitTriangle.mem_cell_reflect_iff.mpr hT),
      triangleAffine_comp_reflect]
  · have h' : ¬ ∃ T : UnitTriangle n, (fun k => x (-k)) ∈ T.cell := fun ⟨T, hT⟩ =>
      h ⟨T.reflect, UnitTriangle.mem_cell_reflect_iff.mp (by simpa using hT)⟩
    simp only [interpolate, h, h', ↓reduceDIte, Vertex.reflect_cornerA]
/-- Compatibility of `interpolate` with `Hive.reflect`. -/
theorem interpolate_reflect (h : RealHive n) (x : Fin 3 → ℝ) :
    interpolate h.reflect x = interpolate h (fun k => x (-k)) := by
  rw [coe_reflect]; exact interpolate_comp_reflect h x

/-- Simplicial extension of `f : Vertex n → ℝ` to `EuclideanSpace ℝ (Fin 2)` that is continuous and
piecewise affine on `planarSimplex n`, defined by pulling `interpolate f` back along
`planeInvAffine n`. -/
noncomputable def planarInterpolate (f : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  interpolate f (planeInvAffine n u)

theorem planarInterpolate_def (f : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate f u = interpolate f (planeInvAffine n u) := (rfl)
@[simp] theorem planarInterpolate_plane (f : Vertex n → ℝ) (p : Vertex n) :
    planarInterpolate f p.plane = f p := by simp [planarInterpolate]
theorem planarInterpolate_planeLinear (f : Vertex n → ℝ) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) : planarInterpolate f (planeLinear x) = interpolate f x := by
  rw [planarInterpolate, planeInvAffine_planeLinear hx]
/-- Any function that is affine on every planar unit-triangle cell `planeLinear '' T.cell` and
agrees with `f` on `Vertex.plane` equals `planarInterpolate f` on `planarSimplex n`. -/
theorem eqOn_planarInterpolate_of_affineOn_cell {f : Vertex n → ℝ}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} (hg_vert : ∀ p : Vertex n, g p.plane = f p)
    (hg_aff : ∀ T : UnitTriangle n,
      ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ, EqOn g A (planeLinear '' T.cell)) :
    EqOn g (planarInterpolate f) (planarSimplex n) := fun _ hu => by
  simpa [planarInterpolate_def] using eqOn_interpolate_of_affineOn_cell (f := f)
    (g := g ∘ planeLinear) (fun p => by simp [hg_vert]) (fun T => let ⟨A, hA⟩ := hg_aff T
      ⟨A.comp planeLinear.toLinearMap.toAffineMap, fun x hx => hA ⟨x, hx, rfl⟩⟩)
    (mem_planarSimplex_iff.mp hu)
/-- Outside `planarSimplex n`, `planarInterpolate f` takes the fallback value `f (cornerA n)`. -/
theorem planarInterpolate_of_notMem_planarSimplex (f : Vertex n → ℝ) {u : EuclideanSpace ℝ (Fin 2)}
    (hu : u ∉ planarSimplex n) : planarInterpolate f u = f (Vertex.cornerA n) :=
  interpolate_of_notMem_barycentricSimplex f (mt mem_planarSimplex_iff.mpr hu)
@[simp] theorem planarInterpolate_rank_zero (f : Vertex 0 → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate f u = f (Vertex.cornerA 0) := by simp [planarInterpolate]
/-- Along any unit lattice edge `(a, c)`, `planarInterpolate f` is affine on `[0, 1]`. -/
theorem planarInterpolate_lineMap_of_isUnitEdge (f : Vertex n → ℝ) {a c : Vertex n}
    (h : IsUnitEdge a c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    planarInterpolate f (AffineMap.lineMap a.plane c.plane t) = (1 - t) * f a + t * f c := by
  rw [planarInterpolate, (planeInvAffine n).apply_lineMap, planeInvAffine_plane,
    planeInvAffine_plane, interpolate_lineMap_of_isUnitEdge f h ht]
theorem planarInterpolate_add (f g : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (f + g) u = planarInterpolate f u + planarInterpolate g u :=
  interpolate_add f g (planeInvAffine n u)
theorem planarInterpolate_smul (c : ℝ) (f : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (c • f) u = c * planarInterpolate f u :=
  interpolate_smul c f (planeInvAffine n u)
theorem planarInterpolate_neg (f : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (-f) u = -planarInterpolate f u := interpolate_neg f (planeInvAffine n u)
theorem planarInterpolate_sub (f g : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (f - g) u = planarInterpolate f u - planarInterpolate g u :=
  interpolate_sub f g (planeInvAffine n u)
@[simp] theorem planarInterpolate_zero (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (0 : Vertex n → ℝ) u = 0 := interpolate_zero (planeInvAffine n u)
@[simp] theorem planarInterpolate_const (c : ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (fun _ : Vertex n => c) u = c := interpolate_const c (planeInvAffine n u)
theorem planarInterpolate_ofRhombusConcave (f : Vertex n → ℝ) (hf : IsRhombusConcave f)
    (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate (ofRhombusConcave f hf) u = planarInterpolate f u - f (Vertex.cornerA n) :=
  interpolate_ofRhombusConcave f hf (planeInvAffine n u)
theorem planarInterpolate_affine (β γ : ℝ) {u : EuclideanSpace ℝ (Fin 2)}
    (hu : u ∈ planarSimplex n) :
    planarInterpolate (affine n β γ) u =
      2 * u 1 / Real.sqrt 3 * β + (u 0 - u 1 / Real.sqrt 3) * γ := by
  simpa [planarInterpolate_def] using interpolate_affine (n := n) β γ (mem_planarSimplex_iff.mp hu)
/-- `planarInterpolate f` is piecewise affine on `planarSimplex n` (outside which it uses the
constant fallback `f (cornerA n)`). -/
theorem isPiecewiseAffineOn_planarInterpolate (f : Vertex n → ℝ) :
    IsPiecewiseAffineOn (planarInterpolate f) (planarSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).comp
    (isPiecewiseAffineOn_continuousAffineMap (planeInvAffine n) (planarSimplex n))
    fun _ hu => mem_planarSimplex_iff.mp hu
/-- `planarInterpolate f` is piecewise linear (`IsPLOn`) on `planarSimplex n`. -/
theorem isPLOn_planarInterpolate (f : Vertex n → ℝ) :
    IsPLOn (planarInterpolate f) (planarSimplex n) :=
  (isPiecewiseAffineOn_planarInterpolate f).isPLOn
/-- `planarInterpolate f` is continuous on `planarSimplex n`. -/
theorem continuousOn_planarInterpolate (f : Vertex n → ℝ) :
    ContinuousOn (planarInterpolate f) (planarSimplex n) :=
  (isPiecewiseAffineOn_planarInterpolate f).continuousOn

end TauCeti.Hive
