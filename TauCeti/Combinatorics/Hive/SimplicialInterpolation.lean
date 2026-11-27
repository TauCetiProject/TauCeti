/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Basic
public import TauCeti.Combinatorics.Hive.Interpolation
public import TauCeti.Combinatorics.Hive.UnitTriangle
public import TauCeti.Topology.PL.Map
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Simplicial hive interpolation and zero-sum triangle gradients

Simplicial interpolation on the `n²` unit equilateral triangles (`TauCeti.Hive.UnitTriangle n`)
extends `f : Vertex n → ℝ` to a continuous piecewise-affine function `interpolate f` on
`barycentricSimplex n` (defined by pulling back `TauCeti.Hive.interpolation f` along
`x ↦ (x 1, x 2)`, `interpolate_eq_interpolation`, and via `planarInterpolate f` to
`planarSimplex n ⊆ ℝ²`), agreeing on each unit triangle `T` with
`triangleAffine T f = ∑ i, f (T.vertex i) • T.weight i`. Its finite differences along the
outer-perimeter unit steps `(-1, 1, 0)`, `(0, -1, 1)`, `(1, 0, -1)` form the zero-sum triple
`triangleGradient f T` over any additive abelian group (matching the directional derivatives of
`triangleAffine T f` when `R = ℝ`); across the shared edge of `down s` and `adjacentUp s i`, the
`(i + 1)`-coordinate is constant while the `i`-th jumps by the rhombus slack.

## Main definitions and results

* `TauCeti.Hive.triangleGradient`, `TauCeti.Hive.triangleAffine`, `TauCeti.Hive.interpolate`,
  `TauCeti.Hive.planarInterpolate`.
* `TauCeti.Hive.triangleGradient_adjacentUp_add_one`,
  `TauCeti.Hive.triangleGradient_adjacentUp_sub_down_self`,
  `TauCeti.Hive.triangleGradient_up_edgePoint`, `TauCeti.Hive.isRhombusConcave_iff_adjacent`.
* `TauCeti.Hive.eq_triangleAffine_of_vertex`, `TauCeti.Hive.eqOn_interpolate_of_affineOn_cell`,
  `TauCeti.Hive.eqOn_planarInterpolate_of_affineOn_cell`.
* `TauCeti.Hive.triangleAffine_contLinear_unitStepVec`,
  `TauCeti.Hive.interpolate_eq_interpolation`,
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
`B → C` (`s = 1`, `(0, -1, 1)`), and `C → A` (`s = 2`, `(1, 0, -1)`), bundled as an `S`-linear
map in `f`. Both upward and downward vertex cycles `vertex 0 → vertex 1 → vertex 2` run
clockwise in the plane: on `up b`, each edge `vertex s → vertex (s + 1)` matches the `s`-th
perimeter direction (`f (vertex (s + 1)) - f (vertex s)`); on `down b`, each indexed edge
`vertex s → vertex (s + 1)` points opposite to the `s`-th perimeter direction, giving
`f (vertex s) - f (vertex (s + 1))`. -/
def triangleGradient (S : Type*) {n : ℕ} {R : Type*} [Semiring S] [AddCommGroup R]
    [Module S R] : (Vertex n → R) →ₗ[S] (UnitTriangle n → Fin 3 → R) :=
  LinearMap.pi fun T => LinearMap.pi fun s => match T with
    | .up b => LinearMap.proj (R := S) (φ := fun _ => R) ((UnitTriangle.up b).vertex (s + 1)) -
        LinearMap.proj (R := S) (φ := fun _ => R) ((UnitTriangle.up b).vertex s)
    | .down b => LinearMap.proj (R := S) (φ := fun _ => R) ((UnitTriangle.down b).vertex s) -
        LinearMap.proj (R := S) (φ := fun _ => R) ((UnitTriangle.down b).vertex (s + 1))

@[simp] theorem triangleGradient_up (S : Type*) [Semiring S] [Module S R]
    (f : Vertex (m + 1) → R) (b : Vertex m) (s : Fin 3) :
    triangleGradient S f (UnitTriangle.up b) s =
      f ((UnitTriangle.up b).vertex (s + 1)) - f ((UnitTriangle.up b).vertex s) := by
  simp [triangleGradient]
@[simp] theorem triangleGradient_down (S : Type*) [Semiring S] [Module S R]
    (f : Vertex (m + 2) → R) (b : Vertex m) (s : Fin 3) :
    triangleGradient S f (UnitTriangle.down b) s =
      f ((UnitTriangle.down b).vertex s) - f ((UnitTriangle.down b).vertex (s + 1)) := by
  simp [triangleGradient]
@[simp] theorem sum_triangleGradient (S : Type*) [Semiring S] [Module S R]
    (f : Vertex n → R) (T : UnitTriangle n) :
    ∑ s : Fin 3, triangleGradient S f T s = 0 := by
  have h1 : (0 : Fin 3) + 1 = 1 := rfl
  have h2 : (1 : Fin 3) + 1 = 2 := rfl
  have h3 : (2 : Fin 3) + 1 = 0 := rfl
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, Fin.sum_univ_three,
    h1, h2, h3] <;> abel
@[simp] theorem triangleGradient_const (S : Type*) [Semiring S] [Module S R]
    (c : R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient S (fun _ : Vertex n => c) T s = 0 := by cases T <;> simp
theorem triangleGradient_comp (S : Type*) {R' F : Type*} [Semiring S] [AddCommGroup R']
    [Module S R'] [FunLike F R R'] [AddMonoidHomClass F R R'] (φ : F) (f : Vertex n → R)
    (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient S (φ ∘ f) T s = φ (triangleGradient ℤ f T s) := by cases T <;> simp
@[simp] theorem triangleGradient_map (S : Type*) [Preorder R] {R' : Type*} [AddCommGroup R']
    [Preorder R'] [Semiring S] [Module S R'] (φ : R →+o R') (h : Hive n R)
    (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient S (h.map φ) T s = φ (triangleGradient ℤ h T s) := by cases T <;> simp
@[simp] theorem triangleGradient_ofInt (S R : Type*) [Semiring S] [Ring R] [PartialOrder R]
    [IsOrderedRing R] [Module S R] (h : IntegerHive n) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient S (ofInt R h) T s = ((triangleGradient ℤ h T s : ℤ) : R) := by
  cases T <;> simp
@[simp high] theorem triangleGradient_barycentricLinear (S : Type*) [Semiring S] [Module S R]
    (c₀ α β γ : R) (T : UnitTriangle n) :
    triangleGradient S (barycentricLinear c₀ α β γ) T = ![β - α, γ - β, α - γ] := by
  ext s; cases T <;> fin_cases s <;> simp [add_nsmul] <;> abel
@[simp high] theorem triangleGradient_affine (S : Type*) [Preorder R] [Semiring S] [Module S R]
    (β γ : R) (T : UnitTriangle n) :
    triangleGradient S (affine n β γ) T = ![β, γ - β, -γ] := by
  ext s; cases T <;> fin_cases s <;> simp [add_nsmul] <;> abel
theorem triangleGradient_comp_add (S : Type*) [Semiring S] [Module S R]
    (f : Vertex (m + k) → R) (p : Vertex m) (T : UnitTriangle k) (s : Fin 3) :
    triangleGradient S (fun q => f (p.add q)) T s = triangleGradient S f (T.addLeft p) s := by
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, UnitTriangle.addLeft_up,
    UnitTriangle.addLeft_down, ← UnitTriangle.vertex_addLeft]
@[simp] theorem triangleGradient_subtriangle (S : Type*) [Preorder R] [IsOrderedAddMonoid R]
    [Semiring S] [Module S R] (h : Hive (m + k) R) (p : Vertex m) (T : UnitTriangle k)
    (s : Fin 3) :
    triangleGradient S (h.subtriangle p) T s = triangleGradient S h (T.addLeft p) s := by
  rw [coe_subtriangle, ← Pi.sub_def, map_sub]
  simp [triangleGradient_comp_add]
theorem triangleGradient_comp_rotate (S : Type*) [Semiring S] [Module S R]
    (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient S (fun p => f p.rotate) T s = triangleGradient S f T.rotate (s + 1) := by
  cases T <;> simp
@[simp] theorem triangleGradient_rotate (S : Type*) [Preorder R] [IsOrderedAddMonoid R]
    [Semiring S] [Module S R] (h : Hive n R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient S h.rotate T s = triangleGradient S h T.rotate (s + 1) := by
  rw [coe_rotate, ← Pi.sub_def, map_sub]
  simp [triangleGradient_comp_rotate]
theorem triangleGradient_comp_reflect (S : Type*) [Semiring S] [Module S R]
    (f : Vertex n → R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient S (fun p => f p.reflect) T s = -triangleGradient S f T.reflect s.rev := by
  have h1 : -(s + 1) = s.rev := by fin_cases s <;> rfl
  have h2 : -s = s.rev + 1 := by fin_cases s <;> rfl
  cases T <;> simp only [triangleGradient_up, triangleGradient_down, UnitTriangle.reflect_up,
    UnitTriangle.reflect_down, ← UnitTriangle.vertex_reflect, h1, h2] <;> abel
@[simp] theorem triangleGradient_reflect (S : Type*) [Preorder R] [Semiring S] [Module S R]
    (h : Hive n R) (T : UnitTriangle n) (s : Fin 3) :
    triangleGradient S h.reflect T s = -triangleGradient S h T.reflect s.rev := by
  rw [coe_reflect]; exact triangleGradient_comp_reflect S h T s
@[simp] theorem triangleGradient_adjacentUp (S : Type*) [Semiring S] [Module S R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i j : Fin 3) :
    triangleGradient S f (adjacentUp s i) j =
      f ((adjacentUp s i).vertex (j + 1)) - f ((adjacentUp s i).vertex j) := by
  rw [adjacentUp_def, triangleGradient_up, ← adjacentUp_def]

/-- Across the shared edge of `down s` and `adjacentUp s i` opposite `(down s).vertex i`, the
`(i + 1)`-coordinate of `triangleGradient` is constant. -/
theorem triangleGradient_adjacentUp_add_one (S : Type*) [Semiring S] [Module S R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i : Fin 3) :
    triangleGradient S f (adjacentUp s i) (i + 1) =
      triangleGradient S f (UnitTriangle.down s) (i + 1) := by
  rw [triangleGradient_adjacentUp, triangleGradient_down, (by fin_cases i <;> rfl : i + 1 + 1 =
    i + 2), vertex_adjacentUp_add_two, vertex_adjacentUp_add_one]
/-- Across the shared edge of `down s` and `adjacentUp s i` opposite `(down s).vertex i`, the
`i`-th coordinate of `triangleGradient` jumps by the unit-rhombus slack. -/
theorem triangleGradient_adjacentUp_sub_down_self (S : Type*) [Semiring S] [Module S R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i : Fin 3) :
    triangleGradient S f (adjacentUp s i) i - triangleGradient S f (UnitTriangle.down s) i =
      rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  rw [triangleGradient_adjacentUp, triangleGradient_down, rhombusSlack_def,
    vertex_adjacentUp_add_one]; abel
/-- Across the shared edge of `down s` and `adjacentUp s i` opposite `(down s).vertex i`, the
`(i + 2)`-th coordinate of `triangleGradient` jumps by minus the unit-rhombus slack. -/
theorem triangleGradient_adjacentUp_sub_down_add_two (S : Type*) [Semiring S] [Module S R]
    (f : Vertex (m + 2) → R) (s : Vertex m) (i : Fin 3) :
    triangleGradient S f (adjacentUp s i) (i + 2) -
        triangleGradient S f (UnitTriangle.down s) (i + 2) =
      -rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  rw [triangleGradient_adjacentUp, triangleGradient_down, (by fin_cases i <;> rfl : i + 2 + 1 = i),
    rhombusSlack_def, vertex_adjacentUp_add_two]; abel

/-- At size `m + 2`, rhombus concavity over any ordered additive abelian group is completely
determined by the unit rhombi `isRhombus_adjacent s i` across shared interior unit edges. -/
theorem isRhombusConcave_iff_adjacent [Preorder R] [IsOrderedAddMonoid R]
    (f : Vertex (m + 2) → R) :
    IsRhombusConcave f ↔ ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  rw [isRhombusConcave_iff_rhombusSlack_nonneg]
  refine ⟨fun hf s i => hf (isRhombus_adjacent s i), fun hadj a b c d hr => ?_⟩
  obtain ⟨s, i, hac, hbd⟩ := hr.exists_adjacentUp
  rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hbd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simpa [rhombusSlack_def, add_comm] using hadj s i

/-- Along side `s` of the perimeter, the `s`-th coordinate of `triangleGradient` on the upward
perimeter triangle `up (edgePoint m s i)` equals `boundaryLinear S (m + 1) R f s i`. -/
theorem triangleGradient_up_edgePoint (S : Type*) [Semiring S] [Module S R]
    (f : Vertex (m + 1) → R) (s : Fin 3) (i : Fin (m + 1)) :
    triangleGradient S f (UnitTriangle.up (Vertex.edgePoint m s i)) s =
      boundaryLinear S (m + 1) R f s i := by
  fin_cases s <;> rw [triangleGradient_up, boundaryLinear_apply] <;>
    congr 2 <;> ext <;> simp <;> omega
/-- At size `1`, the zero-sum gradient of the unique unit triangle equals the clockwise boundary
`(λ₁, μ₁, ν₁)` of `f`. -/
theorem triangleGradient_up_cornerA_zero (S : Type*) [Semiring S] [Module S R]
    (f : Vertex 1 → R) (s : Fin 3) :
    triangleGradient S f (UnitTriangle.up (Vertex.cornerA 0)) s =
      boundaryLinear S 1 R f s 0 := by
  rw [Subsingleton.elim (Vertex.cornerA 0) (Vertex.edgePoint 0 s 0), triangleGradient_up_edgePoint]

end

/-! ### Simplicial affine pieces and continuous piecewise-affine interpolation -/

/-- Continuous affine extension of `f : Vertex n → ℝ` on a unit triangle `T : UnitTriangle n`,
bundled as a linear map in `f`. -/
noncomputable def triangleAffine (T : UnitTriangle n) :
    (Vertex n → ℝ) →ₗ[ℝ] ((Fin 3 → ℝ) →ᴬ[ℝ] ℝ) :=
  (Fintype.linearCombination ℝ T.weight).comp (LinearMap.funLeft ℝ ℝ T.vertex)

theorem triangleAffine_apply (T : UnitTriangle n) (f : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    triangleAffine T f x = ∑ i : Fin 3, f (T.vertex i) * T.weight i x := by
  simp [triangleAffine, Fintype.linearCombination_apply, Fin.sum_univ_three]
theorem triangleAffine_const (c : ℝ) (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) : triangleAffine T (fun _ : Vertex n => c) x = c := by
  rw [triangleAffine_apply, ← Finset.mul_sum, T.sum_weight hx, mul_one]
theorem triangleAffine_ofRhombusConcave (f : Vertex n → ℝ) (hf : IsRhombusConcave f)
    (T : UnitTriangle n) {x : Fin 3 → ℝ} (hx : ∑ i, x i = (n : ℝ)) :
    triangleAffine T (ofRhombusConcave f hf) x = triangleAffine T f x - f (Vertex.cornerA n) := by
  rw [coe_ofRhombusConcave, ← Pi.sub_def, map_sub,
    ContinuousAffineMap.sub_apply, triangleAffine_const _ T hx]
theorem triangleAffine_addLeft (f : Vertex (m + n) → ℝ) (p : Vertex m) (T : UnitTriangle n)
    (x : Fin 3 → ℝ) : triangleAffine (T.addLeft p) f (p.barycentric + x) =
      triangleAffine T (fun q => f (p.add q)) x := by
  simp [triangleAffine_apply, UnitTriangle.vertex_addLeft, UnitTriangle.weight_addLeft_apply]
theorem triangleAffine_subtriangle (h : RealHive (m + k)) (p : Vertex m) (T : UnitTriangle k)
    {x : Fin 3 → ℝ} (hx : ∑ i, x i = (k : ℝ)) : triangleAffine T (h.subtriangle p) x =
      triangleAffine (T.addLeft p) h (p.barycentric + x) - h (p.add (Vertex.cornerA k)) := by
  rw [coe_subtriangle, ← Pi.sub_def, map_sub,
    ContinuousAffineMap.sub_apply, ← triangleAffine_addLeft, triangleAffine_const _ T hx]
theorem triangleAffine_comp_rotate (f : Vertex n → ℝ) (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine T (fun p => f p.rotate) x = triangleAffine T.rotate f (fun k => x (k - 1)) := by
  simp only [triangleAffine_apply]
  exact Fintype.sum_equiv (Equiv.addRight (1 : Fin 3)) _ _ fun i => by
    simp [UnitTriangle.vertex_rotate, UnitTriangle.weight_rotate_apply]
theorem triangleAffine_rotate (h : RealHive n) (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) : triangleAffine T h.rotate x =
      triangleAffine T.rotate h (fun k => x (k - 1)) - h (Vertex.cornerA n).rotate := by
  rw [coe_rotate, ← Pi.sub_def, map_sub, ContinuousAffineMap.sub_apply,
    triangleAffine_comp_rotate, triangleAffine_const _ T hx]
theorem triangleAffine_comp_reflect (f : Vertex n → ℝ) (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine T (fun p => f p.reflect) x = triangleAffine T.reflect f (fun k => x (-k)) := by
  simp only [triangleAffine_apply]
  exact Fintype.sum_equiv (Equiv.neg (Fin 3)) _ _ fun i => by
    rw [Equiv.neg_apply, UnitTriangle.vertex_reflect, UnitTriangle.weight_reflect_apply]
theorem triangleAffine_reflect (h : RealHive n) (T : UnitTriangle n) (x : Fin 3 → ℝ) :
    triangleAffine T h.reflect x = triangleAffine T.reflect h (fun k => x (-k)) := by
  rw [coe_reflect]; exact triangleAffine_comp_reflect h T x
@[simp] theorem triangleAffine_vertex (f : Vertex n → ℝ) (T : UnitTriangle n) (i : Fin 3) :
    triangleAffine T f (T.vertex i).barycentric = f (T.vertex i) := by
  rw [triangleAffine_apply]; fin_cases i <;> simp
/-- Any affine map agreeing with `f` on the vertices of `T` equals `triangleAffine T f` on the
hyperplane `{x | ∑ i, x i = n}`. -/
theorem eq_triangleAffine_of_vertex {f : Vertex n → ℝ} {T : UnitTriangle n}
    {A : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ} (hA : ∀ i, A (T.vertex i).barycentric = f (T.vertex i))
    {x : Fin 3 → ℝ} (hx : ∑ i, x i = (n : ℝ)) : A x = triangleAffine T f x := by
  have hw := T.sum_weight hx
  have h := (Finset.univ.map_affineCombination (fun i => (T.vertex i).barycentric)
    (fun i => T.weight i x) hw A).symm
  simp only [Finset.affineCombination_eq_linear_combination _ _ _ hw,
    T.sum_weight_smul_vertex hx] at h
  rw [← h]
  simp [triangleAffine_apply, hA, mul_comm]
/-- Any affine map agreeing with `f` on the vertices of `T` agrees with `triangleAffine T f` on
`T.cell`. -/
theorem eqOn_triangleAffine_of_vertex {f : Vertex n → ℝ} {T : UnitTriangle n}
    {A : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ} (hA : ∀ i, A (T.vertex i).barycentric = f (T.vertex i)) :
    EqOn A (triangleAffine T f) T.cell := fun _ hx => eq_triangleAffine_of_vertex hA
  (mem_barycentricSimplex_iff.mp (T.cell_subset_barycentricSimplex hx)).2
theorem triangleAffine_barycentricLinear (c₀ α β γ : ℝ) (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) :
    triangleAffine T (barycentricLinear c₀ α β γ) x = c₀ + x 0 * α + x 1 * β + x 2 * γ := by
  let p (i : Fin 3) : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj i).toContinuousAffineMap
  let A := ContinuousAffineMap.const ℝ _ c₀ + α • p 0 + β • p 1 + γ • p 2
  simpa [A, p, mul_comm] using (eq_triangleAffine_of_vertex (A := A.toAffineMap)
    (fun i => by simp [A, p, mul_comm]) hx).symm
theorem triangleAffine_affine (β γ : ℝ) (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) : triangleAffine T (affine n β γ) x = x 1 * β + x 2 * γ := by
  let p (i : Fin 3) : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj i).toContinuousAffineMap
  simpa [p, mul_comm] using (eq_triangleAffine_of_vertex (A := (β • p 1 + γ • p 2).toAffineMap)
    (fun i => by simp [p, mul_comm]) hx).symm

/-- The `s`-th clockwise perimeter unit-step vector `(-1, 1, 0)`, `(0, -1, 1)`, `(1, 0, -1)`. -/
def unitStepVec (s : Fin 3) : Fin 3 → ℝ := Pi.single (s + 1) (1 : ℝ) - Pi.single s 1

@[simp] theorem unitStepVec_apply (s k : Fin 3) :
    unitStepVec s k = (if k = s + 1 then 1 else 0) - (if k = s then 1 else 0) := by
  simp [unitStepVec, Pi.single_apply]
theorem sum_unitStepVec (s : Fin 3) : ∑ i : Fin 3, unitStepVec s i = 0 := by
  simp [unitStepVec, Finset.sum_pi_single']

/-- The directional derivative of `triangleAffine T f` along `unitStepVec s` equals the
combinatorial edge slope `triangleGradient ℝ f T s`. -/
@[simp] theorem triangleAffine_contLinear_unitStepVec (f : Vertex n → ℝ) (T : UnitTriangle n)
    (s : Fin 3) : (triangleAffine T f).contLinear (unitStepVec s) = triangleGradient ℝ f T s := by
  cases T <;> fin_cases s <;>
    simp [triangleAffine, Fintype.linearCombination_apply, Fin.sum_univ_three] <;> ring

private noncomputable def interpolateFun (f : Vertex n → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  open Classical in
  if x ∈ barycentricSimplex n then interpolation f (x 1, x 2) else f (Vertex.cornerA n)

private theorem interpolateFun_eq_triangleAffine (f : Vertex n → ℝ) {T : UnitTriangle n}
    {x : Fin 3 → ℝ} (hx : x ∈ T.cell) : interpolateFun f x = triangleAffine T f x := by
  have hxS := T.cell_subset_barycentricSimplex hx
  simp only [interpolateFun, hxS, ↓reduceIte]
  have hsum : x 0 + x 1 + x 2 = (n : ℝ) := by
    simpa [Fin.sum_univ_three, add_assoc] using (mem_barycentricSimplex_iff.mp hxS).2
  cases T with
  | up b =>
    have hq : ((UnitTriangle.up b).vertex 1).yz = ((UnitTriangle.up b).vertex 0).yz + (1, 0) := by
      ext <;> simp
    have hr : ((UnitTriangle.up b).vertex 2).yz = ((UnitTriangle.up b).vertex 0).yz + (0, 1) := by
      ext <;> simp
    have hx0 : 0 ≤ x 0 - (b.x : ℝ) := by simpa using (UnitTriangle.up b).weight_nonneg hx 0
    have hx1 : 0 ≤ x 1 - (b.y : ℝ) := by simpa using (UnitTriangle.up b).weight_nonneg hx 1
    have hx2 : 0 ≤ x 2 - (b.z : ℝ) := by simpa using (UnitTriangle.up b).weight_nonneg hx 2
    have hb_sum := congrArg (Nat.cast (R := ℝ)) b.sum_eq
    push_cast at hb_sum hsum
    have hle : (x 1 - (b.y : ℝ)) + (x 2 - (b.z : ℝ)) ≤ 1 := by linarith
    have hint := interpolation_up f hq hr hx1 hx2 hle
    have hx_eq : ((((UnitTriangle.up b).vertex 0).y : ℝ) + (x 1 - (b.y : ℝ)),
        (((UnitTriangle.up b).vertex 0).z : ℝ) + (x 2 - (b.z : ℝ))) = (x 1, x 2) := by
      ext <;> simp
    rw [hx_eq] at hint
    rw [hint, triangleAffine_apply, Fin.sum_univ_three]
    simp only [UnitTriangle.weight_up_apply, Vertex.coord_zero, Vertex.coord_one,
      Vertex.coord_two]
    have hdiff : 1 - (x 1 - (b.y : ℝ)) - (x 2 - (b.z : ℝ)) = x 0 - (b.x : ℝ) := by linarith
    rw [hdiff]; ring
  | down b =>
    have hq : ((UnitTriangle.down b).vertex 1).yz =
        ((UnitTriangle.down b).vertex 0).yz + (-1, 0) := by
      ext <;> simp
    have hr : ((UnitTriangle.down b).vertex 2).yz =
        ((UnitTriangle.down b).vertex 0).yz + (0, -1) := by
      ext <;> simp
    have hx0 : 0 ≤ (b.x : ℝ) + 1 - x 0 := by simpa using (UnitTriangle.down b).weight_nonneg hx 0
    have hx1 : 0 ≤ (b.y : ℝ) + 1 - x 1 := by simpa using (UnitTriangle.down b).weight_nonneg hx 1
    have hx2 : 0 ≤ (b.z : ℝ) + 1 - x 2 := by simpa using (UnitTriangle.down b).weight_nonneg hx 2
    have hb_sum := congrArg (Nat.cast (R := ℝ)) b.sum_eq
    push_cast at hb_sum hsum
    have hle : ((b.y : ℝ) + 1 - x 1) + ((b.z : ℝ) + 1 - x 2) ≤ 1 := by linarith
    have hint := interpolation_down f hq hr hx1 hx2 hle
    have hx_eq : ((((UnitTriangle.down b).vertex 0).y : ℝ) - ((b.y : ℝ) + 1 - x 1),
        (((UnitTriangle.down b).vertex 0).z : ℝ) - ((b.z : ℝ) + 1 - x 2)) = (x 1, x 2) := by
      ext <;> simp
    rw [hx_eq] at hint
    rw [hint, triangleAffine_apply, Fin.sum_univ_three]
    simp only [UnitTriangle.weight_down_apply, Vertex.coord_zero, Vertex.coord_one,
      Vertex.coord_two]
    have hdiff : 1 - ((b.y : ℝ) + 1 - x 1) - ((b.z : ℝ) + 1 - x 2) = (b.x : ℝ) + 1 - x 0 := by
      linarith
    rw [hdiff]; ring

private theorem exists_linearMap_interpolateFun (n : ℕ) (x : Fin 3 → ℝ) :
    ∃ L : (Vertex n → ℝ) →ₗ[ℝ] ℝ, ∀ f : Vertex n → ℝ, interpolateFun f x = L f := by
  by_cases hx : x ∈ barycentricSimplex n
  · rcases n with _ | m
    · rw [barycentricSimplex_zero, mem_singleton_iff] at hx
      refine ⟨LinearMap.proj (Vertex.cornerA 0), fun f => ?_⟩
      simpa [interpolateFun, hx] using interpolation_vertex f (Vertex.cornerA 0)
    · obtain ⟨T, hT⟩ := UnitTriangle.exists_mem_cell hx
      refine ⟨{ toFun := fun f => triangleAffine T f x
                map_add' := fun f g => by simp
                map_smul' := fun c f => by simp },
        fun f => interpolateFun_eq_triangleAffine f hT⟩
  · refine ⟨LinearMap.proj (Vertex.cornerA n), fun f => ?_⟩
    simp [interpolateFun, hx]

/-- Simplicial extension of `f : Vertex n → ℝ` to `Fin 3 → ℝ`, agreeing with
`TauCeti.Hive.interpolation f (x 1, x 2)` (and with `triangleAffine T f` on each cell `T.cell`)
on `barycentricSimplex n` and taking fallback value `f (cornerA n)` outside `barycentricSimplex n`
(and for `n = 0`), bundled as a linear map in `f`. -/
noncomputable def interpolate {n : ℕ} : (Vertex n → ℝ) →ₗ[ℝ] ((Fin 3 → ℝ) → ℝ) where
  toFun := interpolateFun
  map_add' f g := funext fun x => by
    obtain ⟨L, hL⟩ := exists_linearMap_interpolateFun n x
    simp [hL]
  map_smul' c f := funext fun x => by
    obtain ⟨L, hL⟩ := exists_linearMap_interpolateFun n x
    simp [hL]

/-- On `barycentricSimplex n`, the simplicial interpolation `interpolate f` agrees with the
`(y, z)`-chart interpolation `interpolation f` under the coordinate projection `x ↦ (x 1, x 2)`. -/
theorem interpolate_eq_interpolation (f : Vertex n → ℝ) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex n) :
    interpolate f x = interpolation f (x 1, x 2) := by simp [interpolate, interpolateFun, hx]
theorem interpolate_eq_triangleAffine (f : Vertex n → ℝ) {T : UnitTriangle n} {x : Fin 3 → ℝ}
    (hx : x ∈ T.cell) : interpolate f x = triangleAffine T f x :=
  interpolateFun_eq_triangleAffine f hx
/-- Two unit triangles whose cells both contain `x` assign the same affine value at `x`. -/
theorem triangleAffine_eq_of_mem_cell (f : Vertex n → ℝ) {T₁ T₂ : UnitTriangle n} {x : Fin 3 → ℝ}
    (hx₁ : x ∈ T₁.cell) (hx₂ : x ∈ T₂.cell) : triangleAffine T₁ f x = triangleAffine T₂ f x :=
  (interpolate_eq_triangleAffine f hx₁).symm.trans (interpolate_eq_triangleAffine f hx₂)
/-- Outside `barycentricSimplex n`, `interpolate f` takes the fallback value `f (cornerA n)`. -/
theorem interpolate_of_notMem_barycentricSimplex (f : Vertex n → ℝ) {x : Fin 3 → ℝ}
    (hx : x ∉ barycentricSimplex n) : interpolate f x = f (Vertex.cornerA n) := by
  simp [interpolate, interpolateFun, hx]
@[simp] theorem interpolate_rank_zero (f : Vertex 0 → ℝ) (x : Fin 3 → ℝ) :
    interpolate f x = f (Vertex.cornerA 0) := by
  by_cases hx : x ∈ barycentricSimplex 0
  · rw [interpolate_eq_interpolation f hx]
    rw [barycentricSimplex_zero, mem_singleton_iff] at hx
    subst hx
    simpa using interpolation_vertex f (Vertex.cornerA 0)
  · exact interpolate_of_notMem_barycentricSimplex f hx
/-- `interpolate f` extends `f` from the lattice vertices `Vertex n` via `Vertex.barycentric`. -/
@[simp] theorem interpolate_barycentric (f : Vertex n → ℝ) (p : Vertex n) :
    interpolate f p.barycentric = f p := by
  rw [interpolate_eq_interpolation f (barycentric_mem_barycentricSimplex p)]
  simp
/-- Any function that is affine on every unit-triangle cell and agrees with `f` on lattice vertices
equals `interpolate f` on `barycentricSimplex n`. -/
theorem eqOn_interpolate_of_affineOn_cell {f : Vertex n → ℝ} {g : (Fin 3 → ℝ) → ℝ}
    (hg_vert : ∀ p : Vertex n, g p.barycentric = f p)
    (hg_aff : ∀ T : UnitTriangle n, ∃ A : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ, EqOn g A T.cell) :
    EqOn g (interpolate f) (barycentricSimplex n) := fun x hx => by
  rcases n with _ | m
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx
    rw [hx, ← Vertex.barycentric_cornerA_zero, hg_vert, interpolate_rank_zero]
  · obtain ⟨T, hT⟩ := UnitTriangle.exists_mem_cell hx
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
    (triangleAffine T f).apply_lineMap, triangleAffine_vertex, triangleAffine_vertex,
    AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]

/-- `interpolate f` is piecewise affine on `barycentricSimplex n` (outside which it uses the
constant fallback `f (cornerA n)`). -/
theorem isPiecewiseAffineOn_interpolate (f : Vertex n → ℝ) :
    IsPiecewiseAffineOn (interpolate f) (barycentricSimplex n) := by
  rcases n with _ | m
  · exact (isPiecewiseAffineOn_continuousAffineMap
      (ContinuousAffineMap.const ℝ _ (f (Vertex.cornerA 0))) _).congr fun _ _ => by simp
  · exact isPiecewiseAffineOn_of_finite (C := UnitTriangle.cell) (A := fun T => triangleAffine T f)
      (fun T => T.isConvexPolyhedron_cell) (by rw [UnitTriangle.iUnion_cell_eq_barycentricSimplex])
      fun _ _ hx => interpolate_eq_triangleAffine f hx.2
/-- `interpolate f` is piecewise linear (`IsPLOn`) on `barycentricSimplex n`. -/
theorem isPLOn_interpolate (f : Vertex n → ℝ) : IsPLOn (interpolate f) (barycentricSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).isPLOn
/-- `interpolate f` is continuous on `barycentricSimplex n`. -/
theorem continuousOn_interpolate (f : Vertex n → ℝ) :
    ContinuousOn (interpolate f) (barycentricSimplex n) :=
  (isPiecewiseAffineOn_interpolate f).continuousOn

@[simp] theorem interpolate_const (c : ℝ) (x : Fin 3 → ℝ) :
    interpolate (fun _ : Vertex n => c) x = c := by
  by_cases hx : x ∈ barycentricSimplex n
  · rcases n with _ | m
    · simp
    · obtain ⟨T, hT⟩ := UnitTriangle.exists_mem_cell hx
      rw [interpolate_eq_triangleAffine _ hT]
      exact triangleAffine_const c T (mem_barycentricSimplex_iff.mp hx).2
  · exact interpolate_of_notMem_barycentricSimplex _ hx
theorem interpolate_ofRhombusConcave (f : Vertex n → ℝ) (hf : IsRhombusConcave f) (x : Fin 3 → ℝ) :
    interpolate (ofRhombusConcave f hf) x = interpolate f x - f (Vertex.cornerA n) := by
  rw [coe_ofRhombusConcave, ← Pi.sub_def, map_sub, Pi.sub_apply, interpolate_const]
theorem interpolate_barycentricLinear (c₀ α β γ : ℝ) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex n) :
    interpolate (barycentricLinear (n := n) c₀ α β γ) x = c₀ + x 0 * α + x 1 * β + x 2 * γ := by
  rcases n with _ | m
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx; subst hx; simp
  · obtain ⟨T, hT⟩ := UnitTriangle.exists_mem_cell hx
    rw [interpolate_eq_triangleAffine _ hT,
      triangleAffine_barycentricLinear _ _ _ _ T (mem_barycentricSimplex_iff.mp hx).2]
theorem interpolate_affine (β γ : ℝ) {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex n) :
    interpolate (affine n β γ) x = x 1 * β + x 2 * γ := by
  rcases n with _ | m
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx; subst hx; simp
  · obtain ⟨T, hT⟩ := UnitTriangle.exists_mem_cell hx
    rw [interpolate_eq_triangleAffine _ hT,
      triangleAffine_affine _ _ T (mem_barycentricSimplex_iff.mp hx).2]
/-- Compatibility of `interpolate` with lattice translation by `p : Vertex m`. -/
theorem interpolate_comp_add (f : Vertex (m + k) → ℝ) (p : Vertex m) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex k) :
    interpolate (fun q : Vertex k => f (p.add q)) x = interpolate f (p.barycentric + x) := by
  rcases k with _ | k'
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx; subst hx; simp
  · obtain ⟨T, hT⟩ := UnitTriangle.exists_mem_cell hx
    rw [interpolate_eq_triangleAffine _ hT,
      interpolate_eq_triangleAffine _ (UnitTriangle.mem_cell_addLeft_iff.mpr hT),
      triangleAffine_addLeft]
/-- Compatibility of `interpolate` with restriction to `h.subtriangle p`. -/
theorem interpolate_subtriangle (h : RealHive (m + k)) (p : Vertex m) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex k) : interpolate (h.subtriangle p) x =
      interpolate h (p.barycentric + x) - h (p.add (Vertex.cornerA k)) := by
  rw [coe_subtriangle, ← Pi.sub_def, map_sub, Pi.sub_apply,
    interpolate_comp_add h p hx, interpolate_const]
/-- Compatibility of `interpolate` with clockwise rotation on `barycentricSimplex n`. -/
theorem interpolate_comp_rotate (f : Vertex n → ℝ) {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex n) :
    interpolate (fun p => f p.rotate) x = interpolate f (fun k => x (k - 1)) := by
  rcases n with _ | m
  · rw [interpolate_rank_zero, interpolate_rank_zero,
      Subsingleton.elim (Vertex.cornerA 0).rotate (Vertex.cornerA 0)]
  · obtain ⟨T, hT⟩ := UnitTriangle.exists_mem_cell hx
    rw [interpolate_eq_triangleAffine _ hT,
      interpolate_eq_triangleAffine _ (UnitTriangle.mem_cell_rotate_iff.mpr hT),
      triangleAffine_comp_rotate]
/-- Compatibility of `interpolate` with `Hive.rotate` on `barycentricSimplex n`. -/
theorem interpolate_rotate (h : RealHive n) {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex n) :
    interpolate h.rotate x = interpolate h (fun k => x (k - 1)) - h (Vertex.cornerA n).rotate := by
  rw [coe_rotate, ← Pi.sub_def, map_sub, Pi.sub_apply, interpolate_comp_rotate h hx,
    interpolate_const]
/-- Compatibility of `interpolate` with reflection fixing `A = (n, 0, 0)`. -/
theorem interpolate_comp_reflect (f : Vertex n → ℝ) (x : Fin 3 → ℝ) :
    interpolate (fun p => f p.reflect) x = interpolate f (fun k => x (-k)) := by
  by_cases hx : x ∈ barycentricSimplex n
  · rcases n with _ | m
    · simp [Vertex.reflect_cornerA]
    · obtain ⟨T, hT⟩ := UnitTriangle.exists_mem_cell hx
      rw [interpolate_eq_triangleAffine _ hT,
        interpolate_eq_triangleAffine _ (UnitTriangle.mem_cell_reflect_iff.mpr hT),
        triangleAffine_comp_reflect]
  · have hx' : (fun k => x (-k)) ∉ barycentricSimplex n :=
      mt reflect_mem_barycentricSimplex_iff.mp hx
    rw [interpolate_of_notMem_barycentricSimplex _ hx,
      interpolate_of_notMem_barycentricSimplex _ hx', Vertex.reflect_cornerA]
/-- Compatibility of `interpolate` with `Hive.reflect`. -/
theorem interpolate_reflect (h : RealHive n) (x : Fin 3 → ℝ) :
    interpolate h.reflect x = interpolate h (fun k => x (-k)) := by
  rw [coe_reflect]; exact interpolate_comp_reflect h x

/-- Simplicial extension of `f : Vertex n → ℝ` to `EuclideanSpace ℝ (Fin 2)` that is continuous and
piecewise affine on `planarSimplex n`, defined by pulling `interpolate f` back along
`planeInvAffine n`, bundled as a linear map in `f`. -/
noncomputable def planarInterpolate {n : ℕ} :
    (Vertex n → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (planeInvAffine n)).comp interpolate

theorem planarInterpolate_def (f : Vertex n → ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    planarInterpolate f u = interpolate f (planeInvAffine n u) := by simp [planarInterpolate]
@[simp] theorem planarInterpolate_plane (f : Vertex n → ℝ) (p : Vertex n) :
    planarInterpolate f p.plane = f p := by simp [planarInterpolate]
theorem planarInterpolate_planeLinear (f : Vertex n → ℝ) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) : planarInterpolate f (planeLinear x) = interpolate f x := by
  rw [planarInterpolate_def, planeInvAffine_planeLinear hx]
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
  rw [planarInterpolate_def, (planeInvAffine n).apply_lineMap, planeInvAffine_plane,
    planeInvAffine_plane, interpolate_lineMap_of_isUnitEdge f h ht]
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
