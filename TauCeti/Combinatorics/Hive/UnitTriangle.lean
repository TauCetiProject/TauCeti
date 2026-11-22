/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.Combinatorics.Hive.Lattice
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Unit triangles and the simplicial subdivision of the hive triangle

This file constructs the unit-triangle subdivision of the continuous barycentric simplex
`barycentricSimplex n = {x : Fin 3 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = n}` and its Euclidean image
`planarSimplex n = planeLinear '' barycentricSimplex n`. Polyhedral unit cells, continuous affine
barycentric weights, and the active-vertex overlap lemma give the cover and boundary-agreement data
for continuous piecewise-affine hive interpolation, while adjacency across interior unit edges
encodes the unit rhombi of `Vertex n`.

Unit triangles `TauCeti.Hive.UnitTriangle n` have two orientations (`UnitTriangle 0` is empty and
`UnitTriangle 1` has only `up (cornerA 0)`):
- `n = m + 1`: upward triangles `up base` (`base : Vertex m`), `base.coord i ≤ x i`, vertices
  `base + unitCorner i`;
- `n = m + 2`: downward triangles `down base` (`base : Vertex m`), `x i ≤ base.coord i + 1`,
  vertices `base + oppUnitCorner i`.

## Main definitions and results

* `TauCeti.Hive.barycentricSimplex`, `TauCeti.Hive.planeLinear`, `TauCeti.Hive.planeInvAffine`,
  `TauCeti.Hive.planarSimplex`.
* `TauCeti.Hive.UnitTriangle` (`card`, `weight`, `cell`, `isConvexPolyhedron_cell`,
  `cell_eq_convexHull`, `iUnion_cell_eq_barycentricSimplex`, `mem_range_vertex_of_weight_pos`).
* `TauCeti.Hive.adjacentUp`, `TauCeti.Hive.adjacentCell`, `TauCeti.Hive.exists_cell_of_isUnitEdge`,
  `TauCeti.Hive.IsRhombus.exists_adjacentUp`.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §2, App. 2.
-/

public section

open Set
open scoped BigOperators

namespace TauCeti.Hive

/-! ### The continuous simplex and the Euclidean chart -/

section

variable {n m k : ℕ}

/-- The continuous size-`n` barycentric simplex `{x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = n}`. -/
def barycentricSimplex (n : ℕ) : Set (Fin 3 → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = (n : ℝ)}

@[simp] theorem mem_barycentricSimplex_iff {x : Fin 3 → ℝ} :
    x ∈ barycentricSimplex n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = (n : ℝ) := Iff.rfl
theorem barycentric_mem_barycentricSimplex (p : Vertex n) : p.barycentric ∈ barycentricSimplex n :=
  ⟨p.barycentric_nonneg, p.sum_barycentric⟩
@[simp] theorem barycentricSimplex_zero : barycentricSimplex 0 = {0} := by
  ext x; simp only [mem_barycentricSimplex_iff, Nat.cast_zero, Fin.sum_univ_three]
  refine ⟨fun ⟨hpos, hsum⟩ => ?_, fun hx => by rw [mem_singleton_iff.mp hx]; simp⟩
  ext i; fin_cases i <;> simp <;> linarith [hpos 0, hpos 1, hpos 2, hsum]
theorem add_mem_barycentricSimplex {x y : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex m)
    (hy : y ∈ barycentricSimplex k) : x + y ∈ barycentricSimplex (m + k) :=
  ⟨fun i => add_nonneg (hx.1 i) (hy.1 i), by simp [Finset.sum_add_distrib, hx.2, hy.2]⟩
theorem rotate_mem_barycentricSimplex_iff {x : Fin 3 → ℝ} :
    (fun k => x (k - 1)) ∈ barycentricSimplex n ↔ x ∈ barycentricSimplex n :=
  and_congr ⟨fun h i => by simpa using h (i + 1), fun h i => h _⟩ <| by
    rw [Fintype.sum_equiv (Equiv.subRight (1 : Fin 3)) (fun k => x (k - 1)) x fun _ => rfl]
theorem reflect_mem_barycentricSimplex_iff {x : Fin 3 → ℝ} :
    (fun k => x (-k)) ∈ barycentricSimplex n ↔ x ∈ barycentricSimplex n :=
  and_congr ⟨fun h i => by simpa using h (-i), fun h i => h _⟩ <| by
    rw [Fintype.sum_equiv (Equiv.neg (Fin 3)) (fun k => x (-k)) x fun _ => rfl]

/-- The continuous barycentric simplex `barycentricSimplex n` is a convex polyhedron. -/
theorem isConvexPolyhedron_barycentricSimplex (n : ℕ) :
    IsConvexPolyhedron (barycentricSimplex n) := by
  let p (i : Fin 3) : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj i).toContinuousAffineMap
  let S := p 0 + p 1 + p 2; let c := ContinuousAffineMap.const ℝ (Fin 3 → ℝ) (n : ℝ)
  convert isConvexPolyhedron_setOf_forall ![-p 0, -p 1, -p 2, S - c, c - S] using 1
  ext x; simp [p, S, c, Fin.sum_univ_three, Fin.forall_fin_succ, le_antisymm_iff, and_assoc]

theorem convex_barycentricSimplex (n : ℕ) : Convex ℝ (barycentricSimplex n) :=
  (isConvexPolyhedron_barycentricSimplex n).convex
theorem isClosed_barycentricSimplex (n : ℕ) : IsClosed (barycentricSimplex n) :=
  (isConvexPolyhedron_barycentricSimplex n).isClosed

/-- `barycentricSimplex n` is the convex hull of the three perimeter corners `(n, 0, 0)`,
`(0, n, 0)`, `(0, 0, n)`. -/
theorem barycentricSimplex_eq_convexHull_corners (n : ℕ) : barycentricSimplex n =
    convexHull ℝ (Set.range fun s : Fin 3 => (Vertex.edgePoint n s 0).barycentric) := by
  refine Subset.antisymm (fun x hx => ?_) (convexHull_min
    (fun _ ⟨_, h⟩ => h ▸ barycentric_mem_barycentricSimplex _) (convex_barycentricSimplex _))
  rcases eq_or_ne n 0 with rfl | hn
  · exact (mem_singleton_iff.mp (barycentricSimplex_zero ▸ hx)) ▸
      subset_convexHull ℝ _ ⟨0, by simp [Vertex.barycentric_cornerA_zero]⟩
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hcomb : ∑ s : Fin 3, (x s / n) • (Vertex.edgePoint n s 0).barycentric = x := by
      ext i; fin_cases i <;> simp [Fin.sum_univ_three, div_mul_cancel₀ _ hn'.ne']
    exact hcomb ▸ (convex_convexHull ℝ _).sum_mem (fun s _ => div_nonneg (hx.1 s) hn'.le)
      (by rw [← Finset.sum_div, hx.2, div_self hn'.ne']) fun s _ => subset_convexHull ℝ _ ⟨s, rfl⟩

theorem barycentricSimplex_eq_convexHull (n : ℕ) :
    barycentricSimplex n = convexHull ℝ (Set.range (Vertex.barycentric (n := n))) :=
  Subset.antisymm (barycentricSimplex_eq_convexHull_corners n ▸ convexHull_mono
      (by rintro _ ⟨s, rfl⟩; exact ⟨Vertex.edgePoint n s 0, rfl⟩))
    (convexHull_min (fun _ ⟨_, h⟩ => h ▸ barycentric_mem_barycentricSimplex _)
      (convex_barycentricSimplex _))

/-- Continuous linear map extending `Vertex.plane` to all of `Fin 3 → ℝ`:
`(x₀, x₁, x₂) ↦ (x₂ + x₁ / 2, √3 * x₁ / 2)`. -/
noncomputable def planeLinear : (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => !₂[x 2 + x 1 / 2, Real.sqrt 3 * x 1 / 2]
      map_add' := fun x y => by ext i; fin_cases i <;> simp <;> ring
      map_smul' := fun c x => by ext i; fin_cases i <;> simp <;> ring }

@[simp] theorem planeLinear_zero_coord (x : Fin 3 → ℝ) :
    planeLinear x 0 = x 2 + x 1 / 2 := by simp [planeLinear]
@[simp] theorem planeLinear_one_coord (x : Fin 3 → ℝ) :
    planeLinear x 1 = Real.sqrt 3 * x 1 / 2 := by simp [planeLinear]
@[simp] theorem planeLinear_barycentric (p : Vertex n) : planeLinear p.barycentric = p.plane := by
  ext i; fin_cases i <;> simp

/-- Continuous affine inverse of `planeLinear` onto the affine hyperplane `{x | ∑ i, x i = n}`. -/
noncomputable def planeInvAffine (n : ℕ) : EuclideanSpace ℝ (Fin 2) →ᴬ[ℝ] (Fin 3 → ℝ) :=
  (LinearMap.toContinuousLinearMap
    { toFun := fun (u : EuclideanSpace ℝ (Fin 2)) =>
        ![-u 0 - u 1 / Real.sqrt 3, 2 * u 1 / Real.sqrt 3, u 0 - u 1 / Real.sqrt 3]
      map_add' := fun u v => by ext i; fin_cases i <;> simp <;> ring
      map_smul' := fun c u => by ext i; fin_cases i <;> simp <;> ring }).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) ![(n : ℝ), 0, 0]

@[simp] theorem planeInvAffine_zero_coord (n : ℕ) (u : EuclideanSpace ℝ (Fin 2)) :
    planeInvAffine n u 0 = (n : ℝ) - u 0 - u 1 / Real.sqrt 3 := by simp [planeInvAffine]; ring
@[simp] theorem planeInvAffine_one_coord (n : ℕ) (u : EuclideanSpace ℝ (Fin 2)) :
    planeInvAffine n u 1 = 2 * u 1 / Real.sqrt 3 := by simp [planeInvAffine]
@[simp] theorem planeInvAffine_two_coord (n : ℕ) (u : EuclideanSpace ℝ (Fin 2)) :
    planeInvAffine n u 2 = u 0 - u 1 / Real.sqrt 3 := by simp [planeInvAffine]
@[simp] theorem sum_planeInvAffine (n : ℕ) (u : EuclideanSpace ℝ (Fin 2)) :
    ∑ i, planeInvAffine n u i = (n : ℝ) := by simp [Fin.sum_univ_three]; ring
@[simp] theorem planeLinear_planeInvAffine (n : ℕ) (u : EuclideanSpace ℝ (Fin 2)) :
    planeLinear (planeInvAffine n u) = u := by
  ext i; fin_cases i <;> simp <;> field_simp; ring
theorem planeInvAffine_planeLinear {x : Fin 3 → ℝ} (hx : ∑ i, x i = (n : ℝ)) :
    planeInvAffine n (planeLinear x) = x := by
  have hx' : x 0 + x 1 + x 2 = (n : ℝ) := by simpa [Fin.sum_univ_three, add_assoc] using hx
  ext i; fin_cases i <;> simp <;> field_simp <;> linarith
@[simp] theorem planeInvAffine_plane (p : Vertex n) : planeInvAffine n p.plane = p.barycentric := by
  rw [← planeLinear_barycentric, planeInvAffine_planeLinear p.sum_barycentric]

/-- The continuous size-`n` equilateral triangle in `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def planarSimplex (n : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  planeLinear '' barycentricSimplex n

theorem planarSimplex_def (n : ℕ) : planarSimplex n = planeLinear '' barycentricSimplex n := (rfl)
theorem planarSimplex_eq_preimage (n : ℕ) :
    planarSimplex n = planeInvAffine n ⁻¹' barycentricSimplex n := by
  ext u; simp only [planarSimplex, mem_image, mem_preimage]
  exact ⟨fun ⟨x, hx, h⟩ => h ▸ (planeInvAffine_planeLinear hx.2).symm ▸ hx,
    fun hu => ⟨planeInvAffine n u, hu, planeLinear_planeInvAffine n u⟩⟩
@[simp] theorem mem_planarSimplex_iff {u : EuclideanSpace ℝ (Fin 2)} :
    u ∈ planarSimplex n ↔ planeInvAffine n u ∈ barycentricSimplex n := by
  rw [planarSimplex_eq_preimage]; rfl
theorem plane_mem_planarSimplex (p : Vertex n) : p.plane ∈ planarSimplex n :=
  ⟨p.barycentric, barycentric_mem_barycentricSimplex p, planeLinear_barycentric p⟩
theorem isConvexPolyhedron_planarSimplex (n : ℕ) : IsConvexPolyhedron (planarSimplex n) :=
  planarSimplex_eq_preimage n ▸ (isConvexPolyhedron_barycentricSimplex _).preimage _
theorem convex_planarSimplex (n : ℕ) : Convex ℝ (planarSimplex n) :=
  (isConvexPolyhedron_planarSimplex n).convex
theorem isClosed_planarSimplex (n : ℕ) : IsClosed (planarSimplex n) :=
  (isConvexPolyhedron_planarSimplex n).isClosed
theorem planarSimplex_eq_convexHull (n : ℕ) :
    planarSimplex n = convexHull ℝ (Set.range (Vertex.plane (n := n))) := by
  rw [planarSimplex, barycentricSimplex_eq_convexHull, ← planeLinear.coe_coe,
    LinearMap.image_convexHull, ← Set.range_comp]
  exact congrArg _ (congrArg Set.range (funext planeLinear_barycentric))

end

/-! ### Standard corners and unit triangles -/

/-- The `i`-th corner of `Δ₁`: `(1, 0, 0)`, `(0, 1, 0)`, `(0, 0, 1)`. -/
def unitCorner : Fin 3 → Vertex 1
  | ⟨0, _⟩ => ⟨1, 0, 0, rfl⟩ | ⟨1, _⟩ => ⟨0, 1, 0, rfl⟩ | ⟨2, _⟩ => ⟨0, 0, 1, rfl⟩

@[simp] theorem coord_unitCorner (i j : Fin 3) : (unitCorner i).coord j = if i = j then 1 else 0 :=
  by fin_cases i <;> fin_cases j <;> simp [unitCorner]
@[simp] theorem unitCorner_x (i : Fin 3) : (unitCorner i).x = if i = 0 then 1 else 0 := by
  fin_cases i <;> rfl
@[simp] theorem unitCorner_y (i : Fin 3) : (unitCorner i).y = if i = 1 then 1 else 0 := by
  fin_cases i <;> rfl
@[simp] theorem unitCorner_z (i : Fin 3) : (unitCorner i).z = if i = 2 then 1 else 0 := by
  fin_cases i <;> rfl
@[simp] theorem rotate_unitCorner (i : Fin 3) : (unitCorner i).rotate = unitCorner (i + 1) := by
  fin_cases i <;> ext <;> simp [unitCorner]
@[simp] theorem reflect_unitCorner (i : Fin 3) : (unitCorner i).reflect = unitCorner (-i) := by
  fin_cases i <;> ext <;> simp [unitCorner, Fin.neg_def]

/-- Midpoint vertex of `Δ₂` opposite corner `i`: `(0, 1, 1)`, `(1, 0, 1)`, `(1, 1, 0)`. -/
def oppUnitCorner : Fin 3 → Vertex 2
  | ⟨0, _⟩ => ⟨0, 1, 1, rfl⟩ | ⟨1, _⟩ => ⟨1, 0, 1, rfl⟩ | ⟨2, _⟩ => ⟨1, 1, 0, rfl⟩

@[simp] theorem coord_oppUnitCorner (i j : Fin 3) :
    (oppUnitCorner i).coord j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> simp [oppUnitCorner]
@[simp] theorem oppUnitCorner_x (i : Fin 3) : (oppUnitCorner i).x = if i = 0 then 0 else 1 := by
  fin_cases i <;> rfl
@[simp] theorem oppUnitCorner_y (i : Fin 3) : (oppUnitCorner i).y = if i = 1 then 0 else 1 := by
  fin_cases i <;> rfl
@[simp] theorem oppUnitCorner_z (i : Fin 3) : (oppUnitCorner i).z = if i = 2 then 0 else 1 := by
  fin_cases i <;> rfl
@[simp] theorem rotate_oppUnitCorner (i : Fin 3) :
    (oppUnitCorner i).rotate = oppUnitCorner (i + 1) := by
  fin_cases i <;> ext <;> simp [oppUnitCorner]
@[simp] theorem reflect_oppUnitCorner (i : Fin 3) :
    (oppUnitCorner i).reflect = oppUnitCorner (-i) := by
  fin_cases i <;> ext <;> simp [oppUnitCorner, Fin.neg_def]

/-- A unit equilateral lattice triangle inside `Δₙ`: either an **upward** triangle `up base` for
`n = m + 1` (`base : Vertex m`), or a **downward** triangle `down base` for `n = m + 2`
(`base : Vertex m`). `UnitTriangle 0` is empty, and `UnitTriangle 1` has only `up (cornerA 0)`. -/
inductive UnitTriangle : ℕ → Type
  /-- An upward unit triangle of `Δ_{m + 1}` with base vertex `base : Vertex m`. -/
  | up {m : ℕ} (base : Vertex m) : UnitTriangle (m + 1)
  /-- A downward unit triangle of `Δ_{m + 2}` with base vertex `base : Vertex m`. -/
  | down {m : ℕ} (base : Vertex m) : UnitTriangle (m + 2)

namespace UnitTriangle

variable {n m k : ℕ}

instance isEmptyZero : IsEmpty (UnitTriangle 0) := ⟨fun T => nomatch T⟩
instance instInhabited : Inhabited (UnitTriangle (m + 1)) := ⟨up (Vertex.cornerA m)⟩
/-- Equivalence `UnitTriangle 1 ≃ Vertex 0` sending `up base` to `base`. -/
def equivOne : UnitTriangle 1 ≃ Vertex 0 :=
  ⟨fun | up b => b, up, fun | up _ => rfl, fun _ => rfl⟩
@[simp] theorem equivOne_up (base : Vertex 0) : equivOne (up base) = base := (rfl)
@[simp] theorem equivOne_symm_apply (base : Vertex 0) : equivOne.symm base = up base := (rfl)
/-- At size `1`, the unique unit triangle is `up (cornerA 0)`. -/
instance uniqueOne : Unique (UnitTriangle 1) := ⟨⟨default⟩, fun _ =>
  equivOne.injective (Subsingleton.elim _ _)⟩
/-- For `n = m + 2`, unit triangles decompose into upward (`Vertex (m + 1)`) and downward
(`Vertex m`) triangles. -/
def equivSuccSucc (m : ℕ) : UnitTriangle (m + 2) ≃ Vertex (m + 1) ⊕ Vertex m :=
  ⟨fun | up b => .inl b | down b => .inr b, fun | .inl b => up b | .inr b => down b,
    fun | up _ => rfl | down _ => rfl, fun | .inl _ => rfl | .inr _ => rfl⟩
@[simp] theorem equivSuccSucc_up (m : ℕ) (b : Vertex (m + 1)) :
    equivSuccSucc m (up b) = Sum.inl b := (rfl)
@[simp] theorem equivSuccSucc_down (m : ℕ) (b : Vertex m) :
    equivSuccSucc m (down b) = Sum.inr b := (rfl)
@[simp] theorem equivSuccSucc_symm_inl (m : ℕ) (b : Vertex (m + 1)) :
    (equivSuccSucc m).symm (Sum.inl b) = up b := (rfl)
@[simp] theorem equivSuccSucc_symm_inr (m : ℕ) (b : Vertex m) :
    (equivSuccSucc m).symm (Sum.inr b) = down b := (rfl)
instance instDecidableEq : {n : ℕ} → DecidableEq (UnitTriangle n)
  | 0 => fun T => nomatch T | 1 => Equiv.decidableEq equivOne
  | m + 2 => Equiv.decidableEq (equivSuccSucc m)
instance instFintype : (n : ℕ) → Fintype (UnitTriangle n)
  | 0 => Fintype.ofIsEmpty | 1 => Fintype.ofEquiv (Vertex 0) equivOne.symm
  | m + 2 => Fintype.ofEquiv (Vertex (m + 1) ⊕ Vertex m) (equivSuccSucc m).symm
/-- There are `n ^ 2` unit triangles in `UnitTriangle n`. -/
@[simp] theorem card (n : ℕ) : Fintype.card (UnitTriangle n) = n ^ 2 := by
  match n with
  | 0 => simp | 1 => rw [Fintype.card_congr equivOne, Vertex.card 0]; norm_num
  | m + 2 =>
    rw [Fintype.card_congr (equivSuccSucc m), Fintype.card_sum]
    exact Nat.mul_left_cancel Nat.zero_lt_two
      (by linarith [Vertex.two_mul_card (m + 1), Vertex.two_mul_card m])

/-- The `i`-th vertex of a unit triangle `T : UnitTriangle n`. -/
def vertex : UnitTriangle n → Fin 3 → Vertex n
  | up base, i => base.add (unitCorner i) | down base, i => base.add (oppUnitCorner i)
@[simp] theorem vertex_up (b : Vertex m) (i : Fin 3) :
    (up b).vertex i = b.add (unitCorner i) := (rfl)
@[simp] theorem vertex_down (b : Vertex m) (i : Fin 3) :
    (down b).vertex i = b.add (oppUnitCorner i) := (rfl)
theorem coord_vertex_up (base : Vertex m) (i j : Fin 3) :
    ((up base).vertex i).coord j = base.coord j + if i = j then 1 else 0 := by fin_cases j <;> simp
theorem coord_vertex_down (b : Vertex m) (i j : Fin 3) :
    ((down b).vertex i).coord j = b.coord j + if i = j then 0 else 1 := by fin_cases j <;> simp
theorem vertex_injective (T : UnitTriangle n) : Function.Injective T.vertex := by
  cases T <;> intro i j h <;> fin_cases i <;> fin_cases j <;>
    simp_all [Vertex.ext_iff, unitCorner, oppUnitCorner]
/-- Any two distinct vertices of a unit triangle form a unit lattice edge. -/
theorem isUnitEdge_vertex (T : UnitTriangle n) {i j : Fin 3} (hij : i ≠ j) :
    IsUnitEdge (T.vertex i) (T.vertex j) := by
  cases T <;> simp only [vertex_up, vertex_down, isUnitEdge_def] <;>
    fin_cases i <;> fin_cases j <;> simp_all [unitCorner, oppUnitCorner, Vertex.sqDist_def]

/-- Clockwise rotation of a unit triangle by one third of a turn. -/
def rotate : UnitTriangle n → UnitTriangle n
  | up base => up base.rotate | down base => down base.rotate
@[simp] theorem rotate_up (b : Vertex m) : (up b).rotate = up b.rotate := (rfl)
@[simp] theorem rotate_down (b : Vertex m) : (down b).rotate = down b.rotate := (rfl)
@[simp] theorem rotate_rotate_rotate (T : UnitTriangle n) : T.rotate.rotate.rotate = T := by
  cases T <;> simp
theorem rotate_injective : Function.Injective (rotate (n := n)) := fun _ _ h => by
  simpa using congrArg (fun r => r.rotate.rotate) h
theorem vertex_rotate (T : UnitTriangle n) (i : Fin 3) :
    T.rotate.vertex (i + 1) = (T.vertex i).rotate := by cases T <;> simp
/-- Reflection of a unit triangle fixing `A = (n, 0, 0)` and interchanging `B` and `C`. -/
def reflect : UnitTriangle n → UnitTriangle n
  | up base => up base.reflect | down base => down base.reflect
@[simp] theorem reflect_up (b : Vertex m) : (up b).reflect = up b.reflect := (rfl)
@[simp] theorem reflect_down (b : Vertex m) : (down b).reflect = down b.reflect := (rfl)
@[simp] theorem reflect_reflect (T : UnitTriangle n) : T.reflect.reflect = T := by cases T <;> simp
theorem reflect_injective : Function.Injective (reflect (n := n)) :=
  Function.Involutive.injective reflect_reflect
@[simp] theorem reflect_rotate (T : UnitTriangle n) :
    T.rotate.reflect = T.reflect.rotate.rotate := by cases T <;> simp
theorem vertex_reflect (T : UnitTriangle n) (i : Fin 3) :
    T.reflect.vertex (-i) = (T.vertex i).reflect := by cases T <;> simp
/-- Translate a unit triangle of `Δₙ` into `Δ_{k + n}` by adding `p : Vertex k`. -/
def addLeft (p : Vertex k) : UnitTriangle n → UnitTriangle (k + n)
  | up base => up (p.add base) | down base => down (p.add base)
@[simp] theorem addLeft_up (p : Vertex k) (b : Vertex m) : (up b).addLeft p = up (p.add b) := (rfl)
@[simp] theorem addLeft_down (p : Vertex k) (b : Vertex m) :
    (down b).addLeft p = down (p.add b) := (rfl)
@[simp] theorem rotate_addLeft (p : Vertex k) (T : UnitTriangle n) :
    (T.addLeft p).rotate = T.rotate.addLeft p.rotate := by cases T <;> simp
@[simp] theorem reflect_addLeft (p : Vertex k) (T : UnitTriangle n) :
    (T.addLeft p).reflect = T.reflect.addLeft p.reflect := by cases T <;> simp
@[simp] theorem vertex_addLeft (p : Vertex k) (T : UnitTriangle n) (i : Fin 3) :
    (T.addLeft p).vertex i = p.add (T.vertex i) := by cases T <;> ext <;> simp [Nat.add_assoc]

/-! ### Continuous affine barycentric weights and polyhedral cells -/

/-- The `i`-th local barycentric weight of `T : UnitTriangle n` as a continuous affine functional
on `Fin 3 → ℝ`: `x i - base.coord i` on `up base` and `base.coord i + 1 - x i` on `down base`. -/
def weight : UnitTriangle n → Fin 3 → (Fin 3 → ℝ) →ᴬ[ℝ] ℝ
  | up base, i => (ContinuousLinearMap.proj i).toContinuousAffineMap -
      ContinuousAffineMap.const ℝ (Fin 3 → ℝ) (base.coord i : ℝ)
  | down base, i => ContinuousAffineMap.const ℝ (Fin 3 → ℝ) ((base.coord i : ℝ) + 1) -
      (ContinuousLinearMap.proj i).toContinuousAffineMap
@[simp] theorem weight_up_apply (base : Vertex m) (i : Fin 3) (x : Fin 3 → ℝ) :
    (up base).weight i x = x i - (base.coord i : ℝ) := by simp [weight]
@[simp] theorem weight_down_apply (base : Vertex m) (i : Fin 3) (x : Fin 3 → ℝ) :
    (down base).weight i x = (base.coord i : ℝ) + 1 - x i := by simp [weight]
@[simp] theorem weight_up_contLinear (base : Vertex m) (i : Fin 3) (v : Fin 3 → ℝ) :
    ((up base).weight i).contLinear v = v i := by simp [weight]
@[simp] theorem weight_down_contLinear (base : Vertex m) (i : Fin 3) (v : Fin 3 → ℝ) :
    ((down base).weight i).contLinear v = -v i := by simp [weight]
@[simp high] theorem weight_up_barycentric_add_unitCorner (b : Vertex m) (i j : Fin 3) :
    (up b).weight i (b.add (unitCorner j)).barycentric = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [unitCorner]
@[simp high] theorem weight_down_barycentric_add_oppUnitCorner (b : Vertex m) (i j : Fin 3) :
    (down b).weight i (b.add (oppUnitCorner j)).barycentric = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [oppUnitCorner]
@[simp high] theorem weight_vertex (T : UnitTriangle n) (i j : Fin 3) :
    T.weight i (T.vertex j).barycentric = if i = j then 1 else 0 := by cases T <;> simp
theorem sum_weight (T : UnitTriangle n) {x : Fin 3 → ℝ} (hx : ∑ i, x i = (n : ℝ)) :
    ∑ i, T.weight i x = 1 := by
  cases T <;> simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, hx, ← Vertex.barycentric_apply,
    Vertex.sum_barycentric]; norm_num
theorem sum_weight_smul_vertex (T : UnitTriangle n) {x : Fin 3 → ℝ} (hx : ∑ i, x i = (n : ℝ)) :
    ∑ i, T.weight i x • (T.vertex i).barycentric = x := by
  have hsw : T.weight 0 x + T.weight 1 x + T.weight 2 x = 1 := by
    simpa [Fin.sum_univ_three, add_assoc] using T.sum_weight hx
  ext j; cases T <;> fin_cases j <;>
    simp [Fin.sum_univ_three, unitCorner, oppUnitCorner] at hsw ⊢ <;> nlinarith
theorem weight_rotate_apply (T : UnitTriangle n) (i : Fin 3) (x : Fin 3 → ℝ) :
    T.rotate.weight (i + 1) (fun k => x (k - 1)) = T.weight i x := by
  cases T <;> simp [Vertex.coord_rotate]
theorem weight_reflect_apply (T : UnitTriangle n) (i : Fin 3) (x : Fin 3 → ℝ) :
    T.reflect.weight (-i) (fun k => x (-k)) = T.weight i x := by
  cases T <;> simp [Vertex.coord_reflect]
@[simp] theorem weight_addLeft_apply (p : Vertex k) (T : UnitTriangle n) (i : Fin 3)
    (x : Fin 3 → ℝ) : (T.addLeft p).weight i (p.barycentric + x) = T.weight i x := by
  cases T <;> simp; ring

/-- The closed continuous cell of a unit triangle `T : UnitTriangle n` inside
`barycentricSimplex n`. -/
def cell (T : UnitTriangle n) : Set (Fin 3 → ℝ) :=
  {x ∈ barycentricSimplex n | ∀ i, 0 ≤ T.weight i x}
@[simp] theorem mem_cell_iff {T : UnitTriangle n} {x : Fin 3 → ℝ} :
    x ∈ T.cell ↔ x ∈ barycentricSimplex n ∧ ∀ i, 0 ≤ T.weight i x := Iff.rfl
theorem mem_cell_rotate_iff {T : UnitTriangle n} {x : Fin 3 → ℝ} :
    (fun k => x (k - 1)) ∈ T.rotate.cell ↔ x ∈ T.cell :=
  and_congr rotate_mem_barycentricSimplex_iff
    ⟨fun h i => by simpa [weight_rotate_apply] using h (i + 1),
      fun h i => by have := h (i - 1); rwa [← weight_rotate_apply, sub_add_cancel] at this⟩
theorem mem_cell_reflect_iff {T : UnitTriangle n} {x : Fin 3 → ℝ} :
    (fun k => x (-k)) ∈ T.reflect.cell ↔ x ∈ T.cell :=
  and_congr reflect_mem_barycentricSimplex_iff
    ⟨fun h i => by simpa [weight_reflect_apply] using h (-i),
      fun h i => by have := h (-i); rwa [← weight_reflect_apply, neg_neg] at this⟩
theorem mem_cell_addLeft_iff {p : Vertex k} {T : UnitTriangle n} {x : Fin 3 → ℝ} :
    p.barycentric + x ∈ (T.addLeft p).cell ↔ x ∈ T.cell := by
  refine ⟨fun ⟨hpx, hw⟩ => ?_, fun hx =>
    ⟨add_mem_barycentricSimplex (barycentric_mem_barycentricSimplex p) hx.1,
      fun i => by simpa [weight_addLeft_apply] using hx.2 i⟩⟩
  have hw' : ∀ i, 0 ≤ T.weight i x := fun i => by simpa [weight_addLeft_apply] using hw i
  have hsum : ∑ i, x i = (n : ℝ) := by
    have := hpx.2; simp only [Pi.add_apply, Finset.sum_add_distrib, p.sum_barycentric,
      Nat.cast_add] at this; linarith
  exact ⟨T.sum_weight_smul_vertex hsum ▸ (convex_barycentricSimplex n).sum_mem
    (fun i _ => hw' i) (T.sum_weight hsum) fun i _ => barycentric_mem_barycentricSimplex _, hw'⟩
theorem cell_subset_barycentricSimplex (T : UnitTriangle n) : T.cell ⊆ barycentricSimplex n :=
  fun _ hx => hx.1
theorem weight_nonneg {T : UnitTriangle n} {x : Fin 3 → ℝ} (hx : x ∈ T.cell) (i : Fin 3) :
    0 ≤ T.weight i x := hx.2 i
theorem weight_le_one {T : UnitTriangle n} {x : Fin 3 → ℝ} (hx : x ∈ T.cell) (i : Fin 3) :
    T.weight i x ≤ 1 :=
  T.sum_weight hx.1.2 ▸ Finset.single_le_sum (fun j _ => hx.2 j) (Finset.mem_univ i)
theorem barycentric_vertex_mem_cell (T : UnitTriangle n) (i : Fin 3) :
    (T.vertex i).barycentric ∈ T.cell :=
  ⟨barycentric_mem_barycentricSimplex _, fun j => by rw [weight_vertex]; split_ifs <;> norm_num⟩
/-- Every unit-triangle cell is a convex polyhedron. -/
theorem isConvexPolyhedron_cell (T : UnitTriangle n) : IsConvexPolyhedron T.cell := by
  convert (isConvexPolyhedron_barycentricSimplex n).inter
    (isConvexPolyhedron_setOf_forall fun i : Fin 3 => -T.weight i) using 1; ext x; simp
theorem convex_cell (T : UnitTriangle n) : Convex ℝ T.cell := T.isConvexPolyhedron_cell.convex
theorem isClosed_cell (T : UnitTriangle n) : IsClosed T.cell := T.isConvexPolyhedron_cell.isClosed
/-- Each unit-triangle cell is the convex hull of its three lattice vertices. -/
theorem cell_eq_convexHull (T : UnitTriangle n) :
    T.cell = convexHull ℝ (Set.range fun i => (T.vertex i).barycentric) :=
  Subset.antisymm (fun _ hx => T.sum_weight_smul_vertex hx.1.2 ▸
      (convex_convexHull ℝ _).sum_mem (fun i _ => hx.2 i) (T.sum_weight hx.1.2)
        fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
    (convexHull_min (by rintro _ ⟨i, rfl⟩; exact T.barycentric_vertex_mem_cell i) T.convex_cell)
/-- At size `1`, the single upward unit triangle covers all of `barycentricSimplex 1`. -/
@[simp] theorem cell_up_cornerA_zero : (up (Vertex.cornerA 0)).cell = barycentricSimplex 1 := by
  ext x; simp only [mem_cell_iff, mem_barycentricSimplex_iff, weight_up_apply, and_iff_left_iff_imp]
  exact fun hx i => by fin_cases i <;> simp [hx.1 _]
/-- If `x ∈ T.cell` has positive `i`-th weight, then the `i`-th vertex of `T` lies strictly within
`1` of `x` in every coordinate. -/
theorem abs_vertex_sub_lt_one_of_weight_pos {T : UnitTriangle n} {x : Fin 3 → ℝ} (hx : x ∈ T.cell)
    {i : Fin 3} (hi : 0 < T.weight i x) (k : Fin 3) : |((T.vertex i).coord k : ℝ) - x k| < 1 := by
  have hsum : T.weight 0 x + T.weight 1 x + T.weight 2 x = 1 := by
    simpa [Fin.sum_univ_three, add_assoc] using T.sum_weight hx.1.2
  have h0 := hx.2 0; have h1 := hx.2 1; have h2 := hx.2 2
  cases T <;> [rw [coord_vertex_up]; rw [coord_vertex_down]] <;> rw [Nat.cast_add, abs_lt] <;>
    constructor <;> fin_cases i <;> fin_cases k <;> simp at hsum hi h0 h1 h2 ⊢ <;> linarith
/-- Any lattice vertex `p : Vertex n` whose real embedding lies in `T.cell` is one of the three
vertices of `T`. -/
theorem mem_range_vertex_of_barycentric_mem_cell {T : UnitTriangle n} {p : Vertex n}
    (hp : p.barycentric ∈ T.cell) : p ∈ Set.range T.vertex := by
  have hp_sum := p.sum_eq; cases T with
  | up b =>
    have hb := b.sum_eq
    have h (i : Fin 3) : b.coord i ≤ p.coord i := by simpa [sub_nonneg] using hp.2 i
    have h0 := h 0; have h1 := h 1; have h2 := h 2; simp at h0 h1 h2
    rcases (by omega : p.x = b.x + 1 ∨ p.y = b.y + 1 ∨ p.z = b.z + 1) with h | h | h <;>
      [refine ⟨0, ?_⟩; refine ⟨1, ?_⟩; refine ⟨2, ?_⟩] <;> ext <;> simp [unitCorner] <;> omega
  | down b =>
    have hb := b.sum_eq
    have h (i : Fin 3) : p.coord i ≤ b.coord i + 1 := Nat.cast_le.mp
      (by simpa [sub_nonneg] using hp.2 i : (p.coord i : ℝ) ≤ ((b.coord i + 1 : ℕ)))
    have h0 := h 0; have h1 := h 1; have h2 := h 2; simp at h0 h1 h2
    rcases (by omega : p.x = b.x ∨ p.y = b.y ∨ p.z = b.z) with h | h | h <;>
      [refine ⟨0, ?_⟩; refine ⟨1, ?_⟩; refine ⟨2, ?_⟩] <;> ext <;> simp [oppUnitCorner] <;> omega
/-- **Active-vertex overlap lemma**: if `x ∈ T₁.cell ∩ T₂.cell` and `T₁.weight i x > 0`, then
`T₁.vertex i` is also a vertex of `T₂`. -/
theorem mem_range_vertex_of_weight_pos {T₁ T₂ : UnitTriangle n} {x : Fin 3 → ℝ} (hx₁ : x ∈ T₁.cell)
    (hx₂ : x ∈ T₂.cell) {i : Fin 3} (hi : 0 < T₁.weight i x) :
    T₁.vertex i ∈ Set.range T₂.vertex := by
  refine mem_range_vertex_of_barycentric_mem_cell
    ⟨barycentric_mem_barycentricSimplex _, fun k => ?_⟩
  have habs := abs_lt.mp (abs_vertex_sub_lt_one_of_weight_pos hx₁ hi k); have hxk := hx₂.2 k
  cases T₂ <;> simp only [weight_up_apply, weight_down_apply, Vertex.barycentric_apply,
    sub_nonneg] at hxk ⊢ <;>
    exact_mod_cast Nat.lt_succ_iff.mp (Nat.cast_lt (α := ℝ).mp (by push_cast; linarith))
/-- For `n = m + 1 ≥ 1`, the `n ^ 2` unit-triangle cells cover `barycentricSimplex (m + 1)`. -/
theorem iUnion_cell_eq_barycentricSimplex (m : ℕ) :
    (⋃ T : UnitTriangle (m + 1), T.cell) = barycentricSimplex (m + 1) := by
  refine Subset.antisymm (iUnion_subset fun T => T.cell_subset_barycentricSimplex) fun x hx => ?_
  rw [mem_iUnion]; let b : Fin 3 → ℕ := fun i => ⌊x i⌋₊
  have hb_le (i : Fin 3) : (b i : ℝ) ≤ x i := Nat.floor_le (hx.1 i)
  have hx_lt (i : Fin 3) : x i < (b i : ℝ) + 1 := Nat.lt_floor_add_one (x i)
  have hsum_x : x 0 + x 1 + x 2 = (m : ℝ) + 1 := by simpa [Fin.sum_univ_three, add_assoc] using hx.2
  have hnat_le : b 0 + b 1 + b 2 ≤ m + 1 := Nat.cast_le.mp
    (by push_cast; linarith [hb_le 0, hb_le 1, hb_le 2] : ((_ : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ))
  have hnat_lt : m + 1 < b 0 + b 1 + b 2 + 3 := Nat.cast_lt.mp
    (by push_cast; linarith [hx_lt 0, hx_lt 1, hx_lt 2] : ((m + 1 : ℕ) : ℝ) < ((_ : ℕ) : ℝ))
  rcases (by omega : b 0 + b 1 + b 2 = m ∨ b 0 + b 1 + b 2 + 1 = m ∨ b 0 + b 1 + b 2 = m + 1) with
    hm | hm1 | hm_top
  · exact ⟨up ⟨b 0, b 1, b 2, hm⟩, hx, fun i => by fin_cases i <;> simp [sub_nonneg, hb_le _]⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨b 0 + b 1 + b 2, hm1.symm⟩
    exact ⟨down ⟨b 0, b 1, b 2, by omega⟩, hx, fun i => by
      fin_cases i <;> simp [sub_nonneg, (hx_lt _).le]⟩
  · have hx_eq (i : Fin 3) : x i = b i := by
      have : (b 0 : ℝ) + b 1 + b 2 = m + 1 := by exact_mod_cast hm_top
      fin_cases i <;> dsimp <;> linarith [hb_le 0, hb_le 1, hb_le 2]
    rcases (by omega : 1 ≤ b 0 ∨ 1 ≤ b 1 ∨ 1 ≤ b 2) with hb | hb | hb <;>
      [refine ⟨up ⟨b 0 - 1, b 1, b 2, by omega⟩, hx, ?_⟩;
       refine ⟨up ⟨b 0, b 1 - 1, b 2, by omega⟩, hx, ?_⟩;
       refine ⟨up ⟨b 0, b 1, b 2 - 1, by omega⟩, hx, ?_⟩] <;>
      exact fun i => by fin_cases i <;> simp [hx_eq _, Nat.cast_sub hb]
end UnitTriangle

variable {n m k : ℕ}

/-- Every unit lattice edge `(a, c)` in `Vertex n` lies in the cell of a unit triangle. -/
theorem exists_cell_of_isUnitEdge {a c : Vertex n} (h : IsUnitEdge a c) :
    ∃ T : UnitTriangle n, a.barycentric ∈ T.cell ∧ c.barycentric ∈ T.cell := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h.one_le)
  have hsq : ((a.x : ℤ) - c.x) ^ 2 + ((a.y : ℤ) - c.y) ^ 2 + ((a.z : ℤ) - c.z) ^ 2 = 2 := by
    rwa [isUnitEdge_def, Vertex.sqDist_def] at h
  have hmin (u v : ℕ) (huv : ((u : ℤ) - v) ^ 2 ≤ 2) :
      2 * ((min u v : ℕ) : ℤ) = (u : ℤ) + v - ((u : ℤ) - v) ^ 2 := by
    have : -1 ≤ (u : ℤ) - v ∧ (u : ℤ) - v ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    rcases (by omega : (u : ℤ) - v = -1 ∨ (u : ℤ) - v = 0 ∨ (u : ℤ) - v = 1) with h1 | h1 | h1 <;>
      { rw [h1]; norm_num; omega }
  have hx := hmin a.x c.x (by nlinarith); have hy := hmin a.y c.y (by nlinarith)
  have hz := hmin a.z c.z (by nlinarith); have ha := a.sum_eq; have hc := c.sum_eq
  refine ⟨UnitTriangle.up ⟨min a.x c.x, min a.y c.y, min a.z c.z, by
      zify at hx hy hz ha hc ⊢; linarith⟩,
    ⟨barycentric_mem_barycentricSimplex a, fun i => by fin_cases i <;> simp [sub_nonneg]⟩,
    ⟨barycentric_mem_barycentricSimplex c, fun i => by fin_cases i <;> simp [sub_nonneg]⟩⟩

/-! ### Adjacent unit triangles and union rhombus cells -/

/-- The upward unit triangle sharing the edge of `down s` opposite `(down s).vertex i`
(joining `(down s).vertex (i + 1)` and `(down s).vertex (i + 2)` along `x i = s.coord i + 1`). -/
def adjacentUp (s : Vertex m) (i : Fin 3) : UnitTriangle (m + 2) :=
  UnitTriangle.up (s.add (unitCorner i))
theorem adjacentUp_def (s : Vertex m) (i : Fin 3) :
    adjacentUp s i = UnitTriangle.up (s.add (unitCorner i)) := (rfl)
theorem vertex_adjacentUp (s : Vertex m) (i j : Fin 3) :
    (adjacentUp s i).vertex j = (s.add (unitCorner i)).add (unitCorner j) := (rfl)
@[simp] theorem rotate_adjacentUp (s : Vertex m) (i : Fin 3) :
    (adjacentUp s i).rotate = adjacentUp s.rotate (i + 1) := by simp [adjacentUp]
@[simp] theorem reflect_adjacentUp (s : Vertex m) (i : Fin 3) :
    (adjacentUp s i).reflect = adjacentUp s.reflect (-i) := by simp [adjacentUp]
@[simp] theorem addLeft_adjacentUp (p : Vertex k) (s : Vertex m) (i : Fin 3) :
    (adjacentUp s i).addLeft p = adjacentUp (p.add s) i := by
  simp only [adjacentUp, UnitTriangle.addLeft_up]; congr 1; ext <;> simp [Nat.add_assoc]
@[simp] theorem weight_adjacentUp_apply (s : Vertex m) (i j : Fin 3) (x : Fin 3 → ℝ) :
    (adjacentUp s i).weight j x = x j - ((s.coord j : ℝ) + if i = j then 1 else 0) := by
  simp [adjacentUp]
/-- The `(i + 1)`-th vertex of `adjacentUp s i` coincides with `(down s).vertex (i + 2)`. -/
theorem vertex_adjacentUp_add_one (s : Vertex m) (i : Fin 3) :
    (adjacentUp s i).vertex (i + 1) = (UnitTriangle.down s).vertex (i + 2) :=
  Vertex.ext_coord fun j => by fin_cases i <;> fin_cases j <;> simp [adjacentUp]
/-- The `(i + 2)`-th vertex of `adjacentUp s i` coincides with `(down s).vertex (i + 1)`. -/
theorem vertex_adjacentUp_add_two (s : Vertex m) (i : Fin 3) :
    (adjacentUp s i).vertex (i + 2) = (UnitTriangle.down s).vertex (i + 1) :=
  Vertex.ext_coord fun j => by fin_cases i <;> fin_cases j <;> simp [adjacentUp]
/-- The upward triangle `adjacentUp s i` and the downward triangle `down s` form a unit rhombus
with obtuse corners on their shared edge opposite `(down s).vertex i` and acute corners
`(adjacentUp s i).vertex i` and `(down s).vertex i`. -/
theorem isRhombus_adjacent (s : Vertex m) (i : Fin 3) :
    IsRhombus ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
      ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  have hv (a b : Vertex (m + 2)) (h : ∀ j, a.coord j = b.coord j := by
      intro j; simp only [adjacentUp, UnitTriangle.coord_vertex_up, UnitTriangle.coord_vertex_down]
      fin_cases j <;> simp) : a = b := Vertex.ext_coord h
  fin_cases i
  · convert isRhombus_at_cornerA.add s using 1 <;> exact hv _ _
  · convert isRhombus_at_cornerA.rotate.add s using 1 <;> exact hv _ _
  · convert isRhombus_at_cornerA.rotate.rotate.add s using 1 <;> exact hv _ _
private abbrev IsAdjRhombus (s : Vertex m) (i : Fin 3) (a b c d : Vertex (m + 2)) : Prop :=
  ((a = (UnitTriangle.down s).vertex (i + 2) ∧ c = (UnitTriangle.down s).vertex (i + 1)) ∨
    (a = (UnitTriangle.down s).vertex (i + 1) ∧ c = (UnitTriangle.down s).vertex (i + 2))) ∧
  ((b = (adjacentUp s i).vertex i ∧ d = (UnitTriangle.down s).vertex i) ∨
    (b = (UnitTriangle.down s).vertex i ∧ d = (adjacentUp s i).vertex i))
private theorem exists_adjacentUp_of_sub_x_eq_two {a b c d : Vertex (m + 2)}
    (hr : IsRhombus a b c d) (hbd : (b.x : ℤ) - d.x = 2) :
    ∃ s : Vertex m, ((a = (UnitTriangle.down s).vertex 2 ∧ c = (UnitTriangle.down s).vertex 1) ∨
      (a = (UnitTriangle.down s).vertex 1 ∧ c = (UnitTriangle.down s).vertex 2)) ∧
      b = (adjacentUp s 0).vertex 0 ∧ d = (UnitTriangle.down s).vertex 0 := by
  have hsum (p : Vertex (m + 2)) : (p.x : ℤ) + p.y + p.z = m + 2 := by exact_mod_cast p.sum_eq
  have hlong := hr.long; rw [Vertex.sqDist_def] at hlong
  have hby : (d.y : ℤ) = b.y + 1 := by nlinarith [sq_nonneg ((b.y : ℤ) - d.y + 1), hsum b, hsum d]
  have hbz : (d.z : ℤ) = b.z + 1 := by have := hsum b; have := hsum d; omega
  have hbx : (b.x : ℤ) = d.x + 2 := by omega
  let s : Vertex m := ⟨d.x, b.y, b.z, by have := d.sum_eq; omega⟩
  have hab := hr.side_ab; have hda := hr.side_da
  rw [Vertex.sqDist_def, hbx] at hab; rw [Vertex.sqDist_def, hby, hbz] at hda
  have hax : (a.x : ℤ) = d.x + 1 := by nlinarith [hsum a, hsum d]
  have haz : (a.z : ℤ) - b.z = 1 - ((a.y : ℤ) - b.y) := by have := hsum a; have := hsum d; omega
  rw [hax, haz] at hab
  have hay := mul_eq_zero.mp (by nlinarith [hab] : ((a.y : ℤ) - b.y) * ((a.y : ℤ) - b.y - 1) = 0)
  have hmx := hr.midpoint_x; have hmy := hr.midpoint_y; have hmz := hr.midpoint_z
  refine ⟨s, ?_, by ext <;> simp [s, adjacentUp]; omega, by ext <;> simp [s] <;> omega⟩
  rcases hay with h | h <;> [right; left] <;>
    exact ⟨by ext <;> simp [s] <;> omega, by ext <;> simp [s] <;> omega⟩
private theorem exists_adjacentUp_of_rotate {a b c d : Vertex (m + 2)}
    (h : ∃ (s : Vertex m) (i : Fin 3), IsAdjRhombus s i a.rotate b.rotate c.rotate d.rotate) :
    ∃ (s : Vertex m) (i : Fin 3), IsAdjRhombus s i a b c d := by
  obtain ⟨s, i, hac, hbd⟩ := h
  have hd (j : Fin 3) : ((UnitTriangle.down s).vertex j).rotate.rotate =
      (UnitTriangle.down s.rotate.rotate).vertex (j + 2) := by
    rw [← UnitTriangle.vertex_rotate, ← UnitTriangle.vertex_rotate, add_assoc]; rfl
  have hu : ((adjacentUp s i).vertex i).rotate.rotate =
      (adjacentUp s.rotate.rotate (i + 2)).vertex (i + 2) := by
    rw [← UnitTriangle.vertex_rotate, ← UnitTriangle.vertex_rotate, rotate_adjacentUp,
      rotate_adjacentUp, add_assoc]; rfl
  have inv {p q : Vertex (m + 2)} (hp : p.rotate = q) : p = q.rotate.rotate :=
    hp ▸ p.rotate_rotate_rotate.symm
  exact ⟨s.rotate.rotate, i + 2,
    hac.imp (fun ⟨ha, hc⟩ => ⟨by rw [inv ha, hd], by rw [inv hc, hd, add_right_comm]⟩)
      (fun ⟨ha, hc⟩ => ⟨by rw [inv ha, hd, add_right_comm], by rw [inv hc, hd]⟩),
    hbd.imp (fun ⟨hb, hd'⟩ => ⟨by rw [inv hb, hu], by rw [inv hd', hd]⟩)
      (fun ⟨hb, hd'⟩ => ⟨by rw [inv hb, hd], by rw [inv hd', hu]⟩)⟩
/-- Every unit rhombus `(a, b, c, d)` in `Vertex (m + 2)` arises from a downward unit triangle
`down s` and an adjacent upward triangle `adjacentUp s i` up to exchanging the obtuse corners
`a, c` and exchanging the acute corners `b, d`. -/
theorem IsRhombus.exists_adjacentUp {a b c d : Vertex (m + 2)} (hr : IsRhombus a b c d) :
    ∃ (s : Vertex m) (i : Fin 3),
      ((a = (UnitTriangle.down s).vertex (i + 2) ∧ c = (UnitTriangle.down s).vertex (i + 1)) ∨
        (a = (UnitTriangle.down s).vertex (i + 1) ∧ c = (UnitTriangle.down s).vertex (i + 2))) ∧
      ((b = (adjacentUp s i).vertex i ∧ d = (UnitTriangle.down s).vertex i) ∨
        (b = (UnitTriangle.down s).vertex i ∧ d = (adjacentUp s i).vertex i)) := by
  have hx_case {a' b' c' d' : Vertex (m + 2)} (hr' : IsRhombus a' b' c' d')
      (h : (b'.x : ℤ) - d'.x = 2 ∨ (b'.x : ℤ) - d'.x = -2) :
      ∃ s i, IsAdjRhombus s i a' b' c' d' := by
    rcases h with h2 | hm2
    · obtain ⟨s, hac, hb, hd⟩ := exists_adjacentUp_of_sub_x_eq_two hr' h2
      exact ⟨s, 0, hac, Or.inl ⟨hb, hd⟩⟩
    · obtain ⟨s, hac, hd, hb⟩ := exists_adjacentUp_of_sub_x_eq_two hr'.reverse (by omega)
      exact ⟨s, 0, hac, Or.inr ⟨hb, hd⟩⟩
  have hlong := hr.long; rw [Vertex.sqDist_def] at hlong
  have hsq_le {u : ℤ} (hu6 : u ^ 2 ≤ 6) (h2 : u ≠ 2) (hm2 : u ≠ -2) : u ^ 2 ≤ 1 := by
    have : -1 ≤ u ∧ u ≤ 1 := by have : -2 ≤ u ∧ u ≤ 2 := ⟨by nlinarith, by nlinarith⟩; omega
    nlinarith
  by_cases hx : (b.x : ℤ) - d.x = 2 ∨ (b.x : ℤ) - d.x = -2
  · exact hx_case hr hx
  by_cases hz : (b.z : ℤ) - d.z = 2 ∨ (b.z : ℤ) - d.z = -2
  · exact exists_adjacentUp_of_rotate (hx_case hr.rotate (by simpa using hz))
  have hy : (b.y : ℤ) - d.y = 2 ∨ (b.y : ℤ) - d.y = -2 := by
    by_contra! hny; push Not at hx hz
    linarith [hsq_le (by nlinarith) hx.1 hx.2, hsq_le (by nlinarith) hny.1 hny.2,
      hsq_le (by nlinarith) hz.1 hz.2]
  exact exists_adjacentUp_of_rotate
    (exists_adjacentUp_of_rotate (hx_case hr.rotate.rotate (by simpa using hy)))

/-- The union of the cells of `adjacentUp s i` and `down s`, a continuous unit rhombus inside
`barycentricSimplex (m + 2)`. -/
def adjacentCell (s : Vertex m) (i : Fin 3) : Set (Fin 3 → ℝ) :=
  (adjacentUp s i).cell ∪ (UnitTriangle.down s).cell
@[simp] theorem mem_adjacentCell_iff {s : Vertex m} {i : Fin 3} {x : Fin 3 → ℝ} :
    x ∈ adjacentCell s i ↔ x ∈ (adjacentUp s i).cell ∨ x ∈ (UnitTriangle.down s).cell := Iff.rfl
/-- `adjacentCell s i` is cut out inside `barycentricSimplex (m + 2)` by bounding the two
coordinates other than `i` to `[s_{i+1}, s_{i+1} + 1]` and `[s_{i+2}, s_{i+2} + 1]`. -/
theorem adjacentCell_eq (s : Vertex m) (i : Fin 3) :
    adjacentCell s i = {x ∈ barycentricSimplex (m + 2) |
      (s.coord (i + 1) : ℝ) ≤ x (i + 1) ∧ x (i + 1) ≤ (s.coord (i + 1) : ℝ) + 1 ∧
      (s.coord (i + 2) : ℝ) ≤ x (i + 2) ∧ x (i + 2) ≤ (s.coord (i + 2) : ℝ) + 1} := by
  ext x; simp only [adjacentCell, mem_union, UnitTriangle.mem_cell_iff, mem_ofPred_eq]
  have hs : (s.x : ℝ) + s.y + s.z = m := by exact_mod_cast s.sum_eq
  refine ⟨fun h => ?_, fun ⟨hx, h1, h2, h3, h4⟩ => ?_⟩
  · rcases h with ⟨hx, hw⟩ | ⟨hx, hw⟩ <;>
    · have hsum : x 0 + x 1 + x 2 = m + 2 := by simpa [Fin.sum_univ_three, add_assoc] using hx.2
      have h0 := hw 0; have h1 := hw 1; have h2 := hw 2
      refine ⟨hx, ?_, ?_, ?_, ?_⟩ <;> (fin_cases i <;> simp at h0 h1 h2 ⊢ <;> linarith [hs, hsum])
  · have : x 0 + x 1 + x 2 = m + 2 := by simpa [Fin.sum_univ_three, add_assoc] using hx.2
    rcases le_total ((s.coord i : ℝ) + 1) (x i) with h | h <;>
      [refine Or.inl ⟨hx, fun k => ?_⟩; refine Or.inr ⟨hx, fun k => ?_⟩] <;>
      (fin_cases i <;> fin_cases k <;> simp at h1 h2 h3 h4 h ⊢ <;> linarith)
/-- Every union rhombus cell `adjacentCell s i` is a convex polyhedron. -/
theorem isConvexPolyhedron_adjacentCell (s : Vertex m) (i : Fin 3) :
    IsConvexPolyhedron (adjacentCell s i) := by
  let p (k : Fin 3) : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj k).toContinuousAffineMap
  let c (k : Fin 3) : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ _ (s.coord k : ℝ)
  let one : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ _ 1
  convert (isConvexPolyhedron_barycentricSimplex (m + 2)).inter (isConvexPolyhedron_setOf_forall
    ![c (i + 1) - p (i + 1), p (i + 1) - (c (i + 1) + one),
      c (i + 2) - p (i + 2), p (i + 2) - (c (i + 2) + one)]) using 1
  ext x; simp [adjacentCell_eq, p, c, one, Fin.forall_fin_succ, and_assoc]
theorem convex_adjacentCell (s : Vertex m) (i : Fin 3) : Convex ℝ (adjacentCell s i) :=
  (isConvexPolyhedron_adjacentCell s i).convex

end TauCeti.Hive
