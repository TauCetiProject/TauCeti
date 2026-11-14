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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Unit edges, unit triangles, and the simplicial subdivision of the hive triangle

For `n ≥ 1`, the continuous barycentric triangle
`barycentricSimplex n = {x : Fin 3 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = n}`
and its Euclidean planar realization `planarSimplex n ⊆ ℝ²` are tiled by `n²` unit equilateral
triangles (`TauCeti.Hive.UnitTriangle n`):
- `n * (n + 1) / 2` **upward** unit triangles `UnitTriangle.up base` (`base : Vertex (n - 1)`),
  cut out inside `barycentricSimplex n` by `base.coord i ≤ x i` for `i : Fin 3`, with vertices
  `base + (1, 0, 0)`, `base + (0, 1, 0)`, `base + (0, 0, 1)`;
- `(n - 1) * n / 2` **downward** unit triangles `UnitTriangle.down base` (`base : Vertex (n - 2)`),
  cut out inside `barycentricSimplex n` by `x i ≤ base.coord i + 1` for `i : Fin 3`, with vertices
  `base + (0, 1, 1)`, `base + (1, 0, 1)`, `base + (1, 1, 0)`.

Each unit triangle carries three continuous affine barycentric coordinate weights `T.weight i`
summing to `1` on `{x | ∑ i, x i = n}`, expressing its closed cell `T.cell` both as a
`TauCeti.IsConvexPolyhedron` and as the `convexHull` of its three lattice vertices.

## Main definitions

* `TauCeti.Hive.Vertex.barycentric`, `TauCeti.Hive.barycentricSimplex`: real barycentric embedding
  of lattice vertices and the continuous size-`n` barycentric simplex.
* `TauCeti.Hive.planeLinear`, `TauCeti.Hive.planeInvAffine`, `TauCeti.Hive.planarSimplex`:
  continuous linear planar projection, its affine inverse on sum-`n` triples, and the Euclidean
  size-`n` triangle.
* `TauCeti.Hive.IsUnitEdge`, `TauCeti.Hive.UnitEdge`: unit lattice edges (`sqDist = 2`, Euclidean
  length `1`).
* `TauCeti.Hive.UnitTriangle`: upward and downward unit triangles of `Δₙ`, with vertices, dihedral
  symmetries, subtriangle shifts, affine barycentric weights `weight`, and polyhedral cells `cell`.

## Main results

* `TauCeti.Hive.Vertex.card`, `TauCeti.Hive.UnitTriangle.card`: `|Vertex n| = (n + 1)(n + 2) / 2`
  and `|UnitTriangle n| = n ^ 2`.
* `TauCeti.Hive.UnitTriangle.isConvexPolyhedron_cell`,
  `TauCeti.Hive.UnitTriangle.cell_eq_convexHull`,
  `TauCeti.Hive.UnitTriangle.iUnion_cell_eq_barycentricSimplex`.
* `TauCeti.Hive.UnitTriangle.mem_range_vertex_of_weight_pos`: active vertices of a point lying in
  two unit-triangle cells belong to both triangles.
* `TauCeti.Hive.exists_cell_of_isUnitEdge`: every unit lattice edge lies in a unit-triangle cell.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §2 and
  Appendix 2.
-/

public section

open Set
open scoped BigOperators

namespace TauCeti.Hive

/-! ### Real barycentric coordinates, the continuous simplex, and the Euclidean chart -/

namespace Vertex

variable {n : ℕ}

theorem ext_coord {p q : Vertex n} (h : ∀ i : Fin 3, p.coord i = q.coord i) : p = q :=
  Vertex.ext (by simpa using h 0) (by simpa using h 1) (by simpa using h 2)

@[simp] theorem coord_add {m : ℕ} (p : Vertex n) (q : Vertex m) (i : Fin 3) :
    (p.add q).coord i = p.coord i + q.coord i := by
  fin_cases i <;> simp

theorem coord_rotate (p : Vertex n) (i : Fin 3) : p.rotate.coord (i + 1) = p.coord i := by
  fin_cases i <;> simp

theorem coord_reflect (p : Vertex n) (i : Fin 3) : p.reflect.coord (-i) = p.coord i := by
  have h1 : (-1 : Fin 3) = 2 := rfl
  have h2 : (-2 : Fin 3) = 1 := rfl
  fin_cases i <;> simp [h1, h2]

@[simp] theorem rotate_add {m : ℕ} (p : Vertex n) (q : Vertex m) :
    (p.add q).rotate = p.rotate.add q.rotate := by
  ext <;> simp

@[simp] theorem reflect_add {m : ℕ} (p : Vertex n) (q : Vertex m) :
    (p.add q).reflect = p.reflect.add q.reflect := by
  ext <;> simp

/-- Embed a lattice vertex `p : Vertex n` into real barycentric coordinates `Fin 3 → ℝ`. -/
def barycentric (p : Vertex n) : Fin 3 → ℝ := fun i => (p.coord i : ℝ)

@[simp] theorem barycentric_apply (p : Vertex n) (i : Fin 3) :
    p.barycentric i = (p.coord i : ℝ) := (rfl)

theorem barycentric_nonneg (p : Vertex n) (i : Fin 3) : 0 ≤ p.barycentric i :=
  Nat.cast_nonneg (p.coord i)

theorem sum_barycentric (p : Vertex n) : ∑ i, p.barycentric i = (n : ℝ) := by
  have hp : (p.x : ℝ) + p.y + p.z = n := by exact_mod_cast p.sum_eq
  simpa [Fin.sum_univ_three, add_assoc] using hp

theorem barycentric_injective : Function.Injective (barycentric (n := n)) := fun _ _ h =>
  ext_coord fun i => Nat.cast_injective (congrFun h i)

@[simp] theorem barycentric_eq_iff {p q : Vertex n} :
    p.barycentric = q.barycentric ↔ p = q := barycentric_injective.eq_iff

@[simp] theorem barycentric_add {m : ℕ} (p : Vertex n) (q : Vertex m) :
    (p.add q).barycentric = p.barycentric + q.barycentric := by
  ext i; fin_cases i <;> simp

@[simp] theorem barycentric_cornerA_zero : (cornerA 0).barycentric = 0 := by
  ext i; fin_cases i <;> simp

theorem sqDist_eq_sum_sub_sq (p q : Vertex n) :
    (p.sqDist q : ℝ) = ∑ i, (p.barycentric i - q.barycentric i) ^ 2 := by
  simp [sqDist_def, Fin.sum_univ_three, add_assoc]

/-- At size `0`, the unique lattice vertex is `cornerA 0 = (0, 0, 0)`. -/
instance uniqueZero : Unique (Vertex 0) where
  default := cornerA 0
  uniq p := by have := p.sum_eq; ext <;> simp <;> omega

/-- Splitting `Vertex (n + 1)` into side `B → C` (`x = 0`) and `(1, 0, 0) + Vertex n` (`x > 0`). -/
def equivFinSumSucc (n : ℕ) : Vertex (n + 1) ≃ Fin (n + 2) ⊕ Vertex n where
  toFun p :=
    if hx : p.x = 0 then
      Sum.inl ⟨p.z, by have := p.sum_eq; omega⟩
    else
      Sum.inr ⟨p.x - 1, p.y, p.z, by have := p.sum_eq; omega⟩
  invFun
    | Sum.inl k => edgePoint (n + 1) 1 k
    | Sum.inr q => ⟨q.x + 1, q.y, q.z, by have := q.sum_eq; omega⟩
  left_inv p := by
    by_cases hx : p.x = 0
    · simp only [hx, ↓reduceDIte]
      ext <;> simp <;> have := p.sum_eq <;> omega
    · simp only [hx, ↓reduceDIte]
      ext <;> simp; omega
  right_inv
    | Sum.inl k => by simp
    | Sum.inr q => by simp

theorem two_mul_card (n : ℕ) : 2 * Fintype.card (Vertex n) = (n + 1) * (n + 2) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fintype.card_congr (equivFinSumSucc m), Fintype.card_sum, Fintype.card_fin]
    calc 2 * (m + 2 + Fintype.card (Vertex m))
        = 2 * (m + 2) + 2 * Fintype.card (Vertex m) := by ring
      _ = 2 * (m + 2) + (m + 1) * (m + 2) := by rw [ih]
      _ = (m + 1 + 1) * (m + 1 + 2) := by ring

/-- The triangular lattice `Vertex n` has `(n + 1) * (n + 2) / 2` vertices. -/
theorem card (n : ℕ) : Fintype.card (Vertex n) = (n + 1) * (n + 2) / 2 := by
  rw [← two_mul_card n]
  omega

end Vertex

/-- The continuous size-`n` barycentric simplex `{x : Fin 3 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = n}`.
-/
def barycentricSimplex (n : ℕ) : Set (Fin 3 → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = (n : ℝ)}

@[simp] theorem mem_barycentricSimplex_iff {n : ℕ} {x : Fin 3 → ℝ} :
    x ∈ barycentricSimplex n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = (n : ℝ) := Iff.rfl

theorem barycentric_mem_barycentricSimplex {n : ℕ} (p : Vertex n) :
    p.barycentric ∈ barycentricSimplex n :=
  ⟨p.barycentric_nonneg, p.sum_barycentric⟩

@[simp] theorem barycentricSimplex_zero : barycentricSimplex 0 = {0} := by
  ext x
  simp only [mem_barycentricSimplex_iff, Nat.cast_zero, Fin.sum_univ_three, mem_singleton_iff]
  refine ⟨fun ⟨hpos, hsum⟩ => ?_, fun hx => by subst hx; simp⟩
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
  ext i; fin_cases i <;> simp <;> linarith [h0, h1, h2, hsum]

theorem add_mem_barycentricSimplex {m k : ℕ} {x y : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex m) (hy : y ∈ barycentricSimplex k) :
    x + y ∈ barycentricSimplex (m + k) :=
  ⟨fun i => add_nonneg (hx.1 i) (hy.1 i), by
    simp [Finset.sum_add_distrib, hx.2, hy.2, Nat.cast_add]⟩

/-- The continuous affine coordinate functional `x ↦ x i` on `Fin 3 → ℝ`. -/
def coordAffine (i : Fin 3) : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).toContinuousAffineMap

@[simp] theorem coordAffine_apply (i : Fin 3) (x : Fin 3 → ℝ) : coordAffine i x = x i := (rfl)

@[simp] theorem coordAffine_contLinear (i : Fin 3) :
    (coordAffine i).contLinear = ContinuousLinearMap.proj i := (rfl)

/-- The continuous barycentric simplex `barycentricSimplex n` is a convex polyhedron. -/
theorem isConvexPolyhedron_barycentricSimplex (n : ℕ) :
    IsConvexPolyhedron (barycentricSimplex n) := by
  let S : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := coordAffine 0 + coordAffine 1 + coordAffine 2
  let c : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ (Fin 3 → ℝ) (n : ℝ)
  let g : Fin 5 → ((Fin 3 → ℝ) →ᴬ[ℝ] ℝ) :=
    ![-coordAffine 0, -coordAffine 1, -coordAffine 2, S - c, c - S]
  have heq : barycentricSimplex n = {x | ∀ i, g i x ≤ 0} := by
    ext x
    simp only [mem_barycentricSimplex_iff, mem_ofPred_eq, Fin.forall_fin_succ,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true, Fin.sum_univ_three,
      g, S, c, Matrix.cons_val_zero, Matrix.cons_val_succ, ContinuousAffineMap.neg_apply,
      ContinuousAffineMap.sub_apply, ContinuousAffineMap.add_apply, coordAffine_apply,
      ContinuousAffineMap.coe_const, Function.const_apply]
    refine ⟨fun ⟨⟨_, _, _⟩, _⟩ =>
        ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩,
      fun ⟨_, _, _, _, _⟩ => ⟨⟨by linarith, by linarith, by linarith⟩, by linarith⟩⟩
  rw [heq]
  exact isConvexPolyhedron_setOf_forall g

theorem convex_barycentricSimplex (n : ℕ) : Convex ℝ (barycentricSimplex n) :=
  (isConvexPolyhedron_barycentricSimplex n).convex

theorem isClosed_barycentricSimplex (n : ℕ) : IsClosed (barycentricSimplex n) :=
  (isConvexPolyhedron_barycentricSimplex n).isClosed

/-- `barycentricSimplex n` is the convex hull of the three perimeter corners `(n, 0, 0)`,
`(0, n, 0)`, `(0, 0, n)`. -/
theorem barycentricSimplex_eq_convexHull_corners (n : ℕ) :
    barycentricSimplex n =
      convexHull ℝ (Set.range fun s : Fin 3 => (Vertex.edgePoint n s 0).barycentric) := by
  refine Subset.antisymm (fun x hx => ?_)
    (convexHull_min (by rintro _ ⟨s, rfl⟩; exact barycentric_mem_barycentricSimplex _)
      (convex_barycentricSimplex n))
  rcases eq_or_ne n 0 with rfl | hn
  · rw [barycentricSimplex_zero, mem_singleton_iff] at hx
    rw [hx]
    exact subset_convexHull ℝ _ ⟨0, by simp⟩
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hw : ∀ s : Fin 3, 0 ≤ x s / n := fun s => div_nonneg (hx.1 s) hn'.le
    have hsum : ∑ s : Fin 3, x s / n = 1 := by
      rw [← Finset.sum_div, hx.2, div_self hn'.ne']
    have hcomb : ∑ s : Fin 3, (x s / n) • (Vertex.edgePoint n s 0).barycentric = x := by
      ext i
      simp only [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Vertex.barycentric_apply]
      fin_cases i <;> simp [div_mul_cancel₀ _ hn'.ne']
    rw [← hcomb]
    exact (convex_convexHull ℝ _).sum_mem (fun s _ => hw s) hsum
      fun s _ => subset_convexHull ℝ _ ⟨s, rfl⟩

theorem barycentricSimplex_eq_convexHull (n : ℕ) :
    barycentricSimplex n = convexHull ℝ (Set.range (Vertex.barycentric (n := n))) := by
  refine Subset.antisymm ?_
    (convexHull_min (by rintro _ ⟨p, rfl⟩; exact barycentric_mem_barycentricSimplex p)
      (convex_barycentricSimplex n))
  rw [barycentricSimplex_eq_convexHull_corners]
  exact convexHull_mono (by rintro _ ⟨s, rfl⟩; exact ⟨Vertex.edgePoint n s 0, rfl⟩)

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

@[simp] theorem planeLinear_barycentric {n : ℕ} (p : Vertex n) :
    planeLinear p.barycentric = p.plane := by
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
    planeInvAffine n u 0 = (n : ℝ) - u 0 - u 1 / Real.sqrt 3 := by
  simp [planeInvAffine]; ring

@[simp] theorem planeInvAffine_one_coord (n : ℕ) (u : EuclideanSpace ℝ (Fin 2)) :
    planeInvAffine n u 1 = 2 * u 1 / Real.sqrt 3 := by
  simp [planeInvAffine]

@[simp] theorem planeInvAffine_two_coord (n : ℕ) (u : EuclideanSpace ℝ (Fin 2)) :
    planeInvAffine n u 2 = u 0 - u 1 / Real.sqrt 3 := by
  simp [planeInvAffine]

@[simp] theorem sum_planeInvAffine (n : ℕ) (u : EuclideanSpace ℝ (Fin 2)) :
    ∑ i, planeInvAffine n u i = (n : ℝ) := by
  simp [Fin.sum_univ_three]; ring

@[simp] theorem planeLinear_planeInvAffine (n : ℕ) (u : EuclideanSpace ℝ (Fin 2)) :
    planeLinear (planeInvAffine n u) = u := by
  have hs : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  ext i; fin_cases i
  · simp; ring
  · simp; field_simp

theorem planeInvAffine_planeLinear {n : ℕ} {x : Fin 3 → ℝ} (hx : ∑ i, x i = (n : ℝ)) :
    planeInvAffine n (planeLinear x) = x := by
  have hs : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hx' : x 0 + x 1 + x 2 = (n : ℝ) := by simpa [Fin.sum_univ_three, add_assoc] using hx
  ext i; fin_cases i
  · simp; field_simp; linarith
  · simp; field_simp
  · simp; field_simp; ring

@[simp] theorem planeInvAffine_plane {n : ℕ} (p : Vertex n) :
    planeInvAffine n p.plane = p.barycentric := by
  rw [← planeLinear_barycentric, planeInvAffine_planeLinear p.sum_barycentric]

/-- The continuous size-`n` equilateral triangle in `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def planarSimplex (n : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  planeLinear '' barycentricSimplex n

theorem planarSimplex_eq_preimage (n : ℕ) :
    planarSimplex n = planeInvAffine n ⁻¹' barycentricSimplex n := by
  ext u
  simp only [planarSimplex, mem_image, mem_preimage]
  refine ⟨?_, fun hu => ⟨planeInvAffine n u, hu, planeLinear_planeInvAffine n u⟩⟩
  rintro ⟨x, hx, rfl⟩
  rwa [planeInvAffine_planeLinear hx.2]

@[simp] theorem mem_planarSimplex_iff {n : ℕ} {u : EuclideanSpace ℝ (Fin 2)} :
    u ∈ planarSimplex n ↔ planeInvAffine n u ∈ barycentricSimplex n := by
  rw [planarSimplex_eq_preimage]; rfl

theorem plane_mem_planarSimplex {n : ℕ} (p : Vertex n) : p.plane ∈ planarSimplex n :=
  ⟨p.barycentric, barycentric_mem_barycentricSimplex p, planeLinear_barycentric p⟩

theorem isConvexPolyhedron_planarSimplex (n : ℕ) : IsConvexPolyhedron (planarSimplex n) := by
  rw [planarSimplex_eq_preimage]
  exact (isConvexPolyhedron_barycentricSimplex n).preimage (planeInvAffine n)

theorem convex_planarSimplex (n : ℕ) : Convex ℝ (planarSimplex n) :=
  (isConvexPolyhedron_planarSimplex n).convex

theorem isClosed_planarSimplex (n : ℕ) : IsClosed (planarSimplex n) :=
  (isConvexPolyhedron_planarSimplex n).isClosed

theorem planarSimplex_eq_convexHull (n : ℕ) :
    planarSimplex n = convexHull ℝ (Set.range (Vertex.plane (n := n))) := by
  have hcoe : (planeLinear : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 2)) =
      planeLinear.toLinearMap := rfl
  rw [planarSimplex, barycentricSimplex_eq_convexHull, hcoe, LinearMap.image_convexHull]
  congr 1
  ext u
  simp only [mem_image, mem_range]
  refine ⟨fun ⟨_, ⟨p, rfl⟩, hu⟩ => ⟨p, (planeLinear_barycentric p).symm.trans hu⟩,
    fun ⟨p, hp⟩ => ⟨p.barycentric, ⟨p, rfl⟩, (planeLinear_barycentric p).trans hp⟩⟩

/-! ### Unit lattice edges -/

/-- Two vertices `p, q : Vertex n` form a **unit lattice edge** if `p.sqDist q = 2`
(equivalently, Euclidean planar distance `1`). -/
def IsUnitEdge {n : ℕ} (p q : Vertex n) : Prop := p.sqDist q = 2

theorem isUnitEdge_def {n : ℕ} (p q : Vertex n) : IsUnitEdge p q ↔ p.sqDist q = 2 := Iff.rfl

instance {n : ℕ} (p q : Vertex n) : Decidable (IsUnitEdge p q) :=
  decidable_of_iff (p.sqDist q = 2) (isUnitEdge_def p q).symm

/-- The finite type of ordered unit edges in `Vertex n`. -/
abbrev UnitEdge (n : ℕ) := {e : Vertex n × Vertex n // IsUnitEdge e.1 e.2}

namespace IsUnitEdge

variable {n : ℕ} {p q : Vertex n}

theorem symm (h : IsUnitEdge p q) : IsUnitEdge q p := by
  rwa [isUnitEdge_def, Vertex.sqDist_comm]

theorem ne (h : IsUnitEdge p q) : p ≠ q := by
  rintro rfl
  rw [isUnitEdge_def, Vertex.sqDist_self] at h
  omega

theorem one_le (h : IsUnitEdge p q) : 1 ≤ n := by
  by_contra hn
  obtain rfl : n = 0 := by omega
  exact h.ne (Subsingleton.elim p q)

theorem dist_plane_sq (h : IsUnitEdge p q) : dist p.plane q.plane ^ 2 = 1 := by
  have hsq : p.sqDist q = 2 := h
  rw [Vertex.dist_plane_sq, hsq]; norm_num

theorem dist_plane (h : IsUnitEdge p q) : dist p.plane q.plane = 1 := by
  have hd : 0 ≤ dist p.plane q.plane := dist_nonneg
  nlinarith [h.dist_plane_sq]

theorem rotate (h : IsUnitEdge p q) : IsUnitEdge p.rotate q.rotate := by
  simpa [IsUnitEdge] using h

theorem reflect (h : IsUnitEdge p q) : IsUnitEdge p.reflect q.reflect := by
  simpa [IsUnitEdge] using h

theorem add {m : ℕ} (h : IsUnitEdge p q) (r : Vertex m) : IsUnitEdge (r.add p) (r.add q) := by
  simpa [IsUnitEdge] using h

end IsUnitEdge

theorem isUnitEdge_comm {n : ℕ} {p q : Vertex n} :
    IsUnitEdge p q ↔ IsUnitEdge q p := ⟨IsUnitEdge.symm, IsUnitEdge.symm⟩

@[simp] theorem isUnitEdge_rotate_iff {n : ℕ} {p q : Vertex n} :
    IsUnitEdge p.rotate q.rotate ↔ IsUnitEdge p q := by simp [IsUnitEdge]

@[simp] theorem isUnitEdge_reflect_iff {n : ℕ} {p q : Vertex n} :
    IsUnitEdge p.reflect q.reflect ↔ IsUnitEdge p q := by simp [IsUnitEdge]

@[simp] theorem isUnitEdge_add_left_iff {m n : ℕ} (r : Vertex m) {p q : Vertex n} :
    IsUnitEdge (r.add p) (r.add q) ↔ IsUnitEdge p q := by simp [IsUnitEdge]

/-- Consecutive perimeter vertices along any side `s` form a unit edge. -/
theorem isUnitEdge_edgePoint_succ (n : ℕ) (s : Fin 3) (k : Fin n) :
    IsUnitEdge (Vertex.edgePoint n s k.castSucc) (Vertex.edgePoint n s k.succ) := by
  have hk : k.val + 1 ≤ n := k.isLt
  have hsub : ((n - (k.val + 1) : ℕ) : ℤ) = (n : ℤ) - k.val - 1 := by omega
  have hsub0 : ((n - k.val : ℕ) : ℤ) = (n : ℤ) - k.val := by omega
  fin_cases s <;>
    · rw [isUnitEdge_def, Vertex.sqDist_def]
      simp [hsub, hsub0]

namespace IsRhombus

variable {n : ℕ} {a b c d : Vertex n}

theorem isUnitEdge_short (h : IsRhombus a b c d) : IsUnitEdge a c := h.short
theorem isUnitEdge_ab (h : IsRhombus a b c d) : IsUnitEdge a b := h.side_ab
theorem isUnitEdge_bc (h : IsRhombus a b c d) : IsUnitEdge b c := h.side_bc
theorem isUnitEdge_cd (h : IsRhombus a b c d) : IsUnitEdge c d := h.side_cd
theorem isUnitEdge_da (h : IsRhombus a b c d) : IsUnitEdge d a := h.side_da

end IsRhombus

/-! ### Standard corners and unit triangles -/

/-- The `i`-th corner of `Δ₁`: `(1, 0, 0)`, `(0, 1, 0)`, `(0, 0, 1)`. -/
def unitCorner : Fin 3 → Vertex 1
  | ⟨0, _⟩ => ⟨1, 0, 0, rfl⟩
  | ⟨1, _⟩ => ⟨0, 1, 0, rfl⟩
  | ⟨2, _⟩ => ⟨0, 0, 1, rfl⟩

@[simp] theorem unitCorner_coord (i j : Fin 3) :
    (unitCorner i).coord j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [unitCorner]

@[simp] theorem unitCorner_x (i : Fin 3) : (unitCorner i).x = if i = 0 then 1 else 0 := by
  fin_cases i <;> rfl

@[simp] theorem unitCorner_y (i : Fin 3) : (unitCorner i).y = if i = 1 then 1 else 0 := by
  fin_cases i <;> rfl

@[simp] theorem unitCorner_z (i : Fin 3) : (unitCorner i).z = if i = 2 then 1 else 0 := by
  fin_cases i <;> rfl

@[simp] theorem rotate_unitCorner (i : Fin 3) : (unitCorner i).rotate = unitCorner (i + 1) := by
  fin_cases i <;> ext <;> simp [unitCorner]

@[simp] theorem reflect_unitCorner (i : Fin 3) : (unitCorner i).reflect = unitCorner (-i) := by
  have h1 : (-1 : Fin 3) = 2 := rfl
  have h2 : (-2 : Fin 3) = 1 := rfl
  fin_cases i <;> ext <;> simp [unitCorner, h1, h2]

/-- The `i`-th midpoint vertex of `Δ₂` opposite corner `i`:
`(0, 1, 1)`, `(1, 0, 1)`, `(1, 1, 0)`. -/
def oppUnitCorner : Fin 3 → Vertex 2
  | ⟨0, _⟩ => ⟨0, 1, 1, rfl⟩
  | ⟨1, _⟩ => ⟨1, 0, 1, rfl⟩
  | ⟨2, _⟩ => ⟨1, 1, 0, rfl⟩

@[simp] theorem oppUnitCorner_coord (i j : Fin 3) :
    (oppUnitCorner i).coord j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> simp [oppUnitCorner]

@[simp] theorem rotate_oppUnitCorner (i : Fin 3) :
    (oppUnitCorner i).rotate = oppUnitCorner (i + 1) := by
  fin_cases i <;> ext <;> simp [oppUnitCorner]

@[simp] theorem reflect_oppUnitCorner (i : Fin 3) :
    (oppUnitCorner i).reflect = oppUnitCorner (-i) := by
  have h1 : (-1 : Fin 3) = 2 := rfl
  have h2 : (-2 : Fin 3) = 1 := rfl
  fin_cases i <;> ext <;> simp [oppUnitCorner, h1, h2]

/-- A unit equilateral lattice triangle inside `Δₙ`: either an **upward** triangle translated by
`base : Vertex (n - 1)`, or a **downward** triangle translated by `base : Vertex (n - 2)`. -/
inductive UnitTriangle : ℕ → Type
  /-- An upward unit triangle of `Δ_{m + 1}` with base vertex `base : Vertex m`. -/
  | up {m : ℕ} (base : Vertex m) : UnitTriangle (m + 1)
  /-- A downward unit triangle of `Δ_{m + 2}` with base vertex `base : Vertex m`. -/
  | down {m : ℕ} (base : Vertex m) : UnitTriangle (m + 2)

namespace UnitTriangle

instance isEmptyZero : IsEmpty (UnitTriangle 0) := ⟨fun T => nomatch T⟩

/-- At size `1`, the unique unit triangle is `up (cornerA 0)`. -/
def equivOne : UnitTriangle 1 ≃ Vertex 0 where
  toFun
    | up base => base
  invFun base := up base
  left_inv
    | up _ => rfl
  right_inv _ := rfl

instance uniqueOne : Unique (UnitTriangle 1) := Equiv.unique equivOne

/-- For `n = m + 2`, unit triangles decompose into upward (`Vertex (m + 1)`) and downward
(`Vertex m`) triangles. -/
def equivSuccSucc (m : ℕ) : UnitTriangle (m + 2) ≃ Vertex (m + 1) ⊕ Vertex m where
  toFun
    | up base => Sum.inl base
    | down base => Sum.inr base
  invFun
    | Sum.inl base => up base
    | Sum.inr base => down base
  left_inv
    | up _ => rfl
    | down _ => rfl
  right_inv
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl

instance instDecidableEq : {n : ℕ} → DecidableEq (UnitTriangle n)
  | 0 => fun T => nomatch T
  | 1 => Equiv.decidableEq equivOne
  | m + 2 => Equiv.decidableEq (equivSuccSucc m)

instance instFintype : (n : ℕ) → Fintype (UnitTriangle n)
  | 0 => Fintype.ofIsEmpty
  | 1 => Fintype.ofEquiv (Vertex 0) equivOne.symm
  | m + 2 => Fintype.ofEquiv (Vertex (m + 1) ⊕ Vertex m) (equivSuccSucc m).symm

/-- `Δₙ` is tiled by `n ^ 2` unit triangles. -/
theorem card (n : ℕ) : Fintype.card (UnitTriangle n) = n ^ 2 := by
  match n with
  | 0 => simp
  | 1 => rw [Fintype.card_congr equivOne, Vertex.card 0]; norm_num
  | m + 2 =>
    rw [Fintype.card_congr (equivSuccSucc m), Fintype.card_sum]
    have h2c : 2 * (Fintype.card (Vertex (m + 1)) + Fintype.card (Vertex m)) = 2 * (m + 2) ^ 2 :=
      calc 2 * (Fintype.card (Vertex (m + 1)) + Fintype.card (Vertex m))
          = 2 * Fintype.card (Vertex (m + 1)) + 2 * Fintype.card (Vertex m) := by ring
        _ = (m + 2) * (m + 3) + (m + 1) * (m + 2) := by
            rw [Vertex.two_mul_card (m + 1), Vertex.two_mul_card m]
        _ = 2 * (m + 2) ^ 2 := by ring
    exact Nat.mul_left_cancel Nat.zero_lt_two h2c

/-- The `i`-th vertex of a unit triangle `T : UnitTriangle n`. -/
def vertex {n : ℕ} : UnitTriangle n → Fin 3 → Vertex n
  | up base, i => base.add (unitCorner i)
  | down base, i => base.add (oppUnitCorner i)

@[simp] theorem vertex_up {m : ℕ} (base : Vertex m) (i : Fin 3) :
    (up base).vertex i = base.add (unitCorner i) := (rfl)

@[simp] theorem vertex_down {m : ℕ} (base : Vertex m) (i : Fin 3) :
    (down base).vertex i = base.add (oppUnitCorner i) := (rfl)

theorem vertex_coord_up {m : ℕ} (base : Vertex m) (i j : Fin 3) :
    ((up base).vertex i).coord j = base.coord j + if i = j then 1 else 0 := by
  fin_cases j <;> simp

theorem vertex_coord_down {m : ℕ} (base : Vertex m) (i j : Fin 3) :
    ((down base).vertex i).coord j = base.coord j + if i = j then 0 else 1 := by
  fin_cases j <;> simp [vertex_down, ← oppUnitCorner_coord i _]

theorem vertex_injective {n : ℕ} (T : UnitTriangle n) : Function.Injective T.vertex := by
  intro i j h
  cases T with
  | up base =>
    have hc := congrArg (fun p => p.coord i) h
    simp only [vertex_coord_up, ↓reduceIte] at hc
    by_contra hij
    simp [Ne.symm hij] at hc
  | down base =>
    have hc := congrArg (fun p => p.coord i) h
    simp only [vertex_coord_down, ↓reduceIte] at hc
    by_contra hij
    simp [Ne.symm hij] at hc

/-- Any two distinct vertices of a unit triangle form a unit lattice edge. -/
theorem isUnitEdge_vertex {n : ℕ} (T : UnitTriangle n) {i j : Fin 3} (hij : i ≠ j) :
    IsUnitEdge (T.vertex i) (T.vertex j) := by
  cases T with
  | up base =>
    rw [vertex_up, vertex_up, isUnitEdge_add_left_iff, isUnitEdge_def]
    fin_cases i <;> fin_cases j <;> simp_all [unitCorner, Vertex.sqDist_def]
  | down base =>
    rw [vertex_down, vertex_down, isUnitEdge_add_left_iff, isUnitEdge_def]
    fin_cases i <;> fin_cases j <;> simp_all [oppUnitCorner, Vertex.sqDist_def]

/-- Clockwise rotation of a unit triangle by one third of a turn. -/
def rotate {n : ℕ} : UnitTriangle n → UnitTriangle n
  | up base => up base.rotate
  | down base => down base.rotate

@[simp] theorem rotate_up {m : ℕ} (base : Vertex m) : (up base).rotate = up base.rotate := (rfl)
@[simp] theorem rotate_down {m : ℕ} (base : Vertex m) :
    (down base).rotate = down base.rotate := (rfl)

@[simp] theorem rotate_rotate_rotate {n : ℕ} (T : UnitTriangle n) :
    T.rotate.rotate.rotate = T := by cases T <;> simp

theorem vertex_rotate {n : ℕ} (T : UnitTriangle n) (i : Fin 3) :
    T.rotate.vertex (i + 1) = (T.vertex i).rotate := by
  cases T <;> simp

/-- Reflection of a unit triangle across `A = (n, 0, 0)`. -/
def reflect {n : ℕ} : UnitTriangle n → UnitTriangle n
  | up base => up base.reflect
  | down base => down base.reflect

@[simp] theorem reflect_up {m : ℕ} (base : Vertex m) : (up base).reflect = up base.reflect := (rfl)
@[simp] theorem reflect_down {m : ℕ} (base : Vertex m) :
    (down base).reflect = down base.reflect := (rfl)

@[simp] theorem reflect_reflect {n : ℕ} (T : UnitTriangle n) : T.reflect.reflect = T := by
  cases T <;> simp

theorem vertex_reflect {n : ℕ} (T : UnitTriangle n) (i : Fin 3) :
    T.reflect.vertex (-i) = (T.vertex i).reflect := by
  cases T <;> simp

/-- Translate a unit triangle of `Δₙ` into `Δ_{k + n}` by adding `p : Vertex k`. -/
def addLeft {k n : ℕ} (p : Vertex k) : UnitTriangle n → UnitTriangle (k + n)
  | up base => up (p.add base)
  | down base => down (p.add base)

@[simp] theorem addLeft_up {k m : ℕ} (p : Vertex k) (base : Vertex m) :
    (up base).addLeft p = up (p.add base) := (rfl)

@[simp] theorem addLeft_down {k m : ℕ} (p : Vertex k) (base : Vertex m) :
    (down base).addLeft p = down (p.add base) := (rfl)

@[simp] theorem vertex_addLeft {k n : ℕ} (p : Vertex k) (T : UnitTriangle n) (i : Fin 3) :
    (T.addLeft p).vertex i = p.add (T.vertex i) := by
  cases T <;> ext <;> simp [Nat.add_assoc]

/-! ### Continuous affine barycentric weights and polyhedral cells -/

/-- The `i`-th local barycentric weight of `T : UnitTriangle n` as a continuous affine functional
on `Fin 3 → ℝ`: `x i - base.coord i` on `up base` and `base.coord i + 1 - x i` on `down base`. -/
def weight {n : ℕ} : UnitTriangle n → Fin 3 → (Fin 3 → ℝ) →ᴬ[ℝ] ℝ
  | up base, i =>
      coordAffine i - ContinuousAffineMap.const ℝ (Fin 3 → ℝ) (base.coord i : ℝ)
  | down base, i =>
      ContinuousAffineMap.const ℝ (Fin 3 → ℝ) ((base.coord i : ℝ) + 1) - coordAffine i

@[simp] theorem weight_up_apply {m : ℕ} (base : Vertex m) (i : Fin 3) (x : Fin 3 → ℝ) :
    (up base).weight i x = x i - (base.coord i : ℝ) := (rfl)

@[simp] theorem weight_down_apply {m : ℕ} (base : Vertex m) (i : Fin 3) (x : Fin 3 → ℝ) :
    (down base).weight i x = (base.coord i : ℝ) + 1 - x i := (rfl)

@[simp] theorem weight_up_contLinear {m : ℕ} (base : Vertex m) (i : Fin 3) (v : Fin 3 → ℝ) :
    ((up base).weight i).contLinear v = v i := by simp [weight]

@[simp] theorem weight_down_contLinear {m : ℕ} (base : Vertex m) (i : Fin 3) (v : Fin 3 → ℝ) :
    ((down base).weight i).contLinear v = -v i := by simp [weight]

@[simp] theorem weight_vertex {n : ℕ} (T : UnitTriangle n) (i j : Fin 3) :
    T.weight i (T.vertex j).barycentric = if i = j then 1 else 0 := by
  cases T with
  | up base => fin_cases i <;> fin_cases j <;> simp [unitCorner]
  | down base => fin_cases i <;> fin_cases j <;> simp [oppUnitCorner]

theorem sum_weight {n : ℕ} (T : UnitTriangle n) {x : Fin 3 → ℝ} (hx : ∑ i, x i = (n : ℝ)) :
    ∑ i, T.weight i x = 1 := by
  cases T with
  | up base =>
    have hbsum : ∑ i : Fin 3, (base.coord i : ℝ) = ((_ : ℕ) : ℝ) := base.sum_barycentric
    simp only [weight_up_apply, Finset.sum_sub_distrib, hx, hbsum, Nat.cast_add, Nat.cast_one]
    ring
  | down base =>
    have hbsum : ∑ i : Fin 3, (base.coord i : ℝ) = ((_ : ℕ) : ℝ) := base.sum_barycentric
    simp only [weight_down_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul, hx, hbsum, Nat.cast_add, Nat.cast_ofNat]
    ring

theorem sum_weight_smul_vertex {n : ℕ} (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : ∑ i, x i = (n : ℝ)) :
    ∑ i, T.weight i x • (T.vertex i).barycentric = x := by
  have hsw := T.sum_weight hx
  ext j
  cases T with
  | up base =>
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Vertex.barycentric_apply,
      vertex_coord_up, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    have hsw' : ∑ i : Fin 3, (up base).weight i x = 1 := hsw
    calc ∑ i : Fin 3, (up base).weight i x * ((base.coord j : ℝ) + if i = j then 1 else 0)
        = (∑ i : Fin 3, (up base).weight i x) * (base.coord j : ℝ) + (up base).weight j x := by
          fin_cases j <;> { simp [Fin.sum_univ_three]; ring }
      _ = x j := by rw [hsw', one_mul, weight_up_apply]; ring
  | down base =>
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Vertex.barycentric_apply,
      vertex_coord_down, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    have hsw' : ∑ i : Fin 3, (down base).weight i x = 1 := hsw
    calc ∑ i : Fin 3, (down base).weight i x * ((base.coord j : ℝ) + if i = j then 0 else 1)
        = (∑ i : Fin 3, (down base).weight i x) * ((base.coord j : ℝ) + 1) -
            (down base).weight j x := by
          fin_cases j <;> { simp [Fin.sum_univ_three]; ring }
      _ = x j := by rw [hsw', one_mul, weight_down_apply]; ring

theorem weight_rotate_apply {n : ℕ} (T : UnitTriangle n) (i : Fin 3) (x : Fin 3 → ℝ) :
    T.rotate.weight (i + 1) (fun k => x (k - 1)) = T.weight i x := by
  cases T <;> simp [Vertex.coord_rotate]

theorem weight_reflect_apply {n : ℕ} (T : UnitTriangle n) (i : Fin 3) (x : Fin 3 → ℝ) :
    T.reflect.weight (-i) (fun k => x (-k)) = T.weight i x := by
  cases T <;> simp [Vertex.coord_reflect]

@[simp] theorem weight_addLeft_apply {k n : ℕ} (p : Vertex k) (T : UnitTriangle n) (i : Fin 3)
    (x : Fin 3 → ℝ) :
    (T.addLeft p).weight i (p.barycentric + x) = T.weight i x := by
  cases T
  · simp
  · simp; ring

/-- The closed continuous cell of a unit triangle `T : UnitTriangle n` inside
`barycentricSimplex n`. -/
def cell {n : ℕ} (T : UnitTriangle n) : Set (Fin 3 → ℝ) :=
  {x ∈ barycentricSimplex n | ∀ i, 0 ≤ T.weight i x}

@[simp] theorem mem_cell_iff {n : ℕ} {T : UnitTriangle n} {x : Fin 3 → ℝ} :
    x ∈ T.cell ↔ x ∈ barycentricSimplex n ∧ ∀ i, 0 ≤ T.weight i x := Iff.rfl

theorem cell_subset_barycentricSimplex {n : ℕ} (T : UnitTriangle n) :
    T.cell ⊆ barycentricSimplex n := fun _ hx => hx.1

theorem weight_nonneg {n : ℕ} {T : UnitTriangle n} {x : Fin 3 → ℝ} (hx : x ∈ T.cell) (i : Fin 3) :
    0 ≤ T.weight i x := hx.2 i

theorem weight_le_one {n : ℕ} {T : UnitTriangle n} {x : Fin 3 → ℝ} (hx : x ∈ T.cell) (i : Fin 3) :
    T.weight i x ≤ 1 := by
  rw [← T.sum_weight hx.1.2]
  exact Finset.single_le_sum (fun j _ => hx.2 j) (Finset.mem_univ i)

theorem vertex_barycentric_mem_cell {n : ℕ} (T : UnitTriangle n) (i : Fin 3) :
    (T.vertex i).barycentric ∈ T.cell :=
  ⟨barycentric_mem_barycentricSimplex _, fun j => by
    rw [weight_vertex]; split_ifs <;> norm_num⟩

/-- Every unit-triangle cell is a convex polyhedron. -/
theorem isConvexPolyhedron_cell {n : ℕ} (T : UnitTriangle n) : IsConvexPolyhedron T.cell := by
  have heq : T.cell = barycentricSimplex n ∩ {x | ∀ i : Fin 3, (-T.weight i) x ≤ 0} := by
    ext x; simp
  rw [heq]
  exact (isConvexPolyhedron_barycentricSimplex n).inter
    (isConvexPolyhedron_setOf_forall fun i : Fin 3 => -T.weight i)

theorem convex_cell {n : ℕ} (T : UnitTriangle n) : Convex ℝ T.cell :=
  T.isConvexPolyhedron_cell.convex

theorem isClosed_cell {n : ℕ} (T : UnitTriangle n) : IsClosed T.cell :=
  T.isConvexPolyhedron_cell.isClosed

/-- Each unit-triangle cell is the convex hull of its three lattice vertices. -/
theorem cell_eq_convexHull {n : ℕ} (T : UnitTriangle n) :
    T.cell = convexHull ℝ (Set.range fun i => (T.vertex i).barycentric) := by
  refine Subset.antisymm (fun x hx => ?_)
    (convexHull_min (by rintro _ ⟨i, rfl⟩; exact T.vertex_barycentric_mem_cell i) T.convex_cell)
  rw [← T.sum_weight_smul_vertex hx.1.2]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hx.2 i) (T.sum_weight hx.1.2)
    fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩

/-- At size `1`, the single upward unit triangle covers all of `barycentricSimplex 1`. -/
@[simp] theorem cell_up_cornerA_zero :
    (up (Vertex.cornerA 0)).cell = barycentricSimplex 1 := by
  ext x
  simp only [mem_cell_iff, mem_barycentricSimplex_iff, weight_up_apply, and_iff_left_iff_imp]
  intro hx i
  have hc : (Vertex.cornerA 0).coord i = 0 := by fin_cases i <;> simp
  simp [hc, hx.1 i]

/-- If `x ∈ T.cell` has positive `i`-th weight, then the `i`-th vertex of `T` lies strictly within
`1` of `x` in every coordinate. -/
theorem abs_vertex_sub_lt_one_of_weight_pos {n : ℕ} {T : UnitTriangle n} {x : Fin 3 → ℝ}
    (hx : x ∈ T.cell) {i : Fin 3} (hi : 0 < T.weight i x) (k : Fin 3) :
    |((T.vertex i).coord k : ℝ) - x k| < 1 := by
  have hsum := T.sum_weight hx.1.2
  have hw0 := hx.2 0; have hw1 := hx.2 1; have hw2 := hx.2 2
  have hle : ∀ j, T.weight j x ≤ 1 := T.weight_le_one hx
  cases T with
  | up base =>
    rw [vertex_coord_up, Nat.cast_add]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte, Nat.cast_one]
      have hw : 0 < x i - (base.coord i : ℝ) := hi
      have hw' : x i - (base.coord i : ℝ) ≤ 1 := hle i
      rw [abs_lt]; constructor <;> linarith
    · simp only [hik, ↓reduceIte, Nat.cast_zero, add_zero]
      have hw : 0 ≤ x k - (base.coord k : ℝ) := hx.2 k
      have hw' : x k - (base.coord k : ℝ) < 1 := by
        have hsum' : (up base).weight 0 x + (up base).weight 1 x + (up base).weight 2 x = 1 := by
          simpa only [Fin.sum_univ_three, add_assoc] using hsum
        fin_cases i <;> fin_cases k <;> simp_all <;> linarith
      rw [abs_lt]; constructor <;> linarith
  | down base =>
    rw [vertex_coord_down, Nat.cast_add]
    by_cases hik : i = k
    · subst hik
      simp only [↓reduceIte, Nat.cast_zero, add_zero]
      have hw : 0 < (base.coord i : ℝ) + 1 - x i := hi
      have hw' : (base.coord i : ℝ) + 1 - x i ≤ 1 := hle i
      rw [abs_lt]; constructor <;> linarith
    · simp only [hik, ↓reduceIte, Nat.cast_one]
      have hw : 0 ≤ (base.coord k : ℝ) + 1 - x k := hx.2 k
      have hw' : (base.coord k : ℝ) + 1 - x k < 1 := by
        have hsum' :
            (down base).weight 0 x + (down base).weight 1 x + (down base).weight 2 x = 1 := by
          simpa only [Fin.sum_univ_three, add_assoc] using hsum
        fin_cases i <;> fin_cases k <;> simp_all <;> linarith
      rw [abs_lt]; constructor <;> linarith

/-- Any lattice vertex `p : Vertex n` whose real embedding lies in `T.cell` is one of the three
vertices of `T`. -/
theorem mem_range_vertex_of_barycentric_mem_cell {n : ℕ} {T : UnitTriangle n} {p : Vertex n}
    (hp : p.barycentric ∈ T.cell) : p ∈ Set.range T.vertex := by
  cases T with
  | up base =>
    have hge : ∀ k : Fin 3, base.coord k ≤ p.coord k := fun k => by
      have hk := hp.2 k
      simp only [weight_up_apply, Vertex.barycentric_apply, sub_nonneg] at hk
      exact_mod_cast hk
    have h0 := hge 0; have h1 := hge 1; have h2 := hge 2
    simp only [Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two] at h0 h1 h2
    have hp_sum := p.sum_eq; have hb_sum := base.sum_eq
    rcases (by omega :
        p.x = base.x + 1 ∧ p.y = base.y ∧ p.z = base.z ∨
        p.x = base.x ∧ p.y = base.y + 1 ∧ p.z = base.z ∨
        p.x = base.x ∧ p.y = base.y ∧ p.z = base.z + 1) with
      ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
    · exact ⟨0, by ext <;> simp [unitCorner, hx, hy, hz]⟩
    · exact ⟨1, by ext <;> simp [unitCorner, hx, hy, hz]⟩
    · exact ⟨2, by ext <;> simp [unitCorner, hx, hy, hz]⟩
  | down base =>
    have hle : ∀ k : Fin 3, p.coord k ≤ base.coord k + 1 := fun k => by
      have hk := hp.2 k
      simp only [weight_down_apply, Vertex.barycentric_apply, sub_nonneg] at hk
      exact_mod_cast hk
    have h0 := hle 0; have h1 := hle 1; have h2 := hle 2
    simp only [Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two] at h0 h1 h2
    have hp_sum := p.sum_eq; have hb_sum := base.sum_eq
    rcases (by omega :
        p.x = base.x ∧ p.y = base.y + 1 ∧ p.z = base.z + 1 ∨
        p.x = base.x + 1 ∧ p.y = base.y ∧ p.z = base.z + 1 ∨
        p.x = base.x + 1 ∧ p.y = base.y + 1 ∧ p.z = base.z) with
      ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
    · exact ⟨0, by ext <;> simp [oppUnitCorner, hx, hy, hz]⟩
    · exact ⟨1, by ext <;> simp [oppUnitCorner, hx, hy, hz]⟩
    · exact ⟨2, by ext <;> simp [oppUnitCorner, hx, hy, hz]⟩

/-- **Active-vertex overlap lemma**: if `x ∈ T₁.cell ∩ T₂.cell` and `T₁.weight i x > 0`, then
`T₁.vertex i` is also a vertex of `T₂`. -/
theorem mem_range_vertex_of_weight_pos {n : ℕ} {T₁ T₂ : UnitTriangle n} {x : Fin 3 → ℝ}
    (hx₁ : x ∈ T₁.cell) (hx₂ : x ∈ T₂.cell) {i : Fin 3} (hi : 0 < T₁.weight i x) :
    T₁.vertex i ∈ Set.range T₂.vertex := by
  refine mem_range_vertex_of_barycentric_mem_cell
    ⟨barycentric_mem_barycentricSimplex _, fun k => ?_⟩
  have habs := abs_lt.mp (abs_vertex_sub_lt_one_of_weight_pos hx₁ hi k)
  cases T₂ with
  | up base =>
    simp only [weight_up_apply, Vertex.barycentric_apply, sub_nonneg]
    have hxk : (base.coord k : ℝ) ≤ x k := by
      have := hx₂.2 k; simp only [weight_up_apply, sub_nonneg] at this; exact this
    have hlt : ((base.coord k : ℤ) : ℝ) - 1 < ((T₁.vertex i).coord k : ℤ) := by
      push_cast; linarith
    have hint : (base.coord k : ℤ) - 1 < (T₁.vertex i).coord k := by exact_mod_cast hlt
    exact_mod_cast (by omega : base.coord k ≤ (T₁.vertex i).coord k)
  | down base =>
    simp only [weight_down_apply, Vertex.barycentric_apply, sub_nonneg]
    have hxk : x k ≤ (base.coord k : ℝ) + 1 := by
      have := hx₂.2 k; simp only [weight_down_apply, sub_nonneg] at this; exact this
    have hlt : (((T₁.vertex i).coord k : ℤ) : ℝ) < (base.coord k : ℤ) + 2 := by
      push_cast; linarith
    have hint : ((T₁.vertex i).coord k : ℤ) < (base.coord k : ℤ) + 2 := by exact_mod_cast hlt
    exact_mod_cast (by omega : (T₁.vertex i).coord k ≤ base.coord k + 1)

/-- For `n = m + 1 ≥ 1`, the `n ^ 2` unit-triangle cells tile `barycentricSimplex (m + 1)`. -/
theorem iUnion_cell_eq_barycentricSimplex (m : ℕ) :
    (⋃ T : UnitTriangle (m + 1), T.cell) = barycentricSimplex (m + 1) := by
  refine Subset.antisymm (iUnion_subset fun T => T.cell_subset_barycentricSimplex) fun x hx => ?_
  rw [mem_iUnion]
  let b : Fin 3 → ℕ := fun i => ⌊x i⌋₊
  have hb_le : ∀ i, (b i : ℝ) ≤ x i := fun i => Nat.floor_le (hx.1 i)
  have hx_lt : ∀ i, x i < (b i : ℝ) + 1 := fun i => Nat.lt_floor_add_one (x i)
  have hsum_x : x 0 + x 1 + x 2 = (m : ℝ) + 1 := by
    simpa [Fin.sum_univ_three, add_assoc] using hx.2
  have hsum_le : ((b 0 + b 1 + b 2 : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
    push_cast; linarith [hb_le 0, hb_le 1, hb_le 2]
  have hsum_lt : (m : ℝ) + 1 < ((b 0 + b 1 + b 2 : ℕ) : ℝ) + 3 := by
    push_cast; linarith [hx_lt 0, hx_lt 1, hx_lt 2]
  have hnat_le : b 0 + b 1 + b 2 ≤ m + 1 := by exact_mod_cast hsum_le
  have hnat_lt : m + 1 < b 0 + b 1 + b 2 + 3 := by exact_mod_cast hsum_lt
  rcases (by omega : b 0 + b 1 + b 2 = m ∨ b 0 + b 1 + b 2 + 1 = m ∨ b 0 + b 1 + b 2 = m + 1) with
    hm | hm1 | hm_top
  · refine ⟨up ⟨b 0, b 1, b 2, hm⟩, hx, fun i => ?_⟩
    fin_cases i <;> simp [sub_nonneg, hb_le _]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨b 0 + b 1 + b 2, hm1.symm⟩
    refine ⟨down ⟨b 0, b 1, b 2, by omega⟩, hx, fun i => ?_⟩
    fin_cases i <;> simp [sub_nonneg, (hx_lt _).le]
  · have hsum_b : (b 0 : ℝ) + b 1 + b 2 = (m : ℝ) + 1 := by exact_mod_cast hm_top
    have hx0 : x 0 = b 0 := by linarith [hb_le 0, hb_le 1, hb_le 2]
    have hx1 : x 1 = b 1 := by linarith [hb_le 0, hb_le 1, hb_le 2]
    have hx2 : x 2 = b 2 := by linarith [hb_le 0, hb_le 1, hb_le 2]
    rcases (by omega : 1 ≤ b 0 ∨ 1 ≤ b 1 ∨ 1 ≤ b 2) with hb0 | hb1 | hb2
    · refine ⟨up ⟨b 0 - 1, b 1, b 2, by omega⟩, hx, fun i => ?_⟩
      fin_cases i <;> simp [hx0, hx1, hx2, Nat.cast_sub hb0]
    · refine ⟨up ⟨b 0, b 1 - 1, b 2, by omega⟩, hx, fun i => ?_⟩
      fin_cases i <;> simp [hx0, hx1, hx2, Nat.cast_sub hb1]
    · refine ⟨up ⟨b 0, b 1, b 2 - 1, by omega⟩, hx, fun i => ?_⟩
      fin_cases i <;> simp [hx0, hx1, hx2, Nat.cast_sub hb2]

end UnitTriangle

/-- Every unit lattice edge `(a, c)` in `Vertex n` lies in the cell of a unit triangle. -/
theorem exists_cell_of_isUnitEdge {n : ℕ} {a c : Vertex n} (h : IsUnitEdge a c) :
    ∃ T : UnitTriangle n, a.barycentric ∈ T.cell ∧ c.barycentric ∈ T.cell := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h.one_le)
  have hsq : a.sqDist c = 2 := h
  rw [Vertex.sqDist_def] at hsq
  have hmin {u v : ℕ} (huv : ((u : ℤ) - v) ^ 2 ≤ 2) :
      2 * ((min u v : ℕ) : ℤ) = (u : ℤ) + v - ((u : ℤ) - v) ^ 2 := by
    have hb : -1 ≤ (u : ℤ) - v ∧ (u : ℤ) - v ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    rcases (by omega : (u : ℤ) - v = -1 ∨ (u : ℤ) - v = 0 ∨ (u : ℤ) - v = 1) with
      h1 | h1 | h1 <;> { rw [h1]; norm_num; omega }
  have hminx := hmin (u := a.x) (v := c.x)
    (by linarith [sq_nonneg ((a.y : ℤ) - c.y), sq_nonneg ((a.z : ℤ) - c.z)])
  have hminy := hmin (u := a.y) (v := c.y)
    (by linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.z : ℤ) - c.z)])
  have hminz := hmin (u := a.z) (v := c.z)
    (by linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.y : ℤ) - c.y)])
  have ha : (a.x : ℤ) + a.y + a.z = m + 1 := by exact_mod_cast a.sum_eq
  have hc : (c.x : ℤ) + c.y + c.z = m + 1 := by exact_mod_cast c.sum_eq
  have : 2 * (((min a.x c.x + min a.y c.y + min a.z c.z : ℕ) : ℤ)) = 2 * m := by
    simp only [Int.natCast_add]; linarith
  let base : Vertex m :=
    ⟨min a.x c.x, min a.y c.y, min a.z c.z, by exact_mod_cast (by omega :
      ((min a.x c.x + min a.y c.y + min a.z c.z : ℕ) : ℤ) = m)⟩
  refine ⟨UnitTriangle.up base, ⟨barycentric_mem_barycentricSimplex a, fun i => ?_⟩,
    ⟨barycentric_mem_barycentricSimplex c, fun i => ?_⟩⟩ <;>
  · fin_cases i <;> simp [base, sub_nonneg]

end TauCeti.Hive
