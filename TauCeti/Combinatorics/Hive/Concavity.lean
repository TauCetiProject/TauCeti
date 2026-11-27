/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import TauCeti.Analysis.Convex.Function.Basic
public import TauCeti.Combinatorics.Hive.Interpolation
public import TauCeti.Combinatorics.Hive.SimplicialInterpolation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import TauCeti.Analysis.Convex.Intrinsic

/-!
# The rhombus concavity criterion and tropical affine-envelope formula

This file proves that for `f : Vertex n → ℝ`, the unit-triangle simplicial extensions
`interpolate f` on `barycentricSimplex n` and `planarInterpolate f` on `planarSimplex n` are
concave if and only if `TauCeti.Hive.IsRhombusConcave f` holds, and satisfy the tropical
affine-envelope formula. Across every shared interior unit edge between `down s` and
`adjacentUp s i`, the difference of their affine pieces is proportional to the unit-rhombus slack
(`triangleAffine_adjacentUp_sub_down`), so concavity on each union rhombus cell
(`concaveOn_adjacentCell_iff`) matches discrete rhombus concavity. On `barycentricSimplex n`,
`interpolate f` agrees with the `(y, z)`-chart interpolation `TauCeti.Hive.interpolation f` under
`x ↦ (x 1, x 2)` (`interpolate_eq_interpolation`), transferring
`TauCeti.Hive.concaveOn_interpolation_iff` to `concaveOn_barycentricSimplex_interpolate_iff` and
`concaveOn_planarSimplex_planarInterpolate_iff`, and discrete supporting planes
(`TauCeti.Hive.IsRhombusConcave.le_barycentricLinear`) yield the tropical envelope formula
`IsRhombusConcave.interpolate_eq_inf'_triangleAffine` for `n = m + 1`.

## Main results

* `TauCeti.Hive.triangleAffine_adjacentUp_sub_down`, `TauCeti.Hive.concaveOn_adjacentCell_iff`.
* `TauCeti.Hive.concaveOn_barycentricSimplex_interpolate_iff`,
  `TauCeti.Hive.concaveOn_planarSimplex_planarInterpolate_iff`.
* `TauCeti.Hive.IsRhombusConcave.interpolate_eq_inf'_triangleAffine`.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §2, App. 2.
-/

public section

open Set
open scoped BigOperators

namespace TauCeti.Hive

variable {n m : ℕ}

/-! ### The adjacent-triangle bending test -/

private theorem rhombusSlack_nonneg_of_concaveOn {f : Vertex n → ℝ} {S : Set (Fin 3 → ℝ)}
    (hconc : ConcaveOn ℝ S (interpolate f)) {a b c d : Vertex n} (hr : IsRhombus a b c d)
    (hb : b.barycentric ∈ S) (hd : d.barycentric ∈ S) : 0 ≤ rhombusSlack f a b c d := by
  have hmid : (1 / 2 : ℝ) • b.barycentric + (1 / 2 : ℝ) • d.barycentric =
      AffineMap.lineMap a.barycentric c.barycentric (1 / 2 : ℝ) := funext fun k => by
    have hk := congrFun hr.midpoint_barycentric k
    simp [AffineMap.lineMap_apply_module] at hk ⊢; linarith
  have h := hconc.2 hb hd (by norm_num) (by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [hmid, interpolate_lineMap_of_isUnitEdge f ((isUnitEdge_def _ _).mpr hr.short)
    ⟨by norm_num, by norm_num⟩, interpolate_barycentric, interpolate_barycentric] at h
  simp only [smul_eq_mul, rhombusSlack_def] at h ⊢; linarith
/-- Exact bending formula across the shared edge of `down s` and `adjacentUp s i` opposite
`(down s).vertex i`: on the sum-`(m + 2)` hyperplane, the difference of their affine pieces equals
`((sᵢ + 1) - xᵢ)` times the unit-rhombus slack. -/
theorem triangleAffine_adjacentUp_sub_down (f : Vertex (m + 2) → ℝ) (s : Vertex m) (i : Fin 3)
    {x : Fin 3 → ℝ} (hx : ∑ k, x k = ((m + 2 : ℕ) : ℝ)) :
    triangleAffine (adjacentUp s i) f x - triangleAffine (UnitTriangle.down s) f x =
      ((s.coord i : ℝ) + 1 - x i) * rhombusSlack f ((UnitTriangle.down s).vertex (i + 2))
        ((adjacentUp s i).vertex i) ((UnitTriangle.down s).vertex (i + 1))
        ((UnitTriangle.down s).vertex i) := by
  let c := rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
    ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i)
  let B := triangleAffine (UnitTriangle.down s) f + c • (UnitTriangle.down s).weight i
  have hB : B x = triangleAffine (adjacentUp s i) f x :=
    eq_triangleAffine_of_vertex (A := B.toAffineMap) (fun j => by
      have hne1 : i ≠ i + 1 := by fin_cases i <;> decide
      have hne2 : i ≠ i + 2 := by fin_cases i <;> decide
      rcases (by fin_cases i <;> fin_cases j <;> decide : j = i ∨ j = i + 1 ∨ j = i + 2) with
        hj | hj | hj
      · rw [hj]; fin_cases i <;> simp [B, c, triangleAffine_apply, Fin.sum_univ_three,
          vertex_adjacentUp, rhombusSlack_def] <;> ring
      all_goals
        rw [hj]
        simp only [B, ContinuousAffineMap.coe_toAffineMap, ContinuousAffineMap.add_apply,
          ContinuousAffineMap.smul_apply, smul_eq_mul, vertex_adjacentUp_add_one,
          vertex_adjacentUp_add_two, triangleAffine_vertex, UnitTriangle.weight_vertex,
          hne1, hne2, ↓reduceIte, mul_zero, add_zero]) hx
  simp only [B, ContinuousAffineMap.add_apply, ContinuousAffineMap.smul_apply, smul_eq_mul,
    UnitTriangle.weight_down_apply] at hB
  linarith
/-- When the unit-rhombus slack across the edge of `down s` opposite `(down s).vertex i` is
nonnegative, `interpolate f` on `adjacentCell s i` equals the pointwise minimum of the two adjacent
affine pieces. -/
theorem eqOn_inf_triangleAffine_adjacentCell {f : Vertex (m + 2) → ℝ} {s : Vertex m} {i : Fin 3}
    (hslack : 0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
      ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i)) :
    EqOn (interpolate f)
      (⇑(triangleAffine (adjacentUp s i) f) ⊓ ⇑(triangleAffine (UnitTriangle.down s) f))
      (adjacentCell s i) := fun x hx_adj => by
  have hdiff := triangleAffine_adjacentUp_sub_down f s i (mem_barycentricSimplex_iff.mp
    ((mem_adjacentCell_iff.mp hx_adj).elim (UnitTriangle.cell_subset_barycentricSimplex _ ·)
      (UnitTriangle.cell_subset_barycentricSimplex _ ·))).2
  rcases mem_adjacentCell_iff.mp hx_adj with hx | hx
  · rw [interpolate_eq_triangleAffine f hx, Pi.inf_apply, eq_comm, inf_eq_left]
    have hw : 0 ≤ x i - ((s.coord i : ℝ) + 1) := by simpa using (adjacentUp s i).weight_nonneg hx i
    linarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : (s.coord i : ℝ) + 1 - x i ≤ 0) hslack]
  · rw [interpolate_eq_triangleAffine f hx, Pi.inf_apply, eq_comm, inf_eq_right]
    linarith [mul_nonneg (by simpa using (UnitTriangle.down s).weight_nonneg hx i :
      0 ≤ (s.coord i : ℝ) + 1 - x i) hslack]
/-- **Adjacent-triangle bending test**: `interpolate f` is concave on the union cell
`adjacentCell s i` of `adjacentUp s i` and `down s` if and only if the corresponding unit-rhombus
slack is nonnegative. -/
theorem concaveOn_adjacentCell_iff (f : Vertex (m + 2) → ℝ) (s : Vertex m) (i : Fin 3) :
    ConcaveOn ℝ (adjacentCell s i) (interpolate f) ↔
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) :=
  ⟨fun hconc => rhombusSlack_nonneg_of_concaveOn hconc (isRhombus_adjacent s i)
      (mem_adjacentCell_iff.mpr (Or.inl ((adjacentUp s i).barycentric_vertex_mem_cell i)))
      (mem_adjacentCell_iff.mpr (Or.inr ((UnitTriangle.down s).barycentric_vertex_mem_cell i))),
    fun hslack => (((triangleAffine (adjacentUp s i) f).toAffineMap.concaveOn
      (convex_adjacentCell s i)).inf ((triangleAffine (UnitTriangle.down s) f).toAffineMap.concaveOn
      (convex_adjacentCell s i))).congr (eqOn_inf_triangleAffine_adjacentCell hslack).symm⟩

/-! ### Comparison with `(y, z)`-chart interpolation and global concavity criterion -/

private def yzProj : (Fin 3 → ℝ) →ᵃ[ℝ] ℝ × ℝ :=
  (AffineMap.proj 1).prod (AffineMap.proj 2)

private noncomputable def yzLift (n : ℕ) : ℝ × ℝ →ᵃ[ℝ] (Fin 3 → ℝ) :=
  AffineMap.pi
    ![AffineMap.const ℝ (ℝ × ℝ) (n : ℝ) - AffineMap.fst - AffineMap.snd,
      AffineMap.fst, AffineMap.snd]

/-- **Rhombus concavity criterion (barycentric chart)**: the simplicial piecewise-affine extension
`interpolate f` is concave on `barycentricSimplex n` if and only if `f` satisfies all unit-rhombus
concavity inequalities. -/
theorem concaveOn_barycentricSimplex_interpolate_iff (f : Vertex n → ℝ) :
    ConcaveOn ℝ (barycentricSimplex n) (interpolate f) ↔ IsRhombusConcave f := by
  refine Iff.trans ⟨fun h => ?_, fun h => ?_⟩ (concaveOn_interpolation_iff f)
  · have hmaps : MapsTo (yzLift n) (yzTriangle ℝ n) (barycentricSimplex n) := fun q hq => by
      obtain ⟨hq1, hq2, hqsum⟩ := mem_yzTriangle.mp hq
      refine mem_barycentricSimplex_iff.mpr ⟨fun i => ?_, ?_⟩
      · fin_cases i <;> simp [yzLift] <;> linarith
      · simp [yzLift, Fin.sum_univ_three]; ring
    refine ((h.comp_affineMap (yzLift n)).subset hmaps convex_yzTriangle).congr fun q hq => ?_
    simpa [yzLift] using interpolate_eq_interpolation f (hmaps hq)
  · refine ((h.comp_affineMap yzProj).subset (fun x hx => ?_)
      (convex_barycentricSimplex n)).congr fun x hx => ?_
    · obtain ⟨hx_pos, hx_sum⟩ := mem_barycentricSimplex_iff.mp hx
      refine mem_yzTriangle.mpr ⟨hx_pos 1, hx_pos 2, ?_⟩
      simp [yzProj]
      have hsum : x 0 + x 1 + x 2 = (n : ℝ) := by simpa [Fin.sum_univ_three, add_assoc] using hx_sum
      linarith [hx_pos 0]
    · exact (interpolate_eq_interpolation f hx).symm

/-- **Rhombus concavity criterion (Euclidean planar chart)**: `planarInterpolate f` is concave on
`planarSimplex n` if and only if `f` is rhombus-concave. -/
theorem concaveOn_planarSimplex_planarInterpolate_iff (f : Vertex n → ℝ) :
    ConcaveOn ℝ (planarSimplex n) (planarInterpolate f) ↔ IsRhombusConcave f := by
  rw [← concaveOn_barycentricSimplex_interpolate_iff]
  refine ⟨fun h => ((h.comp_linearMap planeLinear.toLinearMap).subset (fun x hx =>
      mem_planarSimplex_iff.mpr
        (by simpa [planeInvAffine_planeLinear (mem_barycentricSimplex_iff.mp hx).2] using hx))
      (convex_barycentricSimplex n)).congr fun _ hx =>
        planarInterpolate_planeLinear f (mem_barycentricSimplex_iff.mp hx).2,
    fun h => ((h.comp_affineMap (planeInvAffine n).toAffineMap).subset
      (fun _ hu => mem_planarSimplex_iff.mp hu) (convex_planarSimplex n)).congr
      fun u _ => (planarInterpolate_def f u).symm⟩
/-- Every real hive has concave simplicial interpolation on `barycentricSimplex n`. -/
theorem concaveOn_barycentricSimplex_interpolate (h : RealHive n) :
    ConcaveOn ℝ (barycentricSimplex n) (interpolate h) :=
  (concaveOn_barycentricSimplex_interpolate_iff h).mpr h.isRhombusConcave
/-- Every real hive has concave planar simplicial interpolation on `planarSimplex n`. -/
theorem concaveOn_planarSimplex_planarInterpolate (h : RealHive n) :
    ConcaveOn ℝ (planarSimplex n) (planarInterpolate h) :=
  (concaveOn_planarSimplex_planarInterpolate_iff h).mpr h.isRhombusConcave

/-! ### Discrete supporting planes and tropical affine-envelope formula -/

private theorem IsRhombusConcave.le_triangleAffine_barycentric_aux {f : Vertex n → ℝ}
    (hf : IsRhombusConcave f) (T : UnitTriangle n) (k : Fin 6) (c₀ α β γ : ℝ)
    (hL : ∀ w : Vertex n, barycentricLinear c₀ α β γ w = triangleAffine T f w.barycentric)
    (hq : (T.vertex 1).yz = (T.vertex 0).yz + yzStep k)
    (hr : (T.vertex 2).yz = (T.vertex 0).yz + yzStep (k + 1)) (v : Vertex n) :
    f v ≤ triangleAffine T f v.barycentric := by
  rw [← hL v]
  exact hf.le_barycentricLinear hq hr
    (by rw [hL, triangleAffine_vertex]) (by rw [hL, triangleAffine_vertex])
    (by rw [hL, triangleAffine_vertex]) v

private theorem IsRhombusConcave.le_triangleAffine_barycentric {f : Vertex n → ℝ}
    (hf : IsRhombusConcave f) (T : UnitTriangle n) (v : Vertex n) :
    f v ≤ triangleAffine T f v.barycentric := by
  cases T with
  | up b =>
    -- Upward triangle edges from `vertex 0` follow `yzStep 0 = (1, 0)` and `yzStep 1 = (0, 1)`.
    exact hf.le_triangleAffine_barycentric_aux (UnitTriangle.up b) 0
      (-(f ((UnitTriangle.up b).vertex 0) * b.x + f ((UnitTriangle.up b).vertex 1) * b.y +
        f ((UnitTriangle.up b).vertex 2) * b.z))
      (f ((UnitTriangle.up b).vertex 0)) (f ((UnitTriangle.up b).vertex 1))
      (f ((UnitTriangle.up b).vertex 2))
      (fun w => by simp [barycentricLinear_apply, triangleAffine_apply, Fin.sum_univ_three]; ring)
      (by ext <;> simp [yzStep_def]) (by ext <;> simp [yzStep_def]) v
  | down b =>
    -- Downward triangle edges from `vertex 0` follow `yzStep 3 = (-1, 0)` and `yzStep 4 = (0, -1)`.
    exact hf.le_triangleAffine_barycentric_aux (UnitTriangle.down b) 3
      (f ((UnitTriangle.down b).vertex 0) * ((b.x : ℝ) + 1) +
        f ((UnitTriangle.down b).vertex 1) * ((b.y : ℝ) + 1) +
        f ((UnitTriangle.down b).vertex 2) * ((b.z : ℝ) + 1))
      (-f ((UnitTriangle.down b).vertex 0)) (-f ((UnitTriangle.down b).vertex 1))
      (-f ((UnitTriangle.down b).vertex 2))
      (fun w => by simp [barycentricLinear_apply, triangleAffine_apply, Fin.sum_univ_three]; ring)
      (by ext <;> simp [yzStep_def]) (by ext <;> simp [yzStep_def]) v

/-- Every affine piece `triangleAffine T f` globally upper-bounds `interpolate f` on
`barycentricSimplex n` whenever `f` is rhombus-concave. -/
theorem IsRhombusConcave.interpolate_le_triangleAffine {f : Vertex n → ℝ}
    (hf : IsRhombusConcave f) (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex n) : interpolate f x ≤ triangleAffine T f x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by cases T <;> exact ⟨_, rfl⟩
  obtain ⟨T', hxT'⟩ := UnitTriangle.exists_mem_cell hx
  rw [interpolate_eq_triangleAffine f hxT']
  exact le_of_forall_le_of_mem_convexHull (a := (triangleAffine T' f).toAffineMap)
    (b := (triangleAffine T f).toAffineMap)
    (by
      rintro _ ⟨i, rfl⟩
      rw [ContinuousAffineMap.coe_toAffineMap, ContinuousAffineMap.coe_toAffineMap,
        triangleAffine_vertex]
      exact hf.le_triangleAffine_barycentric T (T'.vertex i))
    (T'.cell_eq_convexHull ▸ hxT')
/-- **Global affine-envelope formula**: for `n = m + 1 ≥ 1` and rhombus-concave `f`,
`interpolate f x` on `barycentricSimplex (m + 1)` is the minimum over all `n²` unit triangles of
`triangleAffine T f x`. -/
theorem IsRhombusConcave.interpolate_eq_inf'_triangleAffine {f : Vertex (m + 1) → ℝ}
    (hf : IsRhombusConcave f) {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex (m + 1)) :
    interpolate f x = Finset.univ.inf' Finset.univ_nonempty
      (fun T : UnitTriangle (m + 1) => triangleAffine T f x) := by
  obtain ⟨T₀, hT₀⟩ := UnitTriangle.exists_mem_cell hx
  exact le_antisymm (Finset.le_inf' _ _ fun T _ => hf.interpolate_le_triangleAffine T hx)
    ((Finset.inf'_le _ (Finset.mem_univ T₀)).trans (interpolate_eq_triangleAffine f hT₀).ge)

/-! ### Small-rank checks -/

section SmallRank
example : ConcaveOn ℝ (barycentricSimplex 2) (interpolate (toReal exampleTwo)) :=
  (toReal exampleTwo).concaveOn_barycentricSimplex_interpolate
example : ConcaveOn ℝ (barycentricSimplex 2) (interpolate (toReal detTwo)) :=
  (toReal detTwo).concaveOn_barycentricSimplex_interpolate
example : ¬ ConcaveOn ℝ (barycentricSimplex 2)
    (interpolate fun p : Vertex 2 => if p = ⟨0, 1, 1, rfl⟩ then (1 : ℝ) else 0) := by
  rw [concaveOn_barycentricSimplex_interpolate_iff]; intro hf
  have h := (isRhombusConcave_def _).mp hf isRhombus_at_cornerA
  simp [Vertex.ext_iff] at h; linarith
end SmallRank

end TauCeti.Hive
