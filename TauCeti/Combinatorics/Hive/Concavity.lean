/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Finset.Lattice.Fold
public import TauCeti.Analysis.Convex.Piecewise
public import TauCeti.Combinatorics.Hive.Interpolation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The rhombus concavity criterion and tropical affine-envelope formula

For any real-valued function `f : Vertex n → ℝ` on the size-`n` triangular lattice, the simplicial
piecewise-affine extension `interpolate f` on `barycentricSimplex n` (and equivalently
`planarInterpolate f` on the Euclidean triangle `planarSimplex n`) is concave if and only if `f`
satisfies all unit-rhombus concavity inequalities (`IsRhombusConcave f`).

We prove this equivalence (`concaveOn_barycentricSimplex_interpolate_iff`) via the
adjacent-triangle bending test and 1D line-segment subdivision:
1. Across the `i`-th edge of any downward unit triangle `down s` and its upward neighbour
   `adjacentUp s i`, the difference of their affine pieces equals `((sᵢ + 1) - xᵢ)` times the
   unit-rhombus slack (`triangleAffine_adjacentUp_sub_down`), so `interpolate f` is concave on
   their union cell `adjacentCell s i` if and only if the slack is nonnegative
   (`concaveOn_adjacentCell_iff`).
2. Every point in the strict interior of `barycentricSimplex (m + 2)` that is not a lattice vertex
   admits an open convex neighbourhood contained in either a single unit-triangle cell or an
   `adjacentCell s i`, where `interpolate f` is concave.
3. Along any strictly interior line segment avoiding the finitely many lattice vertices, Lebesgue's
   number lemma and finite subdivision (`TauCeti.concaveOn_Icc_of_subdivision`) glue local
   concavity into concavity on `[0, 1]`. Uniform vertex-avoiding approximation and continuity of
   `interpolate f` extend concavity to all of `barycentricSimplex (m + 2)`.

As an immediate consequence, whenever `f` is rhombus-concave and `n = m + 1 ≥ 1`, `interpolate f`
is the tropical global minimum of its `n²` affine pieces
(`IsRhombusConcave.interpolate_eq_inf'_triangleAffine`).

## Main results

* `TauCeti.Hive.triangleAffine_adjacentUp_sub_down`, `TauCeti.Hive.concaveOn_adjacentCell_iff`:
  the adjacent-triangle bending formula and local concavity test.
* `TauCeti.Hive.concaveOn_barycentricSimplex_interpolate_iff`,
  `TauCeti.Hive.concaveOn_planarSimplex_planarInterpolate_iff`: `interpolate f` (and
  `planarInterpolate f`) is concave if and only if `IsRhombusConcave f`.
* `TauCeti.Hive.isRhombusConcave_iff_adjacent`: at size `m + 2`, rhombus concavity is completely
  determined by the `3 * |Vertex m|` adjacent-triangle unit rhombi.
* `TauCeti.Hive.IsRhombusConcave.interpolate_eq_inf'_triangleAffine`: global affine-envelope
  presentation of `interpolate f` as the minimum of `triangleAffine f T` over all `T`.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §2 and
  Appendix 2, Proposition 4.
-/

public section

open Set Filter Topology
open scoped BigOperators

namespace TauCeti.Hive

/-! ### The adjacent-triangle bending test -/

/-- Every simplicial affine piece `triangleAffine f T` is concave on any convex set. -/
theorem concaveOn_triangleAffine {n : ℕ} (f : Vertex n → ℝ) (T : UnitTriangle n)
    {s : Set (Fin 3 → ℝ)} (hs : Convex ℝ s) :
    ConcaveOn ℝ s (triangleAffine f T) :=
  ((concaveOn_id convex_univ).comp_affineMap (triangleAffine f T).toAffineMap).subset
    (subset_univ s) hs

/-- Exact bending formula across the shared `i`-th edge of `down s` and `adjacentUp s i`: on the
sum-`(m + 2)` hyperplane, the difference of their affine pieces equals `((sᵢ + 1) - xᵢ)` times the
unit-rhombus slack. -/
theorem triangleAffine_adjacentUp_sub_down {m : ℕ} (f : Vertex (m + 2) → ℝ) (s : Vertex m)
    (i : Fin 3) {x : Fin 3 → ℝ} (hx : ∑ k, x k = ((m + 2 : ℕ) : ℝ)) :
    triangleAffine f (adjacentUp s i) x - triangleAffine f (UnitTriangle.down s) x =
      ((s.coord i : ℝ) + 1 - x i) *
        rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
          ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  let U := adjacentUp s i
  let D := UnitTriangle.down s
  have hr : IsRhombus (D.vertex (i + 2)) (U.vertex i) (D.vertex (i + 1)) (D.vertex i) :=
    isRhombus_adjacent s i
  have hvi : (D.vertex i).barycentric =
      ∑ j : Fin 3, (![1, 1, -1] : Fin 3 → ℝ) j •
        (![(D.vertex (i + 2)).barycentric, (D.vertex (i + 1)).barycentric,
          (U.vertex i).barycentric] : Fin 3 → Fin 3 → ℝ) j := by
    have hmx : ((D.vertex (i + 2)).x : ℝ) + (D.vertex (i + 1)).x =
        (U.vertex i).x + (D.vertex i).x := by exact_mod_cast hr.midpoint_x
    have hmy : ((D.vertex (i + 2)).y : ℝ) + (D.vertex (i + 1)).y =
        (U.vertex i).y + (D.vertex i).y := by exact_mod_cast hr.midpoint_y
    have hmz : ((D.vertex (i + 2)).z : ℝ) + (D.vertex (i + 1)).z =
        (U.vertex i).z + (D.vertex i).z := by exact_mod_cast hr.midpoint_z
    ext k; fin_cases k <;> simp [Fin.sum_univ_three] <;> linarith
  have hw_one : ∑ j : Fin 3, (![1, 1, -1] : Fin 3 → ℝ) j = 1 := by
    simp [Fin.sum_univ_three]
  have hU_vi : triangleAffine f U (D.vertex i).barycentric =
      f (D.vertex (i + 2)) + f (D.vertex (i + 1)) - f (U.vertex i) := by
    rw [hvi, triangleAffine_combo f U hw_one]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, one_mul, neg_mul]
    dsimp only [D, U]
    rw [← adjacentUp_vertex_add_one s i, ← adjacentUp_vertex_add_two s i,
      triangleAffine_vertex, triangleAffine_vertex, triangleAffine_vertex]
    ring
  have hU_v1 : triangleAffine f U (D.vertex (i + 1)).barycentric = f (D.vertex (i + 1)) := by
    rw [← adjacentUp_vertex_add_two s i, triangleAffine_vertex]
  have hU_v2 : triangleAffine f U (D.vertex (i + 2)).barycentric = f (D.vertex (i + 2)) := by
    rw [← adjacentUp_vertex_add_one s i, triangleAffine_vertex]
  have hperm (g : Fin 3 → ℝ) : ∑ k : Fin 3, g k = g i + g (i + 1) + g (i + 2) := by
    fin_cases i <;> simp [Fin.sum_univ_three] <;> ring
  conv_lhs =>
    rw [← D.sum_weight_smul_vertex hx, triangleAffine_combo f U (D.sum_weight hx),
      triangleAffine_combo f D (D.sum_weight hx)]
  rw [hperm, hperm, hU_vi, hU_v1, hU_v2,
    triangleAffine_vertex, triangleAffine_vertex, triangleAffine_vertex]
  have hwi : D.weight i x = (s.coord i : ℝ) + 1 - x i := UnitTriangle.weight_down_apply s i x
  rw [hwi, rhombusSlack_def]
  ring

/-- When the unit-rhombus slack across side `i` of `down s` is nonnegative, `interpolate f` on
`adjacentCell s i` equals the pointwise minimum of the two adjacent affine pieces. -/
theorem eqOn_inf_triangleAffine_adjacentCell {m : ℕ} {f : Vertex (m + 2) → ℝ} {s : Vertex m}
    {i : Fin 3}
    (hslack : 0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2))
      ((adjacentUp s i).vertex i) ((UnitTriangle.down s).vertex (i + 1))
      ((UnitTriangle.down s).vertex i)) :
    EqOn (interpolate f)
      (⇑(triangleAffine f (adjacentUp s i)) ⊓ ⇑(triangleAffine f (UnitTriangle.down s)))
      (adjacentCell s i) := by
  intro x hx_adj
  rcases mem_adjacentCell_iff.mp hx_adj with hx | hx
  · rw [interpolate_eq_triangleAffine f hx, Pi.inf_apply, eq_comm, inf_eq_left]
    have hx_sum : ∑ k, x k = ((m + 2 : ℕ) : ℝ) :=
      (mem_barycentricSimplex_iff.mp ((adjacentUp s i).cell_subset_barycentricSimplex hx)).2
    have hw : 0 ≤ x i - ((s.coord i : ℝ) + 1) := by
      simpa using (adjacentUp s i).weight_nonneg hx i
    have hdiff := triangleAffine_adjacentUp_sub_down f s i hx_sum
    have hnonpos :
        triangleAffine f (adjacentUp s i) x - triangleAffine f (UnitTriangle.down s) x ≤ 0 := by
      rw [hdiff]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hslack
    linarith
  · rw [interpolate_eq_triangleAffine f hx, Pi.inf_apply, eq_comm, inf_eq_right]
    have hx_sum : ∑ k, x k = ((m + 2 : ℕ) : ℝ) :=
      (mem_barycentricSimplex_iff.mp ((UnitTriangle.down s).cell_subset_barycentricSimplex hx)).2
    have hw : 0 ≤ (s.coord i : ℝ) + 1 - x i := by
      simpa using (UnitTriangle.down s).weight_nonneg hx i
    have hdiff := triangleAffine_adjacentUp_sub_down f s i hx_sum
    have hnonneg :
        0 ≤ triangleAffine f (adjacentUp s i) x - triangleAffine f (UnitTriangle.down s) x := by
      rw [hdiff]
      exact mul_nonneg hw hslack
    linarith

/-- **Adjacent-triangle bending test**: `interpolate f` is concave on the union cell
`adjacentCell s i` of `adjacentUp s i` and `down s` if and only if the corresponding unit-rhombus
slack is nonnegative. -/
theorem concaveOn_adjacentCell_iff {m : ℕ} (f : Vertex (m + 2) → ℝ) (s : Vertex m) (i : Fin 3) :
    ConcaveOn ℝ (adjacentCell s i) (interpolate f) ↔
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  refine ⟨fun hconc => ?_, fun hslack => ?_⟩
  · set a := (UnitTriangle.down s).vertex (i + 2)
    set b := (adjacentUp s i).vertex i
    set c := (UnitTriangle.down s).vertex (i + 1)
    set d := (UnitTriangle.down s).vertex i
    have hr : IsRhombus a b c d := isRhombus_adjacent s i
    have hb : b.barycentric ∈ adjacentCell s i :=
      mem_adjacentCell_iff.mpr (Or.inl ((adjacentUp s i).vertex_barycentric_mem_cell i))
    have hd : d.barycentric ∈ adjacentCell s i :=
      mem_adjacentCell_iff.mpr (Or.inr ((UnitTriangle.down s).vertex_barycentric_mem_cell i))
    have hmid : (1 / 2 : ℝ) • b.barycentric + (1 / 2 : ℝ) • d.barycentric =
        AffineMap.lineMap a.barycentric c.barycentric (1 / 2 : ℝ) := by
      rw [AffineMap.lineMap_apply_module]
      have hmx : (a.x : ℝ) + c.x = b.x + d.x := by exact_mod_cast hr.midpoint_x
      have hmy : (a.y : ℝ) + c.y = b.y + d.y := by exact_mod_cast hr.midpoint_y
      have hmz : (a.z : ℝ) + c.z = b.z + d.z := by exact_mod_cast hr.midpoint_z
      ext k; fin_cases k <;> simp <;> linarith
    have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have hineq := hconc.2 hb hd hhalf hhalf (by norm_num)
    rw [hmid, interpolate_lineMap_of_isUnitEdge f hr.isUnitEdge_short ⟨by norm_num, by norm_num⟩,
      interpolate_barycentric, interpolate_barycentric] at hineq
    simp only [smul_eq_mul, rhombusSlack_def] at hineq ⊢
    linarith
  · exact ((concaveOn_triangleAffine f (adjacentUp s i) (convex_adjacentCell s i)).inf
      (concaveOn_triangleAffine f (UnitTriangle.down s) (convex_adjacentCell s i))).congr
      (eqOn_inf_triangleAffine_adjacentCell hslack).symm

/-! ### Line-segment subdivision, vertex-avoiding approximation, and global concavity -/

private theorem exists_open_convex_concaveOn_of_notMem_barycentric {m : ℕ}
    {f : Vertex (m + 2) → ℝ}
    (hadj : ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i))
    {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex (m + 2)) (hpos : ∀ k, 0 < x k)
    (hnot : x ∉ Set.range (Vertex.barycentric (n := m + 2))) :
    ∃ U : Set (Fin 3 → ℝ), IsOpen U ∧ Convex ℝ U ∧ x ∈ U ∧
      ConcaveOn ℝ (barycentricSimplex (m + 2) ∩ U) (interpolate f) := by
  -- Step 1: Record the integer floor coordinates `b k = ⌊x k⌋₊`; not all `x k` can be integers.
  obtain ⟨hx_nonneg, hx_sum⟩ := mem_barycentricSimplex_iff.mp hx
  let b : Fin 3 → ℕ := fun k => ⌊x k⌋₊
  have hb_le : ∀ k, (b k : ℝ) ≤ x k := fun k => Nat.floor_le (hx_nonneg k)
  have hx_lt : ∀ k, x k < (b k : ℝ) + 1 := fun k => Nat.lt_floor_add_one (x k)
  have hsum_x : x 0 + x 1 + x 2 = (m : ℝ) + 2 := by
    simpa [Fin.sum_univ_three, add_assoc] using hx_sum
  have hnot_all : ¬ (∀ k, x k = (b k : ℝ)) := by
    intro hall
    have hsum_b : ((b 0 + b 1 + b 2 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := by
      push_cast; linarith [hall 0, hall 1, hall 2, hsum_x]
    refine hnot ⟨⟨b 0, b 1, b 2, Nat.cast_injective hsum_b⟩, ?_⟩
    ext k; fin_cases k <;> simp [hall _]
  have heq_nat {u v w : ℝ} {bu bv : ℕ} (hu : u = bu) (hv : v = bv) (hw_pos : 0 < w)
      (hsum : u + v + w = (m : ℝ) + 2) : w = ((m + 2 - (bu + bv) : ℕ) : ℝ) := by
    have hle : bu + bv ≤ m + 2 := by
      have : ((bu + bv : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    rw [Nat.cast_sub hle]; push_cast; linarith
  -- Step 2: Split on whether `x` lies in the interior of a shared edge (`∃ i, x i = b i`)
  -- or in the open interior of a single unit triangle (`∀ k, b k < x k`).
  by_cases hex : ∃ i : Fin 3, x i = (b i : ℝ)
  · obtain ⟨i, hi_eq⟩ := hex
    have hsum_perm : x i + x (i + 1) + x (i + 2) = (m : ℝ) + 2 := by
      fin_cases i <;> simp <;> linarith [hsum_x]
    have hi_ne1 : x (i + 1) ≠ (b (i + 1) : ℝ) := by
      intro h1
      apply hnot_all
      have hz := heq_nat hi_eq h1 (hpos (i + 2)) hsum_perm
      have hzb : b (i + 2) = m + 2 - (b i + b (i + 1)) := by
        dsimp only [b]; rw [hz, Nat.floor_natCast]
      have h2 : x (i + 2) = (b (i + 2) : ℝ) := by rw [hzb, hz]
      intro k; fin_cases i <;> fin_cases k <;>
        { simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd]
            at hi_eq h1 h2 ⊢
          assumption }
    have hi_ne2 : x (i + 2) ≠ (b (i + 2) : ℝ) := by
      intro h2
      apply hnot_all
      have hz := heq_nat hi_eq h2 (hpos (i + 1)) (by linarith [hsum_perm])
      have hzb : b (i + 1) = m + 2 - (b i + b (i + 2)) := by
        dsimp only [b]; rw [hz, Nat.floor_natCast]
      have h1 : x (i + 1) = (b (i + 1) : ℝ) := by rw [hzb, hz]
      intro k; fin_cases i <;> fin_cases k <;>
        { simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd]
            at hi_eq h1 h2 ⊢
          assumption }
    have hlt1 : (b (i + 1) : ℝ) < x (i + 1) := lt_of_le_of_ne (hb_le _) hi_ne1.symm
    have hlt2 : (b (i + 2) : ℝ) < x (i + 2) := lt_of_le_of_ne (hb_le _) hi_ne2.symm
    have hbi_pos : 1 ≤ b i := by
      have : (0 : ℝ) < b i := by rw [← hi_eq]; exact hpos i
      exact_mod_cast this
    have hlo_r : ((b i + b (i + 1) + b (i + 2) : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ) := by
      push_cast; linarith [hi_eq, hlt1, hlt2, hsum_perm]
    have hhi_r : ((m + 2 : ℕ) : ℝ) < ((b i + b (i + 1) + b (i + 2) + 2 : ℕ) : ℝ) := by
      push_cast; linarith [hi_eq, hx_lt (i + 1), hx_lt (i + 2), hsum_perm]
    have hlo_n : b i + b (i + 1) + b (i + 2) < m + 2 := by exact_mod_cast hlo_r
    have hhi_n : m + 2 < b i + b (i + 1) + b (i + 2) + 2 := by exact_mod_cast hhi_r
    have hb012 : b i + b (i + 1) + b (i + 2) = m + 1 := by omega
    have hb_sum : b 0 + b 1 + b 2 = m + 1 := by
      fin_cases i <;> simp at hb012 <;> omega
    let s : Vertex m :=
      match i with
      | ⟨0, _⟩ => ⟨b 0 - 1, b 1, b 2, by
          have hb0 : 1 ≤ b 0 := hbi_pos; omega⟩
      | ⟨1, _⟩ => ⟨b 0, b 1 - 1, b 2, by
          have hb1 : 1 ≤ b 1 := hbi_pos; omega⟩
      | ⟨2, _⟩ => ⟨b 0, b 1, b 2 - 1, by
          have hb2 : 1 ≤ b 2 := hbi_pos; omega⟩
    have hs1 : s.coord (i + 1) = b (i + 1) := by fin_cases i <;> simp [s]
    have hs2 : s.coord (i + 2) = b (i + 2) := by fin_cases i <;> simp [s]
    let U : Set (Fin 3 → ℝ) :=
      (fun y : Fin 3 → ℝ => y (i + 1)) ⁻¹' Ioo (s.coord (i + 1) : ℝ) ((s.coord (i + 1) : ℝ) + 1) ∩
      (fun y : Fin 3 → ℝ => y (i + 2)) ⁻¹' Ioo (s.coord (i + 2) : ℝ) ((s.coord (i + 2) : ℝ) + 1)
    have hUo : IsOpen U :=
      (isOpen_Ioo.preimage (continuous_apply _)).inter (isOpen_Ioo.preimage (continuous_apply _))
    have hUc : Convex ℝ U :=
      ((convex_Ioo _ _).linear_preimage (LinearMap.proj (i + 1))).inter
        ((convex_Ioo _ _).linear_preimage (LinearMap.proj (i + 2)))
    have hxU : x ∈ U := by
      simp only [U, mem_inter_iff, mem_preimage, mem_Ioo, hs1, hs2]
      exact ⟨⟨hlt1, hx_lt _⟩, ⟨hlt2, hx_lt _⟩⟩
    have hsub : barycentricSimplex (m + 2) ∩ U ⊆ adjacentCell s i := by
      rw [adjacentCell_eq]
      rintro y ⟨hyS, ⟨hy1_lo, hy1_hi⟩, ⟨hy2_lo, hy2_hi⟩⟩
      exact ⟨hyS, hy1_lo.le, hy1_hi.le, hy2_lo.le, hy2_hi.le⟩
    exact ⟨U, hUo, hUc, hxU,
      ((concaveOn_adjacentCell_iff f s i).mpr (hadj s i)).subset hsub
        ((convex_barycentricSimplex _).inter hUc)⟩
  · push Not at hex
    have hlt : ∀ k, (b k : ℝ) < x k := fun k => lt_of_le_of_ne (hb_le k) (hex k).symm
    let U : Set (Fin 3 → ℝ) :=
      ⋂ k : Fin 3, (fun y : Fin 3 → ℝ => y k) ⁻¹' Ioo (b k : ℝ) ((b k : ℝ) + 1)
    have hUo : IsOpen U := isOpen_iInter_of_finite fun k => isOpen_Ioo.preimage (continuous_apply k)
    have hUc : Convex ℝ U :=
      convex_iInter fun k => (convex_Ioo _ _).linear_preimage (LinearMap.proj k)
    have hxU : x ∈ U := mem_iInter.mpr fun k => ⟨hlt k, hx_lt k⟩
    have hlo_r : ((b 0 + b 1 + b 2 : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ) := by
      push_cast; linarith [hlt 0, hlt 1, hlt 2, hsum_x]
    have hhi_r : ((m + 2 : ℕ) : ℝ) < ((b 0 + b 1 + b 2 + 3 : ℕ) : ℝ) := by
      push_cast; linarith [hx_lt 0, hx_lt 1, hx_lt 2, hsum_x]
    have hlo_n : b 0 + b 1 + b 2 < m + 2 := by exact_mod_cast hlo_r
    have hhi_n : m + 2 < b 0 + b 1 + b 2 + 3 := by exact_mod_cast hhi_r
    rcases (by omega : b 0 + b 1 + b 2 = m + 1 ∨ b 0 + b 1 + b 2 = m) with hm1 | hm0
    · let T : UnitTriangle (m + 2) := UnitTriangle.up ⟨b 0, b 1, b 2, hm1⟩
      have hsub : barycentricSimplex (m + 2) ∩ U ⊆ T.cell := fun y ⟨hyS, hyU⟩ =>
        T.mem_cell_iff.mpr ⟨hyS, fun k => by
          fin_cases k
          · simpa [T] using (mem_iInter.mp hyU 0).1.le
          · simpa [T] using (mem_iInter.mp hyU 1).1.le
          · simpa [T] using (mem_iInter.mp hyU 2).1.le⟩
      exact ⟨U, hUo, hUc, hxU,
        (concaveOn_triangleAffine f T ((convex_barycentricSimplex _).inter hUc)).congr
          fun y hy => (interpolate_eq_triangleAffine f (hsub hy)).symm⟩
    · let T : UnitTriangle (m + 2) := UnitTriangle.down ⟨b 0, b 1, b 2, hm0⟩
      have hsub : barycentricSimplex (m + 2) ∩ U ⊆ T.cell := fun y ⟨hyS, hyU⟩ =>
        T.mem_cell_iff.mpr ⟨hyS, fun k => by
          fin_cases k
          · simpa [T] using (mem_iInter.mp hyU 0).2.le
          · simpa [T] using (mem_iInter.mp hyU 1).2.le
          · simpa [T] using (mem_iInter.mp hyU 2).2.le⟩
      exact ⟨U, hUo, hUc, hxU,
        (concaveOn_triangleAffine f T ((convex_barycentricSimplex _).inter hUc)).congr
          fun y hy => (interpolate_eq_triangleAffine f (hsub hy)).symm⟩

private theorem concaveOn_lineMap_of_notMem_barycentric {m : ℕ} {f : Vertex (m + 2) → ℝ}
    (hadj : ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i))
    {p q : Fin 3 → ℝ} (hp : p ∈ barycentricSimplex (m + 2)) (hq : q ∈ barycentricSimplex (m + 2))
    (hp_pos : ∀ k, 0 < p k) (hq_pos : ∀ k, 0 < q k)
    (hnot : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap p q t ∉ Set.range (Vertex.barycentric (n := m + 2))) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (interpolate f ∘ AffineMap.lineMap p q) := by
  -- Step 1: Pull open convex local-concavity neighbourhoods back along `γ = lineMap p q`.
  let γ : ℝ →ᵃ[ℝ] (Fin 3 → ℝ) := AffineMap.lineMap p q
  have hγ_cont : Continuous γ := by
    have : (γ : ℝ → Fin 3 → ℝ) = fun t => (1 - t) • p + t • q := by
      ext t k; simp [γ, AffineMap.lineMap_apply_module]
    rw [this]
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hγ_mem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ barycentricSimplex (m + 2) := fun t ht => by
    dsimp only [γ]; rw [AffineMap.lineMap_apply_module]
    exact convex_barycentricSimplex (m + 2) hp hq (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have hγ_pos : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k, 0 < γ t k := fun t ht k => by
    dsimp only [γ]; rw [AffineMap.lineMap_apply_module]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · simp [hp_pos k]
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) (hp_pos k).le)
        (mul_pos ht0 (hq_pos k))
  have hlocal : ∀ t : Icc (0 : ℝ) 1, ∃ V : Set ℝ, IsOpen V ∧ t.1 ∈ V ∧ Convex ℝ V ∧
      ConcaveOn ℝ (Icc (0 : ℝ) 1 ∩ V) (interpolate f ∘ γ) := fun t => by
    obtain ⟨U, hUo, hUc, hγU, hconc⟩ :=
      exists_open_convex_concaveOn_of_notMem_barycentric hadj (hγ_mem t.1 t.2) (hγ_pos t.1 t.2)
        (hnot t.1 t.2)
    refine ⟨γ ⁻¹' U, hUo.preimage hγ_cont, hγU, hUc.affine_preimage γ, ?_⟩
    exact (hconc.comp_affineMap γ).subset
      (fun s hs => ⟨hγ_mem s hs.1, hs.2⟩)
      ((convex_Icc 0 1).inter (hUc.affine_preimage γ))
  -- Step 2: Extract a Lebesgue number `δ > 0` on `[0, 1]` and glue along a uniform grid
  -- of mesh `1 / (N + 2) < δ / 2` via `TauCeti.concaveOn_Icc_of_subdivision`.
  choose V hVo htV _ hVconc using hlocal
  obtain ⟨δ, hδ_pos, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hVo
    fun s hs => mem_iUnion.mpr ⟨⟨s, hs⟩, htV ⟨s, hs⟩⟩
  let N : ℕ := ⌊2 / δ⌋₊ + 1
  have hN_pos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hstep_lt : 2 / ((N : ℝ) + 2) < δ := by
    have hgt : 2 / δ < (N : ℝ) + 2 := by
      have := Nat.lt_floor_add_one (2 / δ)
      dsimp [N]; push_cast; linarith
    exact (div_lt_iff₀ hN_pos).mpr (by linarith [(div_lt_iff₀ hδ_pos).mp hgt])
  let t : Fin (N + 3) → ℝ := fun j => (j.val : ℝ) / ((N : ℝ) + 2)
  have ht_mono : StrictMono t := fun i j hij =>
    div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) hN_pos
  have ht0 : t 0 = 0 := by simp [t]
  have ht_last : t (Fin.last (N + 2)) = 1 := by
    simp only [t, Fin.val_last, Nat.cast_add, Nat.cast_ofNat]
    exact div_self hN_pos.ne'
  have hsub_conc : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 → b - a ≤ 2 / ((N : ℝ) + 2) →
      ConcaveOn ℝ (Icc a b) (interpolate f ∘ γ) := by
    intro a b ha0 hab hb1 hlen
    obtain ⟨idx, hidx⟩ := hball a ⟨ha0, hab.trans hb1⟩
    refine (hVconc idx).subset (fun s hs => ⟨⟨ha0.trans hs.1, hs.2.trans hb1⟩, hidx ?_⟩)
      (convex_Icc a b)
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
    exact (sub_le_sub_right hs.2 a).trans_lt (hlen.trans_lt hstep_lt)
  rw [← ht0, ← ht_last]
  refine TauCeti.concaveOn_Icc_of_subdivision ht_mono
    (hsub_conc (by simp [t]) (ht_mono.monotone (Fin.zero_le _))
      (ht_last ▸ ht_mono.monotone (Fin.le_last _)) ?_)
    fun k => hsub_conc (ht0 ▸ ht_mono.monotone (Fin.zero_le _))
      (ht_mono.monotone (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega))
      (ht_last ▸ ht_mono.monotone (Fin.le_last _)) ?_
  · simp only [t, Fin.val_one, Fin.val_zero, Nat.cast_one, Nat.cast_zero, zero_div, sub_zero]
    exact div_le_div_of_nonneg_right (by norm_num) hN_pos.le
  · simp only [t, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring_nf
    exact le_rfl

private theorem exists_perturbation_notMem_barycentric {m : ℕ} (p' q' : Fin 3 → ℝ) {δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    ∃ (w : Fin 3 → ℝ) (η : ℝ), 0 ≤ η ∧ η ≤ δ ∧ ∑ k, w k = 0 ∧ (∀ k, |w k| ≤ 1) ∧
      ∀ t : ℝ, AffineMap.lineMap (p' + η • w) (q' + η • w) t ∉
        Set.range (Vertex.barycentric (n := m + 2)) := by
  let v : Fin 3 → ℝ := q' - p'
  have hline (w : Fin 3 → ℝ) (η t : ℝ) :
      AffineMap.lineMap (p' + η • w) (q' + η • w) t = p' + η • w + t • v := by
    ext k; simp [AffineMap.lineMap_apply_module, v]; ring
  -- Case 1: `v 0 = 0`; shift `x₀` by `δ` or `δ / 2` to avoid integer `x₀`-coordinates.
  by_cases hv0 : v 0 = 0
  · let w : Fin 3 → ℝ := ![1, -1, 0]
    have hw_sum : ∑ k, w k = 0 := by simp [w, Fin.sum_univ_three]
    have hw_abs : ∀ k, |w k| ≤ 1 := fun k => by fin_cases k <;> simp [w]
    by_cases h1 : ∃ r : Vertex (m + 2), p' 0 + δ = r.barycentric 0
    · refine ⟨w, δ / 2, by positivity, by linarith, hw_sum, hw_abs, fun t ⟨r₂, hr₂⟩ => ?_⟩
      obtain ⟨r₁, hr₁⟩ := h1
      have hc0 := congrFun (hline w (δ / 2) t ▸ hr₂.symm) 0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w, Matrix.cons_val_zero, mul_one, hv0,
        mul_zero, add_zero, Vertex.barycentric_apply, Vertex.coord_zero] at hc0 hr₁
      have hdiff : ((r₁.x : ℤ) - (r₂.x : ℤ) : ℝ) = δ / 2 := by push_cast; linarith
      have hgt0 : ((0 : ℤ) : ℝ) < ((r₁.x : ℤ) - r₂.x : ℤ) := by
        push_cast; linarith [hdiff, hδ_pos]
      have hlt1 : (((r₁.x : ℤ) - r₂.x : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
        push_cast; linarith [hdiff, hδ_lt]
      have hz0 : (0 : ℤ) < (r₁.x : ℤ) - r₂.x := Int.cast_lt.mp hgt0
      have hz1 : (r₁.x : ℤ) - r₂.x < 1 := Int.cast_lt.mp hlt1
      omega
    · refine ⟨w, δ, hδ_pos.le, le_rfl, hw_sum, hw_abs, fun t ⟨r, hr⟩ => h1 ⟨r, ?_⟩⟩
      have hc0 := congrFun (hline w δ t ▸ hr.symm) 0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w, Matrix.cons_val_zero, mul_one, hv0,
        mul_zero, add_zero] at hc0
      exact hc0
  -- Case 2: `v 0 ≠ 0`; choose one of `|S| + 1` shifts so `v₁ y₀ - v₀ y₁` misses all vertices.
  · let w : Fin 3 → ℝ := ![0, -1, 1]
    have hw_sum : ∑ k, w k = 0 := by simp [w, Fin.sum_univ_three]
    have hw_abs : ∀ k, |w k| ≤ 1 := fun k => by fin_cases k <;> simp [w]
    let L : (Fin 3 → ℝ) → ℝ := fun y => v 1 * y 0 - v 0 * y 1
    let S : Finset ℝ := Finset.univ.image fun r : Vertex (m + 2) => L r.barycentric
    let step : Fin (S.card + 1) → ℝ := fun j => ((j.val + 1 : ℕ) : ℝ) / ((S.card + 2 : ℕ) : ℝ) * δ
    let φ : Fin (S.card + 1) → ℝ := fun j => L p' + step j * v 0
    have hden_pos : (0 : ℝ) < ((S.card + 2 : ℕ) : ℝ) := by positivity
    have hφ_inj : Function.Injective φ := by
      intro i j hij
      have hstep : step i = step j := mul_right_cancel₀ hv0 (add_left_cancel hij)
      have hdiv : ((i.val + 1 : ℕ) : ℝ) / ((S.card + 2 : ℕ) : ℝ) =
          ((j.val + 1 : ℕ) : ℝ) / ((S.card + 2 : ℕ) : ℝ) := mul_right_cancel₀ hδ_pos.ne' hstep
      have hnat : ((i.val + 1 : ℕ) : ℝ) = ((j.val + 1 : ℕ) : ℝ) :=
        (div_left_inj₀ hden_pos.ne').mp hdiv
      exact Fin.ext (Nat.succ.inj (Nat.cast_injective hnat))
    have hex_j : ∃ j : Fin (S.card + 1), φ j ∉ S := by
      by_contra hall
      push Not at hall
      have hsub : Finset.univ.image φ ⊆ S := by
        intro z hz
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
        exact hall j
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hφ_inj, Finset.card_fin] at hcard
      omega
    obtain ⟨j, hj⟩ := hex_j
    have hstep_nonneg : 0 ≤ step j := by positivity
    have hstep_le : step j ≤ δ := by
      refine mul_le_of_le_one_left hδ_pos.le ((div_le_one hden_pos).mpr ?_)
      exact_mod_cast (by omega : j.val + 1 ≤ S.card + 2)
    refine ⟨w, step j, hstep_nonneg, hstep_le, hw_sum, hw_abs, fun t ⟨r, hr⟩ => hj ?_⟩
    have hLr : L r.barycentric = φ j := by
      rw [hr, hline]
      simp only [L, φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, w, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      ring
    exact hLr ▸ Finset.mem_image_of_mem _ (Finset.mem_univ r)

private theorem concaveOn_barycentricSimplex_of_adjacent {m : ℕ} {f : Vertex (m + 2) → ℝ}
    (hadj : ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i)) :
    ConcaveOn ℝ (barycentricSimplex (m + 2)) (interpolate f) := by
  refine ⟨convex_barycentricSimplex (m + 2), fun p hp q hq a b ha hb hab => ?_⟩
  -- Step 1: Pull `p` and `q` slightly toward the barycenter `c` and perturb away from vertices.
  let c : Fin 3 → ℝ := fun _ => ((m + 2 : ℕ) : ℝ) / 3
  have hc_mem : c ∈ barycentricSimplex (m + 2) :=
    mem_barycentricSimplex_iff.mpr
      ⟨fun _ => by dsimp [c]; positivity, by simp [c]; ring⟩
  let ε : ℕ → ℝ := fun K => (1 / 3 : ℝ) * (1 / ((K : ℝ) + 1))
  have hε_pos : ∀ K, 0 < ε K := fun K => by dsimp [ε]; positivity
  have hε_le : ∀ K, ε K ≤ 1 / 3 := fun K => by
    dsimp [ε]
    have h1 : 1 / ((K : ℝ) + 1) ≤ 1 :=
      div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) K]) (by positivity)
    linarith
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, one_div] using
      (tendsto_const_nhds (x := (3 : ℝ)⁻¹)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpert : ∀ K : ℕ, ∃ (w : Fin 3 → ℝ) (η : ℝ),
      0 ≤ η ∧ η ≤ ε K / 3 ∧ ∑ k, w k = 0 ∧ (∀ k, |w k| ≤ 1) ∧
      ∀ t : ℝ, AffineMap.lineMap (((1 - ε K) • p + ε K • c) + η • w)
        (((1 - ε K) • q + ε K • c) + η • w) t ∉
        Set.range (Vertex.barycentric (n := m + 2)) := fun K =>
    exists_perturbation_notMem_barycentric _ _ (by linarith [hε_pos K])
      (by linarith [hε_le K])
  choose w η hη_nonneg hη_le hw_sum hw_abs havoid using hpert
  let pK : ℕ → Fin 3 → ℝ := fun K => ((1 - ε K) • p + ε K • c) + η K • w K
  let qK : ℕ → Fin 3 → ℝ := fun K => ((1 - ε K) • q + ε K • c) + η K • w K
  -- Step 2: Verify that the perturbed endpoints stay in the strict interior and converge to `p, q`.
  have hpos_shift : ∀ (z : Fin 3 → ℝ), z ∈ barycentricSimplex (m + 2) → ∀ K k,
      0 < (((1 - ε K) • z + ε K • c) + η K • w K) k := by
    intro z hz K k
    have h1e : 0 ≤ 1 - ε K := by linarith [hε_le K]
    have hck : (2 : ℝ) / 3 ≤ c k := by
      dsimp [c]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hwk : -(1 : ℝ) ≤ w K k := (abs_le.mp (hw_abs K k)).1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hterm1 : 0 ≤ (1 - ε K) * z k := mul_nonneg h1e ((mem_barycentricSimplex_iff.mp hz).1 k)
    have hterm2 : 2 * ε K / 3 ≤ ε K * c k := by nlinarith [hε_pos K, hck]
    have hterm3 : -(ε K / 3) ≤ η K * w K k := by nlinarith [hη_nonneg K, hη_le K, hwk]
    linarith [hε_pos K]
  have hmem_shift : ∀ (z : Fin 3 → ℝ), z ∈ barycentricSimplex (m + 2) → ∀ K,
      (((1 - ε K) • z + ε K • c) + η K • w K) ∈ barycentricSimplex (m + 2) := by
    intro z hz K
    refine mem_barycentricSimplex_iff.mpr ⟨fun k => (hpos_shift z hz K k).le, ?_⟩
    have hz_conv : (1 - ε K) • z + ε K • c ∈ barycentricSimplex (m + 2) :=
      convex_barycentricSimplex (m + 2) hz hc_mem (by linarith [hε_le K]) (hε_pos K).le
        (sub_add_cancel 1 _)
    have hsplit : ∑ i, (((1 - ε K) • z + ε K • c) + η K • w K) i =
        ∑ i, ((1 - ε K) • z + ε K • c) i + ∑ i, (η K • w K) i := by
      simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [hsplit, (mem_barycentricSimplex_iff.mp hz_conv).2]
    simp [← Finset.mul_sum, hw_sum K]
  have htend_shift : ∀ (z : Fin 3 → ℝ),
      Tendsto (fun K => ((1 - ε K) • z + ε K • c) + η K • w K) atTop (𝓝 z) := by
    intro z
    refine tendsto_pi_nhds.mpr fun k => tendsto_sub_nhds_zero_iff.mp ?_
    refine squeeze_zero_norm (a := fun K => ε K * (|c k - z k| + 1)) (fun K => ?_) ?_
    · rw [Real.norm_eq_abs]
      have hid : (((1 - ε K) • z + ε K • c + η K • w K) k - z k) =
          ε K * (c k - z k) + η K * w K k := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [hid]
      have hηw : η K * |w K k| ≤ ε K :=
        (mul_le_of_le_one_right (hη_nonneg K) (hw_abs K k)).trans (by linarith [hη_le K, hε_pos K])
      calc |ε K * (c k - z k) + η K * w K k|
          ≤ |ε K * (c k - z k)| + |η K * w K k| := abs_add_le _ _
        _ = ε K * |c k - z k| + η K * |w K k| := by
            rw [abs_mul (ε K), abs_mul (η K), abs_of_pos (hε_pos K), abs_of_nonneg (hη_nonneg K)]
        _ ≤ ε K * (|c k - z k| + 1) := by linarith [hηw]
    · simpa using hε_tendsto.mul tendsto_const_nhds
  -- Step 3: Apply segment concavity along `[pK K, qK K]` and pass to `K → ∞` by continuity.
  have hineqK : ∀ K : ℕ,
      a • interpolate f (pK K) + b • interpolate f (qK K) ≤
        interpolate f (a • pK K + b • qK K) := by
    intro K
    have hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) (interpolate f ∘ AffineMap.lineMap (pK K) (qK K)) :=
      concaveOn_lineMap_of_notMem_barycentric hadj
        (hmem_shift p hp K) (hmem_shift q hq K) (hpos_shift p hp K) (hpos_shift q hq K)
        fun t _ => havoid K t
    have h01 := hconc.2 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) ha hb hab
    have hmid : AffineMap.lineMap (pK K) (qK K) b = a • pK K + b • qK K := by
      ext k
      simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination -pK K k * hab
    simpa [hmid] using h01
  have hf_cont := continuousOn_interpolate f
  have htend_val : ∀ {u : ℕ → Fin 3 → ℝ} {z : Fin 3 → ℝ},
      z ∈ barycentricSimplex (m + 2) → (∀ K, u K ∈ barycentricSimplex (m + 2)) →
      Tendsto u atTop (𝓝 z) → Tendsto (fun K => interpolate f (u K)) atTop (𝓝 (interpolate f z)) :=
    fun {u z} hz hu_mem hu =>
      (hf_cont z hz).tendsto.comp
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu (Eventually.of_forall hu_mem))
  have hp_lim := htend_val hp (hmem_shift p hp) (htend_shift p)
  have hq_lim := htend_val hq (hmem_shift q hq) (htend_shift q)
  have hpq_mem : a • p + b • q ∈ barycentricSimplex (m + 2) :=
    convex_barycentricSimplex (m + 2) hp hq ha hb hab
  have hpqK_mem : ∀ K, a • pK K + b • qK K ∈ barycentricSimplex (m + 2) := fun K =>
    convex_barycentricSimplex (m + 2) (hmem_shift p hp K) (hmem_shift q hq K) ha hb hab
  have hpqK_tend : Tendsto (fun K => a • pK K + b • qK K) atTop (𝓝 (a • p + b • q)) :=
    ((htend_shift p).const_smul a).add ((htend_shift q).const_smul b)
  exact le_of_tendsto_of_tendsto
    ((hp_lim.const_smul a).add (hq_lim.const_smul b))
    (htend_val hpq_mem hpqK_mem hpqK_tend)
    (Eventually.of_forall hineqK)

private theorem isRhombusConcave_of_concaveOn_barycentricSimplex {n : ℕ} {f : Vertex n → ℝ}
    (hconc : ConcaveOn ℝ (barycentricSimplex n) (interpolate f)) :
    IsRhombusConcave f := by
  refine (isRhombusConcave_def f).mpr fun a b c d hr => ?_
  have hb : b.barycentric ∈ barycentricSimplex n := barycentric_mem_barycentricSimplex b
  have hd : d.barycentric ∈ barycentricSimplex n := barycentric_mem_barycentricSimplex d
  have hmid : (1 / 2 : ℝ) • b.barycentric + (1 / 2 : ℝ) • d.barycentric =
      AffineMap.lineMap a.barycentric c.barycentric (1 / 2 : ℝ) := by
    rw [AffineMap.lineMap_apply_module]
    have hmx : (a.x : ℝ) + c.x = b.x + d.x := by exact_mod_cast hr.midpoint_x
    have hmy : (a.y : ℝ) + c.y = b.y + d.y := by exact_mod_cast hr.midpoint_y
    have hmz : (a.z : ℝ) + c.z = b.z + d.z := by exact_mod_cast hr.midpoint_z
    ext k; fin_cases k <;> simp <;> linarith
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hineq := hconc.2 hb hd hhalf hhalf (by norm_num)
  rw [hmid, interpolate_lineMap_of_isUnitEdge f hr.isUnitEdge_short ⟨by norm_num, by norm_num⟩,
    interpolate_barycentric, interpolate_barycentric] at hineq
  simp only [smul_eq_mul] at hineq
  linarith

/-- **Rhombus concavity criterion (barycentric chart)**: the simplicial piecewise-affine extension
`interpolate f` is concave on `barycentricSimplex n` if and only if `f` satisfies all unit-rhombus
concavity inequalities. -/
theorem concaveOn_barycentricSimplex_interpolate_iff {n : ℕ} (f : Vertex n → ℝ) :
    ConcaveOn ℝ (barycentricSimplex n) (interpolate f) ↔ IsRhombusConcave f := by
  refine ⟨isRhombusConcave_of_concaveOn_barycentricSimplex, fun hf => ?_⟩
  match n with
  | 0 =>
    exact (concaveOn_const (f (Vertex.cornerA 0)) (convex_barycentricSimplex 0)).congr
      fun x _ => (interpolate_zero_rank f x).symm
  | 1 =>
    let T : UnitTriangle 1 := UnitTriangle.up (Vertex.cornerA 0)
    exact (concaveOn_triangleAffine f T (convex_barycentricSimplex 1)).congr
      fun x hx =>
        (interpolate_eq_triangleAffine f (by rwa [UnitTriangle.cell_up_cornerA_zero])).symm
  | m + 2 =>
    exact concaveOn_barycentricSimplex_of_adjacent fun s i =>
      (isRhombusConcave_iff_rhombusSlack_nonneg f).mp hf (isRhombus_adjacent s i)

/-- At size `m + 2`, rhombus concavity is completely determined by the `3 * |Vertex m|` interior
adjacent-triangle unit rhombi `isRhombus_adjacent s i`. -/
theorem isRhombusConcave_iff_adjacent {m : ℕ} (f : Vertex (m + 2) → ℝ) :
    IsRhombusConcave f ↔
      ∀ (s : Vertex m) (i : Fin 3),
        0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
          ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) :=
  ⟨fun hf s i => (isRhombusConcave_iff_rhombusSlack_nonneg f).mp hf (isRhombus_adjacent s i),
    fun hadj => isRhombusConcave_of_concaveOn_barycentricSimplex
      (concaveOn_barycentricSimplex_of_adjacent hadj)⟩

/-- **Rhombus concavity criterion (Euclidean planar chart)**: `planarInterpolate f` is concave on
`planarSimplex n` if and only if `f` is rhombus-concave. -/
theorem concaveOn_planarSimplex_planarInterpolate_iff {n : ℕ} (f : Vertex n → ℝ) :
    ConcaveOn ℝ (planarSimplex n) (planarInterpolate f) ↔ IsRhombusConcave f := by
  rw [← concaveOn_barycentricSimplex_interpolate_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hcomp := h.comp_linearMap planeLinear.toLinearMap
    have hpre : barycentricSimplex n ⊆ planeLinear.toLinearMap ⁻¹' planarSimplex n :=
      fun x hx => mem_planarSimplex_iff.mpr (by
        simp only [ContinuousLinearMap.coe_coe,
          planeInvAffine_planeLinear (mem_barycentricSimplex_iff.mp hx).2]
        exact hx)
    exact (hcomp.subset hpre (convex_barycentricSimplex n)).congr
      fun x hx => planarInterpolate_planeLinear f (mem_barycentricSimplex_iff.mp hx).2
  · exact ((h.comp_affineMap (planeInvAffine n).toAffineMap).subset
      (fun _ hu => mem_planarSimplex_iff.mp hu) (convex_planarSimplex n)).congr
      fun u _ => (planarInterpolate_def f u).symm

/-- Every real hive has concave simplicial interpolation on `barycentricSimplex n`. -/
theorem concaveOn_barycentricSimplex_interpolate {n : ℕ} (h : RealHive n) :
    ConcaveOn ℝ (barycentricSimplex n) (interpolate h) :=
  (concaveOn_barycentricSimplex_interpolate_iff h).mpr h.isRhombusConcave

/-- Every real hive has concave planar simplicial interpolation on `planarSimplex n`. -/
theorem concaveOn_planarSimplex_planarInterpolate {n : ℕ} (h : RealHive n) :
    ConcaveOn ℝ (planarSimplex n) (planarInterpolate h) :=
  (concaveOn_planarSimplex_planarInterpolate_iff h).mpr h.isRhombusConcave

/-- Every affine piece `triangleAffine f T` globally upper-bounds `interpolate f` on
`barycentricSimplex n` whenever `f` is rhombus-concave. -/
theorem IsRhombusConcave.interpolate_le_triangleAffine {n : ℕ} {f : Vertex n → ℝ}
    (hf : IsRhombusConcave f) (T : UnitTriangle n) {x : Fin 3 → ℝ}
    (hx : x ∈ barycentricSimplex n) :
    interpolate f x ≤ triangleAffine f T x := by
  let c : Fin 3 → ℝ := ∑ j : Fin 3, (1 / 3 : ℝ) • (T.vertex j).barycentric
  have hc_sum : ∑ j : Fin 3, (1 / 3 : ℝ) = 1 := by norm_num
  have hc_weight : ∀ i : Fin 3, T.weight i c = 1 / 3 := fun i => by
    have hlin : T.weight i c = ∑ j : Fin 3, (1 / 3 : ℝ) * T.weight i (T.vertex j).barycentric := by
      cases T with
      | up base =>
        simp only [c, UnitTriangle.weight_up_apply, Fin.sum_univ_three, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        ring
      | down base =>
        simp only [c, UnitTriangle.weight_down_apply, Fin.sum_univ_three, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        ring
    rw [hlin]
    fin_cases i <;> simp
  have hc_mem : c ∈ barycentricSimplex n :=
    (convex_barycentricSimplex n).sum_mem (fun _ _ => by norm_num) hc_sum
      fun j _ => barycentric_mem_barycentricSimplex (T.vertex j)
  have hc_cell : c ∈ T.cell :=
    T.mem_cell_iff.mpr ⟨hc_mem, fun i => by rw [hc_weight i]; norm_num⟩
  let M : ℝ := |T.weight 0 x| + |T.weight 1 x| + |T.weight 2 x| + 1
  have hM_pos : 0 < M := by dsimp [M]; positivity
  let t : ℝ := 1 / (3 * M + 1)
  have ht_pos : 0 < t := by dsimp [t]; positivity
  have ht_le : t ≤ 1 := div_le_one_of_le₀ (by linarith [hM_pos]) (by positivity)
  let y : Fin 3 → ℝ := (1 - t) • c + t • x
  have hy_cell : y ∈ T.cell := by
    refine T.mem_cell_iff.mpr ⟨convex_barycentricSimplex n hc_mem hx (sub_nonneg.mpr ht_le)
      ht_pos.le (sub_add_cancel 1 t), fun i => ?_⟩
    have hwi : T.weight i y = (1 - t) * (1 / 3) + t * T.weight i x := by
      rw [← hc_weight i]
      cases T <;> simp [y] <;> ring
    rw [hwi]
    have habs : -M ≤ T.weight i x := by
      have : |T.weight i x| ≤ M := by
        fin_cases i <;> simp only [M, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
          linarith [abs_nonneg (T.weight 0 x), abs_nonneg (T.weight 1 x),
            abs_nonneg (T.weight 2 x)]
      linarith [(abs_le.mp this).1]
    have hprod : t * (-M) ≤ t * T.weight i x := mul_le_mul_of_nonneg_left habs ht_pos.le
    have htM : (1 - t) * (1 / 3) - t * M ≥ 0 := by
      have _ : 3 * M + 1 ≠ 0 := by positivity
      dsimp [t]; field_simp; linarith
    linarith
  have hconc := ((concaveOn_barycentricSimplex_interpolate_iff f).mpr hf).2 hc_mem hx
    (sub_nonneg.mpr ht_le) ht_pos.le (sub_add_cancel 1 t)
  have hy_val : interpolate f y = (1 - t) * triangleAffine f T c + t * triangleAffine f T x := by
    rw [interpolate_eq_triangleAffine f hy_cell]
    have hsum : ∑ i : Fin 3, (![1 - t, t, 0] : Fin 3 → ℝ) i = 1 := by simp [Fin.sum_univ_three]
    have hpt : y = ∑ i : Fin 3, (![1 - t, t, 0] : Fin 3 → ℝ) i • (![c, x, 0] : Fin 3 → _) i := by
      ext k; simp [y, Fin.sum_univ_three]
    rw [hpt, triangleAffine_combo f T hsum]
    simp [Fin.sum_univ_three]
  rw [interpolate_eq_triangleAffine f hc_cell, hy_val] at hconc
  simp only [smul_eq_mul] at hconc
  exact le_of_mul_le_mul_left (by linarith) ht_pos

/-- **Global affine-envelope formula**: for `n = m + 1 ≥ 1` and rhombus-concave `f`,
`interpolate f x` on `barycentricSimplex (m + 1)` is the minimum over all `n²` unit triangles of
`triangleAffine f T x`. -/
theorem IsRhombusConcave.interpolate_eq_inf'_triangleAffine {m : ℕ} {f : Vertex (m + 1) → ℝ}
    (hf : IsRhombusConcave f) {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex (m + 1)) :
    interpolate f x = Finset.univ.inf' Finset.univ_nonempty
      (fun T : UnitTriangle (m + 1) => triangleAffine f T x) := by
  obtain ⟨T₀, hT₀⟩ := mem_iUnion.mp ((UnitTriangle.iUnion_cell_eq_barycentricSimplex m).symm ▸ hx)
  refine le_antisymm
    (Finset.le_inf' _ _ fun T _ => hf.interpolate_le_triangleAffine T hx)
    (le_trans (Finset.inf'_le _ (Finset.mem_univ T₀)) (interpolate_eq_triangleAffine f hT₀).ge)

/-! ### Small-rank checks -/

section SmallRank

theorem concaveOn_barycentricSimplex_interpolate_exampleTwo :
    ConcaveOn ℝ (barycentricSimplex 2) (interpolate (toReal exampleTwo)) :=
  (toReal exampleTwo).concaveOn_barycentricSimplex_interpolate

theorem concaveOn_barycentricSimplex_interpolate_detTwo :
    ConcaveOn ℝ (barycentricSimplex 2) (interpolate (toReal detTwo)) :=
  (toReal detTwo).concaveOn_barycentricSimplex_interpolate

/-- Size-`2` non-hive check: the indicator of `m_BC = (0, 1, 1)` has non-concave simplicial
interpolation on `barycentricSimplex 2`. -/
theorem not_concaveOn_barycentricSimplex_interpolate_indicator_mBC :
    ¬ ConcaveOn ℝ (barycentricSimplex 2)
      (interpolate fun p : Vertex 2 => if p = ⟨0, 1, 1, rfl⟩ then (1 : ℝ) else 0) := by
  rw [concaveOn_barycentricSimplex_interpolate_iff]
  intro hf
  have h := (isRhombusConcave_def _).mp hf isRhombus_at_cornerA
  simp [Vertex.ext_iff] at h
  linarith

end SmallRank

end TauCeti.Hive
