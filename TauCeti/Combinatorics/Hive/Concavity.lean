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

private theorem rhombus_barycentric_add {n : ℕ} {a b c d : Vertex n} (hr : IsRhombus a b c d)
    (k : Fin 3) : a.barycentric k + c.barycentric k = b.barycentric k + d.barycentric k := by
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Vertex.barycentric_apply,
    Vertex.coord_zero, Vertex.coord_one, Vertex.coord_two]
  · exact_mod_cast hr.midpoint_x
  · exact_mod_cast hr.midpoint_y
  · exact_mod_cast hr.midpoint_z

private theorem rhombusSlack_nonneg_of_concaveOn {n : ℕ} {f : Vertex n → ℝ} {S : Set (Fin 3 → ℝ)}
    (hconc : ConcaveOn ℝ S (interpolate f)) {a b c d : Vertex n} (hr : IsRhombus a b c d)
    (hb : b.barycentric ∈ S) (hd : d.barycentric ∈ S) : 0 ≤ rhombusSlack f a b c d := by
  have hmid : (1 / 2 : ℝ) • b.barycentric + (1 / 2 : ℝ) • d.barycentric =
      AffineMap.lineMap a.barycentric c.barycentric (1 / 2 : ℝ) := by
    ext k; simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [rhombus_barycentric_add hr k]
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h := hconc.2 hb hd hhalf hhalf (by norm_num)
  rw [hmid, interpolate_lineMap_of_isUnitEdge f hr.isUnitEdge_short ⟨by norm_num, by norm_num⟩,
    interpolate_barycentric, interpolate_barycentric] at h
  simp only [smul_eq_mul, rhombusSlack_def] at h ⊢; linarith

/-- Exact bending formula across the shared `i`-th edge of `down s` and `adjacentUp s i`: on the
sum-`(m + 2)` hyperplane, the difference of their affine pieces equals `((sᵢ + 1) - xᵢ)` times the
unit-rhombus slack. -/
theorem triangleAffine_adjacentUp_sub_down {m : ℕ} (f : Vertex (m + 2) → ℝ) (s : Vertex m)
    (i : Fin 3) {x : Fin 3 → ℝ} (hx : ∑ k, x k = ((m + 2 : ℕ) : ℝ)) :
    triangleAffine f (adjacentUp s i) x - triangleAffine f (UnitTriangle.down s) x =
      ((s.coord i : ℝ) + 1 - x i) *
        rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
          ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) := by
  let U := adjacentUp s i; let D := UnitTriangle.down s
  have hvi : (D.vertex i).barycentric = ∑ j : Fin 3, (![1, 1, -1] : Fin 3 → ℝ) j •
      (![(D.vertex (i + 2)).barycentric, (D.vertex (i + 1)).barycentric,
        (U.vertex i).barycentric] : Fin 3 → _) j := by
    ext k; simp only [Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]; linarith [rhombus_barycentric_add (isRhombus_adjacent s i) k]
  have hU_v1 : triangleAffine f U (D.vertex (i + 1)).barycentric = f (D.vertex (i + 1)) := by
    dsimp [U, D]; rw [← adjacentUp_vertex_add_two s i, triangleAffine_vertex]
  have hU_v2 : triangleAffine f U (D.vertex (i + 2)).barycentric = f (D.vertex (i + 2)) := by
    dsimp [U, D]; rw [← adjacentUp_vertex_add_one s i, triangleAffine_vertex]
  have hU_vi : triangleAffine f U (D.vertex i).barycentric =
      f (D.vertex (i + 2)) + f (D.vertex (i + 1)) - f (U.vertex i) := by
    rw [hvi, triangleAffine_combo f U (by simp [Fin.sum_univ_three])]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, hU_v2, hU_v1, triangleAffine_vertex]; ring
  have hperm (g : Fin 3 → ℝ) : ∑ k : Fin 3, g k = g i + g (i + 1) + g (i + 2) := by
    fin_cases i <;> simp [Fin.sum_univ_three] <;> ring
  conv_lhs => rw [← D.sum_weight_smul_vertex hx, triangleAffine_combo f U (D.sum_weight hx),
    triangleAffine_combo f D (D.sum_weight hx)]
  rw [hperm, hperm, hU_vi, hU_v1, hU_v2, triangleAffine_vertex, triangleAffine_vertex,
    triangleAffine_vertex, UnitTriangle.weight_down_apply s i x, rhombusSlack_def]; ring

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
  intro x hx_adj; rcases mem_adjacentCell_iff.mp hx_adj with hx | hx
  · rw [interpolate_eq_triangleAffine f hx, Pi.inf_apply, eq_comm, inf_eq_left]
    have hdiff := triangleAffine_adjacentUp_sub_down f s i
      (mem_barycentricSimplex_iff.mp ((adjacentUp s i).cell_subset_barycentricSimplex hx)).2
    have hw : 0 ≤ x i - ((s.coord i : ℝ) + 1) := by simpa using (adjacentUp s i).weight_nonneg hx i
    linarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : (s.coord i : ℝ) + 1 - x i ≤ 0) hslack]
  · rw [interpolate_eq_triangleAffine f hx, Pi.inf_apply, eq_comm, inf_eq_right]
    have hdiff := triangleAffine_adjacentUp_sub_down f s i
      (mem_barycentricSimplex_iff.mp ((UnitTriangle.down s).cell_subset_barycentricSimplex hx)).2
    have hw : 0 ≤ (s.coord i : ℝ) + 1 - x i := by
      simpa using (UnitTriangle.down s).weight_nonneg hx i
    linarith [mul_nonneg hw hslack]

/-- **Adjacent-triangle bending test**: `interpolate f` is concave on the union cell
`adjacentCell s i` of `adjacentUp s i` and `down s` if and only if the corresponding unit-rhombus
slack is nonnegative. -/
theorem concaveOn_adjacentCell_iff {m : ℕ} (f : Vertex (m + 2) → ℝ) (s : Vertex m) (i : Fin 3) :
    ConcaveOn ℝ (adjacentCell s i) (interpolate f) ↔
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i) :=
  ⟨fun hconc => rhombusSlack_nonneg_of_concaveOn hconc (isRhombus_adjacent s i)
      (mem_adjacentCell_iff.mpr (Or.inl ((adjacentUp s i).vertex_barycentric_mem_cell i)))
      (mem_adjacentCell_iff.mpr (Or.inr ((UnitTriangle.down s).vertex_barycentric_mem_cell i))),
    fun hslack => ((concaveOn_triangleAffine f (adjacentUp s i) (convex_adjacentCell s i)).inf
      (concaveOn_triangleAffine f (UnitTriangle.down s) (convex_adjacentCell s i))).congr
      (eqOn_inf_triangleAffine_adjacentCell hslack).symm⟩

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
  obtain ⟨hx_nonneg, hx_sum⟩ := mem_barycentricSimplex_iff.mp hx
  let b : Fin 3 → ℕ := fun k => ⌊x k⌋₊
  have hb_le (k : Fin 3) : (b k : ℝ) ≤ x k := Nat.floor_le (hx_nonneg k)
  have hx_lt (k : Fin 3) : x k < (b k : ℝ) + 1 := Nat.lt_floor_add_one (x k)
  have hsum_x : x 0 + x 1 + x 2 = (m : ℝ) + 2 := by
    simpa [Fin.sum_univ_three, add_assoc] using hx_sum
  have hnot_all (hall : ∀ k, x k = (b k : ℝ)) : False :=
    hnot ⟨⟨b 0, b 1, b 2, Nat.cast_injective
        (by push_cast; linarith [hall 0, hall 1, hall 2] : ((_ : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ))⟩,
      by ext k; fin_cases k <;> simp [hall _]⟩
  by_cases hex : ∃ i : Fin 3, x i = (b i : ℝ)
  · obtain ⟨i, hi_eq⟩ := hex
    have hsum_perm : x i + x (i + 1) + x (i + 2) = (m : ℝ) + 2 := by
      fin_cases i <;> simp <;> linarith [hsum_x]
    have htwo {j k : Fin 3} (hp : x i + x j + x k = (m : ℝ) + 2) (hj : x j = b j) : x k = b k := by
      have hle : b i + b j ≤ m + 2 := Nat.cast_le.mp
        (by push_cast; linarith [hpos k] : ((b i + b j : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ))
      have hxk : x k = ((m + 2 - (b i + b j) : ℕ) : ℝ) := by
        rw [Nat.cast_sub hle]; push_cast; linarith
      dsimp [b]; rw [hxk, Nat.floor_natCast]
    have hall12 (h1 : x (i + 1) = b (i + 1)) (h2 : x (i + 2) = b (i + 2)) : False :=
      hnot_all fun k => by
        fin_cases i <;> fin_cases k <;>
          { simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd]
              at hi_eq h1 h2 ⊢; assumption }
    have hlt1 : (b (i + 1) : ℝ) < x (i + 1) :=
      lt_of_le_of_ne (hb_le _) fun h => hall12 h.symm (htwo hsum_perm h.symm)
    have hlt2 : (b (i + 2) : ℝ) < x (i + 2) :=
      lt_of_le_of_ne (hb_le _) fun h => hall12 (htwo (by linarith) h.symm) h.symm
    have hbi_pos : 0 < b i := by exact_mod_cast (hi_eq ▸ hpos i : (0 : ℝ) < b i)
    have hb_sum : b 0 + b 1 + b 2 = m + 1 := by
      have h1 : b i + b (i + 1) + b (i + 2) < m + 2 :=
        Nat.cast_lt.mp (by push_cast; linarith : ((_ : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ))
      have h2 : m + 2 < b i + b (i + 1) + b (i + 2) + 2 := Nat.cast_lt.mp
        (by push_cast; linarith [hx_lt (i + 1), hx_lt (i + 2)] : ((m + 2 : ℕ) : ℝ) < ((_ : ℕ) : ℝ))
      fin_cases i <;> simp at h1 h2 <;> omega
    let s : Vertex m :=
      ⟨b 0 - if i = 0 then 1 else 0, b 1 - if i = 1 then 1 else 0, b 2 - if i = 2 then 1 else 0,
        by fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
          Fin.reduceEq, ↓reduceIte, Nat.sub_zero] at hbi_pos ⊢ <;> omega⟩
    have hs1 : s.coord (i + 1) = b (i + 1) := by fin_cases i <;> simp [s]
    have hs2 : s.coord (i + 2) = b (i + 2) := by fin_cases i <;> simp [s]
    let U : Set (Fin 3 → ℝ) :=
      (fun y : Fin 3 → ℝ => y (i + 1)) ⁻¹' Ioo (s.coord (i + 1) : ℝ) ((s.coord (i + 1) : ℝ) + 1) ∩
      (fun y : Fin 3 → ℝ => y (i + 2)) ⁻¹' Ioo (s.coord (i + 2) : ℝ) ((s.coord (i + 2) : ℝ) + 1)
    have hUc : Convex ℝ U :=
      ((convex_Ioo _ _).linear_preimage (LinearMap.proj (i + 1))).inter
        ((convex_Ioo _ _).linear_preimage (LinearMap.proj (i + 2)))
    refine ⟨U, (isOpen_Ioo.preimage (continuous_apply _)).inter
        (isOpen_Ioo.preimage (continuous_apply _)), hUc, ?_,
      ((concaveOn_adjacentCell_iff f s i).mpr (hadj s i)).subset ?_
        ((convex_barycentricSimplex _).inter hUc)⟩
    · simp only [U, mem_inter_iff, mem_preimage, mem_Ioo, hs1, hs2]
      exact ⟨⟨hlt1, hx_lt _⟩, ⟨hlt2, hx_lt _⟩⟩
    · rw [adjacentCell_eq]
      rintro y ⟨hyS, ⟨hy1_lo, hy1_hi⟩, ⟨hy2_lo, hy2_hi⟩⟩
      exact ⟨hyS, hy1_lo.le, hy1_hi.le, hy2_lo.le, hy2_hi.le⟩
  · push Not at hex
    have hlt (k : Fin 3) : (b k : ℝ) < x k := lt_of_le_of_ne (hb_le k) (hex k).symm
    let U : Set (Fin 3 → ℝ) := ⋂ k : Fin 3, (fun y : Fin 3 → ℝ => y k) ⁻¹' Ioo (b k : ℝ) (b k + 1)
    have hUo : IsOpen U := isOpen_iInter_of_finite fun k => isOpen_Ioo.preimage (continuous_apply k)
    have hUc : Convex ℝ U :=
      convex_iInter fun k => (convex_Ioo _ _).linear_preimage (LinearMap.proj k)
    have hxU : x ∈ U := mem_iInter.mpr fun k => ⟨hlt k, hx_lt k⟩
    have h1 : b 0 + b 1 + b 2 < m + 2 := Nat.cast_lt.mp
      (by push_cast; linarith [hlt 0, hlt 1, hlt 2] : ((_ : ℕ) : ℝ) < ((m + 2 : ℕ) : ℝ))
    have h2 : m + 2 < b 0 + b 1 + b 2 + 3 := Nat.cast_lt.mp
      (by push_cast; linarith [hx_lt 0, hx_lt 1, hx_lt 2] : ((m + 2 : ℕ) : ℝ) < ((_ : ℕ) : ℝ))
    have hcell (T : UnitTriangle (m + 2)) (hsub : barycentricSimplex (m + 2) ∩ U ⊆ T.cell) :
        ConcaveOn ℝ (barycentricSimplex (m + 2) ∩ U) (interpolate f) :=
      (concaveOn_triangleAffine f T ((convex_barycentricSimplex _).inter hUc)).congr
        fun _ hy => (interpolate_eq_triangleAffine f (hsub hy)).symm
    rcases (by omega : b 0 + b 1 + b 2 = m + 1 ∨ b 0 + b 1 + b 2 = m) with hm1 | hm0
    · exact ⟨U, hUo, hUc, hxU, hcell (UnitTriangle.up ⟨b 0, b 1, b 2, hm1⟩) fun y ⟨hyS, hyU⟩ =>
        UnitTriangle.mem_cell_iff.mpr ⟨hyS, fun k => by
          fin_cases k <;> simpa [sub_nonneg] using (mem_iInter.mp hyU _).1.le⟩⟩
    · exact ⟨U, hUo, hUc, hxU, hcell (UnitTriangle.down ⟨b 0, b 1, b 2, hm0⟩) fun y ⟨hyS, hyU⟩ =>
        UnitTriangle.mem_cell_iff.mpr ⟨hyS, fun k => by
          fin_cases k <;> simpa [sub_nonneg] using (mem_iInter.mp hyU _).2.le⟩⟩

private theorem concaveOn_lineMap_of_notMem_barycentric {m : ℕ} {f : Vertex (m + 2) → ℝ}
    (hadj : ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i))
    {p q : Fin 3 → ℝ} (hp : p ∈ barycentricSimplex (m + 2)) (hq : q ∈ barycentricSimplex (m + 2))
    (hp_pos : ∀ k, 0 < p k) (hq_pos : ∀ k, 0 < q k)
    (hnot : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap p q t ∉ Set.range (Vertex.barycentric (n := m + 2))) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (interpolate f ∘ AffineMap.lineMap p q) := by
  let γ : ℝ →ᵃ[ℝ] (Fin 3 → ℝ) := AffineMap.lineMap p q
  have hγ_cont : Continuous γ := by
    rw [show (γ : ℝ → _) = fun t => (1 - t) • p + t • q by
      ext; simp [γ, AffineMap.lineMap_apply_module]]
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hγ_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ barycentricSimplex (m + 2) := by
    simpa [γ, AffineMap.lineMap_apply_module] using
      convex_barycentricSimplex (m + 2) hp hq (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have hγ_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 3) : 0 < γ t k := by
    simp only [γ, AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · simp [hp_pos k]
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) (hp_pos k).le)
        (mul_pos ht0 (hq_pos k))
  have hlocal (t : Icc (0 : ℝ) 1) : ∃ V : Set ℝ, IsOpen V ∧ t.1 ∈ V ∧
      ConcaveOn ℝ (Icc (0 : ℝ) 1 ∩ V) (interpolate f ∘ γ) := by
    obtain ⟨U, hUo, hUc, hγU, hconc⟩ :=
      exists_open_convex_concaveOn_of_notMem_barycentric hadj (hγ_mem t.2) (hγ_pos t.2)
        (hnot t.1 t.2)
    exact ⟨γ ⁻¹' U, hUo.preimage hγ_cont, hγU, (hconc.comp_affineMap γ).subset
      (fun _ hs => ⟨hγ_mem hs.1, hs.2⟩) ((convex_Icc 0 1).inter (hUc.affine_preimage γ))⟩
  choose V hVo htV hVconc using hlocal
  obtain ⟨δ, hδ_pos, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hVo
    fun s hs => mem_iUnion.mpr ⟨⟨s, hs⟩, htV ⟨s, hs⟩⟩
  let N : ℕ := ⌊2 / δ⌋₊ + 1
  have hN_pos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hstep_lt : 2 / ((N : ℝ) + 2) < δ := (div_lt_iff₀ hN_pos).mpr <| by
    have : 2 / δ < (N : ℝ) + 2 := by dsimp [N]; push_cast; linarith [Nat.lt_floor_add_one (2 / δ)]
    linarith [(div_lt_iff₀ hδ_pos).mp this]
  let t : Fin (N + 3) → ℝ := fun j => (j.val : ℝ) / ((N : ℝ) + 2)
  have ht_mono : StrictMono t := fun _ _ hij => div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) hN_pos
  have ht0 : t 0 = 0 := by simp [t]
  have ht_last : t (Fin.last (N + 2)) = 1 := by simpa [t, Nat.cast_add] using div_self hN_pos.ne'
  have hsub_conc {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
      (hlen : b - a ≤ 2 / ((N : ℝ) + 2)) : ConcaveOn ℝ (Icc a b) (interpolate f ∘ γ) := by
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
  · simpa [t] using div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hN_pos.le
  · simp only [t, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]; ring_nf; rfl

private theorem exists_perturbation_notMem_barycentric {m : ℕ} {p' q' : Fin 3 → ℝ} (hpq : p' ≠ q')
    {δ : ℝ} (hδ_pos : 0 < δ) :
    ∃ (w : Fin 3 → ℝ) (η : ℝ), 0 ≤ η ∧ η ≤ δ ∧ ∑ k, w k = 0 ∧ (∀ k, |w k| ≤ 1) ∧
      ∀ t : ℝ, AffineMap.lineMap (p' + η • w) (q' + η • w) t ∉
        Set.range (Vertex.barycentric (n := m + 2)) := by
  let v : Fin 3 → ℝ := q' - p'
  obtain ⟨i, hvi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra! h; exact hpq (funext fun k => (sub_eq_zero.mp (h k)).symm)
  let w : Fin 3 → ℝ := fun k => if k = i + 1 then -1 else if k = i + 2 then 1 else 0
  have hw_sum : ∑ k, w k = 0 := by fin_cases i <;> simp [w, Fin.sum_univ_three]
  have hw_abs : ∀ k, |w k| ≤ 1 := fun k => by fin_cases i <;> fin_cases k <;> simp [w]
  have hwi : w i = 0 := by fin_cases i <;> simp [w]
  have hwi1 : w (i + 1) = -1 := by simp [w]
  let L : (Fin 3 → ℝ) → ℝ := fun y => v (i + 1) * y i - v i * y (i + 1)
  let S : Finset ℝ := Finset.univ.image fun r : Vertex (m + 2) => L r.barycentric
  let step : Fin (S.card + 1) → ℝ := fun j => ((j.val + 1 : ℕ) : ℝ) / ((S.card + 2 : ℕ) : ℝ) * δ
  let φ : Fin (S.card + 1) → ℝ := fun j => L p' + step j * v i
  have hden_pos : (0 : ℝ) < ((S.card + 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hφ_inj : Function.Injective φ := fun a b hab => Fin.ext <| Nat.succ.inj <|
    Nat.cast_injective <| (div_left_inj₀ hden_pos.ne').mp <|
      mul_right_cancel₀ hδ_pos.ne' (mul_right_cancel₀ hvi (add_left_cancel hab))
  obtain ⟨j, hj⟩ : ∃ j, φ j ∉ S := by
    by_contra! hall
    have hsub : Finset.univ.image φ ⊆ S := fun z hz => by
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz; exact hall j
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hφ_inj, Finset.card_fin] at hcard; omega
  refine ⟨w, step j, mul_nonneg (div_nonneg (Nat.cast_nonneg _) hden_pos.le) hδ_pos.le,
    mul_le_of_le_one_left hδ_pos.le ((div_le_one hden_pos).mpr (Nat.cast_le.mpr (by omega))),
    hw_sum, hw_abs, fun t ⟨r, hr⟩ => hj ?_⟩
  have hLr : L r.barycentric = φ j := by
    have hline : AffineMap.lineMap (p' + step j • w) (q' + step j • w) t =
        p' + step j • w + t • v := by ext k; simp [AffineMap.lineMap_apply_module, v]; ring
    rw [hr, hline]
    simp only [L, φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwi, hwi1]; ring
  exact hLr ▸ Finset.mem_image_of_mem _ (Finset.mem_univ r)

private theorem concaveOn_barycentricSimplex_of_adjacent {m : ℕ} {f : Vertex (m + 2) → ℝ}
    (hadj : ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i)) :
    ConcaveOn ℝ (barycentricSimplex (m + 2)) (interpolate f) := by
  refine ⟨convex_barycentricSimplex (m + 2), fun p hp q hq a b ha hb hab => ?_⟩
  rcases eq_or_ne p q with rfl | hpq
  · rw [← add_smul, ← add_smul, hab, one_smul, one_smul]
  let c : Fin 3 → ℝ := fun _ => ((m + 2 : ℕ) : ℝ) / 3
  have hc_mem : c ∈ barycentricSimplex (m + 2) :=
    mem_barycentricSimplex_iff.mpr ⟨fun _ => by dsimp [c]; positivity, by simp [c]; ring⟩
  let ε : ℕ → ℝ := fun K => (1 / 3 : ℝ) * (1 / ((K : ℝ) + 1))
  have hε_pos (K : ℕ) : 0 < ε K := by dsimp [ε]; positivity
  have hε_le (K : ℕ) : ε K ≤ 1 / 3 := by
    dsimp [ε]
    linarith [div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) K] : (1 : ℝ) ≤ K + 1)
      (by positivity)]
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, one_div] using
      (tendsto_const_nhds (x := (3 : ℝ)⁻¹)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpert (K : ℕ) := exists_perturbation_notMem_barycentric (m := m)
    (p' := (1 - ε K) • p + ε K • c) (q' := (1 - ε K) • q + ε K • c)
    (fun heq => hpq (smul_right_injective _ (by linarith [hε_le K] : 1 - ε K ≠ 0)
      (add_right_cancel heq)))
    (by linarith [hε_pos K] : 0 < ε K / 3)
  choose w η hη_nonneg hη_le hw_sum hw_abs havoid using hpert
  let sh (z : Fin 3 → ℝ) (K : ℕ) : Fin 3 → ℝ := ((1 - ε K) • z + ε K • c) + η K • w K
  have hpos_sh {z : Fin 3 → ℝ} (hz : z ∈ barycentricSimplex (m + 2)) (K : ℕ) (k : Fin 3) :
      0 < sh z K k := by
    have hck : (2 : ℝ) / 3 ≤ c k := by dsimp [c]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
    simp only [sh, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : 0 ≤ (1 - ε K) * z k :=
      mul_nonneg (by linarith [hε_le K]) ((mem_barycentricSimplex_iff.mp hz).1 k)
    have h2 : 2 * ε K / 3 ≤ ε K * c k := by nlinarith [hε_pos K, hck]
    have h3 : -(ε K / 3) ≤ η K * w K k := by
      nlinarith [hη_nonneg K, hη_le K, (abs_le.mp (hw_abs K k)).1]
    linarith [hε_pos K]
  have hmem_sh {z : Fin 3 → ℝ} (hz : z ∈ barycentricSimplex (m + 2)) (K : ℕ) :
      sh z K ∈ barycentricSimplex (m + 2) := by
    refine mem_barycentricSimplex_iff.mpr ⟨fun k => (hpos_sh hz K k).le, ?_⟩
    simp only [sh, Pi.add_apply, Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum, (mem_barycentricSimplex_iff.mp hz).2,
      (mem_barycentricSimplex_iff.mp hc_mem).2, hw_sum K]; ring
  have htend_sh (z : Fin 3 → ℝ) : Tendsto (sh z) atTop (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun k => tendsto_sub_nhds_zero_iff.mp <|
      squeeze_zero_norm (a := fun K => ε K * (|c k - z k| + 1)) (fun K => ?_)
        (by simpa using hε_tendsto.mul tendsto_const_nhds)
    rw [Real.norm_eq_abs, show sh z K k - z k = ε K * (c k - z k) + η K * w K k by
      simp only [sh, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring]
    have hηw : η K * |w K k| ≤ ε K :=
      (mul_le_of_le_one_right (hη_nonneg K) (hw_abs K k)).trans (by linarith [hη_le K, hε_pos K])
    calc |ε K * (c k - z k) + η K * w K k|
        ≤ |ε K * (c k - z k)| + |η K * w K k| := abs_add_le _ _
      _ = ε K * |c k - z k| + η K * |w K k| := by
          rw [abs_mul (ε K), abs_mul (η K), abs_of_pos (hε_pos K), abs_of_nonneg (hη_nonneg K)]
      _ ≤ ε K * (|c k - z k| + 1) := by linarith
  have hineqK (K : ℕ) :
      a • interpolate f (sh p K) + b • interpolate f (sh q K) ≤
        interpolate f (a • sh p K + b • sh q K) := by
    have h01 := (concaveOn_lineMap_of_notMem_barycentric hadj (hmem_sh hp K) (hmem_sh hq K)
      (hpos_sh hp K) (hpos_sh hq K) fun t _ => havoid K t).2
      (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) ha hb hab
    simpa [show AffineMap.lineMap (sh p K) (sh q K) b = a • sh p K + b • sh q K by
      ext k; simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination -sh p K k * hab] using h01
  have htend_val {u : ℕ → Fin 3 → ℝ} {z : Fin 3 → ℝ} (hz : z ∈ barycentricSimplex (m + 2))
      (hu_mem : ∀ K, u K ∈ barycentricSimplex (m + 2)) (hu : Tendsto u atTop (𝓝 z)) :
      Tendsto (fun K => interpolate f (u K)) atTop (𝓝 (interpolate f z)) :=
    (continuousOn_interpolate f z hz).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu (Eventually.of_forall hu_mem))
  exact le_of_tendsto_of_tendsto
    (((htend_val hp (hmem_sh hp) (htend_sh p)).const_smul a).add
      ((htend_val hq (hmem_sh hq) (htend_sh q)).const_smul b))
    (htend_val (convex_barycentricSimplex (m + 2) hp hq ha hb hab)
      (fun K => convex_barycentricSimplex (m + 2) (hmem_sh hp K) (hmem_sh hq K) ha hb hab)
      (((htend_sh p).const_smul a).add ((htend_sh q).const_smul b)))
    (Eventually.of_forall hineqK)

private theorem isRhombusConcave_of_concaveOn_barycentricSimplex {n : ℕ} {f : Vertex n → ℝ}
    (hconc : ConcaveOn ℝ (barycentricSimplex n) (interpolate f)) : IsRhombusConcave f :=
  (isRhombusConcave_iff_rhombusSlack_nonneg f).mpr fun _ _ _ _ hr =>
    rhombusSlack_nonneg_of_concaveOn hconc hr
      (barycentric_mem_barycentricSimplex _) (barycentric_mem_barycentricSimplex _)

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
    exact (concaveOn_triangleAffine f (UnitTriangle.up (Vertex.cornerA 0))
      (convex_barycentricSimplex 1)).congr fun _ hx =>
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
  refine ⟨fun h => ((h.comp_linearMap planeLinear.toLinearMap).subset
      (fun x hx => mem_planarSimplex_iff.mpr
        (by simpa [planeInvAffine_planeLinear (mem_barycentricSimplex_iff.mp hx).2] using hx))
      (convex_barycentricSimplex n)).congr
      fun _ hx => planarInterpolate_planeLinear f (mem_barycentricSimplex_iff.mp hx).2,
    fun h => ((h.comp_affineMap (planeInvAffine n).toAffineMap).subset
      (fun _ hu => mem_planarSimplex_iff.mp hu) (convex_planarSimplex n)).congr
      fun u _ => (planarInterpolate_def f u).symm⟩

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
    (hx : x ∈ barycentricSimplex n) : interpolate f x ≤ triangleAffine f T x := by
  let c : Fin 3 → ℝ := ∑ j : Fin 3, (1 / 3 : ℝ) • (T.vertex j).barycentric
  have hc_weight (i : Fin 3) : T.weight i c = 1 / 3 := by
    rw [show T.weight i c = ∑ j : Fin 3, (1 / 3 : ℝ) * T.weight i (T.vertex j).barycentric by
      cases T with
      | up => simp only [c, UnitTriangle.weight_up_apply, Fin.sum_univ_three, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]; ring
      | down => simp only [c, UnitTriangle.weight_down_apply, Fin.sum_univ_three, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]; ring]
    fin_cases i <;> simp
  have hc_mem : c ∈ barycentricSimplex n :=
    (convex_barycentricSimplex n).sum_mem (fun _ _ => by norm_num) (by norm_num)
      fun j _ => barycentric_mem_barycentricSimplex (T.vertex j)
  have hc_cell : c ∈ T.cell := T.mem_cell_iff.mpr ⟨hc_mem, fun i => by rw [hc_weight i]; norm_num⟩
  let M : ℝ := |T.weight 0 x| + |T.weight 1 x| + |T.weight 2 x| + 1
  have hM_pos : 0 < M := by dsimp [M]; positivity
  let t : ℝ := 1 / (3 * M + 1)
  have ht_pos : 0 < t := by dsimp [t]; positivity
  have ht_le : t ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
  let y : Fin 3 → ℝ := (1 - t) • c + t • x
  have hy_cell : y ∈ T.cell := T.mem_cell_iff.mpr
    ⟨convex_barycentricSimplex n hc_mem hx (sub_nonneg.mpr ht_le) ht_pos.le (sub_add_cancel 1 t),
      fun i => by
        rw [show T.weight i y = (1 - t) * (1 / 3) + t * T.weight i x by
          rw [← hc_weight i]; cases T <;> simp [y] <;> ring]
        have habs : -M ≤ T.weight i x := neg_le_of_abs_le (by
          fin_cases i <;> dsimp [M] <;>
            linarith [abs_nonneg (T.weight 0 x), abs_nonneg (T.weight 1 x),
              abs_nonneg (T.weight 2 x)])
        have htM : 0 ≤ (1 - t) * (1 / 3) - t * M := by dsimp [t]; field_simp; linarith
        linarith [mul_le_mul_of_nonneg_left habs ht_pos.le]⟩
  have hconc := ((concaveOn_barycentricSimplex_interpolate_iff f).mpr hf).2 hc_mem hx
    (sub_nonneg.mpr ht_le) ht_pos.le (sub_add_cancel 1 t)
  have hy_val : interpolate f y = (1 - t) * triangleAffine f T c + t * triangleAffine f T x := by
    rw [interpolate_eq_triangleAffine f hy_cell,
      show y = ∑ i : Fin 3, (![1 - t, t, 0] : Fin 3 → ℝ) i • (![c, x, 0] : Fin 3 → _) i by
        ext; simp [y, Fin.sum_univ_three],
      triangleAffine_combo f T (by simp [Fin.sum_univ_three])]
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
  exact le_antisymm (Finset.le_inf' _ _ fun T _ => hf.interpolate_le_triangleAffine T hx)
    ((Finset.inf'_le _ (Finset.mem_univ T₀)).trans (interpolate_eq_triangleAffine f hT₀).ge)

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
  rw [concaveOn_barycentricSimplex_interpolate_iff]; intro hf
  have h := (isRhombusConcave_def _).mp hf isRhombus_at_cornerA
  simp [Vertex.ext_iff] at h; linarith

end SmallRank

end TauCeti.Hive
