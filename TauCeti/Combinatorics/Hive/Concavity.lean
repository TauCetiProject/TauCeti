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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The rhombus concavity criterion and tropical affine-envelope formula

For any `f : Vertex n → ℝ` on the size-`n` triangular lattice, the simplicial piecewise-affine
extension `interpolate f` on `barycentricSimplex n` (and `planarInterpolate f` on `planarSimplex n`)
is concave iff `f` satisfies all unit-rhombus concavity inequalities (`IsRhombusConcave`).

We prove this equivalence (`concaveOn_barycentricSimplex_interpolate_iff`) via the
adjacent-triangle bending test and 1D line-segment subdivision:
1. Across the shared edge of `down s` opposite `(down s).vertex i` and `adjacentUp s i`, the
   difference of their affine pieces equals `((sᵢ + 1) - xᵢ)` times the unit-rhombus slack
   (`triangleAffine_adjacentUp_sub_down`), so `interpolate f` is concave on `adjacentCell s i` iff
   the slack is nonnegative (`concaveOn_adjacentCell_iff`).
2. Every strictly interior non-vertex point of `barycentricSimplex (m + 2)` admits an open convex
   neighbourhood whose slice lies in a single unit-triangle cell or an `adjacentCell s i`.
3. Along any strictly interior vertex-avoiding segment, local concavity glues into segment
   concavity (`TauCeti.concaveOn_of_local`); vertex-avoiding approximation and continuity of
   `interpolate f` extend concavity to all of `barycentricSimplex (m + 2)`.

Whenever `f` is rhombus-concave and `n = m + 1 ≥ 1`, `interpolate f` is the tropical global minimum
of its `n²` affine pieces (`IsRhombusConcave.interpolate_eq_inf'_triangleAffine`).

## Main results

* `TauCeti.Hive.triangleAffine_adjacentUp_sub_down`, `TauCeti.Hive.concaveOn_adjacentCell_iff`.
* `TauCeti.Hive.concaveOn_barycentricSimplex_interpolate_iff`,
  `TauCeti.Hive.concaveOn_planarSimplex_planarInterpolate_iff`.
* `TauCeti.Hive.IsRhombusConcave.interpolate_eq_inf'_triangleAffine`.

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
    {s : Set (Fin 3 → ℝ)} (hs : Convex ℝ s) : ConcaveOn ℝ s (triangleAffine f T) :=
  ((concaveOn_id convex_univ).comp_affineMap (triangleAffine f T).toAffineMap).subset
    (subset_univ s) hs

private theorem rhombusSlack_nonneg_of_concaveOn {n : ℕ} {f : Vertex n → ℝ} {S : Set (Fin 3 → ℝ)}
    (hconc : ConcaveOn ℝ S (interpolate f)) {a b c d : Vertex n} (hr : IsRhombus a b c d)
    (hb : b.barycentric ∈ S) (hd : d.barycentric ∈ S) : 0 ≤ rhombusSlack f a b c d := by
  have hmid : (1 / 2 : ℝ) • b.barycentric + (1 / 2 : ℝ) • d.barycentric =
      AffineMap.lineMap a.barycentric c.barycentric (1 / 2 : ℝ) := by
    ext k; simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hk := congrFun hr.barycentric_add k; simp only [Pi.add_apply] at hk; linarith
  have h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h := hconc.2 hb hd h12 h12 (by norm_num)
  rw [hmid, interpolate_lineMap_of_isUnitEdge f hr.isUnitEdge_short ⟨by norm_num, by norm_num⟩,
    interpolate_barycentric, interpolate_barycentric] at h
  simp only [smul_eq_mul, rhombusSlack_def] at h ⊢; linarith

/-- Exact bending formula across the shared edge of `down s` and `adjacentUp s i` opposite
`(down s).vertex i`: on the sum-`(m + 2)` hyperplane, the difference of their affine pieces equals
`((sᵢ + 1) - xᵢ)` times the unit-rhombus slack. -/
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
      Matrix.head_cons]
    have hmid := congrFun (isRhombus_adjacent s i).barycentric_add k
    simp only [Pi.add_apply] at hmid; linarith
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

/-- When the unit-rhombus slack across the edge of `down s` opposite `(down s).vertex i` is
nonnegative, `interpolate f` on `adjacentCell s i` equals the pointwise minimum of the two adjacent
affine pieces. -/
theorem eqOn_inf_triangleAffine_adjacentCell {m : ℕ} {f : Vertex (m + 2) → ℝ} {s : Vertex m}
    {i : Fin 3} (hslack : 0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2))
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

private theorem exists_open_convex_concaveOn_of_notMem_barycentric {m : ℕ} {f : Vertex (m + 2) → ℝ}
    (hadj : ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i))
    {x : Fin 3 → ℝ} (hx : x ∈ barycentricSimplex (m + 2)) (hpos : ∀ k, 0 < x k)
    (hnot : x ∉ Set.range (Vertex.barycentric (n := m + 2))) :
    ∃ U : Set (Fin 3 → ℝ), IsOpen U ∧ Convex ℝ U ∧ x ∈ U ∧
      ConcaveOn ℝ (barycentricSimplex (m + 2) ∩ U) (interpolate f) := by
  by_cases hex : ∃ i : Fin 3, x i = (⌊x i⌋₊ : ℝ)
  · obtain ⟨i, hi⟩ := hex
    obtain ⟨s, U, hUo, hUc, hxU, hsub⟩ :=
      exists_open_convex_subset_adjacentCell_of_eq_floor hx hpos hnot hi
    exact ⟨U, hUo, hUc, hxU, ((concaveOn_adjacentCell_iff f s i).mpr (hadj s i)).subset hsub
      ((convex_barycentricSimplex _).inter hUc)⟩
  · push Not at hex
    obtain ⟨T, U, hUo, hUc, hxU, hsub⟩ := exists_open_convex_subset_cell_of_ne_floor hx hex
    exact ⟨U, hUo, hUc, hxU,
      (concaveOn_triangleAffine f T ((convex_barycentricSimplex _).inter hUc)).congr
        fun _ hy => (interpolate_eq_triangleAffine f (hsub hy)).symm⟩

private theorem concaveOn_segment_of_notMem_barycentric {m : ℕ} {f : Vertex (m + 2) → ℝ}
    (hadj : ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i))
    {p q : Fin 3 → ℝ} (hp : p ∈ barycentricSimplex (m + 2)) (hq : q ∈ barycentricSimplex (m + 2))
    (hp_pos : ∀ k, 0 < p k) (hq_pos : ∀ k, 0 < q k)
    (hnot : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap p q t ∉ Set.range (Vertex.barycentric (n := m + 2))) :
    ConcaveOn ℝ (AffineMap.lineMap p q '' Icc (0 : ℝ) 1) (interpolate f) := by
  let γ : ℝ →ᵃ[ℝ] (Fin 3 → ℝ) := AffineMap.lineMap p q
  have hγ_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ barycentricSimplex (m + 2) :=
    (convex_barycentricSimplex (m + 2)).lineMap_mem hp hq ht
  have hγ_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 3) : 0 < γ t k := by
    simp only [γ, AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · simp [hp_pos k]
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) (hp_pos k).le)
        (mul_pos ht0 (hq_pos k))
  refine TauCeti.concaveOn_of_local ((convex_Icc (0 : ℝ) 1).affine_image γ) ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨U, hUo, _, hγU, hconc⟩ :=
    exists_open_convex_concaveOn_of_notMem_barycentric hadj (hγ_mem ht) (hγ_pos ht) (hnot t ht)
  refine ⟨barycentricSimplex (m + 2) ∩ U, mem_of_superset
    (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hγU))) ?_, hconc⟩
  rintro _ ⟨⟨s, hs, rfl⟩, hU⟩; exact ⟨hγ_mem hs, hU⟩

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
  have hw_abs (k : Fin 3) : |w k| ≤ 1 := by fin_cases i <;> fin_cases k <;> simp [w]
  have hwi : w i = 0 := by fin_cases i <;> simp [w]
  have hwi1 : w (i + 1) = -1 := by simp [w]
  let L (y : Fin 3 → ℝ) : ℝ := v (i + 1) * y i - v i * y (i + 1)
  let S : Finset ℝ := Finset.univ.image fun r : Vertex (m + 2) => L r.barycentric
  let st (j : Fin (S.card + 1)) : ℝ := ((j.val + 1 : ℕ) : ℝ) / ((S.card + 2 : ℕ) : ℝ) * δ
  let φ (j : Fin (S.card + 1)) : ℝ := L p' + st j * v i
  have hden_pos : (0 : ℝ) < ((S.card + 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hφ_inj : Function.Injective φ := fun a b hab => Fin.ext <| Nat.succ.inj <|
    Nat.cast_injective <| (div_left_inj₀ hden_pos.ne').mp <|
      mul_right_cancel₀ hδ_pos.ne' (mul_right_cancel₀ hvi (add_left_cancel hab))
  obtain ⟨j, hj⟩ : ∃ j, φ j ∉ S := by
    by_contra! hall
    have hcard := Finset.card_le_card (s := Finset.univ.image φ) (t := S) fun z hz => by
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz; exact hall j
    rw [Finset.card_image_of_injective _ hφ_inj, Finset.card_fin] at hcard; omega
  refine ⟨w, st j, mul_nonneg (div_nonneg (Nat.cast_nonneg _) hden_pos.le) hδ_pos.le,
    mul_le_of_le_one_left hδ_pos.le ((div_le_one hden_pos).mpr (Nat.cast_le.mpr (by omega))),
    hw_sum, hw_abs, fun t ⟨r, hr⟩ => hj ?_⟩
  have hline : AffineMap.lineMap (p' + st j • w) (q' + st j • w) t = p' + st j • w + t • v := by
    ext k; simp [AffineMap.lineMap_apply_module, v]; ring
  have hLr : L r.barycentric = φ j := by
    rw [hr, hline]; simp only [L, φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwi, hwi1]; ring
  exact hLr ▸ Finset.mem_image_of_mem _ (Finset.mem_univ r)

private theorem exists_seq_tendsto_barycentricSimplex_notMem_barycentric {m : ℕ}
    {p q : Fin 3 → ℝ} (hp : p ∈ barycentricSimplex (m + 2))
    (hq : q ∈ barycentricSimplex (m + 2)) (hpq : p ≠ q) :
    ∃ u v : ℕ → Fin 3 → ℝ,
      (∀ K, u K ∈ barycentricSimplex (m + 2)) ∧ (∀ K, v K ∈ barycentricSimplex (m + 2)) ∧
      (∀ K k, 0 < u K k) ∧ (∀ K k, 0 < v K k) ∧
      (∀ (K : ℕ) (t : ℝ),
        AffineMap.lineMap (u K) (v K) t ∉ Set.range (Vertex.barycentric (n := m + 2))) ∧
      Tendsto u atTop (𝓝 p) ∧ Tendsto v atTop (𝓝 q) := by
  let c : Fin 3 → ℝ := fun _ => ((m + 2 : ℕ) : ℝ) / 3
  have hc_sum : ∑ k, c k = ((m + 2 : ℕ) : ℝ) := by simp [c]; ring
  let ε (K : ℕ) : ℝ := (1 / 3 : ℝ) * (1 / ((K : ℝ) + 1))
  have hε_pos (K : ℕ) : 0 < ε K := by dsimp [ε]; positivity
  have hε_le (K : ℕ) : ε K ≤ 1 / 3 := by
    dsimp [ε]; linarith [div_le_one_of_le₀
      (by linarith [Nat.cast_nonneg (α := ℝ) K] : (1 : ℝ) ≤ K + 1) (by positivity)]
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, one_div] using
      (tendsto_const_nhds (x := (3 : ℝ)⁻¹)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose w η hη_nonneg hη_le hw_sum hw_abs havoid using fun K : ℕ =>
    exists_perturbation_notMem_barycentric (m := m)
      (p' := (1 - ε K) • p + ε K • c) (q' := (1 - ε K) • q + ε K • c)
      (fun heq => hpq (smul_right_injective _ (by linarith [hε_le K] : 1 - ε K ≠ 0)
        (add_right_cancel heq))) (by linarith [hε_pos K] : 0 < ε K / 3)
  let sh (z : Fin 3 → ℝ) (K : ℕ) : Fin 3 → ℝ := ((1 - ε K) • z + ε K • c) + η K • w K
  have hpos_sh {z : Fin 3 → ℝ} (hz : z ∈ barycentricSimplex (m + 2)) (K : ℕ) (k : Fin 3) :
      0 < sh z K k := by
    have hck : (2 : ℝ) / 3 ≤ c k := by dsimp [c]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hz0 := mul_nonneg (by linarith [hε_le K] : 0 ≤ 1 - ε K)
      ((mem_barycentricSimplex_iff.mp hz).1 k)
    simp only [sh, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hε_pos K, hck, hη_nonneg K, hη_le K, (abs_le.mp (hw_abs K k)).1]
  have hmem_sh {z : Fin 3 → ℝ} (hz : z ∈ barycentricSimplex (m + 2)) (K : ℕ) :
      sh z K ∈ barycentricSimplex (m + 2) :=
    mem_barycentricSimplex_iff.mpr ⟨fun k => (hpos_sh hz K k).le, by
      simp only [sh, Pi.add_apply, Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul,
        ← Finset.mul_sum, (mem_barycentricSimplex_iff.mp hz).2, hc_sum, hw_sum K]; ring⟩
  have htend_sh (z : Fin 3 → ℝ) : Tendsto (sh z) atTop (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun k => tendsto_sub_nhds_zero_iff.mp <|
      squeeze_zero_norm (a := fun K => ε K * (|c k - z k| + 1)) (fun K => ?_)
        (by simpa using hε_tendsto.mul tendsto_const_nhds)
    have hsub : sh z K k - z k = ε K * (c k - z k) + η K * w K k := by
      simp only [sh, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h1 : |ε K * (c k - z k)| = ε K * |c k - z k| := by rw [abs_mul, abs_of_pos (hε_pos K)]
    have h2 : |η K * w K k| ≤ ε K := by
      rw [abs_mul, abs_of_nonneg (hη_nonneg K)]
      exact (mul_le_of_le_one_right (hη_nonneg K) (hw_abs K k)).trans
        (by linarith [hη_le K, hε_pos K])
    rw [Real.norm_eq_abs, hsub]; linarith [abs_add_le (ε K * (c k - z k)) (η K * w K k)]
  exact ⟨sh p, sh q, hmem_sh hp, hmem_sh hq, hpos_sh hp, hpos_sh hq, havoid,
    htend_sh p, htend_sh q⟩

private theorem concaveOn_barycentricSimplex_of_adjacent {m : ℕ} {f : Vertex (m + 2) → ℝ}
    (hadj : ∀ (s : Vertex m) (i : Fin 3),
      0 ≤ rhombusSlack f ((UnitTriangle.down s).vertex (i + 2)) ((adjacentUp s i).vertex i)
        ((UnitTriangle.down s).vertex (i + 1)) ((UnitTriangle.down s).vertex i)) :
    ConcaveOn ℝ (barycentricSimplex (m + 2)) (interpolate f) := by
  refine ⟨convex_barycentricSimplex (m + 2), fun p hp q hq a b ha hb hab => ?_⟩
  rcases eq_or_ne p q with rfl | hpq
  · rw [← add_smul, ← add_smul, hab, one_smul, one_smul]
  obtain ⟨u, v, hu_mem, hv_mem, hu_pos, hv_pos, havoid, hu_tend, hv_tend⟩ :=
    exists_seq_tendsto_barycentricSimplex_notMem_barycentric hp hq hpq
  have hineq (K : ℕ) :
      a • interpolate f (u K) + b • interpolate f (v K) ≤ interpolate f (a • u K + b • v K) :=
    (concaveOn_segment_of_notMem_barycentric hadj (hu_mem K) (hv_mem K) (hu_pos K) (hv_pos K)
      fun t _ => havoid K t).2 ⟨0, left_mem_Icc.mpr zero_le_one, by simp⟩
      ⟨1, right_mem_Icc.mpr zero_le_one, by simp⟩ ha hb hab
  have htend_val {w : ℕ → Fin 3 → ℝ} {z : Fin 3 → ℝ} (hz : z ∈ barycentricSimplex (m + 2))
      (hw_mem : ∀ K, w K ∈ barycentricSimplex (m + 2)) (hw : Tendsto w atTop (𝓝 z)) :
      Tendsto (fun K => interpolate f (w K)) atTop (𝓝 (interpolate f z)) :=
    (continuousOn_interpolate f z hz).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w hw (Eventually.of_forall hw_mem))
  exact le_of_tendsto_of_tendsto
    (((htend_val hp hu_mem hu_tend).const_smul a).add ((htend_val hq hv_mem hv_tend).const_smul b))
    (htend_val (convex_barycentricSimplex (m + 2) hp hq ha hb hab)
      (fun K => convex_barycentricSimplex (m + 2) (hu_mem K) (hv_mem K) ha hb hab)
      ((hu_tend.const_smul a).add (hv_tend.const_smul b)))
    (Eventually.of_forall hineq)

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
  rcases n with _ | _ | m
  · exact (concaveOn_const (f (Vertex.cornerA 0)) (convex_barycentricSimplex 0)).congr
      fun x _ => (interpolate_zero_rank f x).symm
  · exact (concaveOn_triangleAffine f (UnitTriangle.up (Vertex.cornerA 0))
      (convex_barycentricSimplex 1)).congr fun _ hx =>
      (interpolate_eq_triangleAffine f (by rwa [UnitTriangle.cell_up_cornerA_zero])).symm
  · exact concaveOn_barycentricSimplex_of_adjacent ((isRhombusConcave_iff_adjacent _).1 hf)

/-- **Rhombus concavity criterion (Euclidean planar chart)**: `planarInterpolate f` is concave on
`planarSimplex n` if and only if `f` is rhombus-concave. -/
theorem concaveOn_planarSimplex_planarInterpolate_iff {n : ℕ} (f : Vertex n → ℝ) :
    ConcaveOn ℝ (planarSimplex n) (planarInterpolate f) ↔ IsRhombusConcave f := by
  rw [← concaveOn_barycentricSimplex_interpolate_iff]
  refine ⟨fun h => ((h.comp_linearMap planeLinear.toLinearMap).subset
      (fun x hx => mem_planarSimplex_iff.mpr
        (by simpa [planeInvAffine_planeLinear (mem_barycentricSimplex_iff.mp hx).2] using hx))
      (convex_barycentricSimplex n)).congr fun _ hx =>
        planarInterpolate_planeLinear f (mem_barycentricSimplex_iff.mp hx).2,
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
  have hw3 : ∑ _ : Fin 3, (1 / 3 : ℝ) = 1 := by norm_num
  let c : Fin 3 → ℝ := ∑ j : Fin 3, (1 / 3 : ℝ) • (T.vertex j).barycentric
  have hc_weight (i : Fin 3) : T.weight i c = 1 / 3 := by
    dsimp only [c]
    rw [← Finset.univ.affineCombination_eq_linear_combination _ _ hw3,
      ← ContinuousAffineMap.coe_toAffineMap, Finset.univ.map_affineCombination _ _ hw3,
      Finset.univ.affineCombination_eq_linear_combination _ _ hw3]
    fin_cases i <;> simp
  have hc_mem : c ∈ barycentricSimplex n :=
    (convex_barycentricSimplex n).sum_mem (fun _ _ => by norm_num) hw3
      fun j _ => barycentric_mem_barycentricSimplex (T.vertex j)
  have hc_cell : c ∈ T.cell :=
    UnitTriangle.mem_cell_iff.mpr ⟨hc_mem, fun i => by rw [hc_weight i]; norm_num⟩
  let M : ℝ := |T.weight 0 x| + |T.weight 1 x| + |T.weight 2 x| + 1
  have hM_pos : 0 < M := by dsimp [M]; positivity
  let t : ℝ := 1 / (3 * M + 1)
  have ht_pos : 0 < t := by dsimp [t]; positivity
  have ht_le : t ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
  let y : Fin 3 → ℝ := AffineMap.lineMap c x t
  have hy_mem : y ∈ barycentricSimplex n :=
    (convex_barycentricSimplex n).lineMap_mem hc_mem hx ⟨ht_pos.le, ht_le⟩
  have hy_cell : y ∈ T.cell := UnitTriangle.mem_cell_iff.mpr ⟨hy_mem, fun i => by
    dsimp only [y]
    rw [(T.weight i).apply_lineMap, AffineMap.lineMap_apply_module, hc_weight i,
      smul_eq_mul, smul_eq_mul]
    have habs : -M ≤ T.weight i x := neg_le_of_abs_le <| by
      fin_cases i <;> dsimp [M] <;>
        linarith [abs_nonneg (T.weight 0 x), abs_nonneg (T.weight 1 x), abs_nonneg (T.weight 2 x)]
    have htM : 0 ≤ (1 - t) * (1 / 3) - t * M := by dsimp [t]; field_simp; linarith
    linarith [mul_le_mul_of_nonneg_left habs ht_pos.le]⟩
  have hconc := ((concaveOn_barycentricSimplex_interpolate_iff f).mpr hf).2 hc_mem hx
    (sub_nonneg.mpr ht_le) ht_pos.le (sub_add_cancel 1 t)
  have hy_val : interpolate f (AffineMap.lineMap c x t) =
      (1 - t) * triangleAffine f T c + t * triangleAffine f T x := by
    rw [interpolate_eq_triangleAffine f hy_cell, (triangleAffine f T).apply_lineMap,
      AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
  rw [← AffineMap.lineMap_apply_module c x t, interpolate_eq_triangleAffine f hc_cell, hy_val]
    at hconc
  simp only [smul_eq_mul] at hconc; exact le_of_mul_le_mul_left (by linarith) ht_pos

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

/-- Size-`2` check: `exampleTwo` has concave simplicial interpolation on `barycentricSimplex 2`. -/
theorem concaveOn_barycentricSimplex_interpolate_exampleTwo :
    ConcaveOn ℝ (barycentricSimplex 2) (interpolate (toReal exampleTwo)) :=
  (toReal exampleTwo).concaveOn_barycentricSimplex_interpolate
/-- Size-`2` check: `detTwo` has concave simplicial interpolation on `barycentricSimplex 2`. -/
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
