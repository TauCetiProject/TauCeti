/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Uniform Riemann-sum quadrature on compact subsets of the complex plane

Partitioning a compact subset `K₁ ⊆ ℂ` along the half-open square grid of mesh `δ > 0`,

`planarMeshCell δ (j, k) = [j δ, (j + 1) δ) ×ℂ [k δ, (k + 1) δ)`,

and discarding cells whose intersection with `K₁` has planar Lebesgue measure zero produces finitely
many sample nodes `ζ₁, …, ζ_N ∈ K₁` and strictly positive area weights `a₁, …, a_N > 0` summing to
`volume.real K₁` that depend **only** on `(K₁, δ)`. For every Banach-valued function `g : ℂ → E`
continuous on `K₁` whose `2 δ`-oscillation on `K₁` is bounded by `ω ≥ 0`, the Riemann sum
`∑ j, a j • g (ζ j)` approximates `∫ z in K₁, g z` within `ω * volume.real K₁`
(`IsCompact.exists_sum_smul_norm_setIntegral_sub_le`).

Because the nodes and weights are chosen before `g` is specified, a single quadrature rule
approximates an entire equicontinuous family simultaneously:
* For a single continuous integrand `G : ℂ × X → E` on `K₁ ×ˢ K₂` with `K₂` compact, uniform
  continuity supplies `δ > 0` making the Riemann sums converge uniformly in `ξ ∈ K₂`
  (`IsCompact.exists_sum_smul_norm_setIntegral_sub_lt`).
* For the Cauchy–Pompeiu kernel applied to bounded holomorphic functions `f` on a collar of a
  compact set `K`, Cauchy's derivative estimate controls the oscillation uniformly in `f`, yielding
  linear finite-rank Runge approximation operators.

## Main definitions and results

* `TauCeti.planarMeshCell`: the half-open planar mesh square `[j δ, (j + 1) δ) ×ℂ [k δ, (k + 1) δ)`.
* `IsCompact.exists_sum_smul_norm_setIntegral_sub_le`: nodes `ζ j ∈ K₁` and positive weights `a j`
  summing to `volume.real K₁`, depending only on `(K₁, δ)`, with universal error bound
  `ω * volume.real K₁` for every continuous `g : ℂ → E` of `2 δ`-oscillation at most `ω`.
* `IsCompact.exists_sum_smul_norm_setIntegral_sub_lt`: uniform Riemann-sum approximation of
  `ξ ↦ ∫ z in K₁, G (z, ξ)` on a compact parameter set `K₂`.

## References

* A. Rainer, *Advanced Complex Analysis*, Lemma 11.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.1.
-/

public section

open Complex Function MeasureTheory Metric Set
open scoped ENNReal

namespace TauCeti

/-- The half-open square `[p.1 * δ, (p.1 + 1) * δ) ×ℂ [p.2 * δ, (p.2 + 1) * δ)` of side `δ` in the
complex plane, indexed by `p : ℤ × ℤ`. -/
def planarMeshCell (δ : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  Ico (p.1 * δ) ((p.1 + 1 : ℤ) * δ) ×ℂ Ico (p.2 * δ) ((p.2 + 1 : ℤ) * δ)

/-- Unfolding membership in `TauCeti.planarMeshCell`. -/
theorem mem_planarMeshCell_iff {δ : ℝ} {p : ℤ × ℤ} {z : ℂ} :
    z ∈ planarMeshCell δ p ↔
      z.re ∈ Ico ((p.1 : ℝ) * δ) (((p.1 + 1 : ℤ) : ℝ) * δ) ∧
        z.im ∈ Ico ((p.2 : ℝ) * δ) (((p.2 + 1 : ℤ) : ℝ) * δ) :=
  (Iff.rfl)

/-- Every planar mesh cell is Borel measurable. -/
theorem measurableSet_planarMeshCell (δ : ℝ) (p : ℤ × ℤ) :
    MeasurableSet (planarMeshCell δ p) :=
  (measurableSet_Ico.preimage continuous_re.measurable).inter
    (measurableSet_Ico.preimage continuous_im.measurable)

/-- For `δ > 0`, a point `z ∈ planarMeshCell δ p` determines its integer grid index
`p = (⌊z.re / δ⌋, ⌊z.im / δ⌋)`. -/
theorem eq_floor_div_of_mem_planarMeshCell {δ : ℝ} (hδ : 0 < δ) {p : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ planarMeshCell δ p) : p = (⌊z.re / δ⌋, ⌊z.im / δ⌋) := by
  rcases hz with ⟨⟨hre₁, hre₂⟩, ⟨him₁, him₂⟩⟩
  ext <;> symm <;> rw [Int.floor_eq_iff]
  · exact ⟨(le_div_iff₀ hδ).2 hre₁, (div_lt_iff₀ hδ).2 (by push_cast at hre₂ ⊢; exact hre₂)⟩
  · exact ⟨(le_div_iff₀ hδ).2 him₁, (div_lt_iff₀ hδ).2 (by push_cast at him₂ ⊢; exact him₂)⟩

/-- Planar mesh cells of positive mesh `δ` are pairwise disjoint. -/
theorem pairwise_disjoint_planarMeshCell {δ : ℝ} (hδ : 0 < δ) :
    Pairwise (Disjoint on planarMeshCell δ) := fun _ _ hpq ↦
  disjoint_left.2 fun _ hzp hzq ↦
    hpq ((eq_floor_div_of_mem_planarMeshCell hδ hzp).trans
      (eq_floor_div_of_mem_planarMeshCell hδ hzq).symm)

/-- Every point `z : ℂ` belongs to the mesh cell `planarMeshCell δ (⌊z.re / δ⌋, ⌊z.im / δ⌋)`. -/
theorem mem_planarMeshCell_floor {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    z ∈ planarMeshCell δ (⌊z.re / δ⌋, ⌊z.im / δ⌋) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (le_div_iff₀ hδ).1 (Int.floor_le _)
  · push_cast
    exact (div_lt_iff₀ hδ).1 (Int.lt_floor_add_one _)
  · exact (le_div_iff₀ hδ).1 (Int.floor_le _)
  · push_cast
    exact (div_lt_iff₀ hδ).1 (Int.lt_floor_add_one _)

/-- Any two points in the same mesh cell of side `δ` lie at distance at most `2 * δ`. -/
theorem dist_le_two_mul_of_mem_planarMeshCell {δ : ℝ} {p : ℤ × ℤ} {z w : ℂ}
    (hz : z ∈ planarMeshCell δ p) (hw : w ∈ planarMeshCell δ p) : dist z w ≤ 2 * δ := by
  rcases hz with ⟨⟨hzre₁, hzre₂⟩, ⟨hzim₁, hzim₂⟩⟩
  rcases hw with ⟨⟨hwre₁, hwre₂⟩, ⟨hwim₁, hwim₂⟩⟩
  push_cast at hzre₂ hzim₂ hwre₂ hwim₂
  have hre : |(z - w).re| ≤ δ := abs_le.2 ⟨by simp; linarith, by simp; linarith⟩
  have him : |(z - w).im| ≤ δ := abs_le.2 ⟨by simp; linarith, by simp; linarith⟩
  rw [dist_eq_norm]
  linarith [norm_le_abs_re_add_abs_im (z - w)]

/-- A closed disc `closedBall 0 R` is covered by finitely many planar mesh cells of side `δ > 0`. -/
private theorem closedBall_subset_biUnion_planarMeshCell {R δ : ℝ} (hδ : 0 < δ) :
    closedBall (0 : ℂ) R ⊆
      ⋃ p ∈ Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋ ×ˢ Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋, planarMeshCell δ p := by
  intro z hz
  rw [mem_closedBall_zero_iff] at hz
  have hre : -R ≤ z.re ∧ z.re ≤ R := abs_le.1 ((abs_re_le_norm z).trans hz)
  have him : -R ≤ z.im ∧ z.im ≤ R := abs_le.1 ((abs_im_le_norm z).trans hz)
  refine mem_biUnion (Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, Finset.mem_Icc.2 ⟨?_, ?_⟩⟩)
    (mem_planarMeshCell_floor hδ z)
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right hδ).2 hre.1)
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right hδ).2 hre.2)
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right hδ).2 him.1)
  · exact Int.floor_mono ((div_le_div_iff_of_pos_right hδ).2 him.2)

section Quadrature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Quantitative planar Riemann-sum quadrature at fixed mesh `δ > 0`.** For any compact set
`K₁ ⊆ ℂ` and mesh `δ > 0`, there exist `N : ℕ`, sample nodes `ζ : Fin N → ℂ` in `K₁`, and positive
weights `a : Fin N → ℝ` summing to `volume.real K₁` — depending only on `(K₁, δ)` — such that for
every Banach-valued function `g : ℂ → E` continuous on `K₁` whose `2 δ`-oscillation on `K₁` is at
most `ω`,

`‖(∫ z in K₁, g z) - ∑ j, a j • g (ζ j)‖ ≤ ω * volume.real K₁`. -/
theorem _root_.IsCompact.exists_sum_smul_norm_setIntegral_sub_le {K₁ : Set ℂ} (hK₁ : IsCompact K₁)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (a : Fin N → ℝ),
      (∀ j, ζ j ∈ K₁) ∧ (∀ j, 0 < a j) ∧ ∑ j, a j = volume.real K₁ ∧
      ∀ {g : ℂ → E} {ω : ℝ}, ContinuousOn g K₁ →
        (∀ z ∈ K₁, ∀ w ∈ K₁, dist z w ≤ 2 * δ → ‖g z - g w‖ ≤ ω) →
        ‖(∫ z in K₁, g z) - ∑ j, a j • g (ζ j)‖ ≤ ω * volume.real K₁ := by
  obtain ⟨R, hR⟩ := hK₁.isBounded.subset_closedBall 0
  set B : Finset (ℤ × ℤ) := Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋ ×ˢ Finset.Icc ⌊-R / δ⌋ ⌊R / δ⌋
  set A : ℤ × ℤ → Set ℂ := fun p ↦ planarMeshCell δ p ∩ K₁
  have hAmeas (p : ℤ × ℤ) : MeasurableSet (A p) :=
    (measurableSet_planarMeshCell δ p).inter hK₁.isClosed.measurableSet
  have hAlt (p : ℤ × ℤ) : volume (A p) < ⊤ :=
    (measure_mono inter_subset_right).trans_lt hK₁.measure_lt_top
  have hAdisj : Pairwise (Disjoint on A) := fun p q hpq ↦
    (pairwise_disjoint_planarMeshCell hδ hpq).mono inter_subset_left inter_subset_left
  have hAcov : (⋃ p ∈ B, A p) = K₁ := by
    refine Subset.antisymm (iUnion₂_subset fun _ _ ↦ inter_subset_right) fun z hz ↦ ?_
    obtain ⟨p, hpB, hzp⟩ := mem_iUnion₂.1 (closedBall_subset_biUnion_planarMeshCell hδ (hR hz))
    exact mem_biUnion hpB ⟨hzp, hz⟩
  classical
  set S : Finset (ℤ × ℤ) := B.filter fun p ↦ 0 < volume.real (A p)
  have hAnull {p : ℤ × ℤ} (hpB : p ∈ B) (hpS : p ∉ S) : volume (A p) = 0 := by
    have hle : volume.real (A p) ≤ 0 := not_lt.1 fun hpos ↦ hpS (Finset.mem_filter.2 ⟨hpB, hpos⟩)
    have h0 : volume.real (A p) = 0 := le_antisymm hle measureReal_nonneg
    exact (ENNReal.toReal_eq_zero_iff (volume (A p))).1 h0 |>.resolve_right (hAlt p).ne
  have hAne (p : S) : (A p.1).Nonempty := by
    by_contra hemp
    have hpos : 0 < volume.real (A p.1) := (Finset.mem_filter.1 p.2).2
    rw [not_nonempty_iff_eq_empty.1 hemp, measureReal_empty] at hpos
    exact lt_irrefl 0 hpos
  choose ζS hζS using hAne
  let e : Fin S.card ≃ S := S.equivFin.symm
  set ζ : Fin S.card → ℂ := fun j ↦ ζS (e j)
  set a : Fin S.card → ℝ := fun j ↦ volume.real (A (e j).1)
  have hsum_vol : ∑ j, a j = volume.real K₁ := by
    have he : ∑ j, a j = ∑ p ∈ S, volume.real (A p) :=
      Fintype.sum_equiv e _ (fun p : S ↦ volume.real (A p.1)) (fun _ ↦ rfl)
        |>.trans (Finset.sum_attach S fun p ↦ volume.real (A p))
    rw [he, Finset.sum_subset (Finset.filter_subset _ B) fun p hpB hpS ↦ by
      simp [measureReal_def, hAnull hpB hpS]]
    rw [← hAcov, measureReal_biUnion_finset (fun p _ q _ hpq ↦ hAdisj hpq)
      (fun p _ ↦ hAmeas p) (fun p _ ↦ (hAlt p).ne)]
  refine ⟨S.card, ζ, a, fun j ↦ (hζS (e j)).2, fun j ↦ (Finset.mem_filter.1 (e j).2).2,
    hsum_vol, fun {g ω} hg hosc ↦ ?_⟩
  have hintK : IntegrableOn g K₁ := hg.integrableOn_compact hK₁
  have hintA (p : ℤ × ℤ) : IntegrableOn g (A p) := hintK.mono_set inter_subset_right
  -- Split `∫_{K₁} g` across the cells of `B`, then drop the null cells outside `S`.
  have hint_eq : ∫ z in K₁, g z = ∑ j, ∫ z in A (e j).1, g z := by
    rw [← hAcov, integral_biUnion_finset B (fun p _ ↦ hAmeas p) (fun p _ q _ hpq ↦ hAdisj hpq)
      (fun p _ ↦ hintA p)]
    rw [← Finset.sum_subset (Finset.filter_subset _ B) fun p hpB hpS ↦
      setIntegral_measure_zero _ (hAnull hpB hpS)]
    exact (Finset.sum_attach S fun p ↦ ∫ z in A p, g z).symm.trans
      (Fintype.sum_equiv e.symm (fun p : S ↦ ∫ z in A p.1, g z) _ fun _ ↦ by simp)
  have hsub : (∫ z in K₁, g z) - ∑ j, a j • g (ζ j) =
      ∑ j, ∫ z in A (e j).1, (g z - g (ζ j)) := by
    rw [hint_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← setIntegral_const (g (ζ j)),
      integral_sub (hintA (e j).1) (integrableOn_const (hAlt (e j).1).ne)]
  rw [hsub]
  calc ‖∑ j, ∫ z in A (e j).1, (g z - g (ζ j))‖
      ≤ ∑ j, ‖∫ z in A (e j).1, (g z - g (ζ j))‖ := norm_sum_le _ _
    _ ≤ ∑ j, ω * a j := by
        refine Finset.sum_le_sum fun j _ ↦ norm_setIntegral_le_of_norm_le_const (hAlt (e j).1)
          fun z hz ↦ hosc z hz.2 (ζ j) (hζS (e j)).2
            (dist_le_two_mul_of_mem_planarMeshCell hz.1 (hζS (e j)).1)
    _ = ω * ∑ j, a j := (Finset.mul_sum _ _ _).symm
    _ = ω * volume.real K₁ := by rw [hsum_vol]

/-- **Uniform planar Riemann-sum quadrature on `K₁ ×ˢ K₂`.** Let `K₁ ⊆ ℂ` and `K₂ ⊆ X` be compact
and let `G : ℂ × X → E` be continuous on `K₁ ×ˢ K₂`. For every `ε > 0`, there exist `N : ℕ`, sample
nodes `ζ : Fin N → ℂ` in `K₁`, and positive weights `a : Fin N → ℝ` summing to `volume.real K₁`
such that `‖(∫ z in K₁, G (z, ξ)) - ∑ j, a j • G (ζ j, ξ)‖ < ε` for all `ξ ∈ K₂`. -/
theorem _root_.IsCompact.exists_sum_smul_norm_setIntegral_sub_lt {X : Type*} [PseudoMetricSpace X]
    {K₁ : Set ℂ} {K₂ : Set X} {G : ℂ × X → E} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hG : ContinuousOn G (K₁ ×ˢ K₂)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (a : Fin N → ℝ),
      (∀ j, ζ j ∈ K₁) ∧ (∀ j, 0 < a j) ∧ ∑ j, a j = volume.real K₁ ∧
      ∀ ξ ∈ K₂, ‖(∫ z in K₁, G (z, ξ)) - ∑ j, a j • G (ζ j, ξ)‖ < ε := by
  have hvol_pos : 0 < volume.real K₁ + 1 := add_pos_of_nonneg_of_pos measureReal_nonneg one_pos
  set ω : ℝ := ε / (volume.real K₁ + 1)
  have hω : 0 < ω := div_pos hε hvol_pos
  have hunif : UniformContinuousOn G (K₁ ×ˢ K₂) :=
    (hK₁.prod hK₂).uniformContinuousOn_of_continuous hG
  obtain ⟨r, hr, hrG⟩ := Metric.uniformContinuousOn_iff.1 hunif ω hω
  set δ : ℝ := r / 3
  have hδ : 0 < δ := by positivity
  obtain ⟨N, ζ, a, hζ, ha, hsum, hquad⟩ := hK₁.exists_sum_smul_norm_setIntegral_sub_le (E := E) hδ
  refine ⟨N, ζ, a, hζ, ha, hsum, fun ξ hξ ↦ ?_⟩
  have hg_cont : ContinuousOn (fun z ↦ G (z, ξ)) K₁ :=
    hG.comp (continuous_id.prodMk continuous_const).continuousOn fun z hz ↦ ⟨hz, hξ⟩
  have hg_osc : ∀ z ∈ K₁, ∀ w ∈ K₁, dist z w ≤ 2 * δ → ‖G (z, ξ) - G (w, ξ)‖ ≤ ω :=
    fun z hz w hw hzw ↦ by
      rw [← dist_eq_norm]
      refine (hrG (z, ξ) ⟨hz, hξ⟩ (w, ξ) ⟨hw, hξ⟩ ?_).le
      have hdist : dist (z, ξ) (w, ξ) = dist z w := by simp [Prod.dist_eq]
      rw [hdist]
      dsimp only [δ] at hzw
      linarith
  calc ‖(∫ z in K₁, G (z, ξ)) - ∑ j, a j • G (ζ j, ξ)‖
      ≤ ω * volume.real K₁ := hquad hg_cont hg_osc
    _ < ω * (volume.real K₁ + 1) := by gcongr; linarith
    _ = ε := div_mul_cancel₀ ε hvol_pos.ne'

end Quadrature

end TauCeti
