/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Planar Riemann-sum quadrature on half-open square meshes

Given a compact set `K₁ ⊆ ℂ` and a positive mesh `δ > 0`, partitioning an enclosing half-open square
box into half-open squares `TauCeti.planarSquareCell a δ p` of side `δ` decomposes `K₁` into
finitely many pairwise disjoint measurable pieces of diameter at most `√2 * δ`. Retaining only the
cells whose intersection with `K₁` has nonzero Lebesgue area (so cells meeting `K₁` in a set of
area zero, such as along cell boundaries, contribute `0` to both the integral and the sum) and
choosing one sample point in each positive-area intersection produces fixed nodes and area weights
independent of the integrand.

For any real Banach space `E` and integrable `g : ℂ → E`, the error between `∫ z in K₁, g z` and
the weighted sum over those nodes is bounded by `volume.real K₁ * ω` whenever `‖g z - g w‖ ≤ ω` for
all `z, w ∈ K₁` at distance at most `√2 * δ`. When `G : ℂ → X → E` is jointly continuous on
`K₁ ×ˢ K₂` for a compact parameter set `K₂`, uniform equicontinuity along `K₁` yields uniform
Riemann-sum approximation on `K₂`, turning parametric planar integrals (such as cutoff
Cauchy–Pompeiu kernels) into finite-rank linear combinations.

## Main declarations

* `TauCeti.planarSquareCell`: the half-open planar square cell of mesh `δ` anchored at `a : ℂ`.
* `TauCeti.dist_le_sqrt_two_mul_of_mem_planarSquareCell`: any two points of a cell of mesh `δ`
  have distance at most `√2 * δ`.
* `IsCompact.exists_planarSquareCell_quadrature`: constructs a finite positive-area mesh and sample
  points on compact `K₁` satisfying the universal `volume.real K₁ * ω` oscillation error bound.
* `IsCompact.exists_fin_planarSquareCell_quadrature_lt`: uniform Riemann-sum approximation on a
  compact parameter set `K₂` for continuous `G : ℂ → X → E`.

## References

* A. Rainer, *Advanced Complex Analysis*, proof of Theorem 11.1, pp. 25–27.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.3.1.
-/

public section

open Filter MeasureTheory Metric Set
open scoped Topology

namespace TauCeti

/-- The half-open planar square cell
`[a.re + p.1 * δ, a.re + (p.1 + 1) * δ) × [a.im + p.2 * δ, a.im + (p.2 + 1) * δ)` in `ℂ` of mesh
`δ`, anchored at `a`. -/
def planarSquareCell (a : ℂ) (δ : ℝ) (p : ℕ × ℕ) : Set ℂ :=
  {z : ℂ | z.re ∈ Ico (a.re + p.1 * δ) (a.re + (p.1 + 1 : ℕ) * δ) ∧
    z.im ∈ Ico (a.im + p.2 * δ) (a.im + (p.2 + 1 : ℕ) * δ)}

/-- Explicit set-builder form of `TauCeti.planarSquareCell`. -/
theorem planarSquareCell_def (a : ℂ) (δ : ℝ) (p : ℕ × ℕ) :
    planarSquareCell a δ p =
      {z : ℂ | z.re ∈ Ico (a.re + p.1 * δ) (a.re + (p.1 + 1 : ℕ) * δ) ∧
        z.im ∈ Ico (a.im + p.2 * δ) (a.im + (p.2 + 1 : ℕ) * δ)} := (rfl)

@[simp]
theorem mem_planarSquareCell_iff {a z : ℂ} {δ : ℝ} {p : ℕ × ℕ} :
    z ∈ planarSquareCell a δ p ↔
      z.re ∈ Ico (a.re + p.1 * δ) (a.re + (p.1 + 1 : ℕ) * δ) ∧
        z.im ∈ Ico (a.im + p.2 * δ) (a.im + (p.2 + 1 : ℕ) * δ) :=
  Iff.rfl

/-- Every half-open planar square cell is Borel measurable. -/
theorem measurableSet_planarSquareCell (a : ℂ) (δ : ℝ) (p : ℕ × ℕ) :
    MeasurableSet (planarSquareCell a δ p) :=
  (measurableSet_Ico.preimage Complex.measurable_re).inter
    (measurableSet_Ico.preimage Complex.measurable_im)

/-- Distinct grid indices give disjoint half-open planar square cells. -/
theorem pairwiseDisjoint_planarSquareCell (a : ℂ) (δ : ℝ) :
    Pairwise (Function.onFun Disjoint (planarSquareCell a δ)) := by
  intro p q hpq
  refine disjoint_left.mpr fun z hzp hzq ↦ hpq ?_
  rw [mem_planarSquareCell_iff, mem_Ico, mem_Ico] at hzp hzq
  have hδ : 0 < δ := by
    have := hzp.1.1.trans_lt hzp.1.2
    push_cast at this
    linarith
  have coord_eq {x : ℝ} {m n : ℕ} (hm : m * δ ≤ x ∧ x < (m + 1 : ℕ) * δ)
      (hn : n * δ ≤ x ∧ x < (n + 1 : ℕ) * δ) : m = n := by
    have hmn : (m : ℝ) < (n : ℝ) + 1 := by
      have := hm.1.trans_lt hn.2
      push_cast at this
      nlinarith
    have hnm : (n : ℝ) < (m : ℝ) + 1 := by
      have := hn.1.trans_lt hm.2
      push_cast at this
      nlinarith
    exact_mod_cast le_antisymm (Nat.lt_succ_iff.mp (by exact_mod_cast hmn))
      (Nat.lt_succ_iff.mp (by exact_mod_cast hnm))
  ext
  · exact coord_eq (x := z.re - a.re)
      ⟨by linarith [hzp.1.1], by linarith [hzp.1.2]⟩
      ⟨by linarith [hzq.1.1], by linarith [hzq.1.2]⟩
  · exact coord_eq (x := z.im - a.im)
      ⟨by linarith [hzp.2.1], by linarith [hzp.2.2]⟩
      ⟨by linarith [hzq.2.1], by linarith [hzq.2.2]⟩

/-- Points in the same half-open square cell of mesh `δ` are at distance at most `√2 * δ`. -/
theorem dist_le_sqrt_two_mul_of_mem_planarSquareCell {a z w : ℂ} {δ : ℝ} {p : ℕ × ℕ}
    (hz : z ∈ planarSquareCell a δ p) (hw : w ∈ planarSquareCell a δ p) :
    dist z w ≤ √2 * δ := by
  rw [mem_planarSquareCell_iff, mem_Ico, mem_Ico] at hz hw
  push_cast at hz hw
  have hδ : 0 ≤ δ := by linarith [hz.1.1, hz.1.2]
  have hre : |z.re - w.re| ≤ δ := abs_le.mpr ⟨by linarith [hz.1.1, hw.1.2],
    by linarith [hz.1.2, hw.1.1]⟩
  have him : |z.im - w.im| ≤ δ := abs_le.mpr ⟨by linarith [hz.2.1, hw.2.2],
    by linarith [hz.2.2, hw.2.1]⟩
  rw [dist_eq_norm]
  have hsq : ‖z - w‖ ^ 2 ≤ (√2 * δ) ^ 2 := by
    calc ‖z - w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [sq]
      _ = |z.re - w.re| ^ 2 + |z.im - w.im| ^ 2 := by simp
      _ ≤ δ ^ 2 + δ ^ 2 := add_le_add (pow_le_pow_left₀ (abs_nonneg _) hre 2)
          (pow_le_pow_left₀ (abs_nonneg _) him 2)
      _ = (√2 * δ) ^ 2 := by rw [mul_pow, Real.sq_sqrt zero_le_two]; ring
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

/-- A bounded set `K₁ ⊆ ℂ` is covered by a finite `M × M` grid of half-open square cells of mesh
`δ > 0`. -/
private theorem exists_subset_biUnion_planarSquareCell {K₁ : Set ℂ} (hK₁ : Bornology.IsBounded K₁)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : ℂ) (M : ℕ), K₁ ⊆ ⋃ p ∈ Finset.range M ×ˢ Finset.range M, planarSquareCell a δ p := by
  obtain ⟨R, hR⟩ := hK₁.subset_closedBall 0
  set R' : ℝ := max R 0
  set a : ℂ := ⟨-R', -R'⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * R' / δ)
  have hMδ : 2 * R' < M * δ := (div_lt_iff₀ hδ).mp hM
  refine ⟨a, M, fun z hz ↦ ?_⟩
  have hzn : ‖z‖ ≤ R' := (mem_closedBall_zero_iff.mp (hR hz)).trans (le_max_left _ _)
  have hre0 : 0 ≤ z.re - a.re := by
    have := (neg_abs_le z.re).trans' (neg_le_neg ((Complex.abs_re_le_norm z).trans hzn))
    simp only [a]
    linarith
  have hre1 : z.re - a.re < M * δ := by
    have := (le_abs_self z.re).trans ((Complex.abs_re_le_norm z).trans hzn)
    simp only [a]
    linarith
  have him0 : 0 ≤ z.im - a.im := by
    have := (neg_abs_le z.im).trans' (neg_le_neg ((Complex.abs_im_le_norm z).trans hzn))
    simp only [a]
    linarith
  have him1 : z.im - a.im < M * δ := by
    have := (le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans hzn)
    simp only [a]
    linarith
  set j := ⌊(z.re - a.re) / δ⌋₊
  set k := ⌊(z.im - a.im) / δ⌋₊
  have hjM : j < M :=
    (Nat.floor_lt (div_nonneg hre0 hδ.le)).mpr ((div_lt_iff₀ hδ).mpr hre1)
  have hkM : k < M :=
    (Nat.floor_lt (div_nonneg him0 hδ.le)).mpr ((div_lt_iff₀ hδ).mpr him1)
  refine mem_iUnion₂.mpr ⟨(j, k), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hjM,
    Finset.mem_range.mpr hkM⟩, ⟨?_, ?_⟩⟩
  · have hlo := (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hre0 hδ.le))
    have hhi := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((z.re - a.re) / δ))
    exact ⟨by linarith, by push_cast; linarith⟩
  · have hlo := (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg him0 hδ.le))
    have hhi := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((z.im - a.im) / δ))
    exact ⟨by linarith, by push_cast; linarith⟩

/-- On a finite-measure set `A`, replacing an integrable function `g` by a constant value `g ζ`
incurs error at most `ω * volume.real A` whenever `‖g z - g ζ‖ ≤ ω` across `A`. -/
private theorem norm_setIntegral_sub_measureReal_smul_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {A : Set ℂ} (hAf : volume A < ⊤) {g : ℂ → E}
    (hg : IntegrableOn g A) (ζ : ℂ) {ω : ℝ} (hω : ∀ z ∈ A, ‖g z - g ζ‖ ≤ ω) :
    ‖(∫ z in A, g z) - volume.real A • g ζ‖ ≤ ω * volume.real A := by
  have hconst : IntegrableOn (fun _ : ℂ ↦ g ζ) A := integrableOn_const hAf.ne
  rw [← setIntegral_const, ← integral_sub hg hconst]
  exact norm_setIntegral_le_of_norm_le_const hAf fun z hz ↦ hω z hz

end TauCeti

open TauCeti

/-- **Planar square-mesh Riemann-sum quadrature.** For any compact `K₁ ⊆ ℂ` and mesh `δ > 0`, there
exist an anchor `a : ℂ`, a finite set `I` of grid indices whose cells have positive-area
intersection with `K₁` (the remaining cells meeting `K₁` only in a null set), and sample points
`ζ p ∈ planarSquareCell a δ p ∩ K₁` for `p ∈ I` such that for every real Banach space `E` and every
integrable `g : ℂ → E`, the quadrature error is at most `volume.real K₁ * ω` whenever `g` has
oscillation at most `ω` at scale `√2 * δ` on `K₁`. -/
theorem IsCompact.exists_planarSquareCell_quadrature {K₁ : Set ℂ} (hK₁ : IsCompact K₁) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ (a : ℂ) (I : Finset (ℕ × ℕ)) (ζ : (ℕ × ℕ) → ℂ),
      (∀ p ∈ I, volume (planarSquareCell a δ p ∩ K₁) ≠ 0) ∧
      (∀ p ∈ I, ζ p ∈ planarSquareCell a δ p ∩ K₁) ∧
      ∑ p ∈ I, volume.real (planarSquareCell a δ p ∩ K₁) = volume.real K₁ ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        (g : ℂ → E), IntegrableOn g K₁ → ∀ {ω : ℝ},
          (∀ z ∈ K₁, ∀ w ∈ K₁, dist z w ≤ √2 * δ → ‖g z - g w‖ ≤ ω) →
          ‖(∫ z in K₁, g z) - ∑ p ∈ I, volume.real (planarSquareCell a δ p ∩ K₁) • g (ζ p)‖ ≤
            volume.real K₁ * ω := by
  classical
  obtain ⟨a, M, hcov⟩ := exists_subset_biUnion_planarSquareCell hK₁.isBounded hδ
  set G : Finset (ℕ × ℕ) := Finset.range M ×ˢ Finset.range M
  set A : ℕ × ℕ → Set ℂ := fun p ↦ planarSquareCell a δ p ∩ K₁
  have hAm (p : ℕ × ℕ) : MeasurableSet (A p) :=
    (measurableSet_planarSquareCell a δ p).inter hK₁.measurableSet
  have hAf (p : ℕ × ℕ) : volume (A p) < ⊤ :=
    (measure_mono inter_subset_right).trans_lt hK₁.measure_lt_top
  have hdisjG : (G : Set (ℕ × ℕ)).PairwiseDisjoint A := fun p _ q _ hpq ↦
    (pairwiseDisjoint_planarSquareCell a δ hpq).mono inter_subset_left inter_subset_left
  have hunion : (⋃ p ∈ G, A p) = K₁ := by
    refine Subset.antisymm (iUnion₂_subset fun _ _ ↦ inter_subset_right) fun z hz ↦ ?_
    obtain ⟨p, hpG, hzp⟩ := mem_iUnion₂.mp (hcov hz)
    exact mem_iUnion₂.mpr ⟨p, hpG, hzp, hz⟩
  set I : Finset (ℕ × ℕ) := G.filter fun p ↦ volume (A p) ≠ 0
  have hmem (p : ℕ × ℕ) : p ∈ I → (A p).Nonempty := fun hp ↦
    nonempty_of_measure_ne_zero (Finset.mem_filter.mp hp).2
  choose! ζ hζ using hmem
  have hsum_vol : ∑ p ∈ I, volume.real (A p) = volume.real K₁ := by
    rw [← hunion, measureReal_biUnion_finset hdisjG (fun p _ ↦ hAm p) (fun p _ ↦ (hAf p).ne),
      Finset.sum_filter_of_ne]
    intro p _ hp0
    exact fun h0 ↦ hp0 ((measureReal_eq_zero_iff (hAf p).ne).mpr h0)
  refine ⟨a, I, ζ, fun p hp ↦ (Finset.mem_filter.mp hp).2, hζ, hsum_vol, ?_⟩
  intro E _ _ _ g hg ω hosc
  have hint_split : (∫ z in K₁, g z) = ∑ p ∈ I, ∫ z in A p, g z := by
    rw [← hunion, integral_biUnion_finset G (fun p _ ↦ hAm p) hdisjG
      (fun p _ ↦ hg.mono_set inter_subset_right)]
    symm
    refine Finset.sum_subset (Finset.filter_subset _ G) fun p hpG hpI ↦ ?_
    have hp0 : volume (A p) = 0 := by simpa [I, hpG] using hpI
    exact setIntegral_measure_zero _ hp0
  rw [hint_split, ← Finset.sum_sub_distrib]
  calc ‖∑ p ∈ I, ((∫ z in A p, g z) - volume.real (A p) • g (ζ p))‖
      ≤ ∑ p ∈ I, ‖(∫ z in A p, g z) - volume.real (A p) • g (ζ p)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ I, ω * volume.real (A p) := by
        refine Finset.sum_le_sum fun p hp ↦
          norm_setIntegral_sub_measureReal_smul_le (hAf p)
            (hg.mono_set inter_subset_right) (ζ p) fun z hz ↦
            hosc z hz.2 (ζ p) (hζ p hp).2
              (dist_le_sqrt_two_mul_of_mem_planarSquareCell hz.1 (hζ p hp).1)
    _ = volume.real K₁ * ω := by rw [← Finset.mul_sum, hsum_vol, mul_comm]

/-- `Fin N`-indexed form of `IsCompact.exists_planarSquareCell_quadrature`: for a compact planar set
`K₁ ⊆ ℂ` and mesh `δ > 0`, there are `N` nodes in `K₁` and positive area weights summing to
`volume.real K₁` that approximate `∫ z in K₁, g z` with error at most `volume.real K₁ * ω` for
every integrable `g` whose oscillation at scale `√2 * δ` on `K₁` is at most `ω`. -/
theorem IsCompact.exists_fin_planarSquareCell_quadrature {K₁ : Set ℂ} (hK₁ : IsCompact K₁)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (w : Fin N → ℝ),
      (∀ j, ζ j ∈ K₁) ∧ (∀ j, 0 < w j) ∧ ∑ j, w j = volume.real K₁ ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        (g : ℂ → E), IntegrableOn g K₁ → ∀ {ω : ℝ},
          (∀ z ∈ K₁, ∀ z' ∈ K₁, dist z z' ≤ √2 * δ → ‖g z - g z'‖ ≤ ω) →
          ‖(∫ z in K₁, g z) - ∑ j, w j • g (ζ j)‖ ≤ volume.real K₁ * ω := by
  obtain ⟨a, I, ζ₀, hpos, hmem, hsum, herr⟩ := hK₁.exists_planarSquareCell_quadrature hδ
  let e : Fin I.card ≃ ↥I := I.equivFin.symm
  refine ⟨I.card, fun j ↦ ζ₀ (e j).1,
    fun j ↦ volume.real (planarSquareCell a δ (e j).1 ∩ K₁),
    fun j ↦ (hmem _ (e j).2).2, fun j ↦ ?_, ?_, fun g hg ω hosc ↦ ?_⟩
  · have hlt : volume (planarSquareCell a δ (e j).1 ∩ K₁) < ⊤ :=
      (measure_mono inter_subset_right).trans_lt hK₁.measure_lt_top
    dsimp only
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hpos _ (e j).2) hlt.ne
  · rw [← hsum, ← Finset.sum_coe_sort I]
    exact e.sum_comp fun p : ↥I ↦ volume.real (planarSquareCell a δ p.1 ∩ K₁)
  · have hsum_eq : (∑ j, volume.real (planarSquareCell a δ (e j).1 ∩ K₁) • g (ζ₀ (e j).1)) =
        ∑ p ∈ I, volume.real (planarSquareCell a δ p ∩ K₁) • g (ζ₀ p) := by
      rw [← Finset.sum_coe_sort I]
      exact e.sum_comp fun p : ↥I ↦ volume.real (planarSquareCell a δ p.1 ∩ K₁) • g (ζ₀ p)
    rw [hsum_eq]
    exact herr g hg hosc

/-- A jointly continuous family `G : Y → X → E` on `K₁ ×ˢ K₂`, with `K₁` and `K₂` compact, is
uniformly equicontinuous in its first variable across `K₂`. -/
theorem IsCompact.exists_pos_forall_norm_sub_le_of_continuousOn_prod {Y X E : Type*}
    [PseudoMetricSpace Y] [TopologicalSpace X] [SeminormedAddCommGroup E] {K₁ : Set Y} {K₂ : Set X}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) {G : Y → X → E}
    (hG : ContinuousOn G.uncurry (K₁ ×ˢ K₂)) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ z ∈ K₁, ∀ w ∈ K₁, dist z w < r → ∀ ξ ∈ K₂, ‖G z ξ - G w ξ‖ ≤ η := by
  let : CompactSpace K₁ := isCompact_iff_compactSpace.mp hK₁
  have hequi : Equicontinuous (fun (ξ : K₂) (z : K₁) ↦ G z.1 ξ.1) := by
    intro z₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    obtain ⟨v, hv, hball⟩ := hK₂.mem_uniformity_of_prod hG z₀.2 (Metric.dist_mem_uniformity hε)
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hv
    obtain ⟨u, hu, huv⟩ := hv
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hu] with z hz ⟨ξ, hξ⟩
    simpa [dist_comm] using hball z.1 (huv ⟨hz, z.2⟩) ξ hξ
  have hunif := CompactSpace.uniformEquicontinuous_of_equicontinuous hequi
  obtain ⟨r, hr, hdist⟩ := Metric.uniformEquicontinuous_iff.mp hunif η hη
  refine ⟨r, hr, fun z hz w hw hzw ξ hξ ↦ ?_⟩
  have h := hdist (⟨z, hz⟩ : K₁) (⟨w, hw⟩ : K₁) hzw ⟨ξ, hξ⟩
  rw [dist_eq_norm] at h
  exact h.le

/-- **Uniform Riemann-sum approximation on compact products.** If `K₁ ⊆ ℂ` and `K₂ ⊆ X` are
compact and `G : ℂ → X → E` is jointly continuous on `K₁ ×ˢ K₂`, then for every `ε > 0` and every
sufficiently small mesh `δ > 0` there is a `Fin N`-indexed planar square-mesh quadrature with nodes
in `K₁` and positive area weights summing to `volume.real K₁` that approximates
`∫ z in K₁, G z ξ` within `ε` uniformly for all `ξ ∈ K₂`. -/
theorem IsCompact.exists_fin_planarSquareCell_quadrature_lt {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {K₁ : Set ℂ} {K₂ : Set X}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) {G : ℂ → X → E}
    (hG : ContinuousOn G.uncurry (K₁ ×ˢ K₂)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ {δ : ℝ}, 0 < δ → δ < δ₀ →
      ∃ (N : ℕ) (ζ : Fin N → ℂ) (w : Fin N → ℝ),
        (∀ j, ζ j ∈ K₁) ∧ (∀ j, 0 < w j) ∧ ∑ j, w j = volume.real K₁ ∧
        ∀ ξ ∈ K₂, ‖(∫ z in K₁, G z ξ) - ∑ j, w j • G (ζ j) ξ‖ < ε := by
  set η : ℝ := ε / (volume.real K₁ + 1)
  have hη : 0 < η := div_pos hε (by linarith [measureReal_nonneg (μ := volume) (s := K₁)])
  obtain ⟨r, hr, hosc⟩ := hK₁.exists_pos_forall_norm_sub_le_of_continuousOn_prod hK₂ hG hη
  refine ⟨r / 2, half_pos hr, fun {δ} hδ hδr ↦ ?_⟩
  have hsqrt : √2 * δ < r := by
    have h2 : √2 < 2 := by
      rw [Real.sqrt_lt' two_pos]
      norm_num
    nlinarith
  obtain ⟨N, ζ, w, hmem, hpos, hsum, herr⟩ := hK₁.exists_fin_planarSquareCell_quadrature hδ
  refine ⟨N, ζ, w, hmem, hpos, hsum, fun ξ hξ ↦ ?_⟩
  have hGξ : ContinuousOn (fun z ↦ G z ξ) K₁ :=
    hG.comp (continuousOn_id.prodMk continuousOn_const) fun z hz ↦ ⟨hz, hξ⟩
  calc ‖(∫ z in K₁, G z ξ) - ∑ j, w j • G (ζ j) ξ‖
      ≤ volume.real K₁ * η :=
        herr (fun z ↦ G z ξ) (hGξ.integrableOn_compact hK₁) fun z hz z' hz' hzz' ↦
          hosc z hz z' hz' (hzz'.trans_lt hsqrt) ξ hξ
    _ < (volume.real K₁ + 1) * η := by gcongr; linarith
    _ = ε := mul_div_cancel₀ ε (by linarith [measureReal_nonneg (μ := volume) (s := K₁)])

end
