/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.SuccPred.IntervalSucc
import TauCeti.Analysis.Complex.ReProdIm
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Uniform planar Riemann-sum quadrature on compact sets

Given a compact subset `K₁` of `ℂ` and a mesh `δ > 0`, a half-open bounding box containing `K₁`
splits into finitely many pairwise disjoint half-open squares `TauCeti.planarSquare z₀ δ c` of
side `δ` and diameter `√2 * δ`. Retaining only the active cells whose intersection with `K₁` has
nonzero planar Lebesgue measure, and picking a sample tag in each active intersection, yields a
finite quadrature sum `∑ c ∈ A, volume.real (planarSquare z₀ δ c ∩ K₁) • g (ζ c)` approximating
`∫ z in K₁, g z`.

Boundary cells whose intersection with `K₁` has zero planar area have real measure zero and zero
set integral, so omitting them—or assigning arbitrary sample tags to them—leaves the sum unchanged
and introduces no error. For a family `G : ℂ → X → E` into a real Banach space `E`, if the
oscillation of `G · ξ` across points of `K₁` at distance at most `√2 * δ` is bounded by `ε`
uniformly for `ξ ∈ K₂`, the quadrature error on `K₂` is at most `volume.real K₁ * ε`. When `K₂` is
compact in a topological space `X` and `G` is jointly continuous on `K₁ ×ˢ K₂`, uniform
equicontinuity on `K₁` supplies uniform convergence of these planar Riemann sums in `ξ ∈ K₂` as
`δ → 0`.

## Main declarations

* `TauCeti.norm_sum_measureReal_smul_sub_setIntegral_le`: abstract quadrature error bound on a
  finite measurable partition, requiring oscillation control only on cells of nonzero measure.
* `TauCeti.planarSquare`: the half-open square
  `[x₀ + j δ, x₀ + (j + 1) δ) ×ℂ [y₀ + k δ, y₀ + (k + 1) δ)` of mesh `δ`.
* `TauCeti.exists_planarSquare_quadrature_of_isCompact`: finite active square mesh and sample tags
  on a compact `K₁ ⊆ ℂ` with cellwise oscillation error bound.
* `TauCeti.tendstoUniformlyOn_sum_planarSquare_of_continuousOn` and
  `TauCeti.exists_planarSquare_quadrature_lt_of_continuousOn`: uniform planar Riemann-sum
  convergence and `η`-approximation of `ξ ↦ ∫ z in K₁, G z ξ` over a compact parameter set `K₂`.

## References

* A. Rainer, *Advanced Complex Analysis*, proof of Theorem 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.1.
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology Uniformity
open scoped BigOperators ENNReal

namespace TauCeti

section AbstractPartition

variable {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cells of measure zero contribute nothing to a real-measure Riemann sum, so restricting to
cells of nonzero measure leaves the sum unchanged regardless of the tags on null cells. -/
theorem sum_filter_measure_ne_zero_measureReal_smul (μ : Measure α) (s : Finset ι) (P : ι → Set α)
    (ζ : ι → α) (g : α → E) :
    (∑ i ∈ s with μ (P i) ≠ 0, μ.real (P i) • g (ζ i)) =
      ∑ i ∈ s, μ.real (P i) • g (ζ i) := by
  classical
  refine Finset.sum_subset (Finset.filter_subset _ _) fun i hi hnot ↦ ?_
  have hzero : μ (P i) = 0 := not_not.mp fun hne ↦ hnot (Finset.mem_filter.mpr ⟨hi, hne⟩)
  simp [Measure.real, hzero]

/-- **Measurable-partition quadrature bound.** Let `P` be a finite pairwise disjoint measurable
partition of a finite-measure set `K`. If `‖g (ζ i) - g z‖ ≤ ε` on every cell `P i` of nonzero
measure, the tagged sum differs from `∫ z in K, g z ∂μ` by at most `μ.real K * ε`. Cells with
`μ (P i) = 0` require neither a tag inside `P i` nor an oscillation bound. -/
theorem norm_sum_measureReal_smul_sub_setIntegral_le [CompleteSpace E] {μ : Measure α}
    {s : Finset ι} {P : ι → Set α} {K : Set α} (hcover : ⋃ i ∈ s, P i = K)
    (hm : ∀ i ∈ s, MeasurableSet (P i)) (hd : Set.Pairwise (↑s) (Disjoint on P))
    (hK : μ K ≠ ∞) {g : α → E} (hg : IntegrableOn g K μ) (ζ : ι → α) {ε : ℝ}
    (hosc : ∀ i ∈ s, μ (P i) ≠ 0 → ∀ z ∈ P i, ‖g (ζ i) - g z‖ ≤ ε) :
    ‖(∑ i ∈ s, μ.real (P i) • g (ζ i)) - ∫ z in K, g z ∂μ‖ ≤ μ.real K * ε := by
  have hPsub (i : ι) (hi : i ∈ s) : P i ⊆ K := hcover ▸ subset_biUnion_of_mem hi
  have hPfin (i : ι) (hi : i ∈ s) : μ (P i) < ∞ :=
    (measure_mono (hPsub i hi)).trans_lt hK.lt_top
  have hgi (i : ι) (hi : i ∈ s) : IntegrableOn g (P i) μ := hg.mono_set (hPsub i hi)
  have hintK : ∫ z in K, g z ∂μ = ∑ i ∈ s, ∫ z in P i, g z ∂μ := by
    rw [← hcover, integral_biUnion_finset s hm hd hgi]
  rw [hintK, ← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ s, (μ.real (P i) • g (ζ i) - ∫ z in P i, g z ∂μ)‖
      ≤ ∑ i ∈ s, ‖μ.real (P i) • g (ζ i) - ∫ z in P i, g z ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, μ.real (P i) * ε := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      by_cases hμi : μ (P i) = 0
      · simp [Measure.real, hμi, setIntegral_measure_zero _ hμi]
      · rw [← setIntegral_const, ← integral_sub (integrableOn_const (hPfin i hi).ne) (hgi i hi),
          mul_comm]
        exact norm_setIntegral_le_of_norm_le_const (hPfin i hi) (hosc i hi hμi)
    _ = (∑ i ∈ s, μ.real (P i)) * ε := (Finset.sum_mul _ _ _).symm
    _ = μ.real K * ε := by
      rw [← measureReal_biUnion_finset hd hm fun i hi ↦ (hPfin i hi).ne, hcover]

end AbstractPartition

section PlanarSquare

/-- The half-open planar square `[x₀ + j δ, x₀ + (j + 1) δ) ×ℂ [y₀ + k δ, y₀ + (k + 1) δ)` with
base corner `z₀ = x₀ + i y₀`, mesh `δ`, and integer grid indices `c = (j, k)`. -/
def planarSquare (z₀ : ℂ) (δ : ℝ) (c : ℕ × ℕ) : Set ℂ :=
  Ico (z₀.re + c.1 * δ) (z₀.re + (c.1 + 1 : ℕ) * δ) ×ℂ
    Ico (z₀.im + c.2 * δ) (z₀.im + (c.2 + 1 : ℕ) * δ)

@[simp]
theorem mem_planarSquare_iff {z₀ z : ℂ} {δ : ℝ} {c : ℕ × ℕ} :
    z ∈ planarSquare z₀ δ c ↔
      (z₀.re + c.1 * δ ≤ z.re ∧ z.re < z₀.re + (c.1 + 1 : ℕ) * δ) ∧
        (z₀.im + c.2 * δ ≤ z.im ∧ z.im < z₀.im + (c.2 + 1 : ℕ) * δ) := by
  simp [planarSquare, mem_reProdIm]

theorem measurableSet_planarSquare (z₀ : ℂ) (δ : ℝ) (c : ℕ × ℕ) :
    MeasurableSet (planarSquare z₀ δ c) :=
  measurableSet_Ico.reProdIm measurableSet_Ico

/-- For nonnegative mesh `δ`, the half-open squares `planarSquare z₀ δ c` are pairwise disjoint. -/
theorem pairwiseDisjoint_planarSquare (z₀ : ℂ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Pairwise (Disjoint on planarSquare z₀ δ) := by
  have hmono (a : ℝ) : Monotone (fun n : ℕ ↦ a + n * δ) :=
    fun m n hmn ↦ add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmn) hδ) a
  rintro ⟨j₁, k₁⟩ ⟨j₂, k₂⟩ hne
  rw [Function.onFun, Set.disjoint_left]
  intro z hz₁ hz₂
  rcases not_and_or.mp (mt Prod.ext_iff.mpr hne) with hj | hk
  · exact Set.disjoint_left.mp
      ((hmono z₀.re).pairwise_disjoint_on_Ico_succ hj) (mem_reProdIm.mp hz₁).1
      (mem_reProdIm.mp hz₂).1
  · exact Set.disjoint_left.mp
      ((hmono z₀.im).pairwise_disjoint_on_Ico_succ hk) (mem_reProdIm.mp hz₁).2
      (mem_reProdIm.mp hz₂).2

/-- Two points in the same half-open square of mesh `δ ≥ 0` lie at distance at most `√2 * δ`. -/
theorem norm_sub_le_sqrt_two_mul_of_mem_planarSquare {z₀ z w : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) {c : ℕ × ℕ}
    (hz : z ∈ planarSquare z₀ δ c) (hw : w ∈ planarSquare z₀ δ c) :
    ‖z - w‖ ≤ √2 * δ := by
  rw [mem_planarSquare_iff] at hz hw
  push_cast at hz hw
  have hre : |(z - w).re| ≤ δ := by
    rw [sub_re, abs_le]
    constructor <;> linarith
  have him : |(z - w).im| ≤ δ := by
    rw [sub_im, abs_le]
    constructor <;> linarith
  have hsq : (z - w).re ^ 2 + (z - w).im ^ 2 ≤ (√2 * δ) ^ 2 := by
    calc
      (z - w).re ^ 2 + (z - w).im ^ 2
        ≤ δ ^ 2 + δ ^ 2 := add_le_add (sq_le_sq.mpr (by rwa [abs_of_nonneg hδ]))
            (sq_le_sq.mpr (by rwa [abs_of_nonneg hδ]))
      _ = 2 * δ ^ 2 := (two_mul _).symm
      _ = (√2 * δ) ^ 2 := by rw [mul_pow, Real.sq_sqrt zero_le_two]
  rw [Complex.norm_def, Complex.normSq_apply, ← sq, ← sq]
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩

private theorem biUnion_range_Ico_add_mul (a : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (⋃ i ∈ Finset.range n, Ico (a + i * δ) (a + (i + 1 : ℕ) * δ)) = Ico a (a + n * δ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm, ih,
      Ico_union_Ico_eq_Ico (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hδ))
        (add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr n.le_succ) hδ) a)]

/-- An `m × n` grid of half-open squares tiles the half-open rectangle
`[z₀.re, z₀.re + m δ) ×ℂ [z₀.im, z₀.im + n δ)`. -/
theorem biUnion_planarSquare_eq_reProdIm (z₀ : ℂ) {δ : ℝ} (hδ : 0 ≤ δ) (m n : ℕ) :
    (⋃ c ∈ Finset.range m ×ˢ Finset.range n, planarSquare z₀ δ c) =
      Ico z₀.re (z₀.re + m * δ) ×ℂ Ico z₀.im (z₀.im + n * δ) := by
  ext z
  simp only [mem_iUnion₂, Finset.mem_product, Prod.exists, mem_reProdIm, planarSquare]
  rw [← biUnion_range_Ico_add_mul z₀.re hδ m, ← biUnion_range_Ico_add_mul z₀.im hδ n]
  simp only [mem_iUnion, Finset.mem_range]
  exact ⟨fun ⟨j, k, ⟨hj, hk⟩, hre, him⟩ ↦ ⟨⟨j, hj, hre⟩, ⟨k, hk, him⟩⟩,
    fun ⟨⟨j, hj, hre⟩, ⟨k, hk, him⟩⟩ ↦ ⟨j, k, ⟨hj, hk⟩, hre, him⟩⟩

/-- **Planar square mesh quadrature on a compact set.** For a compact `K₁ ⊆ ℂ` and `δ > 0`, a
finite grid of half-open squares `planarSquare z₀ δ c` covers `K₁`. Retaining the active cells
`A` where `volume (planarSquare z₀ δ c ∩ K₁) ≠ 0` and selecting a tag `ζ c` in each active
intersection yields the oscillation bound `volume.real K₁ * ε` for any Banach-space-valued
integrand, while null-area boundary cells drop out of the sum unchanged. -/
theorem exists_planarSquare_quadrature_of_isCompact {K₁ : Set ℂ} (hK₁ : IsCompact K₁)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (z₀ : ℂ) (n : ℕ) (A : Finset (ℕ × ℕ)) (ζ : ℕ × ℕ → ℂ),
      K₁ ⊆ ⋃ c ∈ Finset.range n ×ˢ Finset.range n, planarSquare z₀ δ c ∧
      (∀ c, c ∈ A ↔ c ∈ Finset.range n ×ˢ Finset.range n ∧
        volume (planarSquare z₀ δ c ∩ K₁) ≠ 0) ∧
      (∀ c ∈ A, ζ c ∈ planarSquare z₀ δ c ∩ K₁) ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (g : ℂ → E),
        (∑ c ∈ Finset.range n ×ˢ Finset.range n,
            volume.real (planarSquare z₀ δ c ∩ K₁) • g (ζ c) =
          ∑ c ∈ A, volume.real (planarSquare z₀ δ c ∩ K₁) • g (ζ c)) ∧
        ∀ {ε : ℝ}, IntegrableOn g K₁ volume →
          (∀ c ∈ A, ∀ z ∈ planarSquare z₀ δ c ∩ K₁, ‖g (ζ c) - g z‖ ≤ ε) →
          ‖(∑ c ∈ A, volume.real (planarSquare z₀ δ c ∩ K₁) • g (ζ c)) -
            ∫ z in K₁, g z‖ ≤ volume.real K₁ * ε := by
  classical
  obtain ⟨R, hR⟩ := hK₁.isBounded.subset_closedBall 0
  set M : ℝ := max R 0
  set z₀ : ℂ := ⟨-M, -M⟩
  set n : ℕ := ⌈2 * M / δ⌉₊ + 1
  set grid : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n
  have hcover_K₁ : K₁ ⊆ ⋃ c ∈ grid, planarSquare z₀ δ c := by
    rw [biUnion_planarSquare_eq_reProdIm z₀ hδ.le n n]
    intro z hz
    have hnorm : ‖z‖ ≤ M := (mem_closedBall_zero_iff.mp (hR hz)).trans (le_max_left _ _)
    have hre := abs_re_le_norm z
    have him := abs_im_le_norm z
    rw [abs_le] at hre him
    have hspan : 2 * M < n * δ := by
      have hceil : 2 * M / δ ≤ ⌈2 * M / δ⌉₊ := Nat.le_ceil _
      have hle : 2 * M ≤ ⌈2 * M / δ⌉₊ * δ := (div_le_iff₀ hδ).mp hceil
      have hlt : (⌈2 * M / δ⌉₊ : ℝ) * δ < ((⌈2 * M / δ⌉₊ + 1 : ℕ) : ℝ) * δ := by
        push_cast
        linarith
      exact hle.trans_lt hlt
    simp only [z₀, mem_reProdIm, mem_Ico]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  set A : Finset (ℕ × ℕ) := {c ∈ grid | volume (planarSquare z₀ δ c ∩ K₁) ≠ 0}
  have hnonempty (c : ℕ × ℕ) (hc : c ∈ A) : (planarSquare z₀ δ c ∩ K₁).Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro hempty
    exact (Finset.mem_filter.mp hc).2 (by simp [hempty])
  let ζ : ℕ × ℕ → ℂ := fun c ↦ if hc : c ∈ A then (hnonempty c hc).some else 0
  have hζ (c : ℕ × ℕ) (hc : c ∈ A) : ζ c ∈ planarSquare z₀ δ c ∩ K₁ := by
    simpa [ζ, hc] using (hnonempty c hc).some_mem
  refine ⟨z₀, n, A, ζ, hcover_K₁, fun c ↦ Finset.mem_filter, hζ, ?_⟩
  intro E _ _ _ g
  have hsum_eq : (∑ c ∈ grid, volume.real (planarSquare z₀ δ c ∩ K₁) • g (ζ c)) =
      ∑ c ∈ A, volume.real (planarSquare z₀ δ c ∩ K₁) • g (ζ c) :=
    (sum_filter_measure_ne_zero_measureReal_smul volume grid
      (fun c ↦ planarSquare z₀ δ c ∩ K₁) ζ g).symm
  refine ⟨hsum_eq, fun {ε} hgi hosc ↦ ?_⟩
  rw [← hsum_eq]
  have hpart : (⋃ c ∈ grid, planarSquare z₀ δ c ∩ K₁) = K₁ := by
    rw [← iUnion₂_inter, inter_eq_right.mpr hcover_K₁]
  have hm (c : ℕ × ℕ) (_ : c ∈ grid) : MeasurableSet (planarSquare z₀ δ c ∩ K₁) :=
    (measurableSet_planarSquare z₀ δ c).inter hK₁.measurableSet
  have hd : Set.Pairwise (↑grid) (Disjoint on fun c ↦ planarSquare z₀ δ c ∩ K₁) :=
    ((pairwiseDisjoint_planarSquare z₀ hδ.le).mono fun _ _ h ↦
      h.mono inter_subset_left inter_subset_left).set_pairwise _
  exact norm_sum_measureReal_smul_sub_setIntegral_le hpart hm hd hK₁.measure_lt_top.ne hgi ζ
    fun c hc hμc z hz ↦ hosc c (Finset.mem_filter.mpr ⟨hc, hμc⟩) z hz

/-- **Quantitative uniform planar quadrature bound.** If `G : ℂ → X → E` has `G · ξ` integrable on
compact `K₁` for each `ξ ∈ K₂` and modulus of continuity at scale `√2 * δ` bounded by `ε` uniformly
in `ξ ∈ K₂`, the active planar square Riemann sum approximates `∫ z in K₁, G z ξ` within
`volume.real K₁ * ε` uniformly on `K₂`. -/
theorem exists_planarSquare_quadrature_le_of_oscillation {X E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {K₁ : Set ℂ} (hK₁ : IsCompact K₁) {K₂ : Set X}
    {G : ℂ → X → E} {δ ε : ℝ} (hδ : 0 < δ)
    (hint : ∀ ξ ∈ K₂, IntegrableOn (fun z ↦ G z ξ) K₁ volume)
    (hosc : ∀ z ∈ K₁, ∀ w ∈ K₁, ‖z - w‖ ≤ √2 * δ → ∀ ξ ∈ K₂, ‖G z ξ - G w ξ‖ ≤ ε) :
    ∃ (z₀ : ℂ) (n : ℕ) (A : Finset (ℕ × ℕ)) (ζ : ℕ × ℕ → ℂ),
      A ⊆ Finset.range n ×ˢ Finset.range n ∧
      (∀ c ∈ A, ζ c ∈ planarSquare z₀ δ c ∩ K₁) ∧
      ∀ ξ ∈ K₂,
        ‖(∑ c ∈ A, volume.real (planarSquare z₀ δ c ∩ K₁) • G (ζ c) ξ) -
          ∫ z in K₁, G z ξ‖ ≤ volume.real K₁ * ε := by
  obtain ⟨z₀, n, A, ζ, -, hA, hζ, hbound⟩ := exists_planarSquare_quadrature_of_isCompact hK₁ hδ
  refine ⟨z₀, n, A, ζ, fun c hc ↦ ((hA c).mp hc).1, hζ, fun ξ hξ ↦ ?_⟩
  refine (hbound (fun z ↦ G z ξ)).2 (hint ξ hξ) fun c hc z hz ↦ ?_
  have hζc := hζ c hc
  exact hosc (ζ c) hζc.2 z hz.2
    (norm_sub_le_sqrt_two_mul_of_mem_planarSquare hδ.le hζc.1 hz.1) ξ hξ

/-- **Uniform convergence of planar square Riemann sums on compact products.** Let `K₁ ⊆ ℂ` be
compact, `K₂ ⊆ X` be compact in a topological space `X`, and `G : ℂ → X → E` be jointly continuous
on `K₁ ×ˢ K₂` with values in a real Banach space `E`. For any mesh-indexed grids
`Finset.range (n δ) ×ˢ Finset.range (n δ)` with base corners `z₀ δ` and sample tags `ζ δ` that
eventually cover `K₁` and place tags of positive-measure intersections inside those intersections,
the planar square Riemann sums converge to `ξ ↦ ∫ z in K₁, G z ξ` uniformly for `ξ ∈ K₂` as
`δ → 0⁺`. -/
theorem tendstoUniformlyOn_sum_planarSquare_of_continuousOn {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {K₁ : Set ℂ} {K₂ : Set X}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) {G : ℂ → X → E}
    (hG : ContinuousOn (Function.uncurry G) (K₁ ×ˢ K₂))
    {z₀ : ℝ → ℂ} {n : ℝ → ℕ} {ζ : ℝ → ℕ × ℕ → ℂ}
    (hcover : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      K₁ ⊆ ⋃ c ∈ Finset.range (n δ) ×ˢ Finset.range (n δ), planarSquare (z₀ δ) δ c)
    (hζ : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ c ∈ Finset.range (n δ) ×ˢ Finset.range (n δ),
        volume (planarSquare (z₀ δ) δ c ∩ K₁) ≠ 0 → ζ δ c ∈ planarSquare (z₀ δ) δ c ∩ K₁) :
    TendstoUniformlyOn
      (fun δ ξ ↦ ∑ c ∈ Finset.range (n δ) ×ˢ Finset.range (n δ),
        volume.real (planarSquare (z₀ δ) δ c ∩ K₁) • G (ζ δ c) ξ)
      (fun ξ ↦ ∫ z in K₁, G z ξ) (𝓝[>] 0) K₂ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  set V : ℝ := max (volume.real K₁) 1
  have hV : 0 < V := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set ε : ℝ := η / (2 * V)
  have hε : 0 < ε := by positivity
  have hueq : UniformEquicontinuousOn (fun (ξ : K₂) z ↦ G z ξ) K₁ :=
    hK₁.uniformEquicontinuousOn_of_continuousOn_prod hK₂ hG
  rw [((Metric.uniformity_basis_dist_le.inf_principal (K₁ ×ˢ K₁)).uniformEquicontinuousOn_iff
    Metric.uniformity_basis_dist_le)] at hueq
  obtain ⟨r, hr, hrmod⟩ := hueq ε hε
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r / √2 by positivity), hcover, hζ] with
    δ ⟨hδ0, hδr⟩ hcovδ hζδ ξ hξ
  rw [dist_comm, dist_eq_norm]
  set grid : Finset (ℕ × ℕ) := Finset.range (n δ) ×ˢ Finset.range (n δ)
  have hpart : (⋃ c ∈ grid, planarSquare (z₀ δ) δ c ∩ K₁) = K₁ := by
    rw [← iUnion₂_inter, inter_eq_right.mpr hcovδ]
  have hm (c : ℕ × ℕ) (_ : c ∈ grid) : MeasurableSet (planarSquare (z₀ δ) δ c ∩ K₁) :=
    (measurableSet_planarSquare (z₀ δ) δ c).inter hK₁.measurableSet
  have hd : Set.Pairwise (↑grid) (Disjoint on fun c ↦ planarSquare (z₀ δ) δ c ∩ K₁) :=
    ((pairwiseDisjoint_planarSquare (z₀ δ) hδ0.le).mono fun _ _ h ↦
      h.mono inter_subset_left inter_subset_left).set_pairwise _
  have hint : IntegrableOn (fun z ↦ G z ξ) K₁ volume :=
    (hG.comp (continuousOn_id.prodMk continuousOn_const) fun z hz ↦ ⟨hz, hξ⟩).integrableOn_compact
      hK₁
  have hle : ‖(∑ c ∈ grid, volume.real (planarSquare (z₀ δ) δ c ∩ K₁) • G (ζ δ c) ξ) -
      ∫ z in K₁, G z ξ‖ ≤ volume.real K₁ * ε := by
    refine norm_sum_measureReal_smul_sub_setIntegral_le hpart hm hd hK₁.measure_lt_top.ne hint
      (ζ δ) fun c hc hμc z hz ↦ ?_
    have hζc := hζδ c hc hμc
    have hdist : dist (ζ δ c) z ≤ r := by
      rw [dist_eq_norm]
      calc
        ‖ζ δ c - z‖ ≤ √2 * δ := norm_sub_le_sqrt_two_mul_of_mem_planarSquare hδ0.le hζc.1 hz.1
        _ ≤ √2 * (r / √2) := mul_le_mul_of_nonneg_left hδr.le (Real.sqrt_nonneg _)
        _ = r := by
          have hs2 : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
          field_simp [hs2]
    simpa [dist_eq_norm] using hrmod (ζ δ c) z ⟨hdist, hζc.2, hz.2⟩ ⟨ξ, hξ⟩
  have hvol_le : volume.real K₁ * ε ≤ η / 2 := by
    calc
      volume.real K₁ * ε ≤ V * ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le
      _ = η / 2 := by
        dsimp [ε]
        field_simp [hV.ne']
  exact hle.trans_lt (hvol_le.trans_lt (half_lt_self hη))

/-- **Uniform planar Riemann-sum approximation on compact products.** Let `K₁ ⊆ ℂ` be compact,
`K₂ ⊆ X` be compact in a topological space `X`, and `G : ℂ → X → E` be jointly continuous on
`K₁ ×ˢ K₂` with values in a real Banach space `E`. For every `η > 0`, there exists `δ₀ > 0` such
that at every mesh `0 < δ ≤ δ₀`, an active finite square quadrature on `K₁` approximates
`∫ z in K₁, G z ξ` within `η` uniformly for all `ξ ∈ K₂`. -/
theorem exists_planarSquare_quadrature_lt_of_continuousOn {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {K₁ : Set ℂ} {K₂ : Set X}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) {G : ℂ → X → E}
    (hG : ContinuousOn (Function.uncurry G) (K₁ ×ˢ K₂)) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ > 0, ∀ {δ : ℝ}, 0 < δ → δ ≤ δ₀ →
      ∃ (z₀ : ℂ) (n : ℕ) (A : Finset (ℕ × ℕ)) (ζ : ℕ × ℕ → ℂ),
        A ⊆ Finset.range n ×ˢ Finset.range n ∧
        (∀ c ∈ A, ζ c ∈ planarSquare z₀ δ c ∩ K₁) ∧
        ∀ ξ ∈ K₂,
          ‖(∑ c ∈ A, volume.real (planarSquare z₀ δ c ∩ K₁) • G (ζ c) ξ) -
            ∫ z in K₁, G z ξ‖ < η := by
  set V : ℝ := max (volume.real K₁) 1
  have hV : 0 < V := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set ε : ℝ := η / (2 * V)
  have hε : 0 < ε := by positivity
  have hueq : UniformEquicontinuousOn (fun (ξ : K₂) z ↦ G z ξ) K₁ :=
    hK₁.uniformEquicontinuousOn_of_continuousOn_prod hK₂ hG
  rw [((Metric.uniformity_basis_dist_le.inf_principal (K₁ ×ˢ K₁)).uniformEquicontinuousOn_iff
    Metric.uniformity_basis_dist_le)] at hueq
  obtain ⟨r, hr, hrmod⟩ := hueq ε hε
  refine ⟨r / √2, by positivity, fun {δ} hδ hδle ↦ ?_⟩
  have hint (ξ : X) (hξ : ξ ∈ K₂) : IntegrableOn (fun z ↦ G z ξ) K₁ volume :=
    (hG.comp (continuousOn_id.prodMk continuousOn_const) fun z hz ↦ ⟨hz, hξ⟩).integrableOn_compact
      hK₁
  have hosc (z : ℂ) (hz : z ∈ K₁) (w : ℂ) (hw : w ∈ K₁) (hzw : ‖z - w‖ ≤ √2 * δ)
      (ξ : X) (hξ : ξ ∈ K₂) : ‖G z ξ - G w ξ‖ ≤ ε := by
    have hdist : dist z w ≤ r := by
      rw [dist_eq_norm]
      calc
        ‖z - w‖ ≤ √2 * δ := hzw
        _ ≤ √2 * (r / √2) := mul_le_mul_of_nonneg_left hδle (Real.sqrt_nonneg _)
        _ = r := by
          have hs2 : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
          field_simp [hs2]
    simpa [dist_eq_norm] using hrmod z w ⟨hdist, hz, hw⟩ ⟨ξ, hξ⟩
  obtain ⟨z₀, n, A, ζ, hA, hζ, hbound⟩ :=
    exists_planarSquare_quadrature_le_of_oscillation hK₁ hδ hint hosc
  have hvol_le : volume.real K₁ * ε ≤ η / 2 := by
    calc
      volume.real K₁ * ε ≤ V * ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le
      _ = η / 2 := by
        dsimp [ε]
        field_simp [hV.ne']
  exact ⟨z₀, n, A, ζ, hA, hζ,
    fun ξ hξ ↦ (hbound ξ hξ).trans_lt (hvol_le.trans_lt (half_lt_self hη))⟩

end PlanarSquare

end TauCeti
