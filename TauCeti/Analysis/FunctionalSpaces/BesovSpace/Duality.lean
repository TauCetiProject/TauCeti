/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.Holder

/-!
# The duality pairing of the Besov spaces `B^s_{p,q}` and `B^{-s}_{p',q'}`

Let `Δₖ` be the Littlewood–Paley blocks built from a bump function `φ`, let `p, p'` and `q, q'`
be pairs of Hölder conjugate exponents in `[1, ∞]`, and let `B : F →L[ℂ] G →L[ℂ] K` be a
continuous bilinear map, for instance the scalar multiplication of `F` or the evaluation pairing of
a fiber `F` with its dual. The **Besov duality pairing** of `u ∈ B^s_{p,q}(E, F)` and
`w ∈ B^{-s}_{p',q'}(E, G)` is

`⟨u, w⟩ = ∑ₖ ∫ B ((Δₖ u) x) ((Δ⁺ₖ w) x) dx`,  `Δ⁺ₖ = ∑_{k + 1 - L ≤ j < k + L} Δⱼ`,

where `L = φ.littlewoodPaleyOverlap` is the overlap of the partition: pieces whose indices differ
by at least `L` have disjoint supports, so that `Δ⁺ₖ Δₖ = Δₖ`
(`TemperedDistribution.littlewoodPaleyBlock_eq_sum_Ico_littlewoodPaleyBlock`).
Each term is bounded by Hölder's inequality in `Lᵖ × L^{p'}`, and after weighting the `k`-th
term by `2^{ks} 2^{-ks} = 1` the series is bounded by Hölder's inequality in `ℓ^q × ℓ^{q'}`
(Mathlib's `lp.dualPairing`). Hence `⟨·, ·⟩` is a continuous bilinear map with

`‖⟨u, w⟩‖ ≤ C ‖B‖ ‖u‖_{B^s_{p,q}} ‖w‖_{B^{-s}_{p',q'}}`,

where `C` depends only on `φ` and `s`, not on the exponents.

The pairing extends the action of tempered distributions on test functions, from either side. If
`w` is a scalar Schwartz function `ψ`, then `⟨u, w⟩ = u ψ` for the pairing `B v c = c • v`
(`TauCeti.BesovSpace.toDistr_apply_eq_besovPairing`). If `u` is a scalar Schwartz function `ψ`,
then `⟨u, w⟩ = w ψ` for the pairing `B c v = c • v`
(`TauCeti.BesovSpace.besovPairing_eq_toDistr_apply`). Both follow from the transpose identity
`(Δⱼ u) ψ = u (Δⱼ ψ)` for the even pieces of the partition
(`TemperedDistribution.littlewoodPaleyBlock_apply_apply`) and the reconstruction `u = ∑ₖ Δₖ u`.
For `F = G = K = ℂ` the pairing gives a bounded map from `B^{-s}_{p',q'}` to the continuous dual
of `B^s_{p,q}`, which is the half of the duality `(B^s_{p,q})* = B^{-s}_{p',q'}`, `p, q < ∞`, that
holds for all exponents.

## Main declarations

* `ContinuousLinearMap.besovPairing B φ s p p' q q'`: the duality pairing
  `B^s_{p,q}(E, F) × B^{-s}_{p',q'}(E, G) → K` induced by `B`, as a continuous bilinear map.
* `ContinuousLinearMap.hasSum_besovPairing` and `ContinuousLinearMap.besovPairing_apply`: the
  pairing is the sum of the series `∑ₖ ∑_{k + 1 - L ≤ j < k + L} ∫ B ((Δₖ u) x) ((Δⱼ w) x) dx`.
* `ContinuousLinearMap.exists_norm_besovPairing_le`: `‖⟨u, w⟩‖ ≤ C ‖B‖ ‖u‖ ‖w‖`, with `C`
  depending only on `φ` and `s`.
* `TauCeti.BesovSpace.toDistr_apply_eq_besovPairing` and
  `TauCeti.BesovSpace.besovPairing_eq_toDistr_apply`: on scalar Schwartz functions the pairing is
  the action of a tempered distribution.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, Section 2.11.2 (the dual of
  `B^s_{p,q}` is `B^{-s}_{p',q'}` for `1 ≤ p, q < ∞`).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976,
  Theorem 6.2.7.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Proposition 2.76.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap

variable {E F G K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-! ### The enlarged blocks -/

/-- The sum `Δ⁺ₖ w = ∑_{k + 1 - L ≤ j < k + L} Δⱼ w` of the blocks of `w` near `k`, as an `Lᵖ`
function. -/
private def enlargedBlock (w : BesovSpace G φ s p q) (k : ℕ) : Lp G p (volume : Measure E) :=
  ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap) (k + φ.littlewoodPaleyOverlap), w.block j

omit [Fact (1 ≤ q)] in
/-- The weighted enlarged block `2^{ks} Δ⁺ₖ w` is controlled by the weighted blocks of `w` of index
within `L` of `k`. -/
private theorem norm_smul_enlargedBlock_le (w : BesovSpace G φ s p q) (k : ℕ) :
    ‖(((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlock w k‖ ≤
      2 ^ (|s| * φ.littlewoodPaleyOverlap) * windowNorms φ.littlewoodPaleyOverlap w k := by
  rw [norm_smul, Complex.norm_of_nonneg (by positivity), windowNorms_apply, Finset.mul_sum]
  calc 2 ^ (s * k) * ‖enlargedBlock w k‖ ≤
        ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap) (k + φ.littlewoodPaleyOverlap),
          2 ^ (s * k) * ‖w.block j‖ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap) (k + φ.littlewoodPaleyOverlap),
          2 ^ (|s| * φ.littlewoodPaleyOverlap) * ‖w.weightedBlocks j‖ := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        rw [norm_weightedBlocks_apply, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [Finset.mem_Ico] at hj
        refine Real.rpow_mul_le_rpow_abs_mul_mul_rpow_mul one_le_two s (abs_sub_le_iff.2 ⟨?_, ?_⟩)
        all_goals rw [sub_le_iff_le_add']; exact_mod_cast (by omega)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico (by omega) le_rfl)
          fun _ _ _ ↦ by positivity

/-- The weighted enlarged blocks `(2^{ks} Δ⁺ₖ w)ₖ` of `w ∈ B^s_{p,q}`, an `ℓ^q` sequence of `Lᵖ`
functions. -/
private def enlargedWeightedBlocks (w : BesovSpace G φ s p q) :
    lp (fun _ : ℕ ↦ Lp G p (volume : Measure E)) q :=
  ⟨fun k ↦ (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlock w k,
    ((lp.memℓp (windowNorms φ.littlewoodPaleyOverlap w)).const_mul
      (2 ^ (|s| * φ.littlewoodPaleyOverlap))).mono fun k ↦ norm_smul_enlargedBlock_le w k⟩

omit [Fact (1 ≤ q)] in
private theorem enlargedWeightedBlocks_apply (w : BesovSpace G φ s p q) (k : ℕ) :
    enlargedWeightedBlocks w k = (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlock w k :=
  (rfl)

private theorem norm_enlargedWeightedBlocks_le (w : BesovSpace G φ s p q) :
    ‖enlargedWeightedBlocks w‖ ≤
      2 * φ.littlewoodPaleyOverlap * 2 ^ (|s| * φ.littlewoodPaleyOverlap) * ‖w‖ := by
  have hq : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  calc ‖enlargedWeightedBlocks w‖ ≤
        ‖(2 ^ (|s| * φ.littlewoodPaleyOverlap) : ℝ) • windowNorms φ.littlewoodPaleyOverlap w‖ :=
        lp.norm_mono hq fun k ↦ by
          rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, enlargedWeightedBlocks_apply,
            Real.norm_of_nonneg (by rw [windowNorms_apply]; positivity)]
          exact norm_smul_enlargedBlock_le w k
    _ = 2 ^ (|s| * φ.littlewoodPaleyOverlap) * ‖windowNorms φ.littlewoodPaleyOverlap w‖ := by
        rw [lp.norm_const_smul hq, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2 ^ (|s| * φ.littlewoodPaleyOverlap) * (2 * φ.littlewoodPaleyOverlap * ‖w‖) :=
        mul_le_mul_of_nonneg_left (norm_windowNorms_le _ w) (by positivity)
    _ = _ := by ring

variable (G φ s p q) in
/-- `w ↦ (2^{ks} Δ⁺ₖ w)ₖ` as a bounded operator from `B^s_{p,q}` to `ℓ^q(Lᵖ)`. -/
private def enlargedWeightedBlocksL :
    BesovSpace G φ s p q →L[ℂ] lp (fun _ : ℕ ↦ Lp G p (volume : Measure E)) q :=
  LinearMap.mkContinuous
    { toFun := enlargedWeightedBlocks
      map_add' v w := lp.ext <| funext fun k ↦ by
        simp only [enlargedWeightedBlocks_apply, enlargedBlock, block_add, Finset.sum_add_distrib,
          smul_add, lp.coeFn_add, Pi.add_apply]
      map_smul' c w := lp.ext <| funext fun k ↦ by
        simp only [enlargedWeightedBlocks_apply, enlargedBlock, block_smul, ← Finset.smul_sum,
          smul_comm _ c, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply] }
    (2 * φ.littlewoodPaleyOverlap * 2 ^ (|s| * φ.littlewoodPaleyOverlap))
    norm_enlargedWeightedBlocks_le

private theorem enlargedWeightedBlocksL_apply (w : BesovSpace G φ s p q) :
    enlargedWeightedBlocksL G φ s p q w = enlargedWeightedBlocks w :=
  (rfl)

end TauCeti.BesovSpace

/-! ### The pairing -/

namespace ContinuousLinearMap

open TauCeti TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')]
  [Fact (1 ≤ q)] [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q']

variable (φ s p p' q q') in
/-- The **Besov duality pairing** `⟨u, w⟩ = ∑ₖ ∫ B ((Δₖ u) x) ((Δ⁺ₖ w) x) dx` of
`u ∈ B^s_{p,q}(E, F)` and `w ∈ B^{-s}_{p',q'}(E, G)` for Hölder conjugate pairs `p, p'` and
`q, q'`, induced by a continuous bilinear map `B`. Here `Δ⁺ₖ` is the sum of the blocks `Δⱼ` with
`|j - k| < L`, where `L = φ.littlewoodPaleyOverlap` is the least `L` such that pieces of the
partition whose indices differ by at least `L` have disjoint supports; thus `Δ⁺ₖ Δₖ = Δₖ`
(`ContinuousLinearMap.besovPairing_apply`). On scalar Schwartz functions it is the action of a
tempered distribution (`TauCeti.BesovSpace.toDistr_apply_eq_besovPairing`,
`TauCeti.BesovSpace.besovPairing_eq_toDistr_apply`). -/
def besovPairing (B : F →L[ℂ] G →L[ℂ] K) :
    BesovSpace F φ s p q →L[ℂ] BesovSpace G φ (-s) p' q' →L[ℂ] K :=
  (lp.dualPairing q q' (fun _ : ℕ ↦ B.lpPairing volume p p') (K := ‖B.lpPairing volume p p'‖₊)
    fun _ ↦ le_rfl).bilinearComp
    (⟨weightedBlocksₗ F φ s p q, fun u ↦ by rw [weightedBlocksₗ_apply, norm_weightedBlocks]⟩ :
      BesovSpace F φ s p q →ₗᵢ[ℂ] _).toContinuousLinearMap
    (enlargedWeightedBlocksL G φ (-s) p' q')

/-- The pairing is the `ℓ^q × ℓ^{q'}` pairing of the weighted blocks `(2^{ks} Δₖ u)ₖ` and the
weighted enlarged blocks `(2^{-ks} Δ⁺ₖ w)ₖ`. -/
private theorem besovPairing_apply_eq_dualPairing (B : F →L[ℂ] G →L[ℂ] K)
    (u : BesovSpace F φ s p q) (w : BesovSpace G φ (-s) p' q') :
    B.besovPairing φ s p p' q q' u w =
      lp.dualPairing q q' (fun _ : ℕ ↦ B.lpPairing (volume : Measure E) p p')
        (K := ‖B.lpPairing (volume : Measure E) p p'‖₊) (fun _ ↦ le_rfl) u.weightedBlocks
        (enlargedWeightedBlocks w) := by
  rw [besovPairing, bilinearComp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.coe_mk, weightedBlocksₗ_apply, enlargedWeightedBlocksL_apply]

/-- The pairing is the sum over `k` of the pairings of the weighted blocks `2^{ks} Δₖ u` and
`2^{-ks} Δ⁺ₖ w`. -/
private theorem besovPairing_apply_eq_tsum_lpPairing (B : F →L[ℂ] G →L[ℂ] K)
    (u : BesovSpace F φ s p q) (w : BesovSpace G φ (-s) p' q') :
    B.besovPairing φ s p p' q q' u w =
      ∑' k, B.lpPairing volume p p' (u.weightedBlocks k) (enlargedWeightedBlocks w k) := by
  rw [besovPairing_apply_eq_dualPairing]
  exact lp.dualPairing_apply ..

omit [Fact (1 ≤ q)] [Fact (1 ≤ q')] in
/-- The terms of the pairing are summable: they form an `ℓ¹` sequence by Hölder's inequality in
`ℓ^q × ℓ^{q'}`. -/
private theorem summable_lpPairing (B : F →L[ℂ] G →L[ℂ] K) (u : BesovSpace F φ s p q)
    (w : BesovSpace G φ (-s) p' q') :
    Summable fun k ↦
      B.lpPairing volume p p' (u.weightedBlocks k) (enlargedWeightedBlocks w k) :=
  .of_norm (by
    simpa using (lp.holder (p := q) (q := q') 1 (fun _ : ℕ ↦ B.lpPairing volume p p')
      (K := ‖B.lpPairing volume p p'‖) (fun _ ↦ le_rfl) u.weightedBlocks
      (enlargedWeightedBlocks w)).2.summable (by simp))

omit [Fact (1 ≤ q)] [Fact (1 ≤ q')] [q.HolderConjugate q'] in
/-- The `k`-th term of the pairing is `∫ B ((Δₖ u) x) ((Δ⁺ₖ w) x) dx`: the weights `2^{ks}` and
`2^{-ks}` cancel. -/
private theorem lpPairing_weightedBlocks_enlargedWeightedBlocks (B : F →L[ℂ] G →L[ℂ] K)
    (u : BesovSpace F φ s p q) (w : BesovSpace G φ (-s) p' q') (k : ℕ) :
    B.lpPairing volume p p' (u.weightedBlocks k) (enlargedWeightedBlocks w k) =
      ∫ x, B (u.block k x) (enlargedBlock w k x) := by
  -- The weight `2^{-ks}` of `w` cancels the weight `2^{ks}` of `u`.
  have hweight : (((2 : ℝ) ^ (-s * k) : ℝ) : ℂ) * (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add two_pos]
    simp
  rw [weightedBlocks_apply, enlargedWeightedBlocks_apply, map_smul, map_smul, smul_apply,
    smul_smul, hweight, one_smul, lpPairing_eq_integral]

omit [Fact (1 ≤ q)] [Fact (1 ≤ q')] [q.HolderConjugate q'] in
/-- The `k`-th term `∫ B ((Δₖ u) x) ((Δ⁺ₖ w) x) dx` of the pairing is the sum of the integrals
`∫ B ((Δₖ u) x) ((Δⱼ w) x) dx` over the blocks `Δⱼ w` that make up `Δ⁺ₖ w`. -/
private theorem integral_enlargedBlock (B : F →L[ℂ] G →L[ℂ] K) (u : BesovSpace F φ s p q)
    (w : BesovSpace G φ (-s) p' q') (k : ℕ) :
    ∫ x, B (u.block k x) (enlargedBlock w k x) =
      ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap) (k + φ.littlewoodPaleyOverlap),
        ∫ x, B (u.block k x) (w.block j x) := by
  rw [← lpPairing_eq_integral (p := p) (q := p'), enlargedBlock, map_sum]
  simp only [lpPairing_eq_integral]

/-- **The pairing as a series.** The Besov pairing of `u` and `w` is the sum of the convergent
series `∑ₖ ∑_{k + 1 - L ≤ j < k + L} ∫ B ((Δₖ u) x) ((Δⱼ w) x) dx`, where
`L = φ.littlewoodPaleyOverlap` is the overlap of the partition. -/
theorem hasSum_besovPairing (B : F →L[ℂ] G →L[ℂ] K) (u : BesovSpace F φ s p q)
    (w : BesovSpace G φ (-s) p' q') :
    HasSum (fun k ↦
      ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap) (k + φ.littlewoodPaleyOverlap),
        ∫ x, B (u.block k x) (w.block j x)) (B.besovPairing φ s p p' q q' u w) := by
  rw [besovPairing_apply_eq_tsum_lpPairing]
  simpa only [lpPairing_weightedBlocks_enlargedWeightedBlocks, integral_enlargedBlock] using
    (summable_lpPairing B u w).hasSum

/-- The Besov pairing of `u` and `w` is
`∑ₖ ∑_{k + 1 - L ≤ j < k + L} ∫ B ((Δₖ u) x) ((Δⱼ w) x) dx`, where `L = φ.littlewoodPaleyOverlap`
is the overlap of the partition. -/
theorem besovPairing_apply (B : F →L[ℂ] G →L[ℂ] K) (u : BesovSpace F φ s p q)
    (w : BesovSpace G φ (-s) p' q') :
    B.besovPairing φ s p p' q q' u w =
      ∑' k, ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap) (k + φ.littlewoodPaleyOverlap),
        ∫ x, B (u.block k x) (w.block j x) :=
  (hasSum_besovPairing B u w).tsum_eq.symm

/-- **The pairing as a limit.** If the `k`-th term `∫ B ((Δₖ u) x) ((Δ⁺ₖ w) x) dx` of the pairing
is `a k` and the partial sums of `a` tend to `y`, then the pairing is `y`. -/
private theorem besovPairing_eq_of_tendsto (B : F →L[ℂ] G →L[ℂ] K) {u : BesovSpace F φ s p q}
    {w : BesovSpace G φ (-s) p' q'} {a : ℕ → K}
    (ha : ∀ k, ∫ x, B (u.block k x) (enlargedBlock w k x) = a k) {y : K}
    (hy : Tendsto (fun N ↦ ∑ k ∈ Finset.range N, a k) atTop (𝓝 y)) :
    B.besovPairing φ s p p' q q' u w = y := by
  refine tendsto_nhds_unique ?_ hy
  rw [besovPairing_apply_eq_tsum_lpPairing]
  simpa only [lpPairing_weightedBlocks_enlargedWeightedBlocks, ha] using
    (summable_lpPairing B u w).hasSum.tendsto_sum_nat

variable (φ s) in
/-- **Hölder's inequality for the Besov pairing.** There is `C`, depending only on `φ` and `s`, such
that `‖⟨u, w⟩‖ ≤ C ‖B‖ ‖u‖_{B^s_{p,q}} ‖w‖_{B^{-s}_{p',q'}}` for all Hölder conjugate pairs
`p, p'` and `q, q'`, every continuous bilinear map `B` and all `u` and `w`. -/
theorem exists_norm_besovPairing_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)]
      [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q'] (B : F →L[ℂ] G →L[ℂ] K)
      (u : BesovSpace F φ s p q) (w : BesovSpace G φ (-s) p' q'),
      ‖B.besovPairing φ s p p' q q' u w‖ ≤ C * ‖B‖ * ‖u‖ * ‖w‖ := by
  refine ⟨2 * φ.littlewoodPaleyOverlap * 2 ^ (|-s| * φ.littlewoodPaleyOverlap), by positivity,
    fun {p p' q q'} _ _ _ _ _ _ B u w ↦ ?_⟩
  set D := lp.dualPairing q q' (fun _ : ℕ ↦ B.lpPairing (volume : Measure E) p p')
    (K := ‖B.lpPairing (volume : Measure E) p p'‖₊) fun _ ↦ le_rfl
  have hD : ‖D‖ ≤ ‖B‖ := (lp.norm_dualPairing _ _).trans (norm_lpPairing_le B)
  calc ‖B.besovPairing φ s p p' q q' u w‖ = ‖D u.weightedBlocks (enlargedWeightedBlocks w)‖ := by
        rw [besovPairing_apply_eq_dualPairing]
    _ ≤ ‖D‖ * ‖u.weightedBlocks‖ * ‖enlargedWeightedBlocks w‖ := D.le_opNorm₂ _ _
    _ ≤ ‖B‖ * ‖u‖ *
          (2 * φ.littlewoodPaleyOverlap * 2 ^ (|-s| * φ.littlewoodPaleyOverlap) * ‖w‖) := by
        rw [norm_weightedBlocks]
        gcongr
        exact norm_enlargedWeightedBlocks_le w
    _ = _ := by ring

end ContinuousLinearMap

/-! ### The pairing extends the action of tempered distributions -/

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')]
  [Fact (1 ≤ q)] [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q']

omit [Fact (1 ≤ q)] in
/-- The `Lᵖ` block of an element of a Besov space whose distribution is a scalar Schwartz function
`ψ` is the Schwartz function `Δⱼ ψ`. -/
private theorem block_eq_toLp {u : BesovSpace ℂ φ s p q} {ψ : 𝓢(E, ℂ)}
    (hu : u.toDistr = (ψ : 𝓢'(E, ℂ))) (j : ℕ) :
    u.block j = (SchwartzMap.fourierMultiplierCLM ℂ
      (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) ψ).toLp p volume :=
  LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot <| by
    simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply, coe_block, hu,
      littlewoodPaleyBlock_toTemperedDistributionCLM_eq, Lp.toTemperedDistribution_toLp_eq]

omit [Fact (1 ≤ q)] in
/-- The enlarged block of an element of a Besov space whose distribution is a scalar Schwartz
function `ψ` is the Schwartz function `∑ⱼ Δⱼ ψ`. -/
private theorem enlargedBlock_eq_toLp {u : BesovSpace ℂ φ s p q} {ψ : 𝓢(E, ℂ)}
    (hu : u.toDistr = (ψ : 𝓢'(E, ℂ))) (k : ℕ) :
    enlargedBlock u k =
      (∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap) (k + φ.littlewoodPaleyOverlap),
        SchwartzMap.fourierMultiplierCLM ℂ
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) ψ).toLp p volume := by
  simp_rw [enlargedBlock, block_eq_toLp hu]
  exact (map_sum (SchwartzMap.toLpCLM ℂ ℂ p (volume : Measure E)) _ _).symm

/-- **The pairing extends distributions, acting on the right.** If `w ∈ B^{-s}_{p',q'}` is a scalar
Schwartz function `ψ`, then the Besov pairing of `u ∈ B^s_{p,q}(E, F)` with `w` for the scalar
multiplication `(v, c) ↦ c • v` is the action `u ψ` of the tempered distribution `u`. -/
theorem toDistr_apply_eq_besovPairing (u : BesovSpace F φ s p q)
    {w : BesovSpace ℂ φ (-s) p' q'} {ψ : 𝓢(E, ℂ)} (hw : w.toDistr = (ψ : 𝓢'(E, ℂ))) :
    u.toDistr ψ =
      (ContinuousLinearMap.lsmul ℂ ℂ).flip.besovPairing φ s p p' q q' u w := by
  refine ((ContinuousLinearMap.lsmul ℂ ℂ).flip.besovPairing_eq_of_tendsto (fun k ↦ ?_)
    (tendsto_sum_littlewoodPaleyBlock_apply φ u.toDistr ψ)).symm
  -- Move the enlarged block onto the distribution: it reproduces `Δₖ u`.
  calc ∫ x, (ContinuousLinearMap.lsmul ℂ ℂ).flip (u.block k x) (enlargedBlock w k x) =
        ∫ x, (∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap) (k + φ.littlewoodPaleyOverlap),
          SchwartzMap.fourierMultiplierCLM ℂ
            (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) ψ) x • u.block k x := by
        refine integral_congr_ae ?_
        filter_upwards [(enlargedBlock_eq_toLp hw k).symm ▸ SchwartzMap.coeFn_toLp _ p' volume]
          with x hx
        simp [hx, Finset.sum_smul]
    _ = ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap) (k + φ.littlewoodPaleyOverlap),
          littlewoodPaleyBlock F φ j (littlewoodPaleyBlock F φ k u.toDistr) ψ := by
        rw [← Lp.toTemperedDistribution_apply, coe_block, map_sum]
        simp only [littlewoodPaleyBlock_apply_apply]
    _ = littlewoodPaleyBlock F φ k u.toDistr ψ := by
        rw [← sum_apply, ← littlewoodPaleyBlock_eq_sum_Ico_littlewoodPaleyBlock φ
          φ.inhomogeneousLittlewoodPaley_mul_eq_zero_of_add_littlewoodPaleyOverlap_le]

/-- **The pairing extends distributions, acting on the left.** If `u ∈ B^s_{p,q}` is a scalar
Schwartz function `ψ`, then the Besov pairing of `u` with `w ∈ B^{-s}_{p',q'}(E, G)` for the scalar
multiplication `(c, v) ↦ c • v` is the action `w ψ` of the tempered distribution `w`. -/
theorem besovPairing_eq_toDistr_apply {u : BesovSpace ℂ φ s p q} {ψ : 𝓢(E, ℂ)}
    (hu : u.toDistr = (ψ : 𝓢'(E, ℂ))) (w : BesovSpace G φ (-s) p' q') :
    (ContinuousLinearMap.lsmul ℂ ℂ).besovPairing φ s p p' q q' u w = w.toDistr ψ := by
  refine (ContinuousLinearMap.lsmul ℂ ℂ).besovPairing_eq_of_tendsto (fun k ↦ ?_)
    (tendsto_sum_littlewoodPaleyBlock_apply φ w.toDistr ψ)
  set ψₖ := SchwartzMap.fourierMultiplierCLM ℂ
    (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley k ξ : ℂ)) ψ
  -- Move the block `Δₖ` onto the enlarged block of `w`, which it reproduces.
  calc ∫ x, ContinuousLinearMap.lsmul ℂ ℂ (u.block k x) (enlargedBlock w k x) =
        ∫ x, ψₖ x • enlargedBlock w k x := by
        refine integral_congr_ae ?_
        filter_upwards [(block_eq_toLp hu k).symm ▸ SchwartzMap.coeFn_toLp _ p volume] with x hx
        simp [hx, ψₖ]
    _ = ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap) (k + φ.littlewoodPaleyOverlap),
          littlewoodPaleyBlock G φ j (littlewoodPaleyBlock G φ k w.toDistr) ψ := by
        rw [← Lp.toTemperedDistribution_apply, enlargedBlock, Lp.toTemperedDistribution_sum]
        simp only [coe_block, sum_apply, ψₖ, ← littlewoodPaleyBlock_apply_apply,
          littlewoodPaleyBlock_comm φ k]
    _ = littlewoodPaleyBlock G φ k w.toDistr ψ := by
        rw [← sum_apply, ← littlewoodPaleyBlock_eq_sum_Ico_littlewoodPaleyBlock φ
          φ.inhomogeneousLittlewoodPaley_mul_eq_zero_of_add_littlewoodPaleyOverlap_le]

end TauCeti.BesovSpace
