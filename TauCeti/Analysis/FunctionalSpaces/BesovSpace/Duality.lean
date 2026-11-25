/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.Holder

/-!
# The duality pairing of the Besov spaces `B^s_{p,q}` and `B^{-s}_{p',q'}`

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space, with
inhomogeneous Littlewood–Paley blocks `Δⱼ`, let `p, p'` and `q, q'` be pairs of Hölder conjugate
exponents in `[1, ∞]`, and let `B : F →L[ℂ] G →L[ℂ] K` be a continuous bilinear map, for instance
the scalar multiplication of `F` or the evaluation pairing of a fiber `F` with its dual. The
**Besov duality pairing** of `u ∈ B^s_{p,q}(E, F)` and `w ∈ B^{-s}_{p',q'}(E, G)` is

`⟨u, w⟩ = ∑ₖ ∫ B ((Δₖ u) x) ((Δ⁺ₖ w) x) dx`,  `Δ⁺ₖ = ∑_{k + 1 - L ≤ j < k + L} Δⱼ`,

where `L = φ.littlewoodPaleyOverlap φ` is the overlap of the partition: pieces whose indices differ
by at least `L` have disjoint supports, so that `Δ⁺ₖ Δₖ = Δₖ`
(`TemperedDistribution.enlargedLittlewoodPaleyBlock_littlewoodPaleyBlock`). Smoothness `s` is
paired with smoothness `-s`, and the integrability and fine indices with their conjugates.

Each term is bounded by Hölder's inequality in `Lᵖ × L^{p'}`, and after weighting the `k`-th
term by `2^{ks} 2^{-ks} = 1` the series is bounded by Hölder's inequality in `ℓ^q × ℓ^{q'}`
(Mathlib's `lp.dualPairing`). Hence `⟨·, ·⟩` is a continuous bilinear map with

`‖⟨u, w⟩‖ ≤ C ‖B‖ ‖u‖_{B^s_{p,q}} ‖w‖_{B^{-s}_{p',q'}}`,

where `C` is independent of the exponents, of `B` and of `u, w`. The double series
`∑ₖ ∑_{|j - k| < L} ∫ B ((Δₖ u) x) ((Δⱼ w) x) dx` converges absolutely, so the pairing is symmetric:
pairing `w` with `u` through the flipped map `(w, u) ↦ B u w` gives `⟨u, w⟩`.

The pairing extends the action of tempered distributions on test functions, from either side. If
`w` is a scalar Schwartz function `ψ`, then `⟨u, w⟩ = u ψ` for the pairing `B v c = c • v`
(`TauCeti.BesovSpace.toDistr_apply_eq_besovPairing`). If `u` is a scalar Schwartz function `ψ`,
then `⟨u, w⟩ = w ψ` for the pairing `B c v = c • v`
(`TauCeti.BesovSpace.besovPairing_eq_toDistr_apply`). The first follows from the symmetry
`(Δⱼ u) ψ = u (Δⱼ ψ)` of the blocks, whose pieces are even
(`TemperedDistribution.littlewoodPaleyBlock_apply_apply`), and the reconstruction `u = ∑ₖ Δₖ u`;
the second follows from the first by the symmetry of the pairing.

In particular an element `v` of `B^{-s}_{p',q'}`, with values in any complex Banach space, acts
boundedly on the Schwartz functions for the norm of `B^s_{p,q}`: there is a constant `C`,
depending only on `φ` and `s`, with `‖⟨v, f⟩‖ ≤ C ‖v‖_{B^{-s}_{p',q'}} ‖f‖_{B^s_{p,q}}` for every
Schwartz function `f` (`TauCeti.BesovSpace.exists_norm_toDistr_apply_le`). For `F = G = K = ℂ` the
pairing gives a bounded map from `B^{-s}_{p',q'}` to the continuous dual of `B^s_{p,q}`, which is
the half of the duality `(B^s_{p,q})* = B^{-s}_{p',q'}`, `p, q < ∞`, that holds for all exponents.

## Main declarations

* `ContinuousLinearMap.besovPairing B φ s p p' q q'`: the duality pairing
  `B^s_{p,q}(E, F) × B^{-s}_{p',q'}(E, G) → K` induced by `B`, as a continuous bilinear map.
* `ContinuousLinearMap.hasSum_besovPairing` and `ContinuousLinearMap.besovPairing_apply`: the
  pairing is the sum of the series `∑ₖ ∑_{k + 1 - L ≤ j < k + L} ∫ B ((Δₖ u) x) ((Δⱼ w) x) dx`.
* `ContinuousLinearMap.exists_norm_besovPairing_le`: `‖⟨u, w⟩‖ ≤ C ‖B‖ ‖u‖ ‖w‖`, with `C`
  independent of the exponents, of `B` and of `u, w`.
* `ContinuousLinearMap.besovPairing_flip_apply`: the pairing through `B.flip` at smoothness `-s`
  and swapped exponents is the pairing through `B` with its arguments swapped.
* `TauCeti.BesovSpace.toDistr_apply_eq_besovPairing` and
  `TauCeti.BesovSpace.besovPairing_eq_toDistr_apply`: on scalar Schwartz functions the pairing is
  the action of a tempered distribution; `TauCeti.BesovSpace.besovPairing_toBesovSpaceCLM_left`
  and `TauCeti.BesovSpace.besovPairing_toBesovSpaceCLM_right` are their `simp` forms for the
  canonical inclusion `SchwartzMap.toBesovSpaceCLM`.
* `TauCeti.BesovSpace.exists_norm_toDistr_apply_le`: the duality bound
  `‖⟨v, f⟩‖ ≤ C ‖v‖_{B^{-s}_{p',q'}} ‖f‖_{B^s_{p,q}}`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Proposition 2.76.
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, Section 2.11.2 (the dual of
  `B^s_{p,q}` is `B^{-s}_{p',q'}` for `1 ≤ p, q < ∞`).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976,
  Theorem 6.2.7.
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
  ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ), w.block j

omit [Fact (1 ≤ q)] in
/-- The weighted sum `2^{ks} ∑_{k + 1 - L ≤ j < k + L} ‖Δⱼ w‖` of the norms of the blocks of `w`
near `k` is controlled by the weighted blocks of `w` of index within `L` of `k`. -/
private theorem mul_sum_norm_block_le (w : BesovSpace G φ s p q) (k : ℕ) :
    2 ^ (s * k) * ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ)
        (k + φ.littlewoodPaleyOverlap φ), ‖w.block j‖ ≤
      2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * ∑ j ∈ Finset.Ico (k - φ.littlewoodPaleyOverlap φ)
        (k + φ.littlewoodPaleyOverlap φ), w.weightedBlockNorms j := by
  have hsub : Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ) ⊆
      Finset.Ico (k - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ) :=
    Finset.Ico_subset_Ico (by omega) le_rfl
  rw [Finset.mul_sum, Finset.mul_sum]
  refine (Finset.sum_le_sum fun j hj ↦ ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    fun j _ _ ↦ by rw [weightedBlockNorms_apply]; positivity)
  rw [weightedBlockNorms_apply, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_mul_natCast_le_of_mem_Ico' one_le_two s (hsub hj)) (norm_nonneg _)

omit [Fact (1 ≤ q)] in
/-- The weighted enlarged block `2^{ks} Δ⁺ₖ w` is controlled by the weighted blocks of `w` of index
within `L` of `k`. -/
private theorem norm_smul_enlargedBlock_le (w : BesovSpace G φ s p q) (k : ℕ) :
    ‖(((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlock w k‖ ≤
      2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * ∑ j ∈ Finset.Ico (k - φ.littlewoodPaleyOverlap φ)
        (k + φ.littlewoodPaleyOverlap φ), w.weightedBlockNorms j := by
  rw [norm_smul, Complex.norm_of_nonneg (by positivity), enlargedBlock]
  exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans
    (mul_sum_norm_block_le w k)

/-- The weighted enlarged blocks `(2^{ks} Δ⁺ₖ w)ₖ` of `w ∈ B^s_{p,q}`, an `ℓ^q` sequence of `Lᵖ`
functions. -/
private def enlargedWeightedBlocks (w : BesovSpace G φ s p q) :
    lp (fun _ : ℕ ↦ Lp G p (volume : Measure E)) q :=
  ⟨fun k ↦ (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlock w k,
    (((lp.memℓp w.weightedBlockNorms).sum_Ico_sub_add (φ.littlewoodPaleyOverlap φ)).const_mul
      (2 ^ (|s| * φ.littlewoodPaleyOverlap φ))).mono fun k ↦ norm_smul_enlargedBlock_le w k⟩

omit [Fact (1 ≤ q)] in
private theorem enlargedWeightedBlocks_apply (w : BesovSpace G φ s p q) (k : ℕ) :
    enlargedWeightedBlocks w k = (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlock w k :=
  (rfl)

private theorem norm_enlargedWeightedBlocks_le (w : BesovSpace G φ s p q) :
    ‖enlargedWeightedBlocks w‖ ≤
      2 * φ.littlewoodPaleyOverlap φ * 2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * ‖w‖ := by
  have hq : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  -- The window sums of the weighted block norms of `w`, as an element of `ℓ^q`.
  obtain ⟨b, hb, hbn⟩ :=
    lp.exists_eq_sum_Ico_sub_add_and_norm_le w.weightedBlockNorms (φ.littlewoodPaleyOverlap φ)
  calc ‖enlargedWeightedBlocks w‖ ≤ ‖(2 ^ (|s| * φ.littlewoodPaleyOverlap φ) : ℝ) • b‖ :=
        lp.norm_mono hq fun k ↦ by
          rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, enlargedWeightedBlocks_apply, hb,
            Real.norm_of_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ ↦ by
              rw [weightedBlockNorms_apply]; positivity))]
          exact norm_smul_enlargedBlock_le w k
    _ = 2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * ‖b‖ := by
        rw [lp.norm_const_smul hq, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * (2 * φ.littlewoodPaleyOverlap φ * ‖w‖) := by
        rw [← norm_weightedBlockNorms w]
        gcongr
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
    (2 * φ.littlewoodPaleyOverlap φ * 2 ^ (|s| * φ.littlewoodPaleyOverlap φ))
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
`|j - k| < L`, where `L = φ.littlewoodPaleyOverlap φ` is a width such that pieces of the
partition whose indices differ by at least `L` have disjoint supports
(`ContDiffBump.inhomogeneousLittlewoodPaley_mul_eq_zero`); thus `Δ⁺ₖ Δₖ = Δₖ`
(`TemperedDistribution.enlargedLittlewoodPaleyBlock_littlewoodPaleyBlock`). The pairing is the
sum of the series `∑ₖ ∑_{|j - k| < L} ∫ B ((Δₖ u) x) ((Δⱼ w) x) dx`
(`ContinuousLinearMap.besovPairing_apply`). On scalar Schwartz functions it is the action of a
tempered distribution (`TauCeti.BesovSpace.toDistr_apply_eq_besovPairing`,
`TauCeti.BesovSpace.besovPairing_eq_toDistr_apply`). -/
def besovPairing (B : F →L[ℂ] G →L[ℂ] K) :
    BesovSpace F φ s p q →L[ℂ] BesovSpace G φ (-s) p' q' →L[ℂ] K :=
  (lp.dualPairing q q' (fun _ : ℕ ↦ B.lpPairing volume p p') (K := ‖B.lpPairing volume p p'‖₊)
    fun _ ↦ le_rfl).bilinearComp
    (weightedBlocksₗᵢ F φ s p q).toContinuousLinearMap
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
    weightedBlocksₗᵢ_apply, enlargedWeightedBlocksL_apply]

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
  ((lp.memℓp u.weightedBlocks).holder 1 (lp.memℓp (enlargedWeightedBlocks w))
    (fun _ : ℕ ↦ B.lpPairing volume p p') (K := ‖B.lpPairing volume p p'‖)
    fun _ ↦ le_rfl).summable_of_one

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
      ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ),
        ∫ x, B (u.block k x) (w.block j x) := by
  rw [← lpPairing_eq_integral (p := p) (q := p'), enlargedBlock, map_sum]
  simp only [lpPairing_eq_integral]

/-- **The pairing as a series.** The Besov pairing of `u` and `w` is the sum of the convergent
series `∑ₖ ∑_{k + 1 - L ≤ j < k + L} ∫ B ((Δₖ u) x) ((Δⱼ w) x) dx`, where
`L = φ.littlewoodPaleyOverlap φ` is the overlap of the partition. -/
theorem hasSum_besovPairing (B : F →L[ℂ] G →L[ℂ] K) (u : BesovSpace F φ s p q)
    (w : BesovSpace G φ (-s) p' q') :
    HasSum (fun k ↦
      ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ),
        ∫ x, B (u.block k x) (w.block j x)) (B.besovPairing φ s p p' q q' u w) := by
  rw [besovPairing_apply_eq_tsum_lpPairing]
  simpa only [lpPairing_weightedBlocks_enlargedWeightedBlocks, integral_enlargedBlock] using
    (summable_lpPairing B u w).hasSum

/-- The Besov pairing of `u` and `w` is
`∑ₖ ∑_{k + 1 - L ≤ j < k + L} ∫ B ((Δₖ u) x) ((Δⱼ w) x) dx`, where `L = φ.littlewoodPaleyOverlap φ`
is the overlap of the partition. -/
theorem besovPairing_apply (B : F →L[ℂ] G →L[ℂ] K) (u : BesovSpace F φ s p q)
    (w : BesovSpace G φ (-s) p' q') :
    B.besovPairing φ s p p' q q' u w =
      ∑' k, ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ),
        ∫ x, B (u.block k x) (w.block j x) :=
  (hasSum_besovPairing B u w).tsum_eq.symm

omit [Fact (1 ≤ q)] [Fact (1 ≤ q')] in
/-- The integrals `∫ B ((Δₖ u) x) ((Δⱼ w) x) dx` over the pairs `(k, j)` with
`k + 1 - L ≤ j < k + L` form a summable family: they are bounded by
`‖B‖ 2^{|s| L} (2^{ks} ‖Δₖ u‖) ∑_{k - L ≤ i < k + L} 2^{-is} ‖Δᵢ w‖`, an `ℓ¹` sequence by
Hölder's inequality in `ℓ^q × ℓ^{q'}`. -/
private theorem summable_integral_block (B : F →L[ℂ] G →L[ℂ] K) (u : BesovSpace F φ s p q)
    (w : BesovSpace G φ (-s) p' q') :
    Summable fun x : ℕ × ℕ ↦
      if x.2 ∈ Finset.Ico (x.1 + 1 - φ.littlewoodPaleyOverlap φ) (x.1 + φ.littlewoodPaleyOverlap φ)
      then ∫ y, B (u.block x.1 y) (w.block x.2 y) else 0 := by
  set L := φ.littlewoodPaleyOverlap φ
  have hub : Summable fun k ↦
      u.weightedBlockNorms k * ∑ j ∈ Finset.Ico (k - L) (k + L), w.weightedBlockNorms j :=
    ((lp.memℓp u.weightedBlockNorms).holder 1 ((lp.memℓp w.weightedBlockNorms).sum_Ico_sub_add L)
      (fun _ ↦ ContinuousLinearMap.mul ℝ ℝ)
      fun _ ↦ ContinuousLinearMap.opNorm_mul_le ℝ ℝ).summable_of_one
  refine .of_norm_bounded (g := fun x ↦ if x.2 ∈ Finset.Ico (x.1 + 1 - L) (x.1 + L)
    then ‖B‖ * (‖u.block x.1‖ * ‖w.block x.2‖) else 0) ?_ fun x ↦ ?_
  · refine (summable_prod_of_nonneg fun x ↦ by dsimp only; split_ifs <;> positivity).2
      ⟨fun k ↦ summable_of_ne_finset_zero (s := Finset.Ico (k + 1 - L) (k + L))
          fun j hj ↦ ite_eq_right hj,
        .of_nonneg_of_le (fun k ↦ tsum_nonneg fun j ↦ by dsimp only; split_ifs <;> positivity)
          (fun k ↦ ?_) (hub.mul_left (‖B‖ * 2 ^ (|-s| * L)))⟩
    rw [tsum_eq_sum (s := Finset.Ico (k + 1 - L) (k + L)) fun j hj ↦ ite_eq_right hj,
      Finset.sum_ite_of_true fun j hj ↦ hj]
    simp only [← Finset.mul_sum]
    -- Split `‖Δₖ u‖ = 2^{ks} ‖Δₖ u‖ ⬝ 2^{-ks}` and bound the second factor by the window sum.
    have hweight : (2 : ℝ) ^ (s * k) * 2 ^ (-s * k) = 1 := by
      rw [← Real.rpow_add two_pos]
      simp
    calc ‖B‖ * (‖u.block k‖ * ∑ j ∈ Finset.Ico (k + 1 - L) (k + L), ‖w.block j‖) =
          ‖B‖ * u.weightedBlockNorms k *
            (2 ^ (-s * k) * ∑ j ∈ Finset.Ico (k + 1 - L) (k + L), ‖w.block j‖) := by
          rw [weightedBlockNorms_apply]
          linear_combination (‖B‖ * ‖u.block k‖ *
            ∑ j ∈ Finset.Ico (k + 1 - L) (k + L), ‖w.block j‖) * hweight.symm
      _ ≤ ‖B‖ * u.weightedBlockNorms k *
            (2 ^ (|-s| * L) * ∑ j ∈ Finset.Ico (k - L) (k + L), w.weightedBlockNorms j) := by
          refine mul_le_mul_of_nonneg_left (mul_sum_norm_block_le w k) ?_
          rw [weightedBlockNorms_apply]
          positivity
      _ = _ := by ring
  · split_ifs
    · rw [← lpPairing_eq_integral (p := p) (q := p'), ← mul_assoc]
      exact norm_lpPairing_apply_apply_le B _ _
    · simp

/-- **The flipped pairing.** Pairing `w ∈ B^{-s}_{p',q'}` with `u ∈ B^s_{p,q}` through the flipped
bilinear map `(w, u) ↦ B u w` is the pairing of `u` with `w` through `B`. Here `u'` is `u` viewed as
an element of `B^{-(-s)}_{p,q}`, that is, any element with the same distribution as `u`. -/
theorem besovPairing_flip_apply (B : F →L[ℂ] G →L[ℂ] K) (u : BesovSpace F φ s p q)
    (w : BesovSpace G φ (-s) p' q') {u' : BesovSpace F φ (-(-s)) p q}
    (hu : u'.toDistr = u.toDistr) :
    B.flip.besovPairing φ (-s) p' p q' q w u' = B.besovPairing φ s p p' q q' u w := by
  set L := φ.littlewoodPaleyOverlap φ
  -- Both series sum the same summable family over the pairs `|j - k| < L`, in swapped order.
  simp only [besovPairing_apply, sum_eq_tsum_indicator _ _ (.unconditional ℕ), Set.indicator_apply,
    Finset.mem_coe]
  refine .trans (tsum_congr fun k ↦ tsum_congr fun j ↦ ?_)
    ((summable_integral_block B u w).tsum_comm (f := fun k j ↦
      if j ∈ Finset.Ico (k + 1 - L) (k + L) then ∫ y, B (u.block k y) (w.block j y) else 0))
  simp only [flip_apply, block_eq_of_toDistr_eq hu]
  exact if_congr (by simp only [Finset.mem_Ico]; omega) rfl rfl

/-- **The pairing as a limit.** If the `k`-th term `∫ B ((Δₖ u) x) ((Δ⁺ₖ w) x) dx` of the pairing
is `a k` and the partial sums of `a` tend to `y`, then the pairing is `y`. -/
private theorem besovPairing_eq_of_tendsto (B : F →L[ℂ] G →L[ℂ] K) {u : BesovSpace F φ s p q}
    {w : BesovSpace G φ (-s) p' q'} {a : ℕ → K}
    (ha : ∀ k, ∫ x, B (u.block k x) (enlargedBlock w k x) = a k) {y : K}
    (hy : Tendsto (fun N ↦ ∑ k ∈ Finset.range N, a k) atTop (𝓝 y)) :
    B.besovPairing φ s p p' q q' u w = y :=
  tendsto_nhds_unique (by simpa only [← integral_enlargedBlock, ha] using
    (hasSum_besovPairing B u w).tendsto_sum_nat) hy

variable (φ s) in
/-- **Hölder's inequality for the Besov pairing.** There is `C`, independent of the exponents, of
`B` and of `u, w`, such that `‖⟨u, w⟩‖ ≤ C ‖B‖ ‖u‖_{B^s_{p,q}} ‖w‖_{B^{-s}_{p',q'}}` for all
Hölder conjugate pairs `p, p'` and `q, q'`, every continuous bilinear map `B` and all `u` and
`w`. -/
theorem exists_norm_besovPairing_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)]
      [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q'] (B : F →L[ℂ] G →L[ℂ] K)
      (u : BesovSpace F φ s p q) (w : BesovSpace G φ (-s) p' q'),
      ‖B.besovPairing φ s p p' q q' u w‖ ≤ C * ‖B‖ * ‖u‖ * ‖w‖ := by
  refine ⟨2 * φ.littlewoodPaleyOverlap φ * 2 ^ (|-s| * φ.littlewoodPaleyOverlap φ), by positivity,
    fun {p p' q q'} _ _ _ _ _ _ B u w ↦ ?_⟩
  set D := lp.dualPairing q q' (fun _ : ℕ ↦ B.lpPairing (volume : Measure E) p p')
    (K := ‖B.lpPairing (volume : Measure E) p p'‖₊) fun _ ↦ le_rfl
  have hD : ‖D‖ ≤ ‖B‖ := (lp.norm_dualPairing _ _).trans (norm_lpPairing_le B)
  calc ‖B.besovPairing φ s p p' q q' u w‖ = ‖D u.weightedBlocks (enlargedWeightedBlocks w)‖ := by
        rw [besovPairing_apply_eq_dualPairing]
    _ ≤ ‖D‖ * ‖u.weightedBlocks‖ * ‖enlargedWeightedBlocks w‖ := D.le_opNorm₂ _ _
    _ ≤ ‖B‖ * ‖u‖ *
          (2 * φ.littlewoodPaleyOverlap φ * 2 ^ (|-s| * φ.littlewoodPaleyOverlap φ) * ‖w‖) := by
        rw [norm_weightedBlocks]
        gcongr
        exact norm_enlargedWeightedBlocks_le w
    _ = _ := by ring

end ContinuousLinearMap

/-! ### The pairing extends the action of tempered distributions -/

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')]
  [Fact (1 ≤ q)] [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q']

/-- The `Lᵖ` block of an element of a Besov space whose distribution is a scalar Schwartz function
`ψ` is the Schwartz function `Δⱼ ψ`. -/
private theorem block_eq_toLp {u : BesovSpace ℂ φ s p q} {ψ : 𝓢(E, ℂ)}
    (hu : u.toDistr = (ψ : 𝓢'(E, ℂ))) (j : ℕ) :
    u.block j = (SchwartzMap.fourierMultiplierCLM ℂ
      (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) ψ).toLp p volume :=
  (block_eq_of_toDistr_eq (hu.trans (SchwartzMap.toDistr_toBesovSpaceCLM φ s p q ψ).symm) j).trans
    (block_toBesovSpaceCLM ψ j)

/-- The enlarged block of an element of a Besov space whose distribution is a scalar Schwartz
function `ψ` is the Schwartz function `∑ⱼ Δⱼ ψ`. -/
private theorem enlargedBlock_eq_toLp {u : BesovSpace ℂ φ s p q} {ψ : 𝓢(E, ℂ)}
    (hu : u.toDistr = (ψ : 𝓢'(E, ℂ))) (k : ℕ) :
    enlargedBlock u k =
      (∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ),
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
        ∫ x, (∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ)
            (k + φ.littlewoodPaleyOverlap φ), SchwartzMap.fourierMultiplierCLM ℂ
            (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) ψ) x • u.block k x := by
        refine integral_congr_ae ?_
        filter_upwards [(enlargedBlock_eq_toLp hw k).symm ▸ SchwartzMap.coeFn_toLp _ p' volume]
          with x hx
        simp [hx, Finset.sum_smul]
    _ = ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ),
          littlewoodPaleyBlock F φ j (littlewoodPaleyBlock F φ k u.toDistr) ψ := by
        rw [← Lp.toTemperedDistribution_apply, coe_block, map_sum]
        simp only [littlewoodPaleyBlock_apply_apply]
    _ = littlewoodPaleyBlock F φ k u.toDistr ψ := by
        rw [← sum_apply, ← sum_apply, ← enlargedLittlewoodPaleyBlock_eq_sum_Ico,
          enlargedLittlewoodPaleyBlock_littlewoodPaleyBlock φ
            fun _ _ hjk ξ ↦ φ.inhomogeneousLittlewoodPaley_mul_eq_zero φ hjk ξ]

/-- **The pairing extends distributions, acting on the left.** If `u ∈ B^s_{p,q}` is a scalar
Schwartz function `ψ`, then the Besov pairing of `u` with `w ∈ B^{-s}_{p',q'}(E, G)` for the scalar
multiplication `(c, v) ↦ c • v` is the action `w ψ` of the tempered distribution `w`. -/
theorem besovPairing_eq_toDistr_apply {u : BesovSpace ℂ φ s p q} {ψ : 𝓢(E, ℂ)}
    (hu : u.toDistr = (ψ : 𝓢'(E, ℂ))) (w : BesovSpace G φ (-s) p' q') :
    (ContinuousLinearMap.lsmul ℂ ℂ).besovPairing φ s p p' q q' u w = w.toDistr ψ := by
  -- Pair `w` with `ψ`, viewed in `B^{-(-s)}_{p,q}`, through the flipped multiplication.
  have hψ := SchwartzMap.toDistr_toBesovSpaceCLM φ (-(-s)) p q ψ
  rw [← (ContinuousLinearMap.lsmul ℂ ℂ).besovPairing_flip_apply u w (hψ.trans hu.symm)]
  exact (toDistr_apply_eq_besovPairing w hψ).symm

/-- The pairing of a scalar Schwartz function `ψ ∈ B^s_{p,q}` with `w ∈ B^{-s}_{p',q'}(E, G)` for
the scalar multiplication `(c, v) ↦ c • v` is the action `w ψ` of the tempered distribution `w`. -/
@[simp]
theorem besovPairing_toBesovSpaceCLM_left (ψ : 𝓢(E, ℂ)) (w : BesovSpace G φ (-s) p' q') :
    (ContinuousLinearMap.lsmul ℂ ℂ).besovPairing φ s p p' q q'
      (SchwartzMap.toBesovSpaceCLM ℂ φ s p q ψ) w = w.toDistr ψ :=
  besovPairing_eq_toDistr_apply (SchwartzMap.toDistr_toBesovSpaceCLM φ s p q ψ) w

/-- The pairing of `u ∈ B^s_{p,q}(E, F)` with a scalar Schwartz function `ψ ∈ B^{-s}_{p',q'}` for
the scalar multiplication `(v, c) ↦ c • v` is the action `u ψ` of the tempered distribution `u`. -/
@[simp]
theorem besovPairing_toBesovSpaceCLM_right (u : BesovSpace F φ s p q) (ψ : 𝓢(E, ℂ)) :
    (ContinuousLinearMap.lsmul ℂ ℂ).flip.besovPairing φ s p p' q q' u
      (SchwartzMap.toBesovSpaceCLM ℂ φ (-s) p' q' ψ) = u.toDistr ψ :=
  (toDistr_apply_eq_besovPairing u (SchwartzMap.toDistr_toBesovSpaceCLM φ (-s) p' q' ψ)).symm

/-- **The duality bound.** There is a constant `C`, depending only on the bump function `φ` and
on `s`, such that for all Hölder conjugate pairs `p, p'` and `q, q'` of exponents in `[1, ∞]`,
every `v ∈ B^{-s}_{p',q'}` and every Schwartz function `f`,

`‖⟨v, f⟩‖ ≤ C ‖v‖_{B^{-s}_{p',q'}} ‖f‖_{B^s_{p,q}}`,

where `⟨v, f⟩` is the value of the tempered distribution of `v` at `f`. -/
theorem exists_norm_toDistr_apply_le (φ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)]
      [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q']
      (v : BesovSpace F φ (-s) p' q') (f : 𝓢(E, ℂ)),
      ‖v.toDistr f‖ ≤ C * ‖v‖ * ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q f‖ := by
  obtain ⟨C, hC, h⟩ :=
    ContinuousLinearMap.exists_norm_besovPairing_le (F := ℂ) (G := F) (K := F) φ s
  refine ⟨C, hC, fun {p p' q q'} _ _ _ _ _ _ v f ↦ ?_⟩
  rw [← besovPairing_eq_toDistr_apply (SchwartzMap.toDistr_toBesovSpaceCLM φ s p q f) v]
  calc _ ≤ C * ‖ContinuousLinearMap.lsmul ℂ ℂ‖ * ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q f‖ * ‖v‖ :=
        h _ _ _
    _ ≤ C * 1 * ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q f‖ * ‖v‖ := by
        gcongr
        exact ContinuousLinearMap.opNorm_lsmul_le
    _ = _ := by ring

end TauCeti.BesovSpace
