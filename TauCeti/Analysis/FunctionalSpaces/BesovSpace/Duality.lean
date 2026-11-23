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
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.Holder

/-!
# The duality pairing of the Besov spaces `B^s_{p,q}` and `B^{-s}_{p',q'}`

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space, with
inhomogeneous Littlewood–Paley blocks `Δⱼ`, and let `p, p'` and `q, q'` be pairs of Hölder
conjugate exponents in `[1, ∞]`. This file proves that an element `v` of the Besov space
`B^{-s}_{p',q'}` acts boundedly on the Schwartz functions for the norm of `B^s_{p,q}`: there is a
constant `C`, depending only on `φ` and `s`, with

`‖⟨v, f⟩‖ ≤ C ‖v‖_{B^{-s}_{p',q'}} ‖f‖_{B^s_{p,q}}`

for every Schwartz function `f` (`TauCeti.BesovSpace.exists_norm_toDistr_apply_le`). Here `⟨v, f⟩`
is the value of the tempered distribution of `v` at `f`, and `v` may take values in any complex
Banach space. The constant does not depend on the exponents. This is the bounded half of the
duality `(B^s_{p,q})^* = B^{-s}_{p',q'}`: smoothness `s` is paired with smoothness `-s`, and the
integrability and fine indices with their conjugates.

## The argument

The blocks are Fourier multipliers by the pieces `ψⱼ` of the Littlewood–Paley partition, which are
even functions (`ContDiffBump.inhomogeneousLittlewoodPaley_neg`). Hence they are symmetric for the
pairing of tempered distributions with Schwartz functions,
`(Δⱼ v) f = v (Δⱼ f)` (`TemperedDistribution.littlewoodPaleyBlock_apply_apply`).

By the Littlewood–Paley reconstruction `v = ∑ⱼ Δⱼ v`, the value `v f` is the limit of the partial
sums of `(Δⱼ v) f`. By almost orthogonality, `Δⱼ v = ∑_{j - L ≤ k < j + L} Δⱼ Δₖ v` with `L`
depending only on `φ`, so by symmetry `(Δⱼ v) f = ∑_{j - L ≤ k < j + L} (Δₖ v) (Δⱼ f)`. Each term
is the integral of `Δⱼ f` against the `L^{p'}` function `Δₖ v`, at most `‖Δⱼ f‖_p ‖Δₖ v‖_{p'}` by
Hölder's inequality. Since `|j - k| < L`, the weights satisfy `2^{ks} ≤ 2^{|s| L} 2^{js}`, so

`‖(Δⱼ v) f‖ ≤ 2^{|s| L} aⱼ cⱼ`, with `aⱼ = 2^{js} ‖Δⱼ f‖_p` and
`cⱼ = ∑_{j - L ≤ k < j + L} 2^{-ks} ‖Δₖ v‖_{p'}`.

The sequence `a` has `ℓ^q` norm `‖f‖_{B^s_{p,q}}`, and the window sums `c` have `ℓ^{q'}` norm at
most `2 L ‖v‖_{B^{-s}_{p',q'}}`. Hölder's inequality for sequences bounds `∑ⱼ aⱼ cⱼ` by the
product of these norms, uniformly over the partial sums.

## The pairing on Besov spaces

More generally, let `B : F →L[ℂ] G →L[ℂ] K` be a continuous bilinear map, for instance the scalar
multiplication of `F` or the evaluation pairing of a fiber `F` with its dual. The **Besov duality
pairing** of `u ∈ B^s_{p,q}(E, F)` and `w ∈ B^{-s}_{p',q'}(E, G)` is

`⟨u, w⟩ = ∑ₖ ∫ B ((Δₖ u) x) ((Δ⁺ₖ w) x) dx`,  `Δ⁺ₖ = ∑_{k + 1 - L ≤ j < k + L} Δⱼ`,

where `L = φ.littlewoodPaleyOverlap φ` is the overlap of the partition: pieces whose indices differ
by at least `L` have disjoint supports, so that `Δ⁺ₖ Δₖ = Δₖ`
(`TemperedDistribution.enlargedLittlewoodPaleyBlock_littlewoodPaleyBlock`).
Each term is bounded by Hölder's inequality in `Lᵖ × L^{p'}`, and after weighting the `k`-th
term by `2^{ks} 2^{-ks} = 1` the series is bounded by Hölder's inequality in `ℓ^q × ℓ^{q'}`
(Mathlib's `lp.dualPairing`). Hence `⟨·, ·⟩` is a continuous bilinear map with

`‖⟨u, w⟩‖ ≤ C ‖B‖ ‖u‖_{B^s_{p,q}} ‖w‖_{B^{-s}_{p',q'}}`,

where `C` is independent of the exponents, of `B` and of `u, w`.

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

* `TauCeti.BesovSpace.exists_norm_toDistr_apply_le`: the duality bound
  `‖⟨v, f⟩‖ ≤ C ‖v‖_{B^{-s}_{p',q'}} ‖f‖_{B^s_{p,q}}`.
* `ContinuousLinearMap.besovPairing B φ s p p' q q'`: the duality pairing
  `B^s_{p,q}(E, F) × B^{-s}_{p',q'}(E, G) → K` induced by `B`, as a continuous bilinear map.
* `ContinuousLinearMap.hasSum_besovPairing` and `ContinuousLinearMap.besovPairing_apply`: the
  pairing is the sum of the series `∑ₖ ∑_{k + 1 - L ≤ j < k + L} ∫ B ((Δₖ u) x) ((Δⱼ w) x) dx`.
* `ContinuousLinearMap.exists_norm_besovPairing_le`: `‖⟨u, w⟩‖ ≤ C ‖B‖ ‖u‖ ‖w‖`, with `C`
  independent of the exponents, of `B` and of `u, w`.
* `TauCeti.BesovSpace.toDistr_apply_eq_besovPairing` and
  `TauCeti.BesovSpace.besovPairing_eq_toDistr_apply`: on scalar Schwartz functions the pairing is
  the action of a tempered distribution.

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

open MeasureTheory FourierTransform TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap

variable {E F G K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]

namespace TauCeti.BesovSpace

/-! ### The duality bound on Schwartz functions -/

/-- **One block of the pairing.** If `Δⱼ w = ∑_{j - L ≤ k < j + L} Δⱼ Δₖ w` for every `j` and
every tempered distribution `w`, then for `v ∈ B^{-s}_{p',q'}` and a Schwartz function `f`,
`‖(Δⱼ v) f‖ ≤ 2^{|s| L} 2^{js} ‖Δⱼ f‖_p ∑_{j - L ≤ k < j + L} 2^{-ks} ‖Δₖ v‖_{p'}`. -/
private theorem norm_littlewoodPaleyBlock_toDistr_apply_le {φ : ContDiffBump (0 : E)} {s : ℝ}
    {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)] [p.HolderConjugate p']
    {L : ℕ} (hL : ∀ (j : ℕ) (w : 𝓢'(E, F)), littlewoodPaleyBlock F φ j w =
      ∑ k ∈ Finset.Ico (j - L) (j + L), littlewoodPaleyBlock F φ j (littlewoodPaleyBlock F φ k w))
    (v : BesovSpace F φ (-s) p' q') (f : 𝓢(E, ℂ)) (j : ℕ) :
    ‖littlewoodPaleyBlock F φ j v.toDistr f‖ ≤
      2 ^ (|s| * L) * (2 ^ (s * j) * ‖(SchwartzMap.toBesovSpaceCLM ℂ φ s p q f).block j‖) *
        ∑ k ∈ Finset.Ico (j - L) (j + L), 2 ^ (-s * k) * ‖v.block k‖ := by
  set u := SchwartzMap.toBesovSpaceCLM ℂ φ s p q f
  -- The block `Δⱼ f`, as a Schwartz function.
  set h := SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) f
  have hh : ‖u.block j‖ = (eLpNorm h p).toReal := by
    rw [block_toBesovSpaceCLM, SchwartzMap.norm_toLp]
  -- Hölder's inequality for the pairing of a block of `v` with `Δⱼ f`.
  have hpair (k : ℕ) : ‖littlewoodPaleyBlock F φ k v.toDistr h‖ ≤ ‖u.block j‖ * ‖v.block k‖ := by
    rw [← coe_block, Lp.toTemperedDistribution_apply]
    have hle := ENNReal.toReal_mono (ENNReal.mul_ne_top (h.memLp p volume).eLpNorm_ne_top
      (Lp.eLpNorm_ne_top (v.block k))) (TauCeti.enorm_integral_smul_le (q := p'))
    simpa [hh, Lp.norm_def] using hle
  -- By almost orthogonality and symmetry, `(Δⱼ v) f = ∑_{j - L ≤ k < j + L} (Δₖ v) (Δⱼ f)`.
  have hsum : littlewoodPaleyBlock F φ j v.toDistr f =
      ∑ k ∈ Finset.Ico (j - L) (j + L), littlewoodPaleyBlock F φ k v.toDistr h := by
    rw [hL j]
    simp [h, littlewoodPaleyBlock_apply_apply]
  rw [hsum, mul_assoc, Finset.mul_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ (hpair k).trans ?_)
  -- Since `|j - k| < L`, the weights `2^{-js}` and `2^{-ks}` differ by at most `2^{|s| L}`.
  have hw := Real.rpow_mul_natCast_le_of_mem_Ico' one_le_two (-s) hk
  rw [abs_neg] at hw
  have h1 : (2 : ℝ) ^ (s * j) * 2 ^ (-s * j) = 1 := by
    rw [← Real.rpow_add two_pos]
    simp
  calc ‖u.block j‖ * ‖v.block k‖
      = 2 ^ (s * j) * ‖u.block j‖ * (2 ^ (-s * j) * ‖v.block k‖) := by
        linear_combination (‖u.block j‖ * ‖v.block k‖) * h1.symm
    _ ≤ 2 ^ (s * j) * ‖u.block j‖ * (2 ^ (|s| * L) * 2 ^ (-s * k) * ‖v.block k‖) := by gcongr
    _ = _ := by ring

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
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_eq_sum_Ico (F := F) φ φ
  refine ⟨2 * L * 2 ^ (|s| * L), by positivity, fun {p p' q q'} _ _ _ _ _ _ v f ↦ ?_⟩
  set u := SchwartzMap.toBesovSpaceCLM ℂ φ s p q f
  -- The weighted block norms of `f` in `ℓ^q`, and the window sums of those of `v` in `ℓ^{q'}`.
  set a := u.weightedBlockNorms
  have haj (j : ℕ) : a j = _ := u.weightedBlockNorms_apply j
  have ha : ‖a‖ ≤ ‖u‖ := (norm_weightedBlockNorms u).le
  set b := v.weightedBlockNorms
  have hbk (k : ℕ) : b k = _ := v.weightedBlockNorms_apply k
  have hb : ‖b‖ ≤ ‖v‖ := (norm_weightedBlockNorms v).le
  obtain ⟨c, hcj, hc⟩ := lp.exists_eq_sum_Ico_sub_add_and_norm_le b L
  have hterm (j : ℕ) : ‖littlewoodPaleyBlock F φ j v.toDistr f‖ ≤ 2 ^ (|s| * L) * (a j * c j) := by
    rw [← mul_assoc, haj, hcj, Finset.sum_congr rfl fun k _ ↦ hbk k]
    exact norm_littlewoodPaleyBlock_toDistr_apply_le hL v f j
  -- Hölder's inequality for sequences bounds every partial sum of `∑ⱼ aⱼ cⱼ` by `‖a‖ ‖c‖`.
  have hsum (N : ℕ) : ∑ j ∈ Finset.range N, a j * c j ≤ ‖a‖ * ‖c‖ :=
    (Finset.sum_le_sum fun j _ ↦ (Real.le_norm_self _).trans (norm_mul_le _ _)).trans
      (lp.sum_norm_mul_norm_le a c _)
  -- Pass to the limit in the reconstruction `v = ∑ⱼ Δⱼ v`, evaluated at `f`.
  refine le_of_tendsto' (tendsto_sum_littlewoodPaleyBlock_apply φ v.toDistr f).norm fun N ↦ ?_
  calc ‖∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j v.toDistr f‖
      ≤ ∑ j ∈ Finset.range N, 2 ^ (|s| * L) * (a j * c j) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hterm j)
    _ = 2 ^ (|s| * L) * ∑ j ∈ Finset.range N, a j * c j := (Finset.mul_sum ..).symm
    _ ≤ 2 ^ (|s| * L) * (‖u‖ * (2 * L * ‖v‖)) := by
        gcongr
        exact (hsum N).trans (mul_le_mul ha (hc.trans (by gcongr)) (norm_nonneg _)
          (norm_nonneg _))
    _ = 2 * L * 2 ^ (|s| * L) * ‖v‖ * ‖u‖ := by ring

end TauCeti.BesovSpace

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-! ### The enlarged blocks -/

/-- The sum `Δ⁺ₖ w = ∑_{k + 1 - L ≤ j < k + L} Δⱼ w` of the blocks of `w` near `k`, as an `Lᵖ`
function. -/
private def enlargedBlock (w : BesovSpace G φ s p q) (k : ℕ) : Lp G p (volume : Measure E) :=
  ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ), w.block j

omit [Fact (1 ≤ q)] in
/-- The weighted enlarged block `2^{ks} Δ⁺ₖ w` is controlled by the weighted blocks of `w` of index
within `L` of `k`. -/
private theorem norm_smul_enlargedBlock_le (w : BesovSpace G φ s p q) (k : ℕ) :
    ‖(((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlock w k‖ ≤
      2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * ∑ j ∈ Finset.Ico (k - φ.littlewoodPaleyOverlap φ)
        (k + φ.littlewoodPaleyOverlap φ), w.weightedBlockNorms j := by
  rw [norm_smul, Complex.norm_of_nonneg (by positivity), Finset.mul_sum]
  calc 2 ^ (s * k) * ‖enlargedBlock w k‖ ≤
        ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ),
          2 ^ (s * k) * ‖w.block j‖ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ),
          2 ^ (|s| * φ.littlewoodPaleyOverlap φ) * w.weightedBlockNorms j := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        rw [weightedBlockNorms_apply, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [Finset.mem_Ico] at hj
        refine Real.rpow_mul_le_rpow_abs_mul_mul_rpow_mul one_le_two s (abs_sub_le_iff.2 ⟨?_, ?_⟩)
        all_goals rw [sub_le_iff_le_add']; exact_mod_cast (by omega)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico (by omega) le_rfl)
          fun j _ _ ↦ by rw [weightedBlockNorms_apply]; positivity

/-- The weighted enlarged blocks `(2^{ks} Δ⁺ₖ w)ₖ` of `w ∈ B^s_{p,q}`, an `ℓ^q` sequence of `Lᵖ`
functions. -/
private def enlargedWeightedBlocks (w : BesovSpace G φ s p q) :
    lp (fun _ : ℕ ↦ Lp G p (volume : Measure E)) q :=
  ⟨fun k ↦ (((2 : ℝ) ^ (s * k) : ℝ) : ℂ) • enlargedBlock w k,
    (((lp.memℓp w.weightedBlockNorms).sum_Ico_sub_add φ.littlewoodPaleyOverlap φ).const_mul
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
    lp.exists_eq_sum_Ico_sub_add_and_norm_le w.weightedBlockNorms φ.littlewoodPaleyOverlap φ
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
`|j - k| < L`, where `L = φ.littlewoodPaleyOverlap φ` is the least `L` such that pieces of the
partition whose indices differ by at least `L` have disjoint supports; thus `Δ⁺ₖ Δₖ = Δₖ`
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
        rw [← sum_apply, ← ContinuousLinearMap.sum_apply, ← enlargedLittlewoodPaleyBlock_eq_sum_Ico,
          enlargedLittlewoodPaleyBlock_littlewoodPaleyBlock φ
            fun _ _ hjk ξ ↦ φ.inhomogeneousLittlewoodPaley_mul_eq_zero φ hjk ξ]

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
    _ = ∑ j ∈ Finset.Ico (k + 1 - φ.littlewoodPaleyOverlap φ) (k + φ.littlewoodPaleyOverlap φ),
          littlewoodPaleyBlock G φ j (littlewoodPaleyBlock G φ k w.toDistr) ψ := by
        rw [← Lp.toTemperedDistribution_apply, enlargedBlock, Lp.toTemperedDistribution_sum]
        simp only [coe_block, sum_apply, ψₖ, ← littlewoodPaleyBlock_apply_apply,
          littlewoodPaleyBlock_comm φ k]
    _ = littlewoodPaleyBlock G φ k w.toDistr ψ := by
        rw [← sum_apply, ← ContinuousLinearMap.sum_apply, ← enlargedLittlewoodPaleyBlock_eq_sum_Ico,
          enlargedLittlewoodPaleyBlock_littlewoodPaleyBlock φ
            fun _ _ hjk ξ ↦ φ.inhomogeneousLittlewoodPaley_mul_eq_zero φ hjk ξ]

end TauCeti.BesovSpace
