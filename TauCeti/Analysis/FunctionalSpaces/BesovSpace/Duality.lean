/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.Holder

/-!
# The duality pairing between `B^{-s}_{p',q'}` and `B^s_{p,q}`

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

## Main declarations

* `TauCeti.BesovSpace.exists_norm_toDistr_apply_le`: the duality bound
  `‖⟨v, f⟩‖ ≤ C ‖v‖_{B^{-s}_{p',q'}} ‖f‖_{B^s_{p,q}}`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Proposition 2.76.
* H. Triebel, *Theory of Function Spaces*, Section 2.11.2.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace F]

namespace TauCeti.BesovSpace

open TemperedDistribution

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
  have hlim : Tendsto (fun N ↦ ∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j v.toDistr f)
      atTop (𝓝 (v.toDistr f)) := by
    simpa using PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.1
      (tendsto_sum_littlewoodPaleyBlock φ v.toDistr) f
  refine le_of_tendsto' hlim.norm fun N ↦ ?_
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
