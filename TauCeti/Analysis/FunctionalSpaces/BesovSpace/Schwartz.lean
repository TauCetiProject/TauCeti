/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Postcomp
public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Schwartz functions, dyadic partial sums and smooth density in Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space and let
`Δⱼ` (`j ≥ 0`) be its inhomogeneous Littlewood–Paley blocks. Every Schwartz function `f ∈ 𝓢(E, F)`
lies in `H^{s+1,p}(E, F) ⊆ B^{s+1}_{p,∞}(E, F) ⊆ B^s_{p,q}(E, F)`, giving a continuous linear
inclusion `SchwartzMap.toBesovSpaceCLM` for all `s ∈ ℝ` and `1 ≤ p, q ≤ ∞`.

Conversely, for any `u ∈ B^s_{p,q}(E, F)` the dyadic partial sums
`S_N u = ∑_{j < N} Δⱼ u` define uniformly bounded operators `TauCeti.BesovSpace.partialSumCLM` on
`B^s_{p,q}(E, F)`; the Fourier transform of each `S_N u` is supported in
`Metric.closedBall 0 (2 ^ N * φ.rOut)`. Because the blocks
`Δₖ` and `Δⱼ` interact only at bounded distance `|k - j| < L`, the block `Δₖ (u - S_N u)` is a
bounded window sum of the blocks `Δⱼ u` with `j ≥ N`. Thus `‖u - S_N u‖_{B^s_{p,q}}` is controlled
by the `ℓ^q` norm of the tail `(2^{js} ‖Δⱼ u‖_p)_{j ≥ N}`:

* for `q < ∞` (and all `1 ≤ p ≤ ∞`), `S_N u → u` in `B^s_{p,q}(E, F)` as `N → ∞`;
* since each `S_N u` has compactly supported Fourier transform, it lies in `B^{s+1}_{p,1} ⊆
  H^{s+1,p}`, so for `1 ≤ p < ∞` it lies in the closure of `𝓢(E, F)` in `B^s_{p,q}` (for every
  `1 ≤ q ≤ ∞`, including `q = ∞`);
* combining the two with the density of compactly supported smooth functions in `𝓢(E, F)` shows
  that both `𝓢(E, F)` and `{f ∈ 𝓢(E, F) | HasCompactSupport f}` are norm-dense in `B^s_{p,q}(E, F)`
  whenever `1 ≤ p < ∞` and `1 ≤ q < ∞`.

At `q = ∞`, `S_N u` converges in `B^s_{p,∞}` if and only if `2^{js} ‖Δⱼ u‖_p → 0`; the resulting
closed subspace is the little Besov space studied in
`TauCeti.Analysis.FunctionalSpaces.BesovSpace.Little`.

## Main declarations

* `SchwartzMap.memBesov`: every Schwartz function lies in `B^s_{p,q}` for `1 ≤ p ≤ ∞` and `q ≠ 0`.
* `SchwartzMap.toBesovSpaceCLM`: the continuous linear inclusion `𝓢(E, F) →L[ℂ] B^s_{p,q}(E, F)`.
* `TauCeti.BesovSpace.partialSumCLM`: the dyadic partial-sum operator `u ↦ ∑_{j < N} Δⱼ u` on
  `B^s_{p,q}(E, F)`, bounded uniformly in `N`, `p` and `q`
  (`TauCeti.BesovSpace.exists_norm_sub_partialSumCLM_le`,
  `TauCeti.BesovSpace.exists_norm_partialSumCLM_le`).
* `TauCeti.BesovSpace.tendsto_partialSumCLM`: for `q < ∞`, `S_N u → u` in `B^s_{p,q}(E, F)`.
* `SchwartzMap.denseRange_toBesovSpaceCLM` and
  `SchwartzMap.dense_image_toBesovSpaceCLM_hasCompactSupport`: for `1 ≤ p < ∞` and `1 ≤ q < ∞`,
  Schwartz functions and compactly supported smooth functions are dense in `B^s_{p,q}(E, F)`.
* `TauCeti.BesovSpace.continuousLinearMap_ext` and
  `TauCeti.BesovSpace.continuousLinearMap_ext_hasCompactSupport`: continuous linear maps out of
  `B^s_{p,q}(E, F)` (`p, q < ∞`) are determined by their values on (compactly supported) Schwartz
  functions.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Theorem 3.4.2(b) and
  Section 6.2.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Proposition 2.74.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

namespace SchwartzMap

/-- Every Schwartz function lies in every inhomogeneous Besov space `B^s_{p,q}` with `1 ≤ p ≤ ∞`
and `q ≠ 0`. -/
theorem memBesov (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] {q : ℝ≥0∞}
    (hq : q ≠ 0) (f : 𝓢(E, F)) : (f : 𝓢'(E, F)).MemBesov φ s p q := by
  have hsob := (f.toBesselPotentialSpaceCLM (s + 1) p).memSobolev_toDistr
  rw [toDistr_toBesselPotentialSpaceCLM] at hsob
  exact (hsob.memBesov φ).of_lt (lt_add_one s) hq

/-- The continuous linear inclusion of Schwartz functions into the inhomogeneous Besov space
`B^s_{p,q}(E, F)`, defined by composing `𝓢(E, F) →L[ℂ] H^{s+1,p}(E, F) →L[ℂ] B^{s+1}_{p,∞}(E, F)
→L[ℂ] B^s_{p,q}(E, F)`. -/
def toBesovSpaceCLM (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    𝓢(E, F) →L[ℂ] TauCeti.BesovSpace F φ s p q :=
  TauCeti.BesovSpace.inclusionOfLT F φ p ∞ q (lt_add_one s) ∘L
    BesselPotentialSpace.toBesovSpace φ ∘L
      toBesselPotentialSpaceCLM (s + 1) p

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

@[simp]
theorem toDistr_toBesovSpaceCLM (f : 𝓢(E, F)) :
    (f.toBesovSpaceCLM φ s p q).toDistr = (f : 𝓢'(E, F)) := by
  simp [toBesovSpaceCLM]

/-- The `j`-th Littlewood–Paley block of a Schwartz function in `B^s_{p,q}` is the `Lᵖ` class of
the Schwartz Fourier multiplier `𝓕⁻ (ψⱼ • 𝓕 f)`. -/
theorem block_toBesovSpaceCLM (f : 𝓢(E, F)) (j : ℕ) :
    (f.toBesovSpaceCLM φ s p q).block j =
      (fourierMultiplierCLM F (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) f).toLp p := by
  refine Lp.toTemperedDistribution_injective ?_
  dsimp only
  rw [TauCeti.BesovSpace.coe_block, toDistr_toBesovSpaceCLM,
    TemperedDistribution.littlewoodPaleyBlock_toTemperedDistributionCLM_eq,
    Lp.toTemperedDistribution_toLp_eq]

/-- Almost everywhere, the `j`-th block of `f` in `B^s_{p,q}` is the Schwartz function
`𝓕⁻ (ψⱼ • 𝓕 f)`. -/
theorem coeFn_block_toBesovSpaceCLM (f : 𝓢(E, F)) (j : ℕ) :
    (f.toBesovSpaceCLM φ s p q).block j =ᵐ[volume]
      fourierMultiplierCLM F (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) f := by
  rw [block_toBesovSpaceCLM]
  exact coeFn_toLp _ p volume

@[simp]
theorem inclusion_toBesovSpaceCLM {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q')] (hs : s' ≤ s)
    (hq : q ≤ q') (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.inclusion F φ p hs hq (f.toBesovSpaceCLM φ s p q) =
      f.toBesovSpaceCLM φ s' p q' :=
  TauCeti.BesovSpace.ext (by simp)

@[simp]
theorem inclusionOfLT_toBesovSpaceCLM {s' : ℝ} {q' : ℝ≥0∞} [Fact (1 ≤ q')] (hs : s' < s)
    (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.inclusionOfLT F φ p q q' hs (f.toBesovSpaceCLM φ s p q) =
      f.toBesovSpaceCLM φ s' p q' :=
  TauCeti.BesovSpace.ext (by simp)

@[simp]
theorem bumpEquiv_toBesovSpaceCLM (φ' : ContDiffBump (0 : E)) (f : 𝓢(E, F)) :
    TauCeti.BesovSpace.bumpEquiv F φ φ' s p q (f.toBesovSpaceCLM φ s p q) =
      f.toBesovSpaceCLM φ' s p q :=
  TauCeti.BesovSpace.ext (by simp)

/-- On Schwartz functions, `TauCeti.BesovSpace.postcomp` is post-composition of Schwartz maps. -/
theorem toBesovSpaceCLM_postcompCLM (L : F →L[ℂ] G) (f : 𝓢(E, F)) :
    toBesovSpaceCLM φ s p q (f.postcompCLM L) =
      TauCeti.BesovSpace.postcomp φ s p q L (f.toBesovSpaceCLM φ s p q) := by
  refine TauCeti.BesovSpace.ext ?_
  ext ψ
  rw [toDistr_toBesovSpaceCLM, TauCeti.BesovSpace.toDistr_postcomp_apply,
    toDistr_toBesovSpaceCLM, toTemperedDistributionCLM_postcompCLM_apply]

@[simp]
theorem toBesovSpace_toBesselPotentialSpaceCLM (f : 𝓢(E, F)) :
    BesselPotentialSpace.toBesovSpace φ (f.toBesselPotentialSpaceCLM s p) =
      f.toBesovSpaceCLM φ s p ∞ :=
  TauCeti.BesovSpace.ext (by simp)

@[simp]
theorem toBesselPotentialSpace_toBesovSpaceCLM (f : 𝓢(E, F)) :
    (f.toBesovSpaceCLM φ s p 1).toBesselPotentialSpace = f.toBesselPotentialSpaceCLM s p :=
  BesselPotentialSpace.ext (by simp)

end SchwartzMap

namespace TauCeti.BesovSpace

open TemperedDistribution

section PartialSum

omit [CompleteSpace F] in
/-- For every `k` and `N`, the block `Δₖ (u - ∑_{j < N} Δⱼ u)` is the finite window sum of
`Δₖ Δⱼ u` over `k - L ≤ j < k + L` with `N ≤ j`, where `L` is the almost-orthogonality radius of
`φ`. -/
private theorem exists_littlewoodPaleyBlock_sub_sum_range_eq (φ : ContDiffBump (0 : E)) :
    ∃ L : ℕ, ∀ (N k : ℕ) (u : 𝓢'(E, F)),
      littlewoodPaleyBlock F φ k (u - ∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u) =
        ∑ j ∈ Finset.Ico (k - L) (k + L),
          if N ≤ j then littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) else 0 := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_compL_eq_zero (F := F) φ φ
  refine ⟨L, fun N k u ↦ ?_⟩
  have hvanish {j : ℕ} (hj : j ∉ Finset.Ico (k - L) (k + L)) :
      littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) = 0 := by
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hj
    rcases hj with hj | hj
    · exact congr($((hL j k (by omega)).2) u)
    · exact congr($((hL k j (by omega)).1) u)
  have hfull : littlewoodPaleyBlock F φ k u =
      ∑ j ∈ Finset.Ico (k - L) (k + L),
        littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) := by
    refine tendsto_nhds_unique
      (((map_continuous (littlewoodPaleyBlock F φ k)).tendsto u).comp
        (tendsto_sum_littlewoodPaleyBlock φ u))
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop (k + L)] with M hM
    simp only [Function.comp_apply, map_sum]
    exact Finset.sum_subset (fun j hj ↦ Finset.mem_range.2 ((Finset.mem_Ico.1 hj).2.trans_le hM))
      fun j _ hj ↦ hvanish hj
  have hpart : littlewoodPaleyBlock F φ k (∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u) =
      ∑ j ∈ Finset.Ico (k - L) (k + L),
        if j < N then littlewoodPaleyBlock F φ k (littlewoodPaleyBlock F φ j u) else 0 := by
    rw [map_sum, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun j hj ↦ Finset.mem_range.2 (Finset.mem_filter.1 hj).2)
      fun j hj hj' ↦ hvanish fun hIco ↦
        hj' (Finset.mem_filter.2 ⟨hIco, Finset.mem_range.1 hj⟩)).symm
  rw [map_sub, hfull, hpart, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases lt_or_ge j N with hj | hj
  · simp [hj, not_le.2 hj]
  · simp [hj, not_lt.2 hj]

/-- **Tail bound for dyadic partial sums.** There is `C ≥ 0`, depending only on `φ` and `s`, such
that for every `1 ≤ p, q ≤ ∞`, `N : ℕ` and `u ∈ B^s_{p,q}`, the remainder
`u - ∑_{j < N} Δⱼ u` lies in `B^s_{p,q}` with norm at most `C` times the `ℓ^q` norm of the tail of
`u.weightedBlocks` from index `N` onwards. -/
private theorem exists_remainder_toDistr_eq_and_norm_le (φ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (N : ℕ)
      (u : BesovSpace F φ s p q),
      ∃ r : BesovSpace F φ s p q,
        r.toDistr = u.toDistr - ∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u.toDistr ∧
          ‖r‖ ≤ C * ‖u.weightedBlocks -
            ∑ i ∈ Finset.range N, lp.single q i (u.weightedBlocks i)‖ := by
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_sub_sum_range_eq (F := F) φ
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set K : ℝ := max C₀ 0 * 2 ^ (|s| * L)
  refine ⟨K * (2 * L), by positivity, fun {p q} _ _ N u ↦ ?_⟩
  choose g hg hgn using fun k j ↦ hC₀ (p := p) k (u.block j)
  set G : ℕ → Lp F p (volume : Measure E) :=
    fun k ↦ ∑ j ∈ Finset.Ico (k - L) (k + L), if N ≤ j then g k j else 0
  have hG (k : ℕ) : littlewoodPaleyBlock F φ k
      (u.toDistr - ∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u.toDistr) = G k := by
    rw [hL N k u.toDistr, Lp.toTemperedDistribution_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [← coe_block, hg k j]
    · exact Lp.toTemperedDistribution_zero.symm
  set w := u.weightedBlocks - ∑ i ∈ Finset.range N, lp.single q i (u.weightedBlocks i)
  set b : lp (fun _ : ℕ ↦ ℝ) q := ⟨fun j ↦ ‖w j‖, (lp.memℓp w).norm⟩
  set W : lp (fun _ : ℕ ↦ ℝ) q :=
    ⟨fun k ↦ ∑ j ∈ Finset.Ico (k - L) (k + L), b j, (lp.memℓp b).sum_Ico_sub_add L⟩
  -- Evaluating the anonymous `lp` sequences `b` and `W` at an index.
  have hW (k : ℕ) : W k = ∑ j ∈ Finset.Ico (k - L) (k + L), ‖w j‖ := rfl
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hb : ‖b‖ ≤ ‖w‖ := lp.norm_mono hq0 fun j ↦ (norm_norm _).le
  have hle (k : ℕ) : 2 ^ (s * k) * ‖G k‖ ≤ (K • W) k := by
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hW]
    let x : ℕ → Lp F p (volume : Measure E) := fun j ↦ if N ≤ j then u.block j else 0
    have hgx (j : ℕ) : ‖if N ≤ j then g k j else 0‖ ≤ C₀ * ‖x j‖ := by
      dsimp only [x]
      split_ifs
      · exact hgn k j
      · simp
    refine (two_rpow_mul_norm_sum_Ico_le s hgx k L).trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [lp.sub_sum_single_apply]
    dsimp only [x]
    rcases lt_or_ge j N with hj | hj
    · simp [hj, not_le.2 hj]
    · simp [hj, not_lt.2 hj, norm_weightedBlocks_apply]
  obtain ⟨r, hr, hrn⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq G (K • W) hG hle
  refine ⟨r, hr, hrn.trans ?_⟩
  calc ‖K • W‖ = K * ‖W‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ K * (2 * L * ‖b‖) := by gcongr; exact lp.norm_le_of_forall_eq_sum_Ico_sub_add L fun _ ↦ rfl
    _ ≤ K * (2 * L) * ‖w‖ := by rw [mul_assoc K]; gcongr

/-- **Smoothing property of dyadic partial sums.** Because the Fourier transform of
`∑_{j < N} Δⱼ u` is supported in `closedBall 0 (2^N φ.rOut)`, it has only finitely many nonzero
Littlewood–Paley blocks, so it lies in `B^{s'}_{p,q'}` for every `s' : ℝ` and every `q' : ℝ≥0∞`
(including `q' = 0`). -/
private theorem memBesov_sum_littlewoodPaleyBlock {φ : ContDiffBump (0 : E)} {s : ℝ}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] (s' : ℝ) (q' : ℝ≥0∞) (N : ℕ) (u : BesovSpace F φ s p q) :
    (∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u.toDistr).MemBesov φ s' p q' := by
  obtain ⟨M, hM⟩ := exists_littlewoodPaleyBlock_eq_zero_of_isVanishingOn_compl_closedBall
    (F := F) φ φ.rOut
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set S : 𝓢'(E, F) := ∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u.toDistr
  set fN : Lp F p (volume : Measure E) := ∑ j ∈ Finset.range N, u.block j
  have hfN : S = (fN : 𝓢'(E, F)) := by
    rw [Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun j _ ↦ (coe_block u j).symm
  have hvan : Distribution.IsVanishingOn (FourierTransform.fourier S : 𝓢'(E, F))
      (Metric.closedBall 0 (2 ^ N * φ.rOut))ᶜ :=
    isVanishingOn_fourier_sum_littlewoodPaleyBlock φ
      (fun k hk ↦ (Finset.mem_range.1 hk).le) u.toDistr
  choose g hg _ using fun k ↦ hC₀ (p := p) k fN
  have hg' (k : ℕ) : littlewoodPaleyBlock F φ k S = g k := by rw [hfN, hg k]
  have hfin : {k : ℕ | (2 : ℝ) ^ (s' * k) * ‖g k‖ ≠ 0}.Finite := by
    refine (Finset.finite_toSet (Finset.range (N + M))).subset fun k hk ↦ Finset.mem_range.2 ?_
    by_contra hge
    have hk0 : g k = 0 := Lp.toTemperedDistribution_injective <| by
      dsimp only
      rw [← hg' k, hM N k _ hvan (not_lt.1 hge), Lp.toTemperedDistribution_zero]
    exact hk (by simp [hk0])
  exact memBesov_iff.2 ⟨g, hg', (memℓp_zero hfin).of_exponent_ge zero_le⟩

variable (F) in
/-- **The dyadic partial-sum operator** `S_N u = ∑_{j < N} Δⱼ u` on the inhomogeneous Besov space
`B^s_{p,q}(E, F)`. Its operator norm is bounded uniformly in `N`, `p` and `q`
(`TauCeti.BesovSpace.exists_norm_partialSumCLM_le`), and for `q < ∞` it converges strongly to the
identity as `N → ∞` (`TauCeti.BesovSpace.tendsto_partialSumCLM`). -/
def partialSumCLM (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (N : ℕ) : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s p q :=
  let hC := (exists_remainder_toDistr_eq_and_norm_le (F := F) φ s).choose_spec
  LinearMap.mkContinuous
    { toFun u := (memBesov_sum_littlewoodPaleyBlock s q N u).toBesovSpace
      map_add' u v := ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, toDistr_add, map_add, Finset.sum_add_distrib]
      map_smul' c u := ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, toDistr_smul, map_smul, Finset.smul_sum,
          RingHom.id_apply] }
    (1 + (exists_remainder_toDistr_eq_and_norm_le (F := F) φ s).choose) fun u ↦ by
      have hC0 := hC.1
      obtain ⟨r, hr, hrn⟩ := hC.2 N u
      have hur : (memBesov_sum_littlewoodPaleyBlock s q N u).toBesovSpace = u - r := ext <| by
        rw [MemBesov.toDistr_toBesovSpace, toDistr_sub, hr, sub_sub_cancel]
      have htail : ‖u.weightedBlocks -
          ∑ i ∈ Finset.range N, lp.single q i (u.weightedBlocks i)‖ ≤ ‖u‖ :=
        (lp.norm_sub_sum_single_le (zero_lt_one.trans_le Fact.out).ne' _ _).trans_eq
          (norm_weightedBlocks u)
      calc ‖(memBesov_sum_littlewoodPaleyBlock s q N u).toBesovSpace‖
          = ‖u - r‖ := congrArg norm hur
        _ ≤ ‖u‖ + ‖r‖ := norm_sub_le _ _
        _ ≤ ‖u‖ + _ * ‖u‖ := add_le_add_right (hrn.trans (mul_le_mul_of_nonneg_left htail hC0)) _
        _ = (1 + _) * ‖u‖ := by ring

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

@[simp]
theorem toDistr_partialSumCLM (N : ℕ) (u : BesovSpace F φ s p q) :
    (partialSumCLM F φ s p q N u).toDistr =
      ∑ j ∈ Finset.range N, littlewoodPaleyBlock F φ j u.toDistr :=
  MemBesov.toDistr_toBesovSpace _

@[simp]
theorem partialSumCLM_zero : partialSumCLM F φ s p q 0 = 0 := by
  ext u : 1
  exact ext (by simp)

/-- **Uniform tail estimate for `partialSumCLM`.** There is `C ≥ 0`, depending only on `φ` and `s`,
such that for all `1 ≤ p, q ≤ ∞`, `N : ℕ` and `u ∈ B^s_{p,q}(E, F)`,
`‖u - S_N u‖ ≤ C ‖u.weightedBlocks - ∑_{i < N} single i (u.weightedBlocks i)‖`. -/
theorem exists_norm_sub_partialSumCLM_le (φ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (N : ℕ)
      (u : BesovSpace F φ s p q),
      ‖u - partialSumCLM F φ s p q N u‖ ≤
        C * ‖u.weightedBlocks - ∑ i ∈ Finset.range N, lp.single q i (u.weightedBlocks i)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_remainder_toDistr_eq_and_norm_le (F := F) φ s
  refine ⟨C, hC0, fun {p q} _ _ N u ↦ ?_⟩
  obtain ⟨r, hr, hrn⟩ := hC N u
  have hur : u - partialSumCLM F φ s p q N u = r := ext (by simp [hr])
  rwa [hur]

/-- **Uniform boundedness of `partialSumCLM`.** There is `C ≥ 0`, depending only on `φ` and `s`,
such that `‖partialSumCLM F φ s p q N‖ ≤ C` for all `N : ℕ` and all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_partialSumCLM_le (φ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (N : ℕ),
      ‖partialSumCLM F φ s p q N‖ ≤ C := by
  let C := (exists_remainder_toDistr_eq_and_norm_le (F := F) φ s).choose
  have hC0 : 0 ≤ C := (exists_remainder_toDistr_eq_and_norm_le (F := F) φ s).choose_spec.1
  refine ⟨1 + C, by positivity, fun N ↦ ?_⟩
  rw [partialSumCLM]
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- **Smoothing property of dyadic partial sums.** Because the Fourier transform of `S_N u` is
supported in `closedBall 0 (2^N φ.rOut)`, `S_N u` has only finitely many nonzero Littlewood–Paley
blocks, so it lies in `B^{s'}_{p,q'}` for every `s' : ℝ` and every `q' : ℝ≥0∞` (including
`q' = 0`). -/
theorem memBesov_toDistr_partialSumCLM (s' : ℝ) (q' : ℝ≥0∞) (N : ℕ) (u : BesovSpace F φ s p q) :
    (partialSumCLM F φ s p q N u).toDistr.MemBesov φ s' p q' := by
  rw [toDistr_partialSumCLM]
  exact memBesov_sum_littlewoodPaleyBlock s' q' N u

/-- Every dyadic partial sum `S_N u` comes from any higher-order Besov space `B^{s'}_{p,q'}` with
`s < s'`. -/
theorem partialSumCLM_mem_range_inclusionOfLT {s' : ℝ} (hs : s < s') (q' : ℝ≥0∞) [Fact (1 ≤ q')]
    (N : ℕ) (u : BesovSpace F φ s p q) :
    partialSumCLM F φ s p q N u ∈ Set.range (inclusionOfLT F φ p q' q hs) :=
  ⟨(memBesov_toDistr_partialSumCLM s' q' N u).toBesovSpace, ext (by simp)⟩

/-- **Dyadic partial sums converge in `B^s_{p,q}` for `q < ∞`.** For every `1 ≤ p ≤ ∞` and
`1 ≤ q < ∞`, `S_N u → u` in the `B^s_{p,q}` norm as `N → ∞`. -/
theorem tendsto_partialSumCLM (hq : q ≠ ∞) (u : BesovSpace F φ s p q) :
    Tendsto (fun N ↦ partialSumCLM F φ s p q N u) atTop (𝓝 u) := by
  obtain ⟨C, -, hC⟩ := exists_norm_sub_partialSumCLM_le (F := F) φ s
  have hsum := tendsto_iff_norm_sub_tendsto_zero.1
    (lp.hasSum_single hq u.weightedBlocks).tendsto_sum_nat
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) (by simpa using hsum.const_mul C)
  rw [norm_sub_rev, norm_sub_rev (∑ i ∈ Finset.range N, _)]
  exact hC N u

omit [Fact (1 ≤ q)] in
/-- **Dyadic partial sums converge in `B^s_{p,∞}` when the weighted block norms vanish at
infinity.** The converse holds as well; see
`TauCeti.BesovSpace.mem_littleBesov_iff_tendsto_partialSumCLM`. -/
theorem tendsto_partialSumCLM_top_of_tendsto {u : BesovSpace F φ s p ∞}
    (hu : Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖u.block j‖) atTop (𝓝 0)) :
    Tendsto (fun N ↦ partialSumCLM F φ s p ∞ N u) atTop (𝓝 u) := by
  obtain ⟨C, -, hC⟩ := exists_norm_sub_partialSumCLM_le (F := F) φ s
  have htail : Tendsto (fun N ↦
      ‖u.weightedBlocks - ∑ i ∈ Finset.range N, lp.single ∞ i (u.weightedBlocks i)‖)
      atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hu (ε / 2) (half_pos hε)
    refine ⟨N₀, fun N hN ↦ ?_⟩
    rw [Real.dist_0_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (lp.norm_le_of_forall_le (half_pos hε).le fun j ↦ ?_).trans_lt (half_lt_self hε)
    rw [lp.sub_sum_single_apply]
    split_ifs with hj
    · simp [(half_pos hε).le]
    · rw [norm_weightedBlocks_apply]
      have hj' := hN₀ j (hN.trans (not_lt.1 (mt Finset.mem_range.2 hj)))
      rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at hj'
      exact hj'.le
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) (by simpa using htail.const_mul C)
  rw [norm_sub_rev]
  exact hC N u

end PartialSum

section Density

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- For `1 ≤ p < ∞` and *every* `1 ≤ q ≤ ∞` (including `q = ∞`), each dyadic partial sum `S_N u`
lies in the `B^s_{p,q}`-norm closure of `𝓢(E, F)`: it lifts to `H^{s+1,p}(E, F)`, where Schwartz
functions are dense. -/
theorem partialSumCLM_mem_closure_range_toBesovSpaceCLM (hp : p ≠ ∞) (N : ℕ)
    (u : BesovSpace F φ s p q) :
    partialSumCLM F φ s p q N u ∈ closure (Set.range (SchwartzMap.toBesovSpaceCLM φ s p q)) := by
  let v : BesovSpace F φ (s + 1) p 1 :=
    (memBesov_toDistr_partialSumCLM (s + 1) 1 N u).toBesovSpace
  let w : H^{s + 1, p}(E, F) := v.toBesselPotentialSpace
  let T : H^{s + 1, p}(E, F) →L[ℂ] BesovSpace F φ s p q :=
    inclusionOfLT F φ p ∞ q (lt_add_one s) ∘L BesselPotentialSpace.toBesovSpace φ
  have hTw : T w = partialSumCLM F φ s p q N u := ext (by simp [T, w, v])
  have hw : w ∈ closure (Set.range (SchwartzMap.toBesselPotentialSpaceCLM (s + 1) p)) :=
    SchwartzMap.denseRange_toBesselPotentialSpaceCLM (s + 1) hp w
  rw [← hTw]
  have himg := image_closure_subset_closure_image T.continuous (Set.mem_image_of_mem T hw)
  rwa [← Set.range_comp] at himg

/-- Compactly supported smooth functions and Schwartz functions have the same norm closure in every
Besov space `B^s_{p,q}(E, F)` (`1 ≤ p, q ≤ ∞`), because compactly supported functions are dense in
`𝓢(E, F)` and `SchwartzMap.toBesovSpaceCLM` is continuous. -/
theorem closure_image_toBesovSpaceCLM_hasCompactSupport :
    closure (SchwartzMap.toBesovSpaceCLM φ s p q ''
        {f : 𝓢(E, F) | HasCompactSupport (f : E → F)}) =
      closure (Set.range (SchwartzMap.toBesovSpaceCLM φ s p q)) := by
  refine Set.Subset.antisymm (closure_mono (Set.image_subset_range _ _)) ?_
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨f, rfl⟩
  have hf : f ∈ closure {g : 𝓢(E, F) | HasCompactSupport (g : E → F)} :=
    SchwartzMap.dense_hasCompactSupport f
  exact image_closure_subset_closure_image (SchwartzMap.toBesovSpaceCLM φ s p q).continuous
    (Set.mem_image_of_mem _ hf)

/-- **Schwartz functions are dense in `B^s_{p,q}(E, F)`** for `1 ≤ p < ∞` and `1 ≤ q < ∞`
(Bergh–Löfström, Theorem 6.2.4 / Triebel, Section 2.3.2). -/
theorem _root_.SchwartzMap.denseRange_toBesovSpaceCLM (φ : ContDiffBump (0 : E)) (s : ℝ)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ∞) (hq : q ≠ ∞) :
    DenseRange (SchwartzMap.toBesovSpaceCLM (E := E) (F := F) φ s p q) := fun u ↦
  isClosed_closure.mem_of_tendsto (tendsto_partialSumCLM hq u)
    (Eventually.of_forall fun N ↦ partialSumCLM_mem_closure_range_toBesovSpaceCLM hp N u)

/-- **Compactly supported smooth functions are dense in `B^s_{p,q}(E, F)`** for `1 ≤ p < ∞` and
`1 ≤ q < ∞`. -/
theorem _root_.SchwartzMap.dense_image_toBesovSpaceCLM_hasCompactSupport
    (φ : ContDiffBump (0 : E)) (s : ℝ) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Dense (SchwartzMap.toBesovSpaceCLM φ s p q ''
      {f : 𝓢(E, F) | HasCompactSupport (f : E → F)}) := by
  rw [dense_iff_closure_eq, closure_image_toBesovSpaceCLM_hasCompactSupport,
    ← dense_iff_closure_eq]
  exact SchwartzMap.denseRange_toBesovSpaceCLM φ s hp hq

/-- Explicit norm approximation in `B^s_{p,q}(E, F)` (`p, q < ∞`) by compactly supported Schwartz
functions. -/
theorem exists_hasCompactSupport_norm_sub_lt (hp : p ≠ ∞) (hq : q ≠ ∞)
    (u : BesovSpace F φ s p q) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(E, F), HasCompactSupport (f : E → F) ∧
      ‖u - f.toBesovSpaceCLM φ s p q‖ < ε := by
  obtain ⟨_, ⟨f, hf, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1
    ((SchwartzMap.dense_image_toBesovSpaceCLM_hasCompactSupport φ s hp hq) u) ε hε
  exact ⟨f, hf, by rwa [dist_eq_norm] at hdist⟩

/-- Continuous semilinear maps out of `B^s_{p,q}(E, F)` (`p, q < ∞`) into a Hausdorff space are
determined by their values on compactly supported Schwartz functions. -/
theorem continuousLinearMap_ext_hasCompactSupport {R : Type*} [Semiring R] {σ : ℂ →+* R}
    {Z : Type*} [AddCommMonoid Z] [Module R Z] [TopologicalSpace Z] [T2Space Z]
    (hp : p ≠ ∞) (hq : q ≠ ∞) {T T' : BesovSpace F φ s p q →SL[σ] Z}
    (h : ∀ f : 𝓢(E, F), HasCompactSupport (f : E → F) →
      T (f.toBesovSpaceCLM φ s p q) = T' (f.toBesovSpaceCLM φ s p q)) :
    T = T' := by
  refine ContinuousLinearMap.ext fun u ↦ ?_
  refine (SchwartzMap.dense_image_toBesovSpaceCLM_hasCompactSupport φ s hp hq).induction ?_
    (isClosed_eq T.continuous T'.continuous) u
  rintro _ ⟨f, hf, rfl⟩
  exact h f hf

/-- Continuous semilinear maps out of `B^s_{p,q}(E, F)` (`p, q < ∞`) into a Hausdorff space are
determined by their values on Schwartz functions. -/
theorem continuousLinearMap_ext {R : Type*} [Semiring R] {σ : ℂ →+* R}
    {Z : Type*} [AddCommMonoid Z] [Module R Z] [TopologicalSpace Z] [T2Space Z]
    (hp : p ≠ ∞) (hq : q ≠ ∞) {T T' : BesovSpace F φ s p q →SL[σ] Z}
    (h : ∀ f : 𝓢(E, F), T (f.toBesovSpaceCLM φ s p q) = T' (f.toBesovSpaceCLM φ s p q)) :
    T = T' :=
  continuousLinearMap_ext_hasCompactSupport hp hq fun f _ ↦ h f

end Density

end TauCeti.BesovSpace
