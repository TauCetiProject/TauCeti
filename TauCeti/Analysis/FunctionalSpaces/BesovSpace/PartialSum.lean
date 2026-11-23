/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Dyadic partial-sum operators on inhomogeneous Besov spaces

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space and let
`Δⱼ` (`j ≥ 0`) be its inhomogeneous Littlewood–Paley blocks. For any `u ∈ B^s_{p,q}(E, F)` the
dyadic partial sums `S_N u = ∑_{j < N} Δⱼ u` define uniformly bounded operators
`TauCeti.BesovSpace.partialSumCLM` on `B^s_{p,q}(E, F)`; the Fourier transform of each `S_N u` is
supported in `Metric.closedBall 0 (2 ^ N * φ.rOut)`.

Because the blocks `Δₖ` and `Δⱼ` interact only at bounded distance `|k - j| < L`
(`TemperedDistribution.exists_littlewoodPaleyBlock_sub_sum_range_eq`), the block `Δₖ (u - S_N u)` is
a bounded window sum of the blocks `Δⱼ u` with `j ≥ N`. Thus `‖u - S_N u‖_{B^s_{p,q}}` is controlled
by the `ℓ^q` norm of the tail `(2^{js} ‖Δⱼ u‖_p)_{j ≥ N}`:

* for `q < ∞` (and all `1 ≤ p ≤ ∞`), `S_N u → u` in `B^s_{p,q}(E, F)` as `N → ∞`
  (`TauCeti.BesovSpace.tendsto_partialSumCLM`);
* at `q = ∞` (and all `1 ≤ p ≤ ∞`), `S_N u → u` in `B^s_{p,∞}(E, F)` if and only if
  `2^{js} ‖Δⱼ u‖_p → 0` (`TauCeti.BesovSpace.tendsto_partialSumCLM_top_iff`);
* since the Fourier transform of each `S_N u` has compact support, `S_N u` lies in `B^{s'}_{p,q'}`
  for every `s' ∈ ℝ` and `q' ∈ [0, ∞]` (`TauCeti.BesovSpace.memBesov_toDistr_partialSumCLM`).

## Main declarations

* `TauCeti.BesovSpace.partialSumCLM`: the dyadic partial-sum operator `u ↦ ∑_{j < N} Δⱼ u` on
  `B^s_{p,q}(E, F)`, bounded uniformly in `N`, `p` and `q`
  (`TauCeti.BesovSpace.exists_norm_sub_partialSumCLM_le`,
  `TauCeti.BesovSpace.exists_norm_partialSumCLM_le`).
* `TauCeti.BesovSpace.memBesov_toDistr_partialSumCLM` and
  `TauCeti.BesovSpace.partialSumCLM_mem_range_inclusionOfLT`: smoothing property of `S_N u`.
* `TauCeti.BesovSpace.tendsto_partialSumCLM`,
  `TauCeti.BesovSpace.tendsto_partialSumCLM_top_of_tendsto`, and
  `TauCeti.BesovSpace.tendsto_partialSumCLM_top_iff`: convergence of `S_N u` to `u` for `q < ∞` and
  its characterization at `q = ∞`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2.
* H. Triebel, *Theory of Function Spaces*, Section 2.3.2.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.7.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

open TemperedDistribution

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
        (lp.norm_sub_sum_single_le _ _).trans_eq (norm_weightedBlocks u)
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
infinity.** For the equivalence, see `TauCeti.BesovSpace.tendsto_partialSumCLM_top_iff`. -/
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

omit [Fact (1 ≤ q)] in
/-- **Characterization of partial-sum convergence at `q = ∞`.** For every `1 ≤ p ≤ ∞` and
`u ∈ B^s_{p,∞}(E, F)`, `S_N u → u` in `B^s_{p,∞}(E, F)` if and only if `2^{js} ‖Δⱼ u‖_p → 0` as
`j → ∞`. -/
theorem tendsto_partialSumCLM_top_iff {u : BesovSpace F φ s p ∞} :
    Tendsto (fun N ↦ partialSumCLM F φ s p ∞ N u) atTop (𝓝 u) ↔
      Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (s * j) * ‖u.block j‖) atTop (𝓝 0) := by
  refine ⟨fun ht ↦ isClosed_setOf_tendsto_rpow_mul_norm_block.mem_of_tendsto ht
    (Eventually.of_forall fun N ↦ ?_), tendsto_partialSumCLM_top_of_tendsto⟩
  set v : BesovSpace F φ s p 1 := (memBesov_toDistr_partialSumCLM s 1 N u).toBesovSpace
  have hv_eq : inclusion F φ p le_rfl le_top v = partialSumCLM F φ s p ∞ N u := ext (by simp [v])
  simpa only [Set.mem_ofPred_eq, ← hv_eq, block_inclusion] using
    tendsto_rpow_mul_norm_block ENNReal.one_ne_top v

end TauCeti.BesovSpace
