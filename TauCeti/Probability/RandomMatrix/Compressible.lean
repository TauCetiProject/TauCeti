/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.Compressible.Net
public import TauCeti.Probability.Moments.SubGaussian.Matrix.SmallBall
public import TauCeti.Probability.Moments.SubGaussian.Matrix
import TauCeti.Analysis.SpecialFunctions.Choose

/-!
# Invertibility on compressible vectors

For independent, uniformly sub-Gaussian real entries with second moments bounded below by
one, a matrix with at least half as many rows as columns stretches every compressible unit
vector by a constant times the square root of the row count, outside an exponentially small
event. In particular the bound applies to an `(N - 1) × N` matrix for `N ≥ 2`, whose kernel
is the orthogonal complement of the span of its rows.
The approximation radius, allowed fraction of nonzero coordinates, and exponential rate
depend only on the common variance proxy.

The finite bound retains the binomial factor for the supports and splits off the operator
norm tail. It is stated for outer probabilities, so it also applies to almost everywhere
measurable matrix entries.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Lemma 3.3.
* M. Rudelson and R. Vershynin, *The smallest singular value of a random rectangular matrix*,
  Communications on Pure and Applied Mathematics 62 (2009); Lemma 2.6 of the preprint
  arXiv:0802.3956v4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Finset Matrix
open scoped Matrix.Norms.L2Operator NNReal

namespace ProbabilityTheory.iIndepFun

variable {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [DecidableEq n]
  {P : Measure Ω} {A : Ω → Matrix m n ℝ} {K : ℝ≥0}

omit [MeasurableSpace Ω] in
private theorem compressible_event_subset_net
    {k : ℕ} {ρ η : ℝ≥0} {N : Finset (EuclideanSpace ℝ n)}
    (hcover : IsCover (2 * ρ + η) {x | TauCeti.IsCompressibleVector k ρ x}
      (N : Set (EuclideanSpace ℝ n))) {M t : ℝ} :
    {ω | ‖A ω‖ ≤ M ∧ ∃ x, TauCeti.IsCompressibleVector k ρ x ∧
        ‖toEuclideanLin (A ω) x‖ < t - (2 * (ρ : ℝ) + (η : ℝ)) * M} ⊆
      ⋃ y ∈ N, {ω | ‖toEuclideanLin (A ω) y‖ < t} := by
  rintro ω ⟨hA, x, hx, hsmall⟩
  obtain ⟨y, hy, hxy⟩ := hcover hx
  have hd : dist x y ≤ 2 * (ρ : ℝ) + (η : ℝ) := by
    exact_mod_cast (edist_le_coe.mp hxy)
  let L := toEuclideanLin (A ω)
  have hop : ‖L.toContinuousLinearMap‖ = ‖A ω‖ := by
    rw [Matrix.l2_opNorm_def, LinearEquiv.trans_apply]
  have hdiff : ‖L y - L x‖ ≤ (2 * (ρ : ℝ) + (η : ℝ)) * M := calc
    _ = ‖L (y - x)‖ := by rw [map_sub]
    _ ≤ ‖A ω‖ * dist x y := by
      rw [dist_comm, dist_eq_norm, ← hop]
      exact L.toContinuousLinearMap.le_opNorm (y - x)
    _ ≤ _ := by
      calc
        ‖A ω‖ * dist x y ≤ M * dist x y :=
          mul_le_mul_of_nonneg_right hA dist_nonneg
        _ ≤ _ := by
          rw [mul_comm M]
          exact mul_le_mul_of_nonneg_right hd ((norm_nonneg _).trans hA)
  have hny : ‖L y‖ ≤ ‖L y - L x‖ + ‖L x‖ := norm_le_norm_sub_add _ _
  have hsmall' : ‖L x‖ < t - (2 * (ρ : ℝ) + (η : ℝ)) * M := hsmall
  have ht : ‖L y‖ < t := by linarith only [hny, hdiff, hsmall']
  exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, ht⟩⟩

/-- The probability of the compressible-vector lower-tail event intersected with
`{ω | ‖A ω‖ ≤ M}` is at most the size bound for a sparse sphere net times the fixed-direction
tail. Here `K` is the common variance proxy and `v` bounds every entry's second moment below. -/
theorem measureReal_exists_isCompressibleVector_norm_toEuclideanLin_lt_le
    (hind : iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P)
    (hA : ∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P)
    {v : ℝ} (hmom : ∀ i j, v ≤ ∫ ω, (A ω i j) ^ 2 ∂P)
    {k : ℕ} (hk : k ≤ Fintype.card n) {ρ η : ℝ≥0} (hρ : ρ < 1) (hη : η ≠ 0)
    (M : ℝ) :
    P.real {ω | ‖A ω‖ ≤ M ∧ ∃ x, TauCeti.IsCompressibleVector k ρ x ∧
        ‖toEuclideanLin (A ω) x‖ <
          Real.sqrt (v * Fintype.card m) / 2 - (2 * (ρ : ℝ) + (η : ℝ)) * M} ≤
      ((Fintype.card n).choose k * (1 + 2 / (η : ℝ)) ^ k) *
        (2 * Real.exp (-(1 / 1536) *
          min (v ^ 2 / (4 * (K : ℝ) ^ 2)) (v / (2 * (K : ℝ))) * Fintype.card m)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  obtain ⟨N, hNs, hcover, hcard⟩ :=
    TauCeti.exists_finset_isCover_isCompressibleVector (𝕜 := ℝ) hk hρ hη
  have hcard' : (N.card : ℝ) ≤ (Fintype.card n).choose k * (1 + 2 / (η : ℝ)) ^ k := by
    simpa using hcard
  let t := Real.sqrt (v * Fintype.card m) / 2
  let q := 2 * Real.exp (-(1 / 1536) *
    min (v ^ 2 / (4 * (K : ℝ) ^ 2)) (v / (2 * (K : ℝ))) * Fintype.card m)
  calc
    _ ≤ P.real (⋃ y ∈ N, {ω | ‖toEuclideanLin (A ω) y‖ < t}) :=
      measureReal_mono (compressible_event_subset_net (A := A) hcover) (measure_ne_top _ _)
    _ ≤ ∑ y ∈ N, P.real {ω | ‖toEuclideanLin (A ω) y‖ < t} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ N, q := sum_le_sum fun y hy ↦
      hind.measureReal_norm_toEuclideanLin_lt_le hA hmom (hNs hy).norm_eq_one
    _ = (N.card : ℝ) * q := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard' (by positivity)

private def fixedDirectionRate (L : ℝ≥0) : ℝ :=
  (1 / 1536) * min (1 / (4 * ((L ^ 2 : ℝ≥0) : ℝ) ^ 2)) (1 / (2 * ((L ^ 2 : ℝ≥0) : ℝ)))

private theorem measureReal_compressible_le_exp
    (hind : iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P)
    {L : ℝ≥0} (hA : ∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) (L ^ 2) P)
    (hmom : ∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P)
    (hdim : Fintype.card n ≤ 2 * Fintype.card m) {k : ℕ} (hk : k ≤ Fintype.card n)
    {ρ : ℝ≥0} (hρ : ρ ≠ 0) (hρ₁ : ρ < 1) (hscale : 3 * (ρ : ℝ) * (28 * L) ≤ 1 / 4)
    (hcard : (Fintype.card n).choose k * (1 + 2 / (ρ : ℝ)) ^ k ≤
      Real.exp (fixedDirectionRate L / 2 * Fintype.card m)) :
    P.real {ω | ∃ x, TauCeti.IsCompressibleVector k ρ x ∧
      ‖toEuclideanLin (A ω) x‖ < Real.sqrt (Fintype.card m) / 4} ≤
      4 * Real.exp (-min 1 (fixedDirectionRate L / 2) * Fintype.card m) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let d : ℝ := Fintype.card m
  let M : ℝ := 28 * (L : ℝ) * Real.sqrt d
  let g := fixedDirectionRate L
  have hthreshold : Real.sqrt d / 4 ≤
      Real.sqrt d / 2 - (2 * (ρ : ℝ) + (ρ : ℝ)) * M := by
    dsimp only [M]
    nlinarith [mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg d)]
  have hnet := hind.measureReal_exists_isCompressibleVector_norm_toEuclideanLin_lt_le
    hA hmom hk hρ₁ hρ M
  rw [one_mul, one_pow] at hnet
  have hnorm := hind.measureReal_l2_opNorm_gt_le_of_card_le_two_mul hA hdim
  have hsub : {ω | ∃ x, TauCeti.IsCompressibleVector k ρ x ∧
        ‖toEuclideanLin (A ω) x‖ < Real.sqrt d / 4} ⊆
      {ω | M < ‖A ω‖} ∪ {ω | ‖A ω‖ ≤ M ∧ ∃ x, TauCeti.IsCompressibleVector k ρ x ∧
        ‖toEuclideanLin (A ω) x‖ < Real.sqrt d / 2 - (2 * (ρ : ℝ) + (ρ : ℝ)) * M} := by
    rintro ω ⟨x, hx, hsmall⟩
    rcases le_or_gt ‖A ω‖ M with h | h
    · exact Or.inr ⟨h, x, hx, hsmall.trans_le hthreshold⟩
    · exact Or.inl h
  have hrate (q : ℝ) (hq : min 1 (g / 2) ≤ q) :
      Real.exp (-q * d) ≤ Real.exp (-min 1 (g / 2) * d) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hq) (Nat.cast_nonneg _))
  calc
    _ ≤ _ := (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    _ ≤ 2 * Real.exp (-d) +
        ((Fintype.card n).choose k * (1 + 2 / (ρ : ℝ)) ^ k) *
          (2 * Real.exp (-g * d)) :=
      add_le_add hnorm (by simpa only [g, fixedDirectionRate, neg_mul] using hnet)
    _ ≤ 2 * Real.exp (-d) + Real.exp ((g / 2) * d) * (2 * Real.exp (-g * d)) := by gcongr
    _ = 2 * Real.exp (-d) + 2 * Real.exp (-(g / 2) * d) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 3
      ring
    _ ≤ 2 * Real.exp (-min 1 (g / 2) * d) + 2 * Real.exp (-min 1 (g / 2) * d) := by
      have h₁ : Real.exp (-d) ≤ Real.exp (-min 1 (g / 2) * d) := by
        simpa only [neg_one_mul] using hrate 1 (min_le_left _ _)
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ (by norm_num))
        (mul_le_mul_of_nonneg_left (hrate _ (min_le_right _ _)) (by norm_num))
    _ = _ := by ring

end ProbabilityTheory.iIndepFun

namespace TauCeti.Probability

open ProbabilityTheory.iIndepFun

/-- For a real random matrix with independent, uniformly sub-Gaussian entries of second moments
at least one and at least half as many rows as columns, the outer probability that the matrix
maps some compressible unit vector to a vector of norm below `√(card m) / 4` is exponentially
small in the row count. Compressible means within `ρ` of a vector supported on at most
`⌊δ * card n⌋₊` coordinates. The theorem supplies the sparsity fraction `δ`, the radius `ρ` and
the rate `a`, which depend only on the common sub-Gaussian variance proxy `K`. -/
theorem exists_measureReal_exists_isCompressibleVector_norm_toEuclideanLin_lt_le (K : ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ ∃ a : ℝ, 0 < a ∧
      ∀ {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n] [DecidableEq n]
        {P : Measure Ω} {A : Ω → Matrix m n ℝ},
        iIndepFun (fun ij : m × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        Fintype.card n ≤ 2 * Fintype.card m →
        P.real {ω | ∃ x, TauCeti.IsCompressibleVector ⌊δ * Fintype.card n⌋₊ ρ x ∧
          ‖toEuclideanLin (A ω) x‖ < Real.sqrt (Fintype.card m) / 4} ≤
          4 * Real.exp (-a * Fintype.card m) := by
  let L : ℝ≥0 := K + 1
  let ρ : ℝ≥0 := (336 * L)⁻¹
  let g := fixedDirectionRate L
  have hL : 1 ≤ L := by simp [L]
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hg : 0 < g := by dsimp [g, fixedDirectionRate]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ₄ : ρ ≤ 1 / 4 := by
    apply NNReal.coe_le_coe.mp
    push_cast
    dsimp only [ρ]
    push_cast
    have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
    rw [inv_eq_one_div]
    exact (div_le_div_iff_of_pos_left one_pos (by positivity) (by positivity)).mpr (by linarith)
  obtain ⟨δ, hδ, hδ₁, hentropy⟩ :=
    TauCeti.exists_pos_choose_mul_pow_le_exp (1 + 2 / (ρ : ℝ)) (div_pos hg four_pos)
  refine ⟨δ, hδ, hδ₁, ρ, hρ, hρ₄, min 1 (g / 2), lt_min one_pos (half_pos hg), ?_⟩
  intro Ω m n _ _ _ _ P A hind hA hmom hdim
  let k := ⌊δ * Fintype.card n⌋₊
  have hk : (k : ℝ) ≤ δ * Fintype.card n := Nat.floor_le (by positivity)
  have hkn : k ≤ Fintype.card n := by
    exact_mod_cast hk.trans (mul_le_of_le_one_left (Nat.cast_nonneg (Fintype.card n)) hδ₁)
  have hKL : K ≤ L := le_add_of_nonneg_right zero_le_one
  have hboundK : K ≤ L ^ 2 := hKL.trans (by simpa [pow_two] using
    (le_mul_of_one_le_right (by positivity : (0 : ℝ≥0) ≤ L) hL))
  have hAc i j := (hA i j).mono hboundK
  have hscale : 3 * (ρ : ℝ) * (28 * L) ≤ 1 / 4 := by
    dsimp [ρ]
    have hLn : (L : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
    field_simp
    norm_num
  -- The entropy rate `g / 4` per column is at most `g / 2` per row.
  have hd : g / 4 * Fintype.card n ≤ g / 2 * Fintype.card m := by
    have hd' : (Fintype.card n : ℝ) ≤ 2 * Fintype.card m := by exact_mod_cast hdim
    nlinarith only [hd', hg]
  have hcard := (hentropy (Fintype.card n) k hk).trans (Real.exp_le_exp.2 hd)
  exact hind.measureReal_compressible_le_exp hAc hmom hdim hkn hρ.ne'
    (hρ₄.trans_lt (by norm_num)) hscale hcard

end TauCeti.Probability
