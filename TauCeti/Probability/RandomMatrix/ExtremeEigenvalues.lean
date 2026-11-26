/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.Analysis.Matrix.SpectralMeasure.ExtremeEigenvalues
public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
public import TauCeti.Probability.RandomMatrix.Wigner.SemicircleLaw
import TauCeti.Analysis.Matrix.SampleCovariance.Eigenvalues

/-!
# Extreme eigenvalues beyond the edges of global laws

A weak spectral limit forces eigenvalues near every point of its support. Applied at the edges
of the Marchenko–Pastur and semicircle laws, this gives the lower halves of the edge limit
theorems for sample covariance and Wigner matrices.

For Hermitian matrices whose empirical spectral measures converge weakly to `MP_y`, the largest
eigenvalue eventually exceeds every `c < (1 + √y)²`, and the smallest is eventually below every
`c > (1 - √y)²`. There are also eventually positive
eigenvalues in `(0, c)` for every `c > (1 - √y)²`. For `y > 1` a `p × p` sample covariance
matrix `XXᴴ/n` with `p > n` has the eigenvalue zero, and this bounds its smallest positive
eigenvalue instead. These statements are deterministic: their hypothesis is the global law
itself.

For the corners of a Wigner array under the hypotheses of the almost-sure semicircle law,
almost surely the largest eigenvalue eventually exceeds every `c < 2` and the smallest is
eventually below every `c > -2`.

The matching bounds in the other direction, `limsup λ_max ≤ (1 + √y)²` and
`limsup λ_max(Hₙ) ≤ 2`, are not consequences of the global laws and need moment hypotheses.

## Main statements

* `TauCeti.Probability.eventually_lt_eigenvalues₀_zero_of_tendsto_marchenkoPastur`,
  `TauCeti.Probability.eventually_eigenvalues₀_card_sub_one_lt_of_tendsto_marchenkoPastur`,
  `TauCeti.Probability.eventually_exists_eigenvalues₀_mem_Ioo_of_tendsto_marchenkoPastur`:
  the Marchenko–Pastur edges.
* `TauCeti.Probability.tendsto_eigenvalues₀_zero_iff_of_tendsto_marchenkoPastur`,
  `TauCeti.Probability.tendsto_eigenvalues₀_card_sub_one_iff_of_tendsto_marchenkoPastur`: given
  the global law, convergence of the largest or smallest eigenvalue to the corresponding edge is
  equivalent to the remaining one-sided bound.
* `TauCeti.Probability.tendsto_sInf_pos_eigenvalues₀_sampleCovariance_of_tendsto_marchenkoPastur`:
  a matching lower bound gives convergence of the least positive sample covariance eigenvalue.
* `TauCeti.Probability.ae_eventually_lt_eigenvalues₀_zero_wignerMatrix`,
  `TauCeti.Probability.ae_eventually_eigenvalues₀_card_sub_one_lt_wignerMatrix`: the semicircle
  edges for Wigner matrices.

## References

* Z. Bai and J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer, 2010, Chapter 5.
-/

public section

open Filter MeasureTheory ProbabilityTheory Matrix Set
open scoped Topology NNReal

namespace TauCeti.Probability

section MarchenkoPastur

variable {ι 𝕜 : Type*} {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  [∀ i, Nonempty (n i)] [RCLike 𝕜] {l : Filter ι} {A : (i : ι) → Matrix (n i) (n i) 𝕜}
  {hA : ∀ i, (A i).IsHermitian} {y : ℝ≥0}

/-- If the empirical spectral measures of a family of Hermitian matrices converge weakly to the
Marchenko–Pastur law `MP_y`, then the largest eigenvalue eventually exceeds every
`c < (1 + √y)²`. -/
theorem eventually_lt_eigenvalues₀_zero_of_tendsto_marchenkoPastur
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l
      (𝓝 ⟨marchenkoPastur y, inferInstance⟩))
    {c : ℝ} (hc : c < (1 + √y) ^ 2) :
    ∀ᶠ i in l, c < (hA i).eigenvalues₀ ⟨0, Fintype.card_pos⟩ :=
  eventually_lt_eigenvalues₀_zero_of_tendsto_spectralMeasure h
    (one_add_sqrt_sq_mem_support_marchenkoPastur y) hc

/-- If the empirical spectral measures of a family of Hermitian matrices converge weakly to the
Marchenko–Pastur law `MP_y`, then the smallest eigenvalue is eventually below every
`c > (1 - √y)²`. -/
theorem eventually_eigenvalues₀_card_sub_one_lt_of_tendsto_marchenkoPastur
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l
      (𝓝 ⟨marchenkoPastur y, inferInstance⟩))
    {c : ℝ} (hc : (1 - √y) ^ 2 < c) :
    ∀ᶠ i in l, (hA i).eigenvalues₀ ⟨Fintype.card (n i) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩
      < c :=
  eventually_eigenvalues₀_card_sub_one_lt_of_tendsto_spectralMeasure h
    (one_sub_sqrt_sq_mem_support_marchenkoPastur y) hc

/-- If the empirical spectral measures of a family of Hermitian matrices converge weakly to the
Marchenko–Pastur law `MP_y`, then the largest eigenvalue tends to the upper edge `(1 + √y)²` if
and only if it is eventually below every `c > (1 + √y)²`. -/
theorem tendsto_eigenvalues₀_zero_iff_of_tendsto_marchenkoPastur
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l
      (𝓝 ⟨marchenkoPastur y, inferInstance⟩)) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀ ⟨0, Fintype.card_pos⟩) l (𝓝 ((1 + √y) ^ 2)) ↔
      ∀ c > (1 + √y) ^ 2, ∀ᶠ i in l, (hA i).eigenvalues₀ ⟨0, Fintype.card_pos⟩ < c :=
  tendsto_eigenvalues₀_zero_iff_of_tendsto_spectralMeasure h
    (one_add_sqrt_sq_mem_support_marchenkoPastur y)

/-- If the empirical spectral measures of a family of Hermitian matrices converge weakly to the
Marchenko–Pastur law `MP_y`, then the smallest eigenvalue tends to the lower edge `(1 - √y)²` if
and only if it eventually exceeds every `c < (1 - √y)²`. -/
theorem tendsto_eigenvalues₀_card_sub_one_iff_of_tendsto_marchenkoPastur
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l
      (𝓝 ⟨marchenkoPastur y, inferInstance⟩)) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀
        ⟨Fintype.card (n i) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩) l
        (𝓝 ((1 - √y) ^ 2)) ↔
      ∀ c < (1 - √y) ^ 2, ∀ᶠ i in l, c < (hA i).eigenvalues₀
        ⟨Fintype.card (n i) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩ :=
  tendsto_eigenvalues₀_card_sub_one_iff_of_tendsto_spectralMeasure h
    (one_sub_sqrt_sq_mem_support_marchenkoPastur y)

/-- If the empirical spectral measures of a family of Hermitian matrices converge weakly to the
Marchenko–Pastur law `MP_y`, then for every `c > (1 - √y)²` there is eventually an
eigenvalue in `(0, c)`. For `y > 1` this bounds the smallest positive eigenvalue, which is the
relevant edge for `p × p` sample covariance matrices `XXᴴ/n` with `p > n`, whose smallest
eigenvalue is zero. -/
theorem eventually_exists_eigenvalues₀_mem_Ioo_of_tendsto_marchenkoPastur
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l
      (𝓝 ⟨marchenkoPastur y, inferInstance⟩))
    {c : ℝ} (hc : (1 - √y) ^ 2 < c) :
    ∀ᶠ i in l, ∃ k, (hA i).eigenvalues₀ k ∈ Ioo 0 c := by
  rcases eq_or_ne y 1 with rfl | hy
  · have hc₀ : 0 < c := by simpa using hc
    obtain ⟨x, hx₀, hx⟩ := exists_between (lt_min hc₀ (by norm_num : (0 : ℝ) < 4))
    have hsupp : x ∈ (marchenkoPastur 1).support := by
      rw [support_marchenkoPastur_one]
      exact ⟨hx₀.le, (lt_min_iff.mp hx).2.le⟩
    exact eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure h hsupp
      (Ioo_mem_nhds hx₀ (lt_min_iff.mp hx).1)
  have hsqrt : √(y : ℝ) ≠ 1 := by
    rwa [Ne, Real.sqrt_eq_one, NNReal.coe_eq_one]
  have hpos : 0 < (1 - √(y : ℝ)) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.2 hsqrt.symm)
  exact eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure h
    (one_sub_sqrt_sq_mem_support_marchenkoPastur y) (Ioo_mem_nhds hpos hc)

end MarchenkoPastur

section SampleCovariance

/-- If the sample covariance spectral measures converge to the Marchenko–Pastur law and the
eigenvalues indexed below the sample size have the matching asymptotic lower bound, the least
positive eigenvalue eventually exists and tends to `(√y - 1) ^ 2`. -/
theorem tendsto_sInf_pos_eigenvalues₀_sampleCovariance_of_tendsto_marchenkoPastur
    {ι 𝕜 : Type*} [RCLike 𝕜] {p q : ι → Type*} [∀ i, Fintype (p i)] [∀ i, Fintype (q i)]
    [∀ i, DecidableEq (p i)] [∀ i, Nonempty (p i)] {l : Filter ι} {y : ℝ≥0}
    {X : (i : ι) → Matrix (p i) (q i) 𝕜}
    (hMP : Tendsto (fun i ↦ (sampleCovariance (X i)).spectralMeasure
      (isHermitian_sampleCovariance _)) l (𝓝 (marchenkoPastur y).toProbabilityMeasure))
    (hlow : ∀ c < (√y - 1) ^ 2, ∀ᶠ i in l, ∀ j : Fin (Fintype.card (p i)),
      j.val < Fintype.card (q i) →
      c < (isHermitian_sampleCovariance (X i)).eigenvalues₀ j) :
    let S (n : ι) := {s | 0 < s} ∩ Set.range (isHermitian_sampleCovariance (X n)).eigenvalues₀
    (∀ᶠ n in l, IsLeast (S n) (sInf (S n))) ∧
      Tendsto (fun n ↦ sInf (S n)) l (𝓝 ((√y - 1) ^ 2)) := by
  let S (n : ι) := {s | 0 < s} ∩ Set.range (isHermitian_sampleCovariance (X n)).eigenvalues₀
  have hedge : (1 - √(y : ℝ)) ^ 2 = (√y - 1) ^ 2 := by ring
  have hexists {c : ℝ} (hc : (√y - 1) ^ 2 < c) :
      ∀ᶠ n in l, ∃ i, (isHermitian_sampleCovariance (X n)).eigenvalues₀ i ∈ Set.Ioo 0 c :=
    eventually_exists_eigenvalues₀_mem_Ioo_of_tendsto_marchenkoPastur hMP (hedge.trans_lt hc)
  have hleast : ∀ᶠ n in l, IsLeast (S n) (sInf (S n)) := by
    filter_upwards [hexists (lt_add_one ((√y - 1) ^ 2))] with n ⟨i, hi⟩
    have hfinite : (S n).Finite := (Set.finite_range _).subset Set.inter_subset_right
    obtain ⟨s, hs, hmin⟩ := Set.exists_min_image (S n) id hfinite ⟨_, hi.1, ⟨i, rfl⟩⟩
    have hleast : IsLeast (S n) s := ⟨hs, hmin⟩
    rwa [hleast.csInf_eq]
  refine ⟨hleast, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro c hc
    filter_upwards [hleast, hlow c hc] with n hi hb
    obtain ⟨hpos, i, hi⟩ := hi.1
    have hni : i.val < Fintype.card (q n) := lt_of_not_ge fun hn ↦ (ne_of_gt hpos) (hi.symm.trans
      (eigenvalues₀_sampleCovariance_eq_zero_of_card_le _ i hn))
    exact hi ▸ hb i hni
  · intro c hc
    filter_upwards [hleast, hexists hc] with n hi ⟨j, hj₀, hjc⟩
    exact (hi.2 ⟨hj₀, ⟨j, rfl⟩⟩).trans_lt hjc

end SampleCovariance

section Wigner

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}

local notation "e₀" => (⟨(0, 1), by decide⟩ : StrictUpper)

/-- **Lower bound for the largest Wigner eigenvalue.** Under the hypotheses of the almost-sure
semicircle law, almost surely the largest eigenvalue of the normalized Wigner corners eventually
exceeds every `c < 2`. -/
theorem ae_eventually_lt_eigenvalues₀_zero_wignerMatrix (η : ℕ → Ω → ℝ)
    (hind : iIndepFun ξ P) (hid : ∀ i, IdentDistrib (ξ i) (ξ e₀) P P)
    (hv : ∫ ω, ‖ξ e₀ ω - ∫ ω', ξ e₀ ω' ∂P‖ ^ 2 ∂P = 1)
    (hηind : Pairwise fun i j ↦ IndepFun (η i) (η j) P)
    (hηid : ∀ i, IdentDistrib (η i) (η 0) P P) :
    ∀ᵐ ω ∂P, ∀ c < 2, ∀ᶠ n in atTop,
      c < (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
  filter_upwards [wigner_semicircle_ae η hind hid hv hηind hηid] with ω hω c hc
  exact eventually_lt_eigenvalues₀_zero_of_tendsto_spectralMeasure hω
    (by norm_num [support_semicircleReal]) hc

/-- **Upper bound for the smallest Wigner eigenvalue.** Under the hypotheses of the almost-sure
semicircle law, almost surely the smallest eigenvalue of the normalized Wigner corners is
eventually below every `c > -2`. -/
theorem ae_eventually_eigenvalues₀_card_sub_one_lt_wignerMatrix (η : ℕ → Ω → ℝ)
    (hind : iIndepFun ξ P) (hid : ∀ i, IdentDistrib (ξ i) (ξ e₀) P P)
    (hv : ∫ ω, ‖ξ e₀ ω - ∫ ω', ξ e₀ ω' ∂P‖ ^ 2 ∂P = 1)
    (hηind : Pairwise fun i j ↦ IndepFun (η i) (η j) P)
    (hηid : ∀ i, IdentDistrib (η i) (η 0) P P) :
    ∀ᵐ ω ∂P, ∀ c > -2, ∀ᶠ n in atTop,
      (wignerMatrix_isHermitian ξ η ω (n + 1)).eigenvalues₀
        ⟨Fintype.card (Fin (n + 1)) - 1, Nat.sub_one_lt Fintype.card_ne_zero⟩ < c := by
  filter_upwards [wigner_semicircle_ae η hind hid hv hηind hηid] with ω hω c hc
  exact eventually_eigenvalues₀_card_sub_one_lt_of_tendsto_spectralMeasure hω
    (by norm_num [support_semicircleReal]) hc

end Wigner

end TauCeti.Probability
