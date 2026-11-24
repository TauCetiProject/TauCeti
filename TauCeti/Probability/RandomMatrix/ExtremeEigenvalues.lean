/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.ExtremeEigenvalues
public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
public import TauCeti.Probability.RandomMatrix.Wigner.SemicircleLaw

/-!
# Extreme eigenvalues beyond the edges of global laws

A weak spectral limit forces eigenvalues near every point of its support. Applied at the edges
of the Marchenko–Pastur and semicircle laws, this gives the lower halves of the edge limit
theorems for sample covariance and Wigner matrices.

For Hermitian matrices whose empirical spectral measures converge weakly to `MP_y`, the largest
eigenvalue eventually exceeds every `c < (1 + √y)²`, and the smallest is eventually below every
`c > (1 - √y)²`. For `y ≠ 1` the lower edge `(1 - √y)²` is positive, so there are eventually
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
Marchenko–Pastur law `MP_y` with `y ≠ 1`, then for every `c > (1 - √y)²` there is eventually an
eigenvalue in `(0, c)`. For `y > 1` this bounds the smallest positive eigenvalue, which is the
relevant edge for `p × p` sample covariance matrices `XXᴴ/n` with `p > n`, whose smallest
eigenvalue is zero. -/
theorem eventually_exists_eigenvalues₀_mem_Ioo_of_tendsto_marchenkoPastur
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l
      (𝓝 ⟨marchenkoPastur y, inferInstance⟩))
    (hy : y ≠ 1) {c : ℝ} (hc : (1 - √y) ^ 2 < c) :
    ∀ᶠ i in l, ∃ k, (hA i).eigenvalues₀ k ∈ Ioo 0 c := by
  have hsqrt : √(y : ℝ) ≠ 1 := by
    rwa [Ne, Real.sqrt_eq_one, NNReal.coe_eq_one]
  have hpos : 0 < (1 - √(y : ℝ)) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.2 hsqrt.symm)
  exact eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure h
    (one_sub_sqrt_sq_mem_support_marchenkoPastur y) (Ioo_mem_nhds hpos hc)

end MarchenkoPastur

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
