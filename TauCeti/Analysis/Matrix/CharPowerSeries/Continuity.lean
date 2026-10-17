/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.Basic

/-!
# Continuity of principal-minor coefficients

For ultrametric coefficient rings, the coefficients of `det (1 - T A)` satisfy the
entrywise perturbation estimate

`‖A.charCoeff n - B.charCoeff n‖ ≤ ε * M ^ (n - 1)`

when both matrices have entries of norm at most `M`, corresponding entries differ by at most
`ε`, and the size-`n` principal-minor families are summable. There is no factor depending on
the number of minors or on the size of the index type. Over complete coefficient rings, the
estimate applies in particular to matrices with null row majorants, by
`Matrix.summable_principalMinor`.

Consequently uniform entrywise convergence to a bounded matrix implies convergence of each
coefficient, provided the principal-minor sums converge. This is the coefficientwise continuity
needed to pass from finite-dimensional determinant identities to Fredholm determinants. It does
not assert convergence in Gauss norm without additional control of coefficient tails.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
-/

public section

open Filter Finset Topology

namespace TauCeti

variable {ι R : Type*} [DecidableEq ι]
  [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- Fredholm coefficients are Lipschitz on entrywise bounded sets whenever the defining
principal-minor sums converge. In particular, over a complete coefficient ring this applies to
matrices with null row majorants (`Matrix.summable_principalMinor`).
No completeness hypothesis is needed once summability is supplied. -/
theorem norm_charCoeff_sub_le {A B : Matrix ι ι R} {n : ℕ} {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hA : ∀ i j, ‖A i j‖ ≤ M) (hB : ∀ i j, ‖B i j‖ ≤ M)
    (hAB : ∀ i j, ‖A i j - B i j‖ ≤ ε)
    (hAs : Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s)
    (hBs : Summable fun s : {s : Finset ι // s.card = n} ↦ B.principalMinor s) :
    ‖A.charCoeff n - B.charCoeff n‖ ≤ ε * M ^ (n - 1) := by
  have hsum : ‖∑' s : {s : Finset ι // s.card = n},
      (A.principalMinor s - B.principalMinor s)‖ ≤ ε * M ^ (n - 1) :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun s ↦ by
      simpa only [s.2] using norm_principalMinor_sub_le (s := s.1) hM hε hA hB hAB
  rw [Matrix.charCoeff_def, Matrix.charCoeff_def, ← mul_sub, ← hAs.tsum_sub hBs]
  rcases neg_one_pow_eq_or R n with hn | hn <;> simpa only [hn, one_mul, neg_one_mul,
    norm_neg] using hsum

/-- Uniform entrywise convergence to a bounded matrix implies convergence of each
principal-minor coefficient, as long as the relevant principal-minor sums are summable.
The uniform entry bound is required only for the limit matrix. -/
theorem tendsto_charCoeff_of_tendstoUniformly {α : Type*} {l : Filter α}
    {A : α → Matrix ι ι R} {B : Matrix ι ι R} {M : ℝ} (n : ℕ)
    (hB : ∀ i j, ‖B i j‖ ≤ M)
    (hAs : ∀ᶠ a in l, Summable fun s : {s : Finset ι // s.card = n} ↦
      (A a).principalMinor s)
    (hBs : Summable fun s : {s : Finset ι // s.card = n} ↦ B.principalMinor s)
    (hAB : TendstoUniformly (fun a (p : ι × ι) ↦ A a p.1 p.2)
      (fun p ↦ B p.1 p.2) l) :
    Tendsto (fun a ↦ (A a).charCoeff n) l (𝓝 (B.charCoeff n)) := by
  let C := max 1 M
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  have hBC : ∀ i j, ‖B i j‖ ≤ C := fun i j ↦ (hB i j).trans (le_max_right _ _)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := min 1 (ε / (2 * C ^ (n - 1)))
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  filter_upwards [hAs, Metric.tendstoUniformly_iff.mp hAB δ hδ] with a hAs ha
  have hdiff : ∀ i j, ‖A a i j - B i j‖ ≤ δ := fun i j ↦ by
    simpa only [dist_eq_norm, norm_sub_rev] using (ha (i, j)).le
  have hAC : ∀ i j, ‖A a i j‖ ≤ C := fun i j ↦ by
    calc ‖A a i j‖ ≤ max ‖A a i j - B i j‖ ‖B i j‖ := by
          simpa using IsUltrametricDist.norm_add_le_max (A a i j - B i j) (B i j)
      _ ≤ C := max_le ((hdiff i j).trans ((min_le_left _ _).trans hC)) (hBC i j)
  rw [dist_eq_norm]
  calc ‖(A a).charCoeff n - B.charCoeff n‖ ≤ δ * C ^ (n - 1) :=
        norm_charCoeff_sub_le hC₀.le hδ.le hAC hBC hdiff hAs hBs
    _ ≤ (ε / (2 * C ^ (n - 1))) * C ^ (n - 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hC₀.le _)
    _ < ε := by
      field_simp
      linarith

end TauCeti
