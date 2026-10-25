/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Principal-minor series from two-sided matrix bounds

A bound `‖A i j‖ ≤ c i * d j` controls each principal minor by the product of
`c i * d i` over its indices. If these diagonal products tend to zero cofinitely,
the principal-minor sums converge and their power series is entire. Neither the
rows nor the columns of the matrix need admit a null uniform majorant.

In particular, for `0 < σ < 1`, an entry bound `σ ^ (w i - w' j)` and cofinite
growth of the integer differences `w i - w' i` suffice. The stronger bound
`σ ^ max (w i - w' j) 0` also suffices, since increasing the exponent decreases
its power. Negative diagonal differences are retained: their factors can exceed
one, but the null family of diagonal products is still bounded.

These results concern the convergent matrix minor series. They do not assert
that the matrix defines a bounded or row-compact operator. This distinction is
needed when comparing such a series with an operator determinant by diagonal
intertwining.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach
  p-adiques*, Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
* K. S. Kedlaya, *A little p-adic numerical analysis*, MIT 18.787 notes (2007), §3.
-/

public section

open Filter Finset Topology

namespace TauCeti

private theorem exists_two_sided_bounds_of_zpow {ι R : Type*} [SeminormedAddCommGroup R]
    {A : Matrix ι ι R} {σ : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1) {w w' : ι → ℤ}
    (hA : ∀ i j, ‖A i j‖ ≤ σ ^ (w i - w' j))
    (hw : Tendsto (fun i ↦ w i - w' i) cofinite atTop) :
    ∃ c d : ι → ℝ, (∀ i j, ‖A i j‖ ≤ c i * d j) ∧
      Tendsto (fun i ↦ c i * d i) cofinite (𝓝 0) := by
  refine ⟨(fun i ↦ σ ^ w i), (fun j ↦ σ ^ (-w' j)), ?_, ?_⟩
  · simpa only [← zpow_add₀ hσ₀.ne', ← sub_eq_add_neg] using hA
  · simpa only [← zpow_add₀ hσ₀.ne', ← sub_eq_add_neg, Function.comp_def,
      Real.rpow_intCast] using
      (tendsto_rpow_atTop_of_base_lt_one σ (by linarith) hσ₁).comp
        (tendsto_intCast_atTop_atTop.comp hw)

end TauCeti

namespace Matrix

variable {ι R : Type*} [DecidableEq ι]
  [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- Null diagonal products in a two-sided entry bound imply summability of the
principal minors of every fixed size. -/
theorem summable_principalMinor_of_two_sided [CompleteSpace R]
    {A : Matrix ι ι R} {c d : ι → ℝ} (hA : ∀ i j, ‖A i j‖ ≤ c i * d j)
    (hcd : Tendsto (fun i ↦ c i * d i) cofinite (𝓝 0)) (n : ℕ) :
    Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s :=
  summable_principalMinor_of_le_prod (norm_principalMinor_le_prod_mul hA) hcd n

/-- Null diagonal products in a two-sided entry bound make the principal-minor series
restricted at every radius. Completeness is only needed for summability, not this estimate. -/
theorem isRestricted_charPowerSeries_of_two_sided {A : Matrix ι ι R} {c d : ι → ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ c i * d j)
    (hcd : Tendsto (fun i ↦ c i * d i) cofinite (𝓝 0)) (ρ : ℝ) :
    A.charPowerSeries.IsRestricted ρ :=
  isRestricted_charPowerSeries_of_le_prod (norm_principalMinor_le_prod_mul hA) hcd ρ

/-- Any lower bound for the sum of diagonal weight differences over size-`n` sets
gives a coefficient bound for the principal-minor series. -/
theorem norm_charCoeff_le_zpow {A : Matrix ι ι R} {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1)
    {w w' : ι → ℤ} (hA : ∀ i j, ‖A i j‖ ≤ σ ^ (w i - w' j)) {n : ℕ} {m : ℤ}
    (hm : ∀ s : Finset ι, s.card = n → m ≤ ∑ i ∈ s, (w i - w' i)) :
    ‖A.charCoeff n‖ ≤ σ ^ m :=
  norm_charCoeff_le_of_principalMinor_le (zpow_nonneg hσ₀.le m) fun s hs ↦
    (norm_principalMinor_le_zpow hσ₀ hA s).trans
      (zpow_le_zpow_right_of_le_one₀ hσ₀ hσ₁ (hm s hs))

/-- Cofinite growth of the diagonal weight differences makes the principal minors
summable, without a row-compactness assumption or nonnegativity of the differences. -/
theorem summable_principalMinor_of_zpow [CompleteSpace R] {A : Matrix ι ι R} {σ : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1) {w w' : ι → ℤ}
    (hA : ∀ i j, ‖A i j‖ ≤ σ ^ (w i - w' j))
    (hw : Tendsto (fun i ↦ w i - w' i) cofinite atTop) (n : ℕ) :
    Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s := by
  obtain ⟨c, d, hA, hcd⟩ := TauCeti.exists_two_sided_bounds_of_zpow hσ₀ hσ₁ hA hw
  exact summable_principalMinor_of_two_sided hA hcd n

/-- Cofinite growth of the diagonal weight differences gives an entire matrix minor
series. This applies to two-sided bounds independently of any operator realization. -/
theorem isRestricted_charPowerSeries_of_zpow {A : Matrix ι ι R} {σ : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1) {w w' : ι → ℤ}
    (hA : ∀ i j, ‖A i j‖ ≤ σ ^ (w i - w' j))
    (hw : Tendsto (fun i ↦ w i - w' i) cofinite atTop) (ρ : ℝ) :
    A.charPowerSeries.IsRestricted ρ := by
  obtain ⟨c, d, hA, hcd⟩ := TauCeti.exists_two_sided_bounds_of_zpow hσ₀ hσ₁ hA hw
  exact isRestricted_charPowerSeries_of_two_sided hA hcd ρ

end Matrix
