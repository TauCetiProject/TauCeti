/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.Hausdorff
public import TauCeti.MeasureTheory.OptimalTransport.Brenier.SmallSet
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Mixture.Basic

/-!
# Strict convexity of `W₂ ^ 2` on a Euclidean space

On a finite-dimensional real inner product space `E`, Brenier's theorem for sources vanishing on
globally Lipschitz graphs over hyperplanes
(`TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_null_lipschitz_graphs`) shows that every optimal
plan for the cost `edist ^ 2` out of such a law `μ`, into a law at finite `W₂` distance from `μ`,
is induced by a measurable map. This discharges the map hypothesis of the general strict convexity
theorem `TauCeti.wassersteinEDist_smul_add_smul_rpow_lt`, so `ν ↦ W₂(μ, ν) ^ 2` is strictly convex
whenever `μ` gives zero mass to Lipschitz graphs over hyperplanes—in particular whenever `μ`
vanishes on Borel sets with `dimH A + 1 ≤ finrank ℝ E`, whenever `μ` vanishes on small sets
(`dimH A ≤ finrank ℝ E - 1`, Agueh–Carlier Proposition 2.3), and whenever `μ` is absolutely
continuous with respect to an additive Haar measure.

## Main statements

* `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt_of_null_lipschitz_graphs`,
  `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_add_one_le`, and
  `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_le` — strict convexity of
  `ν ↦ W₂(μ, ν) ^ 2` when `μ` vanishes on Lipschitz hypersurface graphs or small sets;
* `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt` — strict convexity of `ν ↦ W₂(μ, ν) ^ 2`
  for an absolutely continuous `μ`.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43 (2011),
  904–924, Proposition 2.3.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, Chapter 7,
  for strict convexity of `ν ↦ W₂(μ, ν) ^ 2` through Brenier's theorem.
-/

public section

noncomputable section

open MeasureTheory Module Set
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` for a source vanishing on Lipschitz hypersurfaces.**
On a finite-dimensional real inner product space `E`, let `μ` be a probability law that gives mass
`0` to every globally Lipschitz graph over the orthogonal complement of a unit vector, and let
`ν₀ ≠ ν₁` be probability laws at finite `W₂` distance from `μ`. For nonzero weights with
`a + b = 1`, `W₂(μ, a • ν₀ + b • ν₁) ^ 2 < a * W₂(μ, ν₀) ^ 2 + b * W₂(μ, ν₁) ^ 2`. -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt_of_null_lipschitz_graphs {μ ν₀ ν₁ : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0)
    {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞) (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 := by
  have hle := wassersteinEDist_smul_add_smul_rpow_le (p := 2) measurable_edist hab μ ν₀ ν₁
  have hlt := wassersteinEDist_smul_add_smul_rpow_lt two_ne_zero ENNReal.ofNat_ne_top hab ha hb
    (μ := μ) (fun π hπ => ?_) hne
  · simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using hlt
  have hfin : wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ≠ ∞ := by
    obtain ⟨ha', hb'⟩ := ENNReal.add_ne_top.1 (hab ▸ ENNReal.one_ne_top)
    simp only [ENNReal.toReal_ofNat] at hle
    refine fun htop => (ne_top_of_le_ne_top ?_ hle) (by simp [htop])
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ha' (ENNReal.rpow_ne_top_of_nonneg zero_le_two h₀),
        ENNReal.mul_ne_top hb' (ENNReal.rpow_ne_top_of_nonneg zero_le_two h₁)⟩
  rw [ENNReal.toReal_ofNat] at hπ
  obtain ⟨T, hT, hπT⟩ := hπ.exists_eq_graphPlan_of_null_lipschitz_graphs hμ hfin
  exact ⟨T, hT.aemeasurable, hπT⟩

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` when `μ` vanishes on Borel sets with
`dimH A + 1 ≤ finrank ℝ E`.** This hypothesis holds in every finite dimension, including `0`. -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_add_one_le {μ ν₀ ν₁ : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hμ : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) → μ A = 0)
    {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞) (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 :=
  wassersteinEDist_two_smul_add_smul_sq_lt_of_null_lipschitz_graphs
    (fun _ hv _ _ hg => measure_range_add_smul_eq_zero_of_dimH_add_one_le hμ hv hg)
    hab ha hb h₀ h₁ hne

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` when `μ` vanishes on small sets
(`dimH A ≤ finrank ℝ E - 1`)** (Agueh–Carlier, Proposition 2.3). -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_le {μ ν₀ ν₁ : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hμ : ∀ A, MeasurableSet A → dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → μ A = 0)
    {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞) (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 :=
  wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_add_one_le
    (fun _ hA hdim => measure_eq_zero_of_dimH_add_one_le_of_forall_dimH_le hμ hA hdim)
    hab ha hb h₀ h₁ hne

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` for an absolutely continuous `μ`.** On a
finite-dimensional real inner product space, let `μ` be a probability law absolutely continuous
with respect to an additive Haar measure, and let `ν₀ ≠ ν₁` be probability laws at finite `W₂`
distance from `μ`. For nonzero weights with `a + b = 1`,
`W₂(μ, a • ν₀ + b • ν₁) ^ 2 < a * W₂(μ, ν₀) ^ 2 + b * W₂(μ, ν₁) ^ 2`. -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt {ρ : Measure E} [ρ.IsAddHaarMeasure]
    {μ ν₀ ν₁ : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₀]
    [IsProbabilityMeasure ν₁] (hμ : μ ≪ ρ) {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0)
    (hb : b ≠ 0) (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞) (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞)
    (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 :=
  wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_add_one_le
    (fun _ _ hdim => hμ (ρ.addHaar_eq_zero_of_dimH_add_one_le_finrank hdim))
    hab ha hb h₀ h₁ hne

end TauCeti
