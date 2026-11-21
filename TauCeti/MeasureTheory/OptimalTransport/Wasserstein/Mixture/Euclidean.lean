/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import TauCeti.MeasureTheory.OptimalTransport.Brenier
import TauCeti.Analysis.InnerProductSpace.OrthogonalLine.HausdorffDimension

/-!
# Strict convexity of `W₂ ^ 2` on a Euclidean space

On a finite-dimensional real inner product space `E`, strict convexity of the quadratic transport
cost for a finite `c - c`-regular source (`TauCeti.IsCCRegular.transportCost_smul_add_smul_lt`)
transfers directly to `ν ↦ W₂(μ, ν) ^ 2` via
`W₂(μ, ν) ^ 2 = 2 * transportCost (‖x - y‖ ^ 2 / 2) μ ν`. In particular, `ν ↦ W₂(μ, ν) ^ 2` is
strictly convex whenever `μ` is finite and gives zero mass to globally Lipschitz graphs over
hyperplanes—hence whenever `μ` vanishes on Borel sets with `dimH A + 1 ≤ finrank ℝ E`, whenever
`μ` vanishes on small sets (`dimH A ≤ finrank ℝ E - 1`, Agueh–Carlier §3.1, Definition 3.2 and the
proof of Proposition 3.5), and whenever `μ` is absolutely continuous with respect to an additive
Haar measure.

## Main statements

* `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt` — strict convexity of `ν ↦ W₂(μ, ν) ^ 2`
  for a finite `c - c`-regular `μ` (in particular, a finite law absolutely continuous with respect
  to an additive Haar measure);
* `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt_of_null_lipschitz_graphs`,
  `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_add_one_le`, and
  `TauCeti.wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_le` — strict convexity of
  `ν ↦ W₂(μ, ν) ^ 2` when `μ` vanishes on Lipschitz hypersurface graphs or small sets.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43 (2011),
  904–924, §3.1 (Definition 3.2 and the proof of Proposition 3.5).
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, Chapter 7,
  for strict convexity of `ν ↦ W₂(μ, ν) ^ 2` when `μ` is regular.
-/

public section

noncomputable section

open MeasureTheory Module Set
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` for a `c - c`-regular `μ`.** On a finite-dimensional
real inner product space, let `μ` be a finite `c - c`-regular measure (in particular, a finite
measure absolutely continuous with respect to an additive Haar measure), and let `ν₀ ≠ ν₁` be
measures at finite `W₂` distance from `μ`. For nonzero weights with `a + b = 1`,
`W₂(μ, a • ν₀ + b • ν₁) ^ 2 < a * W₂(μ, ν₀) ^ 2 + b * W₂(μ, ν₁) ^ 2`. -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt {μ ν₀ ν₁ : Measure E} [IsFiniteMeasure μ]
    (hμ : IsCCRegular μ) {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞) (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 := by
  have hsq (ν : Measure E) : wassersteinEDist 2 μ ν ^ 2 =
      2 * transportCost (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν := by
    have h := wassersteinEDist_rpow_eq_transportCost (p := 2) (μ := μ) (ν := ν)
      measurable_edist two_ne_zero ENNReal.ofNat_ne_top
    rw [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at h
    rw [h, ← transportCost_const_mul two_ne_zero ENNReal.ofNat_ne_top]
    congr 1
    funext z
    exact edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two z
  have hfin (ν : Measure E) (hν : wassersteinEDist 2 μ ν ≠ ∞) :
      transportCost (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
    intro htop
    have := hsq ν
    rw [htop, ENNReal.mul_top two_ne_zero] at this
    exact ENNReal.pow_ne_top hν this
  rw [hsq, hsq, hsq, mul_left_comm a 2, mul_left_comm b 2, ← mul_add]
  exact ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top
    (hμ.transportCost_smul_add_smul_lt hab ha hb (hfin ν₀ h₀) (hfin ν₁ h₁) hne)

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` for a source vanishing on Lipschitz hypersurfaces.**
On a finite-dimensional real inner product space `E`, let `μ` be a finite measure that gives mass
`0` to every globally Lipschitz graph over the orthogonal complement of a unit vector, and let
`ν₀ ≠ ν₁` be measures at finite `W₂` distance from `μ`. For nonzero weights with `a + b = 1`,
`W₂(μ, a • ν₀ + b • ν₁) ^ 2 < a * W₂(μ, ν₀) ^ 2 + b * W₂(μ, ν₁) ^ 2`. -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt_of_null_lipschitz_graphs {μ ν₀ ν₁ : Measure E}
    [IsFiniteMeasure μ]
    (hμ : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0)
    {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞) (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 :=
  wassersteinEDist_two_smul_add_smul_sq_lt
    (isCCRegular_of_forall_isLipschitzHypersurface fun _ hs => by
      obtain ⟨v, hv, K, g, hg, rfl⟩ := isLipschitzHypersurface_iff_exists_eq_range.1 hs
      exact hμ v hv K g hg)
    hab ha hb h₀ h₁ hne

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` when `μ` vanishes on Borel sets with
`dimH A + 1 ≤ finrank ℝ E`.** The hypothesis `hμ` is satisfiable by finite measures in every
finite dimension (holding vacuously when `finrank ℝ E = 0`, where `ν₀ ≠ ν₁` is impossible for
measures of equal total mass). -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_add_one_le {μ ν₀ ν₁ : Measure E}
    [IsFiniteMeasure μ]
    (hμ : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) → μ A = 0)
    {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞) (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 :=
  wassersteinEDist_two_smul_add_smul_sq_lt_of_null_lipschitz_graphs
    (fun _ hv _ _ hg => measure_range_add_smul_eq_zero_of_dimH_add_one_le hμ hv hg)
    hab ha hb h₀ h₁ hne

/-- **Strict convexity of `ν ↦ W₂(μ, ν) ^ 2` when `μ` vanishes on small sets
(`dimH A ≤ finrank ℝ E - 1`)** (Agueh–Carlier, §3.1, Definition 3.2 and the proof of
Proposition 3.5). -/
theorem wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_le {μ ν₀ ν₁ : Measure E}
    [IsFiniteMeasure μ]
    (hμ : ∀ A, MeasurableSet A → dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → μ A = 0)
    {a b : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : wassersteinEDist 2 μ ν₀ ≠ ∞) (h₁ : wassersteinEDist 2 μ ν₁ ≠ ∞) (hne : ν₀ ≠ ν₁) :
    wassersteinEDist 2 μ (a • ν₀ + b • ν₁) ^ 2
      < a * wassersteinEDist 2 μ ν₀ ^ 2 + b * wassersteinEDist 2 μ ν₁ ^ 2 :=
  wassersteinEDist_two_smul_add_smul_sq_lt_of_dimH_add_one_le
    (fun _ hA hdim => hμ _ hA (by
      simpa only [ENNReal.natCast_sub, Nat.cast_one] using
        ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top hdim))
    hab ha hb h₀ h₁ hne

end TauCeti
