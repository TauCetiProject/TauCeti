/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.AnnularRing.Localization
public import TauCeti.RingTheory.Huber.TateGauge.Away

/-!
# The `T`-adic Tate gauge on `H[1/T]`

Let `H = TauCeti.AnnularRing p` be the integral annular coefficient ring `ℤ_p⟦T, p/T⟧` and let `A`
be any localization of `H` away from `T`. Since `H` is `(T)`-adically complete and `T` is a
non-zero-divisor in `H`, `TauCeti.Huber.awayTateNormDatum` and `TauCeti.Huber.awayNormedCommRing`
give a complete ultrametric Banach–Tate `NormedCommRing` structure on `A` for each radius
`α ∈ (0, 1)`.

This file records the `AnnularRing`-specific computations for that `T`-adic gauge:

* Its closed ball of radius `α ^ n` is characterized by the shifted coefficient bound
  `‖localizedCoeff p x m‖ ≤ p ^ min 0 (m - n)`
  (`TauCeti.AnnularRing.tateNorm_le_zpow_iff_norm_localizedCoeff_le`,
  `TauCeti.AnnularRing.norm_le_zpow_iff_awayNormedCommRing`).
* Every power `U ^ j = p ^ j T ^ (-j)` lies in `H \ T H` and therefore has norm `1`.
* Since `p = T U`, the element `p` has norm `α`.

## Main results

* `TauCeti.AnnularRing.tateNorm_le_zpow_iff_norm_localizedCoeff_le`,
  `TauCeti.AnnularRing.norm_le_zpow_iff_awayNormedCommRing`: closed balls of the `T`-gauge in
  terms of localized coefficients.
* `TauCeti.AnnularRing.tateNorm_U_pow`, `TauCeti.AnnularRing.tateNorm_U`,
  `TauCeti.AnnularRing.tateNorm_p`: exact norms of `U ^ j`, `U`, and `p` in any `T`-adic
  topology.
* `TauCeti.AnnularRing.norm_U_pow_awayNormedCommRing`,
  `TauCeti.AnnularRing.norm_U_awayNormedCommRing`, `TauCeti.AnnularRing.norm_p_awayNormedCommRing`:
  the corresponding norms for `Huber.awayNormedCommRing`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology

namespace TauCeti.AnnularRing

/-! ### Coefficient bounds and `U`, `p` norms in any `T`-adic topology -/

section HasBasis

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A] [TopologicalSpace A]
  (hb : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦
    (Huber.awayNhd (T : AnnularRing p) A n : Set A))
  [IsTopologicalRing A]

/-- The closed ball of radius `α ^ n` for the `T`-gauge on `H[1/T]` is cut out by the shifted
coefficient bound `‖localizedCoeff p x m‖ ≤ p ^ min 0 (m - n)`. -/
theorem tateNorm_le_zpow_iff_norm_localizedCoeff_le {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    {x : A} {n : ℤ} :
    Huber.tateNorm (Huber.awayTateNormDatum hb hα₀ hα₁) x ≤ α ^ n ↔
      ∀ m : ℤ, ‖localizedCoeff p x m‖ ≤ (p : ℝ) ^ min 0 (m - n) := by
  have h := Huber.tateNorm_le_zpow_iff (Huber.awayTateNormDatum hb hα₀ hα₁) (x := x) (n := n)
  rwa [Huber.awayTateNormDatum_radius, Huber.awayTateNormDatum_pseudoUniformizer,
    Huber.awayTateNormDatum_ringOfDefinition, T_zpow_neg_mul_mem_range_iff] at h

/-- Every power `U ^ j` has norm `1` for the `T`-gauge of any radius `α ∈ (0, 1)`. -/
theorem tateNorm_U_pow {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (j : ℕ) :
    Huber.tateNorm (Huber.awayTateNormDatum hb hα₀ hα₁)
      (algebraMap (AnnularRing p) A (U ^ j)) = 1 := by
  have hmem :
      (((Huber.awayTateNormDatum hb hα₀ hα₁).pseudoUniformizer ^ (-(0 : ℤ)) : Aˣ) : A) *
        algebraMap (AnnularRing p) A (U ^ j) ∈
        (Huber.awayTateNormDatum hb hα₀ hα₁).ringOfDefinition := by
    simpa using (algebraMap (AnnularRing p) A).mem_range_self (U ^ j)
  have hnot :
      (((Huber.awayTateNormDatum hb hα₀ hα₁).pseudoUniformizer ^ (-((0 : ℤ) + 1)) : Aˣ) : A) *
        algebraMap (AnnularRing p) A (U ^ j) ∉
        (Huber.awayTateNormDatum hb hα₀ hα₁).ringOfDefinition := by
    intro h
    rw [Huber.awayTateNormDatum_pseudoUniformizer, Huber.awayTateNormDatum_ringOfDefinition,
      zero_add, T_zpow_neg_mul_mem_range_iff] at h
    exact T_not_dvd_U_pow j <| T_dvd_iff.mpr fun m ↦ by
      simpa only [localizedCoeff_algebraMap] using h m
  simpa using Huber.tateNorm_eq_zpow_of_mem_of_not_mem (Huber.awayTateNormDatum hb hα₀ hα₁)
    hmem hnot

/-- The element `U = p / T` has norm `1` for the `T`-gauge of any radius `α ∈ (0, 1)`. -/
theorem tateNorm_U {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    Huber.tateNorm (Huber.awayTateNormDatum hb hα₀ hα₁) (algebraMap (AnnularRing p) A U) = 1 := by
  simpa using tateNorm_U_pow hb hα₀ hα₁ 1

/-- Since `p = T U`, the element `p` has norm `α` for the `T`-gauge of radius `α`. -/
theorem tateNorm_p {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    Huber.tateNorm (Huber.awayTateNormDatum hb hα₀ hα₁) (p : A) = α := by
  rw [← map_natCast (algebraMap (AnnularRing p) A), ← T_mul_U, map_mul,
    ← Huber.coe_awayTateNormDatum_pseudoUniformizer hb hα₀ hα₁,
    Huber.tateNorm_pseudoUniformizer_mul, Huber.awayTateNormDatum_radius, tateNorm_U, mul_one]

end HasBasis

/-! ### Coefficient bounds and `U`, `p` norms in `Huber.awayNormedCommRing` -/

section AwayNormedCommRing

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A] {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)

theorem norm_le_zpow_iff_awayNormedCommRing {x : A} {n : ℤ} :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
    ‖x‖ ≤ α ^ n ↔ ∀ m : ℤ, ‖localizedCoeff p x m‖ ≤ (p : ℝ) ^ min 0 (m - n) := by
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  rw [Huber.norm_awayNormedCommRing]
  exact tateNorm_le_zpow_iff_norm_localizedCoeff_le
    (Huber.hasBasis_nhds_zero_awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors
      hα₀ hα₁)
    hα₀ hα₁

theorem norm_U_pow_awayNormedCommRing (j : ℕ) :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
    ‖algebraMap (AnnularRing p) A (U ^ j)‖ = 1 := by
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  rw [Huber.norm_awayNormedCommRing]
  exact tateNorm_U_pow
    (Huber.hasBasis_nhds_zero_awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors
      hα₀ hα₁)
    hα₀ hα₁ j

theorem norm_U_awayNormedCommRing :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
    ‖algebraMap (AnnularRing p) A U‖ = 1 := by
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  rw [Huber.norm_awayNormedCommRing]
  exact tateNorm_U
    (Huber.hasBasis_nhds_zero_awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors
      hα₀ hα₁)
    hα₀ hα₁

theorem norm_p_awayNormedCommRing :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
    ‖(p : A)‖ = α := by
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  rw [Huber.norm_awayNormedCommRing]
  exact tateNorm_p
    (Huber.hasBasis_nhds_zero_awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors
      hα₀ hα₁)
    hα₀ hα₁

end AwayNormedCommRing

end TauCeti.AnnularRing
