/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Regularity.PlanarPoisson
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Smoothness of weak solutions of the stationary Schrödinger equation in the plane

A function `w` on the plane is a weak solution of the stationary Schrödinger equation

`-Δw + P w = g`

if `∫ w (-Δφ + P φ) = ∫ g φ` for every compactly supported `C²` real function `φ`. This is the
notion of solution produced by the `L²` theory of
`TauCeti.Analysis.PDE.Schrodinger.Stationary`
(`TauCeti.exists_mem_realSobolevFunctions_two_integral_mul_neg_laplacian_add_mul_eq`). This file
shows that such solutions are as regular as the coefficients allow.

* If `w` is continuous and `P`, `g` are of class `C^k`, then `w` is of class `C^(k+1)`
  (`TauCeti.contDiff_of_integral_mul_neg_laplacian_add_mul_eq`), and for `k ≥ 1` it solves
  `Δw = P w - g` at every point
  (`TauCeti.laplacian_eq_of_integral_mul_neg_laplacian_add_mul_eq`). The weak equation is
  the distributional equation `Δw = F(z, w)` with `F(z, t) = P z t - g z`, so this is the planar
  semilinear bootstrap `TauCeti.contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp`.
* A weak solution in `H^s(ℂ)`, `s > 1`, need not be continuous, but it agrees almost everywhere
  with a continuous function by the Sobolev embedding
  (`TemperedDistribution.exists_contDiff_ae_eq_of_mem_realSobolevFunctions`). That representative
  is again a weak solution, so it is a classical solution of class `C^(k+1)`
  (`exists_contDiff_ae_eq_and_laplacian_eq_of_integral_mul_neg_laplacian_add_mul_eq`).

No sign or growth condition on `P` is needed: regularity is local, and continuity of `w` makes all
the integrands locally integrable.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.4 and Chapter 8.
-/

public section

namespace TauCeti

open InnerProductSpace MeasureTheory Set TemperedDistribution TopologicalSpace
open scoped Laplacian ContDiff Distributions

variable {P g w : ℂ → ℝ}

/-- The weak Schrödinger equation `-Δw + P w = g` of a continuous `w` is the distributional
equation `Δw = P w - g`, tested against test functions on the plane. -/
private theorem integral_laplacian_mul_eq_of_integral_mul_neg_laplacian_add_mul_eq
    (hP : Continuous P) (hg : Continuous g) (hw : Continuous w)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, w z * (-Δ φ z + P z * φ z) = ∫ z, g z * φ z)
    (φ : 𝓓((⊤ : Opens ℂ), ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z * w z = ∫ z, φ z * (P z * w z - g z) := by
  have hφ2 : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
  have hφc : HasCompactSupport (φ : ℂ → ℝ) := φ.hasCompactSupport
  have hΔ : Continuous (Δ (φ : ℂ → ℝ)) := hφ2.continuous_laplacian
  have hL : HasCompactSupport fun z ↦ -Δ (φ : ℂ → ℝ) z + P z * φ z :=
    hφc.laplacian.neg.add hφc.mul_left
  have i₁ : Integrable fun z ↦ w z * (-Δ (φ : ℂ → ℝ) z + P z * φ z) :=
    (hw.mul (hΔ.neg.add (hP.mul φ.continuous))).integrable_of_hasCompactSupport hL.mul_left
  have i₂ : Integrable fun z ↦ g z * φ z :=
    (hg.mul φ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have i₃ : Integrable fun z ↦ φ z * (P z * w z - g z) :=
    (φ.continuous.mul ((hP.mul hw).sub hg)).integrable_of_hasCompactSupport hφc.mul_right
  calc ∫ z, Δ (φ : ℂ → ℝ) z * w z
      = ∫ z, (φ z * (P z * w z - g z) -
          (w z * (-Δ (φ : ℂ → ℝ) z + P z * φ z) - g z * φ z)) :=
        integral_congr_ae (.of_forall fun z ↦ by ring)
    _ = (∫ z, φ z * (P z * w z - g z)) -
          ∫ z, (w z * (-Δ (φ : ℂ → ℝ) z + P z * φ z) - g z * φ z) :=
        integral_sub i₃ (i₁.sub i₂)
    _ = ∫ z, φ z * (P z * w z - g z) := by
        rw [integral_sub i₁ i₂, h φ hφ2 hφc, sub_self, sub_zero]

/-- The right side `F(z, t) = P z t - g z` of the distributional equation `Δw = F(z, w)`. -/
private theorem contDiffOn_mul_sub {k : ℕ∞} (hP : ContDiff ℝ k P) (hg : ContDiff ℝ k g) :
    ContDiffOn ℝ k (fun p : ℂ × ℝ ↦ P p.1 * p.2 - g p.1) ((⊤ : Opens ℂ) ×ˢ univ) :=
  (((hP.comp contDiff_fst).mul contDiff_snd).sub (hg.comp contDiff_fst)).contDiffOn

/-- **Regularity of continuous weak solutions of the Schrödinger equation in the plane.** If `w`
is continuous and solves `-Δw + P w = g` weakly, `∫ w (-Δφ + P φ) = ∫ g φ` for every compactly
supported `C²` function `φ`, with `P` and `g` of class `C^k`, then `w` is of class `C^(k+1)`. -/
theorem contDiff_of_integral_mul_neg_laplacian_add_mul_eq {k : ℕ∞}
    (hP : ContDiff ℝ k P) (hg : ContDiff ℝ k g) (hw : Continuous w)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, w z * (-Δ φ z + P z * φ z) = ∫ z, g z * φ z) :
    ContDiff ℝ ((k : ℕ∞ω) + 1) w := by
  have hk := contDiffOn_succ_of_forall_integral_laplacian_mul_eq_comp (contDiffOn_mul_sub hP hg)
    hw.continuousOn (integral_laplacian_mul_eq_of_integral_mul_neg_laplacian_add_mul_eq
      hP.continuous hg.continuous hw h)
  rwa [Opens.coe_top, contDiffOn_univ] at hk

/-- **Continuous weak solutions of the Schrödinger equation in the plane are classical.** If `w`
is continuous and solves `-Δw + P w = g` weakly, with `P` and `g` of class `C¹`, then
`Δw = P w - g` at every point. -/
theorem laplacian_eq_of_integral_mul_neg_laplacian_add_mul_eq
    (hP : ContDiff ℝ 1 P) (hg : ContDiff ℝ 1 g) (hw : Continuous w)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, w z * (-Δ φ z + P z * φ z) = ∫ z, g z * φ z) (z : ℂ) :
    Δ w z = P z * w z - g z :=
  eqOn_laplacian_of_forall_integral_laplacian_mul_eq_comp (contDiffOn_mul_sub (k := 1) hP hg)
    hw.continuousOn (integral_laplacian_mul_eq_of_integral_mul_neg_laplacian_add_mul_eq
      hP.continuous hg.continuous hw h) (by simp)

/-- **Sobolev weak solutions of the Schrödinger equation in the plane have classical
representatives.** Let `h ∈ H^s(ℂ)`, `s > 1`, solve `-Δh + P h = g` weakly, with `P` and `g` of
class `C^k`, `k ≥ 1`. Then `h` agrees almost everywhere with a function `w` of class `C^(k+1)`
satisfying `Δw = P w - g` at every point. -/
theorem exists_contDiff_ae_eq_and_laplacian_eq_of_integral_mul_neg_laplacian_add_mul_eq
    {k : ℕ∞} (hk : 1 ≤ k) (hP : ContDiff ℝ k P) (hg : ContDiff ℝ k g) {s : ℝ} (hs : 1 < s)
    {h : ℂ → ℝ} (hh : h ∈ realSobolevFunctions ℂ s 2)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, h z * (-Δ φ z + P z * φ z) = ∫ z, g z * φ z) :
    ∃ w : ℂ → ℝ, ContDiff ℝ ((k : ℕ∞ω) + 1) w ∧ h =ᵐ[volume] w ∧
      ∀ z, Δ w z = P z * w z - g z := by
  obtain ⟨w, hw, hhw⟩ := exists_contDiff_ae_eq_of_mem_realSobolevFunctions
    (k := 0) (by simpa using finrank_real_complex_lt_two_mul hs) hh
  -- The continuous representative is again a weak solution.
  have hweak' (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
      ∫ z, w z * (-Δ φ z + P z * φ z) = ∫ z, g z * φ z := by
    rw [← hweak φ hφ hφc]
    refine integral_congr_ae ?_
    filter_upwards [hhw] with z hz
    rw [hz]
  have hwc : Continuous w := hw.continuous
  exact ⟨w, contDiff_of_integral_mul_neg_laplacian_add_mul_eq hP hg hwc hweak', hhw,
    laplacian_eq_of_integral_mul_neg_laplacian_add_mul_eq (hP.of_le (by exact_mod_cast hk))
      (hg.of_le (by exact_mod_cast hk)) hwc hweak'⟩

end TauCeti
