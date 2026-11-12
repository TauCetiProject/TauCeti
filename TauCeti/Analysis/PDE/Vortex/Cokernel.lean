/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The cokernel of the gauge-fixed vortex operator on the Sobolev scale

At a field `x` of the affine space `A_m^s` (`TauCeti.Vortex.framedFieldSpace`), the gauge-fixed
vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) maps `C¹` fields of `H^(k+1)` to `H^k`
(`gaugeFixedOperator_mem_sobolevFields`). This file shows that at a smooth vortex of `A_m^s` this
Sobolev realization is onto, for every `k ≥ 2` with `k + 1 < s`: every `g ∈ H^k` is `L_x y` for a
`C^(k-1)` field `y ∈ H^(k+1)` (`exists_mem_sobolevFields_contDiff_gaugeFixedOperator_ae_eq`). So
the cokernel of `L_x : H^(k+1) → H^k` vanishes.

The proof combines three facts.

* **Bounded coefficients.** For `s > n + 1` the coordinates of a continuous field of `A_m^s` have
  bounded `n`-th derivatives (`exists_norm_iteratedFDeriv_apply_le_of_mem_framedFieldSpace`), by
  Sobolev embedding. So the elliptic bootstrap
  `mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq` applies at a smooth
  field of `A_m^s`: a weak `L²` solution of `L_x y = g` with `g ∈ H^k` lies in `H^(k+1)` whenever
  `k + 1 < s` (`mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace`). In particular the weak
  `L²` kernel of `L_x` lies in `H^(k+1)` for each such `k`
  (`mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace_of_integral_inner_eq_zero`).
* **The weak right inverse.** A field of `A_m^s`, `s > 1`, has `|α| → 1` at infinity, so at a
  vortex the bounded weak right inverse `Q` of `L_x` on `L²`
  (`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`) exists, and by the bootstrap it
  gains one derivative, mapping `H^k` into `H^(k+1)`
  (`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mem_framedFieldSpace`).
* **Weak solutions are classical.** A `C¹` weak solution of `L_x y = g` solves it almost
  everywhere (`gaugeFixedOperator_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq`): integration by
  parts against compactly supported test fields
  (`integral_inner_gaugeFixedOperator`) and the fundamental lemma of the calculus of variations.
  For `k ≥ 2` the field `Q g ∈ H^(k+1)` has a `C^(k-1)` representative, which is such a solution.

The kernel of `L_x : H^(k+1) → H^k` and its dimension are not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Regularity at the fields of `A_m^s` -/

/-- **Elliptic regularity at a field of `A_m^s`.** Let `x` be a smooth field of `A_m^s` and
`k + 1 < s`. A square-integrable weak solution of `L_x y = g` with `g ∈ H^k` lies in `H^(k+1)`. -/
theorem mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace {k : ℕ} (hks : k + 1 < s)
    (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    {y g : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume) (hg : g ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪g z, η z⟫) :
    y ∈ sobolevFields (k + 1) := by
  refine mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hxs
    (fun i n hn ↦ ?_) hy hg hweak
  have hn : (n : ℝ) ≤ k := by exact_mod_cast hn
  exact exists_norm_iteratedFDeriv_apply_le_of_mem_framedFieldSpace (by linarith) hx
    hxs.continuous i

/-- **Regularity of the weak kernel.** At a smooth field of `A_m^s`, every square-integrable weak
solution of `L_x y = 0` lies in `H^(k+1)` for each `k` with `k + 1 < s`. -/
theorem mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace_of_integral_inner_eq_zero
    {k : ℕ} (hks : k + 1 < s) (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = 0) :
    y ∈ sobolevFields (k + 1) :=
  mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace hks hx hxs hy (zero_mem _)
    fun η hη hηc ↦ by simpa using hweak η hη hηc

/-! ### Weak solutions are classical -/

/-- **`C¹` weak solutions are classical.** Let `x` be continuous, `y` a `C¹` field and `g` locally
integrable for an additive Haar measure `μ`. If `∫ ⟪y, L_x* η⟫ = ∫ ⟪g, η⟫` for every smooth
compactly supported test field `η`, then `L_x y = g` almost everywhere. -/
theorem gaugeFixedOperator_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq {μ : Measure ℂ}
    [μ.IsAddHaarMeasure] (hx : Continuous x) {y g : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : ContDiff ℝ 1 y) (hg : LocallyIntegrable g μ)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪g z, η z⟫ ∂μ) :
    gaugeFixedOperator x y =ᵐ[μ] g := by
  have hLy : Continuous (gaugeFixedOperator x y) := continuous_gaugeFixedOperator hx hy
  have hF : LocallyIntegrable (gaugeFixedOperator x y - g) μ :=
    hLy.locallyIntegrable.sub hg
  refine (ae_eq_zero_of_integral_contDiff_smul_eq_zero hF fun φ hφ hφc ↦ ?_).mono
    fun z hz ↦ sub_eq_zero.1 hz
  have hint₁ : Integrable (fun z ↦ φ z • gaugeFixedOperator x y z) μ :=
    hLy.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  have hint₂ : Integrable (fun z ↦ φ z • g z) μ :=
    hg.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  -- Test the weak equation against `η = φ • e` for each constant vector `e`.
  refine ext_inner_left ℝ fun e ↦ ?_
  have hη : ContDiff ℝ ∞ fun z ↦ φ z • e := hφ.smul contDiff_const
  have hηc : HasCompactSupport fun z ↦ φ z • e := hφc.smul_right
  have h := hweak _ hη hηc
  rw [← integral_inner_gaugeFixedOperator hx hy (hη.of_le (by simp)) (.inr hηc)] at h
  simp only [Pi.sub_apply, smul_sub, inner_zero_right]
  rw [integral_sub hint₁ hint₂, inner_sub_right, ← integral_inner hint₁, ← integral_inner hint₂]
  simp only [inner_smul_right, real_inner_comm e] at h ⊢
  rw [h, sub_self]

/-! ### The Sobolev right inverse and the vanishing of the cokernel -/

/-- **The right inverse on the Sobolev scale.** Let `x` be a smooth vortex in `A_m^s`, `s > 1`.
There is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` such that

* `Q g` is a weak solution of `L_x y = g` for every `g ∈ L²`;
* `Q g` is orthogonal to the weak kernel of `L_x`;
* `Q` gains one derivative: it maps `H^k` into `H^(k+1)` for every `k` with `k + 1 < s`. -/
theorem exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mem_framedFieldSpace
    (hs : 1 < s) (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
      (∀ g η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q g z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪g z, η z⟫) ∧
      (∀ g u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪Q g z, u z⟫ = 0) ∧
      ∀ (k : ℕ) (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)), k + 1 < s →
        (g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields k →
        (Q g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields (k + 1) := by
  obtain ⟨Q, hQ, hQK⟩ := exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq
    (μ := volume) (hxs.of_le (by simp)) hsol
    (tendsto_normSq_of_mem_framedFieldSpace hs hx hxs.continuous)
  exact ⟨Q, hQ, hQK, fun k g hks hg ↦ mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace
    hks hx hxs (Lp.memLp _) hg fun η hη hηc ↦ hQ g η (hη.of_le (by simp)) hηc⟩

/-- **Vanishing of the cokernel on the Sobolev scale.** Let `x` be a smooth vortex in `A_m^s`, and
let `k ≥ 2` with `k + 1 < s`. Every `g ∈ H^k` is the image under the gauge-fixed operator `L_x` of
a `C^(k-1)` field `y ∈ H^(k+1)`: the realization `L_x : H^(k+1) → H^k` is onto. -/
theorem exists_mem_sobolevFields_contDiff_gaugeFixedOperator_ae_eq {k : ℕ} (hk : 2 ≤ k)
    (hks : k + 1 < s) (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) {g : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hg : g ∈ sobolevFields k) :
    ∃ y ∈ sobolevFields (k + 1), ContDiff ℝ (k - 1 : ℕ) y ∧
      gaugeFixedOperator x y =ᵐ[volume] g := by
  have hs : 1 < s := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  obtain ⟨Q, hQ, -, hreg⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mem_framedFieldSpace hs hx
      hxs hsol
  have hgL := memLp_of_mem_sobolevFields hg
  set u := Q (hgL.toLp g)
  have hu : (u : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields (k + 1) :=
    hreg k _ hks (mem_sobolevFields_of_ae_eq hg hgL.coeFn_toLp.symm)
  -- A `C^(k-1)` representative of `u ∈ H^(k+1)`.
  obtain ⟨y, hyd, huy⟩ := exists_contDiff_ae_eq_of_mem_sobolevFields (n := k - 1)
    (by rw [Nat.cast_sub (by omega)]; push_cast; linarith) hu
  refine ⟨y, mem_sobolevFields_of_ae_eq hu huy, hyd, ?_⟩
  refine gaugeFixedOperator_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq hxs.continuous
    (hyd.of_le (by exact_mod_cast (by omega : 1 ≤ k - 1))) (hgL.locallyIntegrable (by norm_num))
    fun η hη hηc ↦ ?_
  have h := hQ (hgL.toLp g) η (hη.of_le (by simp)) hηc
  have h₁ : ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ :=
    integral_congr_ae (by filter_upwards [huy] with z hz; rw [hz])
  have h₂ : ∫ z, ⟪hgL.toLp g z, η z⟫ = ∫ z, ⟪g z, η z⟫ :=
    integral_congr_ae (by filter_upwards [hgL.coeFn_toLp] with z hz; rw [hz])
  rwa [← h₁, ← h₂]

end TauCeti.Vortex
