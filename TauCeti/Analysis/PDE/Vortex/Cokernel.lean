/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity

/-!
# The cokernel of the gauge-fixed vortex operator on the Sobolev scale

At a field `x` of the affine space `A_m^(k+1)` (`TauCeti.Vortex.framedFieldSpace`), `k ≥ 1`, the
gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a pointwise differential
expression which maps `C¹` fields of `H^(k+1)` to `H^k` (`gaugeFixedOperator_mem_sobolevFields`).
This file shows that at a smooth vortex `x` of `A_m^s`, `s > 2`, this map has no cokernel in the
following sense, for every `k ≥ 2` with `k ≤ s`: every `g ∈ sobolevFields k` agrees almost
everywhere with `L_x y` for a `C^(k-1)` field `y ∈ sobolevFields (k + 1)`
(`exists_mem_sobolevFields_contDiff_gaugeFixedOperator_ae_eq`). No bundled operator
`H^(k+1) → H^k` on equivalence classes is constructed here.

The proof combines three facts.

* **The weak right inverse.** A field of `A_m^s`, `s > 1`, has `|α| → 1` at infinity, so at a
  vortex the bounded weak right inverse `Q` of `L_x` on `L²`
  (`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`) exists.
* **Elliptic regularity.** At a smooth field of `A_m^s`, `s > 2`, a weak `L²` solution of
  `L_x y = g` with `g ∈ H^k`, `k ≤ s`, lies in `H^(k+1)`
  (`mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace`). So `Q` gains one derivative,
  mapping `H^k` into `H^(k+1)`
  (`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mem_framedFieldSpace`).
* **Weak solutions are classical.** A `C¹` weak solution of `L_x y = g` solves it almost
  everywhere (`gaugeFixedOperator_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq`). For `k ≥ 2` the
  field `Q g ∈ H^(k+1)` has a `C^(k-1)` representative, which is such a solution.

The kernel of `L_x` on `H^(k+1)` and its dimension are not treated here.

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

/-! ### The Sobolev right inverse and the vanishing of the cokernel -/

/-- **The right inverse on the Sobolev scale.** Let `x` be a smooth vortex in `A_m^s`, `s > 2`.
There is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` such that

* `Q g` is a weak solution of `L_x y = g` for every `g ∈ L²`;
* `Q g` is orthogonal to the weak kernel of `L_x`;
* `Q` gains one derivative: it maps `H^k` into `H^(k+1)` for every `k ≤ s`. -/
theorem exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mem_framedFieldSpace
    (hs : 2 < s) (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
      (∀ g η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q g z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪g z, η z⟫) ∧
      (∀ g u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪Q g z, u z⟫ = 0) ∧
      ∀ (k : ℕ) (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)), k ≤ s →
        (g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields k →
        (Q g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields (k + 1) := by
  obtain ⟨Q, hQ, hQK⟩ := exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq
    (μ := volume) (hxs.of_le (by simp)) hsol
    (tendsto_normSq_of_mem_framedFieldSpace (by linarith) hx hxs.continuous)
  exact ⟨Q, hQ, hQK, fun k g hks hg ↦ mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace
    hs hks hx hxs (Lp.memLp _) hg fun η hη hηc ↦ hQ g η (hη.of_le (by simp)) hηc⟩

/-- **Vanishing of the cokernel on the Sobolev scale.** Let `x` be a smooth vortex in `A_m^s`,
`s > 2`, and let `2 ≤ k ≤ s`. Every `g ∈ sobolevFields k` agrees almost everywhere with
`gaugeFixedOperator x y` for some `C^(k-1)` field `y ∈ sobolevFields (k + 1)`. -/
theorem exists_mem_sobolevFields_contDiff_gaugeFixedOperator_ae_eq {k : ℕ} (hk : 2 ≤ k)
    (hs : 2 < s) (hks : k ≤ s) (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) {g : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hg : g ∈ sobolevFields k) :
    ∃ y ∈ sobolevFields (k + 1), ContDiff ℝ (k - 1 : ℕ) y ∧
      gaugeFixedOperator x y =ᵐ[volume] g := by
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
