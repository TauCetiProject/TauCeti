/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp

/-!
# Exponentially decaying weak solutions at a plane vortex on the Sobolev scale

At a plane vortex `x`, the gauge-fixed operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) has a weak
right inverse `Q` on the `L²`-orthogonal complement of its weak kernel
(`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`), and with
`ρ(z) = √(1 + |z|²)` and `|c| < 1 / 2` it satisfies the weighted `L²` estimate
`‖exp(c ρ) Q f‖₂ ≤ K ‖exp(c ρ) f‖₂`
(`exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`). This file shows that
the weighted output also gains one derivative on the whole Sobolev scale: if `exp(c ρ) f` lies in
`H^k`, then `exp(c ρ) Q f` lies in `H^(k+1)`. For `c > 0` this says that `Q` maps inputs decaying
like `exp(-c ρ)` in `H^k` to outputs decaying at the same rate in `H^(k+1)`, the form in which
the inverse of the plane-vortex operator is used to correct exponentially localized errors when
vortices are grafted onto the normal discs of a pseudoholomorphic curve.

The weight `w = exp(c ρ)` is smooth, and its logarithmic gradient `c dρ`,
`dρ = ⟪z, ·⟫ / ρ`, has bounded derivatives of every order
(`exists_norm_iteratedFDeriv_inner_mul_one_add_norm_sq_rpow_neg_half_le`). By the Leibniz rule
`L_x* (w η) = w L_x* η + σ*(dw) η` (`gaugeFixedAdjoint_fun_smul`), and since the symbol of the
adjoint is the negative transpose of the symbol of `L_x` (`inner_gaugeFixedAdjointSymbol`), a
weak solution `y` of `L_x y = f` gives a weak solution `w y` of

`L_x (w y) = w f + σ(dw) y = w f + c σ(dρ) (w y)`

(`integral_inner_smul_gaugeFixedAdjoint_eq`). The weighted `L²` estimate puts `w y` in `L²`.
Multiplication by `c σ(dρ)` preserves each `H^j`
(`mulVec_mem_sobolevFields_natCast`), so the elliptic bootstrap
`mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq` raises the regularity of
`w y` one step at a time, from `L²` to `H^(k+1)`.

The statements are membership statements. Bounds on the weighted Sobolev norms, and the
dependence of the constants on the vortex, are not proved here.

## Main results

All in the namespace `TauCeti.Vortex`:

* `integral_inner_smul_gaugeFixedAdjoint_eq`: a smooth real weight `w` turns a weak solution of
  `L_x y = f` into a weak solution of `L_x (w y) = w f + σ(dw) y`.
* `exp_mul_smul_mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq`: at a
  smooth plane vortex with bounded derivatives through order `k` and `|α| → 1`, a weak solution
  `y` of `L_x y = f` orthogonal to the weak kernel has `exp(c ρ) y ∈ H^(k+1)` whenever
  `exp(c ρ) f ∈ H^k` and `|c| < 1 / 2`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

open Complex MeasureTheory Filter
open scoped RealInnerProductSpace Topology ContDiff

namespace TauCeti.Vortex

/-- **The weak equation of a weighted solution.** Let `w` be a smooth real weight and `y` a
square-integrable weak solution of `L_x y = f`, `f ∈ L²`, tested against smooth compactly
supported fields, at a continuous field `x`. Then `w y` is a weak solution of
`L_x (w y) = w f + σ(dw) y`, where `σ` is the principal symbol of `L_x`
(`gaugeFixedOperatorSymbol`). No integrability of `w y` or `w f` is needed: the test fields have
compact support. -/
theorem integral_inner_smul_gaugeFixedAdjoint_eq {x y f : ℂ → EuclideanSpace ℝ (Fin 4)}
    {w : ℂ → ℝ} (hx : Continuous x) (hw : ContDiff ℝ ∞ w) (hy : MemLp y 2 volume)
    (hf : MemLp f 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ∫ z, ⟪w z • y z, gaugeFixedAdjoint x η z⟫ =
      ∫ z, ⟪w z • f z + gaugeFixedOperatorSymbol (fderiv ℝ w z) (y z), η z⟫ := by
  have hwη : ContDiff ℝ ∞ (fun z ↦ w z • η z) := hw.smul hη
  have hwηc : HasCompactSupport (fun z ↦ w z • η z) := hc.mono fun z hz h ↦ hz (by simp [h])
  have hL : MemLp (gaugeFixedAdjoint x fun z ↦ w z • η z) 2 volume :=
    (continuous_gaugeFixedAdjoint hx (hwη.of_le (by simp))).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hwηc)
  have hS : MemLp (fun z ↦ gaugeFixedAdjointSymbol (fderiv ℝ w z) (η z)) 2 volume :=
    (continuous_gaugeFixedAdjointSymbol.comp
      ((hw.continuous_fderiv (by simp)).prodMk hη.continuous)).memLp_of_hasCompactSupport
      (hc.mono fun z hz h ↦ hz (by simp [h, gaugeFixedAdjointSymbol_def]))
  have hwηL : MemLp (fun z ↦ w z • η z) 2 volume :=
    hwη.continuous.memLp_of_hasCompactSupport hwηc
  -- Both sides differ from the pairings with `L_x* (w η)` and with `w η` by the same symbol term.
  have hl (z : ℂ) : ⟪w z • y z, gaugeFixedAdjoint x η z⟫ =
      ⟪y z, gaugeFixedAdjoint x (fun t ↦ w t • η t) z⟫ -
        ⟪y z, gaugeFixedAdjointSymbol (fderiv ℝ w z) (η z)⟫ := by
    rw [gaugeFixedAdjoint_fun_smul x (hw.differentiable (by simp) z)
      (hη.differentiable (by simp) z), inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    ring
  have hr (z : ℂ) : ⟪w z • f z + gaugeFixedOperatorSymbol (fderiv ℝ w z) (y z), η z⟫ =
      ⟪f z, w z • η z⟫ - ⟪y z, gaugeFixedAdjointSymbol (fderiv ℝ w z) (η z)⟫ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_right,
      inner_gaugeFixedAdjointSymbol]
    ring
  have hS' := hy.integrable_inner (𝕜 := ℝ) hS
  calc ∫ z, ⟪w z • y z, gaugeFixedAdjoint x η z⟫
      = ∫ z, (⟪y z, gaugeFixedAdjoint x (fun t ↦ w t • η t) z⟫ -
          ⟪y z, gaugeFixedAdjointSymbol (fderiv ℝ w z) (η z)⟫) :=
        integral_congr_ae (.of_forall hl)
    _ = ∫ z, (⟪f z, w z • η z⟫ - ⟪y z, gaugeFixedAdjointSymbol (fderiv ℝ w z) (η z)⟫) := by
        rw [integral_sub (hy.integrable_inner hL) hS', integral_sub (hf.integrable_inner hwηL) hS',
          hweak _ hwη hwηc]
    _ = _ := integral_congr_ae (.of_forall fun z ↦ (hr z).symm)

/-- The derivative `⟪z, v⟫ / ρ(z)` of `ρ(z) = √(1 + |z|²)` in the direction `v`, with all
derivatives bounded uniformly through order `k`, in the form consumed by
`mulVec_mem_sobolevFields_natCast`. -/
private theorem exists_forall_norm_iteratedFDeriv_inner_mul_le (v : ℂ) (k : ℕ) :
    ∃ M ≥ 0, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n
      (fun z : ℂ ↦ ⟪z, v⟫ * (1 + ‖z‖ ^ 2) ^ (-(1 / 2) : ℝ)) z‖ ≤ M := by
  choose C hC using exists_norm_iteratedFDeriv_inner_mul_one_add_norm_sq_rpow_neg_half_le v
  refine ⟨∑ n ∈ Finset.range (k + 1), max (C n) 0,
    Finset.sum_nonneg fun n _ ↦ le_max_right _ _, fun n hn z ↦ (hC n z).trans ?_⟩
  exact (le_max_left _ _).trans (Finset.single_le_sum (f := fun n ↦ max (C n) 0)
    (fun n _ ↦ le_max_right _ _) (Finset.mem_range.2 (Nat.lt_succ_of_le hn)))

/-- The directions in which the entries of the matrix of `σ(dρ)` differentiate `ρ`: the entry
`(i, j)` is the derivative of `ρ` in the direction `symbolDirections i j`. -/
private noncomputable def symbolDirections : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, I, 0, 0; I, -1, 0, 0; 0, 0, 1, -I; 0, 0, I, 1]

/-- The commutator `σ(dw) v` of `L_x` with the weight `w = exp(c ρ)` is the matrix of `c σ(dρ)`,
whose entries are derivatives of `ρ`, applied to `w v`. -/
private theorem gaugeFixedOperatorSymbol_fderiv_exp_mul_sqrt_eq (c : ℝ) (z : ℂ)
    (v : EuclideanSpace ℝ (Fin 4)) :
    gaugeFixedOperatorSymbol (fderiv ℝ (fun t : ℂ ↦ Real.exp (c * √(1 + ‖t‖ ^ 2))) z) v =
      WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4,
        ⟪z, c • symbolDirections i j⟫ * (1 + ‖z‖ ^ 2) ^ (-(1 / 2) : ℝ) *
          (Real.exp (c * √(1 + ‖z‖ ^ 2)) • v) j) := by
  have hs : (1 + ‖z‖ ^ 2) ^ (-(1 / 2) : ℝ) = (√(1 + ‖z‖ ^ 2))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  rw [fderiv_exp_mul_sqrt_add_norm_sq c one_pos, hs]
  ext i
  fin_cases i <;>
    simp [gaugeFixedOperatorSymbol_def, symbolDirections, Fin.sum_univ_four] <;>
    ring

/-- **The weak right inverse at a plane vortex preserves exponential decay on the Sobolev
scale.** Let `x` be a smooth solution of the plane vortex equation whose coordinates have bounded
derivatives through order `k`, with `|α| → 1` at infinity, and let `ρ(z) = √(1 + |z|²)` and
`|c| < 1 / 2`. Let `y` be a square-integrable weak solution of `L_x y = f`, `f ∈ L²`, orthogonal
to the weak kernel of `L_x`; for instance `y = Q f` for the weak right inverse `Q` of
`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`. If `exp(c ρ) f ∈ H^k`, then
`exp(c ρ) y ∈ H^(k+1)`. -/
theorem exp_mul_smul_mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq
    (k : ℕ) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (hweak : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫)
    (horth : ∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0) →
      ∫ z, ⟪y z, u z⟫ = 0)
    (hf : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) ∈ sobolevFields k) :
    (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) ∈ sobolevFields (k + 1) := by
  have hw : ContDiff ℝ ∞ (fun z : ℂ ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))) :=
    contDiff_exp_mul_sqrt_add_norm_sq c one_pos
  -- The weighted solution `Y = exp(c ρ) y` is square integrable by the weighted `L²` estimate.
  obtain ⟨K, hK⟩ := exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq
    (μ := volume) (hx.of_le (by simp)) hsol hlim hc
  have hYL : MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 volume :=
    (hK f y hweak horth).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (memLp_of_mem_sobolevFields hf).eLpNorm_lt_top)
  -- `Y` is a weak solution of `L_x Y = exp(c ρ) f + c σ(dρ) Y`, with `c σ(dρ)` as a matrix.
  have hYweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z, gaugeFixedAdjoint x η z⟫ =
        ∫ z, ⟪Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4,
          ⟪z, c • symbolDirections i j⟫ * (1 + ‖z‖ ^ 2) ^ (-(1 / 2) : ℝ) *
            (Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) j), η z⟫ := by
    intro η hη hηc
    rw [integral_inner_smul_gaugeFixedAdjoint_eq hx.continuous hw (Lp.memLp y) (Lp.memLp f)
      (fun η hη hηc ↦ hweak η (hη.of_le (by simp)) hηc) hη hηc]
    simp_rw [gaugeFixedOperatorSymbol_fderiv_exp_mul_sqrt_eq]
  have hA (i j : Fin 4) : ContDiff ℝ ∞
      (fun z : ℂ ↦ ⟪z, c • symbolDirections i j⟫ * (1 + ‖z‖ ^ 2) ^ (-(1 / 2) : ℝ)) :=
    (contDiff_id.inner ℝ contDiff_const).mul (contDiff_one_add_norm_sq_rpow _)
  -- Each step of the elliptic bootstrap gains one derivative, from `L²` up to `H^(k+1)`.
  have key : ∀ j ≤ k + 1,
      (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) ∈ sobolevFields j := by
    intro j hj
    induction j with
    | zero => simpa using hYL
    | succ j ih =>
      have hjk : j ≤ k := by omega
      have hG := add_mem (sobolevFields_mono (by exact_mod_cast hjk) hf)
        (mulVec_mem_sobolevFields_natCast j hA (fun i l ↦ by
          obtain ⟨M, hM0, hM⟩ := exists_forall_norm_iteratedFDeriv_inner_mul_le
            (c • symbolDirections i l) k
          exact ⟨M, hM0, fun n hn ↦ hM n (hn.trans hjk)⟩) (ih (by omega)))
      exact_mod_cast mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq j
        hx (fun i n hn ↦ hbound i n (hn.trans hjk)) hYL hG hYweak
  exact_mod_cast key (k + 1) le_rfl

end TauCeti.Vortex
