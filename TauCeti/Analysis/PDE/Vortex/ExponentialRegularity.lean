/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Exponential decay on the Sobolev scale for the right inverse at a plane vortex

At a plane vortex `x`, the gauge-fixed operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) has a
bounded weak right inverse `Q` on `L²(ℂ; ℝ⁴)`: `Q f` is the weak solution of `L_x y = f`
orthogonal to the weak kernel (`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`).
With `ρ(z) = √(1 + |z|²)` and `|c| < 1/2`, it satisfies the weighted `L²` estimate
`‖exp(c ρ) Q f‖₂ ≤ K ‖exp(c ρ) f‖₂`
(`exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`), and it gains one
derivative on the unweighted Sobolev scale
(`mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq`).
This file combines the two: `Q` gains one derivative on the exponentially weighted Sobolev scale,

`exp(c ρ) f ∈ H^k  ⟹  exp(c ρ) Q f ∈ H^(k+1)`,

for every `k` and every `|c| < 1/2`. For `c > 0` this says that `Q` maps inputs decaying like
`exp(-c ρ)` together with `k` derivatives to outputs decaying at the same rate together with
`k + 1` derivatives. These are the decay properties of the inverse used to correct approximate
solutions built from plane vortices, whose errors decay exponentially away from the vortex cores.

The argument is a weighted elliptic bootstrap. For a smooth real weight `w`, the Leibniz rule
`L_x* (w η) = w L_x* η + σ*(dw) η` of the adjoint (`gaugeFixedAdjoint_fun_smul`), where `σ*` is
minus the transpose of the principal symbol `σ` of `L_x` (`inner_gaugeFixedOperatorSymbol`), shows
that `w y` is a weak solution of

`L_x (w y) = w f + σ(dw) y`

whenever `y` is a weak solution of `L_x y = f` (`integral_inner_fun_smul_gaugeFixedAdjoint_eq`).
For the weight `w = exp(c ρ)` the commutator is `σ(dw) y = c σ(dρ) (w y)`, a multiplication of
`w y` by a matrix whose entries are constant multiples of the derivatives `⟪z, e⟫ / ρ(z)` of `ρ`.
These have bounded derivatives of every order
(`TauCeti.exists_norm_iteratedFDeriv_inner_mul_one_add_norm_sq_rpow_le_of_le_neg_half`), so the
multiplication preserves `H^j` (`mulVec_mem_sobolevFields_natCast`). Starting from
`w y ∈ L²`, which the weighted `L²` estimate supplies, the unweighted bootstrap applied to `w y`
then raises its regularity one step at a time up to `H^(k+1)`.

## Main results

* `integral_inner_fun_smul_gaugeFixedAdjoint_eq`: the weak Leibniz rule
  `L_x (w y) = w f + σ(dw) y`.
* `exp_mul_smul_mem_sobolevFields_natCast_add_one_of_memLp`: weighted elliptic regularity at a
  smooth field with bounded derivatives, for weak solutions `y` with `exp(c ρ) y ∈ L²`.
* `exp_mul_smul_mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq`: at a
  plane vortex with `|α| → 1` and `|c| < 1/2`, the weak solution orthogonal to the weak kernel,
  that is `Q f`, satisfies `exp(c ρ) f ∈ H^k ⟹ exp(c ρ) Q f ∈ H^(k+1)`.
* `exp_mul_smul_mem_sobolevFields_natCast_add_one_of_forall_mem_framedFieldSpace`: the same at a
  continuous plane vortex lying in the affine field space `A_m^k` for every `k`.

These are membership statements. The corresponding norm estimate
`‖exp(c ρ) Q f‖_(H^(k+1)) ≤ K ‖exp(c ρ) f‖_(H^k)` is not proved here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open Complex MeasureTheory Filter
open scoped Topology RealInnerProductSpace ContDiff

namespace TauCeti.Vortex

variable {x y f : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### The weak Leibniz rule -/

/-- **The weak Leibniz rule for the gauge-fixed operator.** Let `x` be continuous and let `y` be a
square-integrable weak solution of `L_x y = f` with `f ∈ L²`, tested against smooth compactly
supported fields. For a smooth real weight `w`, the field `w y` is a weak solution of
`L_x (w y) = w f + σ(dw) y`, where `σ` is the principal symbol of `L_x`
(`gaugeFixedOperatorSymbol`). -/
theorem integral_inner_fun_smul_gaugeFixedAdjoint_eq (hx : Continuous x) {w : ℂ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪w z • y z, gaugeFixedAdjoint x η z⟫ =
      ∫ z, ⟪w z • f z + gaugeFixedOperatorSymbol (fderiv ℝ w z) (y z), η z⟫ := by
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hwη : ContDiff ℝ ∞ (fun z ↦ w z • η z) := hw.smul hη
  have hwηc : HasCompactSupport (fun z ↦ w z • η z) := HasCompactSupport.smul_left (f := w) hηc
  -- The commutator `S = σ*(dw) η` of the adjoint is continuous with compact support.
  set S : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦
    gaugeFixedAdjoint x (fun t ↦ w t • η t) z - w z • gaugeFixedAdjoint x η z
  have hS (z : ℂ) : S z = gaugeFixedAdjointSymbol (fderiv ℝ w z) (η z) := by
    simp only [S, gaugeFixedAdjoint_fun_smul x (hw.differentiable (by simp) z)
      (hη.differentiable (by simp) z), add_sub_cancel_left]
  have hSL : MemLp S 2 volume :=
    ((continuous_gaugeFixedAdjoint hx (hwη.of_le h1)).sub (hw.continuous.smul
      (continuous_gaugeFixedAdjoint hx (hη.of_le h1)))).memLp_of_hasCompactSupport
      ((hasCompactSupport_gaugeFixedAdjoint hwηc).sub
        (HasCompactSupport.smul_left (f := w) (hasCompactSupport_gaugeFixedAdjoint hηc)))
  have hwηL : MemLp (fun z ↦ w z • η z) 2 volume :=
    hwη.continuous.memLp_of_hasCompactSupport hwηc
  have hAL : MemLp (gaugeFixedAdjoint x fun t ↦ w t • η t) 2 volume :=
    (continuous_gaugeFixedAdjoint hx (hwη.of_le h1)).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hwηc)
  -- Pointwise, both sides differ from the test against `w η` by the pairing of `y` with `S`.
  have hl (z : ℂ) : ⟪w z • y z, gaugeFixedAdjoint x η z⟫ =
      ⟪y z, gaugeFixedAdjoint x (fun t ↦ w t • η t) z⟫ - ⟪y z, S z⟫ := by
    simp only [S, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    ring
  have hr (z : ℂ) : ⟪w z • f z + gaugeFixedOperatorSymbol (fderiv ℝ w z) (y z), η z⟫ =
      ⟪f z, w z • η z⟫ - ⟪y z, S z⟫ := by
    rw [inner_add_left, inner_gaugeFixedOperatorSymbol, ← hS, real_inner_smul_left,
      real_inner_smul_right]
    ring
  rw [integral_congr_ae (.of_forall hl), integral_congr_ae (.of_forall hr),
    integral_sub (hy.integrable_inner (𝕜 := ℝ) hAL) (hy.integrable_inner (𝕜 := ℝ) hSL),
    integral_sub (hf.integrable_inner (𝕜 := ℝ) hwηL) (hy.integrable_inner (𝕜 := ℝ) hSL),
    hweak _ hwη hwηc]

/-! ### The commutator with the exponential weight -/

/-- The complex numbers `e i j` such that the principal symbol of `L_x` at a real covector `d` is
the matrix `(d (e i j))`. -/
private def symbolDirection : Fin 4 → Fin 4 → ℂ :=
  ![![1, I, 0, 0], ![I, -1, 0, 0], ![0, 0, 1, -I], ![0, 0, I, 1]]

/-- The entries `c ⟪z, e i j⟫ / ρ(z)` of the commutator of `L_x` with the weight `exp(c ρ)`. -/
private def weightCoeff (c : ℝ) (i j : Fin 4) (z : ℂ) : ℝ :=
  inner ℝ z (c • symbolDirection i j) * (1 + ‖z‖ ^ 2) ^ (-(1 / 2) : ℝ)

/-- The coefficients of the commutator are smooth. -/
private theorem contDiff_weightCoeff (c : ℝ) (i j : Fin 4) : ContDiff ℝ ∞ (weightCoeff c i j) :=
  (contDiff_id.inner ℝ contDiff_const).mul (contDiff_one_add_norm_sq_rpow _)

/-- The coefficients of the commutator have bounded derivatives through every order `k`. -/
private theorem exists_norm_iteratedFDeriv_weightCoeff_le (c : ℝ) (i j : Fin 4) (k : ℕ) :
    ∃ M ≥ 0, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (weightCoeff c i j) z‖ ≤ M :=
  have ⟨M, hM⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_exists fun n _ ↦
    exists_norm_iteratedFDeriv_inner_mul_one_add_norm_sq_rpow_le_of_le_neg_half
      (c • symbolDirection i j) le_rfl n
  ⟨M, (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hM).1, hM⟩

/-- The commutator of `L_x` with the weight `w = exp(c ρ)`: `σ(dw) v` is the multiplication of
`w v` by the matrix `weightCoeff c`. -/
private theorem gaugeFixedOperatorSymbol_fderiv_exp_mul_sqrt (c : ℝ) (z : ℂ)
    (v : EuclideanSpace ℝ (Fin 4)) :
    gaugeFixedOperatorSymbol (fderiv ℝ (fun t : ℂ ↦ Real.exp (c * √(1 + ‖t‖ ^ 2))) z) v =
      WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4,
        weightCoeff c i j z * (Real.exp (c * √(1 + ‖z‖ ^ 2)) • v) j) := by
  have hρ : ((1 + ‖z‖ ^ 2) ^ (-(1 / 2) : ℝ)) = (√(1 + ‖z‖ ^ 2))⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
  rw [fderiv_exp_mul_sqrt_add_norm_sq c one_pos]
  simp only [weightCoeff, hρ]
  ext i
  fin_cases i <;>
    simp [gaugeFixedOperatorSymbol_def, symbolDirection, Fin.sum_univ_four, div_eq_mul_inv] <;>
    ring

/-! ### Weighted regularity -/

/-- **Weighted elliptic regularity for the gauge-fixed operator.** Let `x` be a smooth field whose
coordinates have bounded derivatives through order `k`, and let `y` be a square-integrable weak
solution of `L_x y = f` with `f ∈ L²`, tested against smooth compactly supported fields. Put
`ρ(z) = √(1 + |z|²)` and let `c` be real. If `exp(c ρ) y` is square integrable and
`exp(c ρ) f ∈ H^k`, then `exp(c ρ) y ∈ H^(k+1)`. -/
theorem exp_mul_smul_mem_sobolevFields_natCast_add_one_of_memLp (k : ℕ)
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) {c : ℝ}
    (hwy : MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 volume)
    (hwf : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) ∈ sobolevFields k) :
    (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) ∈ sobolevFields (k + 1) := by
  -- `exp(c ρ) y` is a weak solution of `L_x (exp(c ρ) y) = exp(c ρ) f + G`, where `G` is the
  -- multiplication of `exp(c ρ) y` by the matrix `weightCoeff c`.
  have hweakY (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ ∞ η)
      (hηc : HasCompactSupport η) :
      ∫ z, ⟪Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z, gaugeFixedAdjoint x η z⟫ =
        ∫ z, ⟪Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4,
          weightCoeff c i j z * (Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) j), η z⟫ := by
    rw [integral_inner_fun_smul_gaugeFixedAdjoint_eq hx.continuous
      (contDiff_exp_mul_sqrt_add_norm_sq c one_pos) hy hf hweak hη hηc]
    simp only [gaugeFixedOperatorSymbol_fderiv_exp_mul_sqrt]
  -- One step of the bootstrap: `exp(c ρ) y ∈ H^j` gives `exp(c ρ) y ∈ H^(j+1)` for `j ≤ k`.
  have hstep (j : ℕ) (hj : j ≤ k)
      (hYj : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) ∈ sobolevFields j) :
      (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) ∈ sobolevFields (j + 1) := by
    have hG := mulVec_mem_sobolevFields_natCast j (contDiff_weightCoeff c)
      (fun i' j' ↦ exists_norm_iteratedFDeriv_weightCoeff_le c i' j' j) hYj
    exact mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq j hx
      (fun i n hn ↦ hbound i n (hn.trans hj)) hwy
      (add_mem (sobolevFields_mono (by exact_mod_cast hj) hwf) hG) hweakY
  have hall (j : ℕ) (hj : j ≤ k) :
      (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) ∈ sobolevFields (j + 1) := by
    induction j with
    | zero => simpa using hstep 0 hj (by simpa using hwy)
    | succ j ih => exact_mod_cast hstep (j + 1) hj (by exact_mod_cast ih (by omega))
  exact hall k le_rfl

/-- **The right inverse preserves exponential decay on the Sobolev scale.** Let `x` be a smooth
solution of the plane vortex equation with `|α| → 1` at infinity whose coordinates have bounded
derivatives through order `k`, let `ρ(z) = √(1 + |z|²)` and `|c| < 1/2`. Let `y` be the
square-integrable weak solution of `L_x y = f` orthogonal to the weak kernel of `L_x`, that is the
value at `f` of the weak right inverse `Q` of
`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`. If `exp(c ρ) f ∈ H^k`, then
`exp(c ρ) y ∈ H^(k+1)`. -/
theorem exp_mul_smul_mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq
    (k : ℕ) (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {c : ℝ} (hc : |c| < 1 / 2) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume}
    (hweak : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫)
    (horth : ∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0) →
      ∫ z, ⟪y z, u z⟫ = 0)
    (hwf : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) ∈ sobolevFields k) :
    (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) ∈ sobolevFields (k + 1) := by
  obtain ⟨K, hK⟩ := exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq
    (μ := volume) (hx.of_le (by exact_mod_cast le_top)) hsol hlim hc
  have hwy : MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 volume :=
    memLp_iff.2 <| (hK f y hweak horth).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (memLp_of_mem_sobolevFields hwf).eLpNorm_lt_top)
  exact exp_mul_smul_mem_sobolevFields_natCast_add_one_of_memLp k hx hbound (Lp.memLp y)
    (Lp.memLp f) (fun η hη hηc ↦ hweak η (hη.of_le (by norm_cast)) hηc) hwy hwf

/-- **The right inverse at a vortex of every `A_m^k` preserves exponential decay.** Let `x` be a
continuous solution of the plane vortex equations lying in the affine field space `A_m^k` for every
`k`, let `ρ(z) = √(1 + |z|²)` and `|c| < 1/2`. If `y` is the square-integrable weak solution of
`L_x y = f` orthogonal to the weak kernel, then `exp(c ρ) f ∈ H^k` implies
`exp(c ρ) y ∈ H^(k+1)`, for every `k`. -/
theorem exp_mul_smul_mem_sobolevFields_natCast_add_one_of_forall_mem_framedFieldSpace
    {b : ContDiffBump (0 : ℝ)} {m : ℕ} (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace b m k) (hsol : ∀ z, equation x z = 0) {c : ℝ}
    (hc : |c| < 1 / 2) (k : ℕ) {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume}
    (hweak : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫)
    (horth : ∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0) →
      ∫ z, ⟪y z, u z⟫ = 0)
    (hwf : (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) ∈ sobolevFields k) :
    (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) ∈ sobolevFields (k + 1) :=
  exp_mul_smul_mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k
    (contDiff_of_forall_mem_framedFieldSpace hx hmem) hsol
    (tendsto_normSq_of_mem_framedFieldSpace one_lt_two (by exact_mod_cast hmem 2) hx)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2))) hc
    hweak horth hwf

end TauCeti.Vortex
