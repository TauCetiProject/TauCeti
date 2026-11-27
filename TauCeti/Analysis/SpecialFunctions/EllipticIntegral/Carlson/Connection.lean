/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.RJ
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# A connection formula between Carlson's `R_F` and `R_D`

For `x, z ∈ slitPlane` and `y ∈ slitPlane ∪ {0}`,

`(x - y) R_D(y, z, x) + (z - y) R_D(x, y, z) = 3 R_F(x, y, z) - 3 y^(1/2) x^(-1/2) z^(-1/2)`

(DLMF 19.21.8). With `R_D` the partial derivatives of `R_F` (DLMF 19.18.1), it is the
identity behind the derivative of `x R_F(1 - x², 1 - k² x², 1)`, Carlson's form of the
incomplete integral of the first kind as a function of `sin φ`.

The proof is one integration over `(0, ∞)`. The combination of the three integrands is the
derivative of `-2 (t + x)^(-1/2) (t + y)^(1/2) (t + z)^(-1/2)`, which tends to `0` at `∞`.

## Main results

* `Complex.sub_mul_carlsonRD_add_sub_mul_carlsonRD`: the connection formula.

## References

* NIST *Digital Library of Mathematical Functions*, §19.21(iii), <https://dlmf.nist.gov/19.21>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
-/

public section

open MeasureTheory Set Filter Topology

namespace Complex

/-- The antiderivative `-2 (t + x)^(-1/2) (t + y)^(1/2) (t + z)^(-1/2)` has derivative
`A B C (1 - (x - y) (t + x)⁻¹ - (z - y) (t + z)⁻¹)` on `(0, ∞)`, where `A`, `B`, `C` are the
inverse square roots of `t + x`, `t + y`, `t + z`: the `R_F` integrand minus `x - y` times the
`R_J(y, z, x, x)` integrand and `z - y` times the `R_J(x, y, z, z)` integrand. -/
private theorem hasDerivAt_carlsonConnection_primitive {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => -2 * (((s : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((s : ℂ) + y) ^ (1 / 2 : ℂ) * ((s : ℂ) + z) ^ (-(1 / 2) : ℂ)))
      (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) -
        (x - y) * (((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + x)⁻¹) -
        (z - y) * (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z)⁻¹)) t := by
  have htx : (t : ℂ) + x ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane hx ht.le
  have hty : (t : ℂ) + y ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane_of_mem_union hy ht
  have htz : (t : ℂ) + z ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane hz ht.le
  have hd (w s : ℂ) (hs : s ≠ 1) (hw : (t : ℂ) + w ∈ slitPlane) :
      HasDerivAt (fun r : ℝ => ((r : ℂ) + w) ^ s) (s * (((t : ℂ) + w) ^ s * ((t : ℂ) + w)⁻¹))
        t := by
    rw [TauCeti.cpow_mul_inv hs]
    simpa using (((hasDerivAt_id (t : ℂ)).add_const w).cpow_const (c := s) hw).comp_ofReal
  refine ((((hd x _ (by norm_num) htx).fun_mul (hd y _ (by norm_num) hty)).fun_mul
    (hd z _ (by norm_num) htz)).const_mul (-2 : ℂ)).congr_deriv ?_
  set A := ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)
  set C := ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)
  set B := ((t : ℂ) + y) ^ (-(1 / 2) : ℂ)
  have hY : ((t : ℂ) + y) ^ (1 / 2 : ℂ) = B * ((t : ℂ) + y) :=
    (cpow_neg_half_mul_eq_cpow_half _).symm
  have hx₁ : ((t : ℂ) + x) * ((t : ℂ) + x)⁻¹ = 1 := mul_inv_cancel₀ (slitPlane_ne_zero htx)
  have hy₁ : ((t : ℂ) + y) * ((t : ℂ) + y)⁻¹ = 1 := mul_inv_cancel₀ (slitPlane_ne_zero hty)
  have hz₁ : ((t : ℂ) + z) * ((t : ℂ) + z)⁻¹ = 1 := mul_inv_cancel₀ (slitPlane_ne_zero htz)
  rw [hY]
  linear_combination (A * B * C) * hx₁ + (A * B * C) * hz₁ - (A * B * C) * hy₁

/-- The antiderivative `-2 (t + x)^(-1/2) (t + y)^(1/2) (t + z)^(-1/2)` is `O(t^(-1/2))`, so it
tends to `0` at `∞`. -/
private theorem tendsto_carlsonConnection_primitive {x z : ℂ} (hx : x ∈ slitPlane)
    (hz : z ∈ slitPlane) (y : ℂ) :
    Tendsto (fun s : ℝ => -2 * (((s : ℂ) + x) ^ (-(1 / 2) : ℂ) *
      ((s : ℂ) + y) ^ (1 / 2 : ℂ) * ((s : ℂ) + z) ^ (-(1 / 2) : ℂ))) atTop (𝓝 0) := by
  obtain ⟨Cx, hCx0, hCx⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_one_add_rpow hx
    (-(1 / 2))
  obtain ⟨Cz, -, hCz⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_one_add_rpow hz
    (-(1 / 2))
  push_cast at hCx hCz
  set K : ℝ := 2 * Cx * (1 + ‖y‖) ^ (1 / 2 : ℝ) * Cz
  have h0 : Tendsto (fun t : ℝ => K * (1 + t) ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)).const_mul K
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop 0] with t ht
  have h1t : 0 < 1 + t := by linarith
  have hty_le : ‖(t : ℂ) + y‖ ≤ (1 + ‖y‖) * (1 + t) := by
    calc ‖(t : ℂ) + y‖ ≤ ‖(t : ℂ)‖ + ‖y‖ := norm_add_le _ _
      _ = t + ‖y‖ := by rw [norm_real, Real.norm_of_nonneg ht]
      _ ≤ (1 + ‖y‖) * (1 + t) := by nlinarith [norm_nonneg y]
  have hY : ‖((t : ℂ) + y) ^ (1 / 2 : ℂ)‖ ≤ (1 + ‖y‖) ^ (1 / 2 : ℝ) * (1 + t) ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, norm_cpow_real,
      ← Real.mul_rpow (by positivity) h1t.le]
    exact Real.rpow_le_rpow (norm_nonneg _) hty_le (by norm_num)
  have hrpow : (1 + t) ^ (-(1 / 2) : ℝ) * (1 + t) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add h1t]
    norm_num
  simp only [norm_mul, norm_neg, norm_ofNat]
  calc 2 * (‖((t : ℂ) + x) ^ (-(1 / 2) : ℂ)‖ * ‖((t : ℂ) + y) ^ (1 / 2 : ℂ)‖ *
        ‖((t : ℂ) + z) ^ (-(1 / 2) : ℂ)‖)
      ≤ 2 * (Cx * (1 + t) ^ (-(1 / 2) : ℝ) *
          ((1 + ‖y‖) ^ (1 / 2 : ℝ) * (1 + t) ^ (1 / 2 : ℝ)) *
          (Cz * (1 + t) ^ (-(1 / 2) : ℝ))) := by
        gcongr
        · exact hCx t ht
        · exact hCz t ht
    _ = K * (1 + t) ^ (-(1 / 2) : ℝ) *
          ((1 + t) ^ (-(1 / 2) : ℝ) * (1 + t) ^ (1 / 2 : ℝ)) := by ring
    _ = K * (1 + t) ^ (-(1 / 2) : ℝ) := by rw [hrpow, mul_one]

/-- **A connection formula between `R_F` and `R_D`** (DLMF 19.21.8): for `x, z ∈ slitPlane` and
`y ∈ slitPlane ∪ {0}`,
`(x - y) R_D(y, z, x) + (z - y) R_D(x, y, z) = 3 R_F(x, y, z) - 3 y^(1/2) x^(-1/2) z^(-1/2)`.
At `y = 0` the last term vanishes. -/
theorem sub_mul_carlsonRD_add_sub_mul_carlsonRD {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) :
    (x - y) * carlsonRD y z x + (z - y) * carlsonRD x y z =
      3 * carlsonRF x y z - 3 * (y ^ (1 / 2 : ℂ) * x ^ (-(1 / 2) : ℂ) * z ^ (-(1 / 2) : ℂ)) := by
  let H : ℝ → ℂ := fun s => -2 * (((s : ℂ) + x) ^ (-(1 / 2) : ℂ) *
    ((s : ℂ) + y) ^ (1 / 2 : ℂ) * ((s : ℂ) + z) ^ (-(1 / 2) : ℂ))
  let fF : ℝ → ℂ := fun t => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)
  let fx : ℝ → ℂ := fun t => ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + x)⁻¹
  let fz : ℝ → ℂ := fun t => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z)⁻¹
  -- The three integrands are integrable; `y` may vanish, so it goes first where it can.
  have hiF : IntegrableOn fF (Ioi 0) := by
    refine (integrableOn_carlsonRF_integrand hy hx hz).congr_fun (fun t _ => ?_)
      measurableSet_Ioi
    simp only [fF]
    ring
  have hix : IntegrableOn fx (Ioi 0) := integrableOn_carlsonRJ_integrand hy hz hx hx
  have hiz : IntegrableOn fz (Ioi 0) := by
    refine (integrableOn_carlsonRJ_integrand hy hx hz hz).congr_fun (fun t _ => ?_)
      measurableSet_Ioi
    simp only [fz]
    ring
  have hcont : ContinuousWithinAt H (Ici 0) 0 := by
    have hpow (w : ℂ) (hw : w ∈ slitPlane) :
        ContinuousAt (fun s : ℝ => ((s : ℂ) + w) ^ (-(1 / 2) : ℂ)) 0 :=
      (continuous_ofReal.add continuous_const).continuousAt.cpow continuousAt_const
        (by simpa using hw)
    exact (continuousAt_const.mul (((hpow x hx).mul
      (TauCeti.continuous_ofReal_add_cpow_of_re_pos (by norm_num)).continuousAt).mul
        (hpow z hz))).continuousWithinAt
  have hint : IntegrableOn (fun t => fF t - (x - y) * fx t) (Ioi 0) :=
    hiF.fun_sub (hix.const_mul (x - y))
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun t ht => hasDerivAt_carlsonConnection_primitive hx hy hz ht)
    (hint.fun_sub (hiz.const_mul (z - y))) (tendsto_carlsonConnection_primitive hx hz y)
  rw [integral_sub hint (hiz.const_mul _), integral_sub hiF (hix.const_mul _),
    integral_const_mul, integral_const_mul] at hftc
  simp only [H, fF, fx, fz, ofReal_zero, zero_add] at hftc
  rw [carlsonRD_def, carlsonRJ_def, carlsonRD_def, carlsonRJ_def, carlsonRF_def]
  linear_combination (-(3 / 2) : ℂ) * hftc

end Complex
