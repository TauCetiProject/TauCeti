/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.Basic
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.RJ
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Carlson's completely symmetric elliptic integral `R_G`

This file defines Carlson's completely symmetric elliptic integral of the second kind
(DLMF 19.16.3)

`R_G(x, y, z) = ¼ ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2)
  (x / (t + x) + y / (t + y) + z / (t + z)) t dt`

for complex `x, y, z`, with the principal branch of each factor `(t + x) ^ (-1/2 : ℂ)`. In
Carlson's normal form of Legendre's integrals, the complete integral of the second kind is
`E(k) = 2 R_G(0, 1 - k², 1)`, and the perimeter of an ellipse is a multiple of an `R_G` value.

The integral converges absolutely whenever `x, y, z` lie in `Complex.slitPlane ∪ {0}`
(`Complex.integrableOn_carlsonRGIntegrand`), including when two or all three arguments vanish
(at `(0, 0, 0)` the integrand vanishes identically, giving `R_G(0, 0, 0) = 0`). Wherever the
integral fails to converge outside this domain, `carlsonRG` is a totalized value.

## Main results

* `Complex.carlsonRGIntegrand` — the integrand of `R_G`.
* `Complex.carlsonRG` — the integral `R_G`.
* `Complex.integrableOn_carlsonRGIntegrand` — absolute convergence of the defining
  integral on `(slitPlane ∪ {0})³`.
* `Complex.carlsonRG_comm_left`, `Complex.carlsonRG_comm_right` — `R_G` is
  symmetric in its three arguments.
* `Complex.carlsonRG_ofReal_mul` — homogeneity of degree `1/2` under positive real
  scaling.
* `Complex.carlsonRG_self` — the diagonal value `R_G(x, x, x) = x^(1/2)`.
* `Complex.carlsonRG_zero_zero_eq_mul_carlsonRF`, `Complex.carlsonRG_zero_zero` — the degenerate
  value `R_G(0, 0, z) = z^(1/2) / 2` (DLMF 19.20.4).
* `Complex.two_mul_carlsonRG_eq` — reduction of `2 R_G(x, y, z)` to `R_F` and `R_D`
  (DLMF 19.21.10).
* `Complex.carlsonRG_pos` — `R_G` is a positive real number at nonnegative real
  arguments, not all zero.

## References

* NIST *Digital Library of Mathematical Functions*, §19.16, §19.20, and §19.21,
  <https://dlmf.nist.gov/19.16>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
* B. C. Carlson, Numerical computation of real or complex elliptic integrals, *Numer. Algorithms*
  10 (1995), 13–26.

B. Braams' `lean-codes` (<https://github.com/bjbraams/lean-codes>) formalizes Carlson's book,
including `R_G` and `Carlson.two_mul_RG_eq` (`Carlson/Functions/RG.lean`), on top of Carlson's
general `R`-function, a Dirichlet average over a simplex. This file instead works directly from the
integral definition above and is not ported from it.
-/

public section

open MeasureTheory Set Filter Topology
open Complex (slitPlane mem_slitPlane_iff ofReal_mem_slitPlane)
open scoped ComplexOrder

namespace Complex

/-- The integrand of Carlson's `R_G` (DLMF 19.16.3) at `t`:
`(t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2) (x / (t + x) + y / (t + y) + z / (t + z)) t`,
with principal complex powers of each factor. -/
noncomputable def carlsonRGIntegrand (x y z : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
      (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t

/-- The explicit formula for `carlsonRGIntegrand`. -/
theorem carlsonRGIntegrand_def (x y z : ℂ) (t : ℝ) :
    carlsonRGIntegrand x y z t =
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
          (x / ((t : ℂ) + x) + y / ((t : ℂ) + y) + z / ((t : ℂ) + z)) * t :=
  (rfl)

/-- **Carlson's completely symmetric elliptic integral of the second kind** (DLMF 19.16.3):
`R_G(x, y, z) = ¼ ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2)
(x / (t + x) + y / (t + y) + z / (t + z)) t dt`, the integral of `carlsonRGIntegrand`.

The integral converges when `x, y, z ∈ slitPlane ∪ {0}` (`integrableOn_carlsonRGIntegrand`);
wherever the integral fails to converge, the value is a totalized junk value. -/
noncomputable def carlsonRG (x y z : ℂ) : ℂ :=
  (1 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ), carlsonRGIntegrand x y z t

/-- The defining integral of `carlsonRG`. -/
theorem carlsonRG_def (x y z : ℂ) :
    carlsonRG x y z = (1 / 4 : ℂ) * ∫ t in Ioi (0 : ℝ), carlsonRGIntegrand x y z t :=
  (rfl)

/-! ### Convergence -/

/-- **Convergence of `R_G`.** The integrand of `carlsonRG x y z` is integrable on `(0, ∞)`
whenever `x, y, z ∈ slitPlane ∪ {0}`, including when two or all three arguments vanish. -/
theorem integrableOn_carlsonRGIntegrand {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane ∪ {0}) :
    IntegrableOn (carlsonRGIntegrand x y z) (Ioi 0) := by
  -- Each of the three symmetric summands vanishes identically when its numerator argument `u` is
  -- `0`, and equals `u (t + u)^(-3/2) (t + v)^(-1/2) (t + w)^(-1/2) t = O((1 + t)^(-3/2))` on
  -- `(0, ∞)` when `u ∈ slitPlane` (since `(t + v)^(-1/2) (t + w)^(-1/2) t = O(1)`).
  have hterm {u v w : ℂ} (hu : u ∈ slitPlane ∪ {0}) (hv : v ∈ slitPlane ∪ {0})
      (hw : w ∈ slitPlane ∪ {0}) :
      IntegrableOn (fun t : ℝ => ((t : ℂ) + u) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + v) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) *
          (u / ((t : ℂ) + u)) * t) (Ioi 0) := by
    rcases hu with hu | hu
    · have hrew (t : ℝ) : ((t : ℂ) + u) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + v) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) * (u / ((t : ℂ) + u)) * t =
          u * (((t : ℂ) + u) ^ (-(3 / 2) : ℂ) * ((t : ℂ) + v) ^ (-(1 / 2) : ℂ) *
            ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) * t) := by
        have hpow : ((t : ℂ) + u) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + u)⁻¹ =
            ((t : ℂ) + u) ^ (-(3 / 2) : ℂ) := by
          rw [TauCeti.cpow_mul_inv (by norm_num)]
          norm_num
        rw [div_eq_mul_inv u ((t : ℂ) + u)]
        linear_combination
          (u * ((t : ℂ) + v) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) * t) * hpow
      simp_rw [hrew]
      refine Integrable.const_mul ?_ u
      have hcont := (((TauCeti.continuousOn_ofReal_add_cpow (Or.inl hu) (-(3 / 2))).mul
        (TauCeti.continuousOn_ofReal_add_cpow hv (-(1 / 2)))).mul
        (TauCeti.continuousOn_ofReal_add_cpow hw (-(1 / 2)))).mul
        Complex.continuous_ofReal.continuousOn
      obtain ⟨Cu, hCu0, hCu⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_one_add_rpow hu
        (r := -(3 / 2)) (by norm_num)
      have hr : (-(1 / 2) : ℝ) ≤ 0 := by norm_num
      obtain ⟨Cv, hCv⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hv hr
      obtain ⟨Cw, hCw⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hw hr
      have hCv0 : 0 ≤ Cv := by simpa using (norm_nonneg _).trans (hCv 1 one_pos)
      have hCw0 : 0 ≤ Cw := by simpa using (norm_nonneg _).trans (hCw 1 one_pos)
      push_cast at hCu hCv hCw
      refine ((TauCeti.integrableOn_rpow_mul_one_add_rpow one_pos one_half_pos).const_mul
        (Cu * Cv * Cw)).mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have ht_cancel : t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) * t = 1 := by
        rw [← Real.rpow_add ht0]
        norm_num [Real.rpow_neg_one, inv_mul_cancel₀ ht0.ne']
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
      calc ‖((t : ℂ) + u) ^ (-(3 / 2) : ℂ)‖ * ‖((t : ℂ) + v) ^ (-(1 / 2) : ℂ)‖ *
            ‖((t : ℂ) + w) ^ (-(1 / 2) : ℂ)‖ * t
          ≤ (Cu * (1 + t) ^ (-(3 / 2) : ℝ)) * (Cv * t ^ (-(1 / 2) : ℝ)) *
              (Cw * t ^ (-(1 / 2) : ℝ)) * t := by
            gcongr
            exacts [hCu t ht0.le, hCv t ht0, hCw t ht0]
        _ = Cu * Cv * Cw * (t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ) * t) *
            (1 + t) ^ (-(3 / 2) : ℝ) := by ring
        _ = Cu * Cv * Cw * (t ^ ((1 : ℝ) - 1) * (1 + t) ^ (-((1 : ℝ) + 1 / 2))) := by
            rw [ht_cancel]
            norm_num
    · rw [Set.mem_singleton_iff.mp hu]
      simp
  refine (((hterm hx hy hz).add (hterm hy hz hx)).add (hterm hz hx hy)).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, carlsonRGIntegrand]
  ring

/-! ### Symmetry -/

/-- The integrand of `R_G` is symmetric in its first two arguments. -/
theorem carlsonRGIntegrand_comm_left (x y z : ℂ) :
    carlsonRGIntegrand x y z = carlsonRGIntegrand y x z := by
  funext t
  simp only [carlsonRGIntegrand]
  ring

/-- The integrand of `R_G` is symmetric in its second and third arguments. -/
theorem carlsonRGIntegrand_comm_right (x y z : ℂ) :
    carlsonRGIntegrand x y z = carlsonRGIntegrand x z y := by
  funext t
  simp only [carlsonRGIntegrand]
  ring

/-- `R_G` is symmetric in its first two arguments. -/
theorem carlsonRG_comm_left (x y z : ℂ) : carlsonRG x y z = carlsonRG y x z := by
  rw [carlsonRG_def, carlsonRG_def, carlsonRGIntegrand_comm_left]

/-- `R_G` is symmetric in its second and third arguments. Together with `carlsonRG_comm_left`,
`R_G` is symmetric in all three arguments. -/
theorem carlsonRG_comm_right (x y z : ℂ) : carlsonRG x y z = carlsonRG x z y := by
  rw [carlsonRG_def, carlsonRG_def, carlsonRGIntegrand_comm_right]

/-! ### Homogeneity -/

/-- **Homogeneity of `R_G`.** For real `l > 0`, `R_G(l x, l y, l z) = l^(1/2) R_G(x, y, z)`.
No hypothesis on `x, y, z` is needed: the substitution `t = l s` identifies the two integrals
whether or not they converge. -/
theorem carlsonRG_ofReal_mul {l : ℝ} (hl : 0 < l) (x y z : ℂ) :
    carlsonRG (l * x) (l * y) (l * z) = (l : ℂ) ^ (1 / 2 : ℂ) * carlsonRG x y z := by
  have hl0 : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
  have hscale (s : ℝ) (w : ℂ) : (((l * s : ℝ) : ℂ) + l * w) ^ (-(1 / 2) : ℂ) =
      (l : ℂ) ^ (-(1 / 2) : ℂ) * ((s : ℂ) + w) ^ (-(1 / 2) : ℂ) := by
    rw [Complex.ofReal_mul, ← mul_add, TauCeti.ofReal_mul_cpow hl.le]
  have hscale_div (s : ℝ) (w : ℂ) :
      (l : ℂ) * w / (((l * s : ℝ) : ℂ) + l * w) = w / ((s : ℂ) + w) := by
    rw [Complex.ofReal_mul, ← mul_add, mul_div_mul_left _ _ hl0]
  -- `l² · (l^(-1/2))³ = l^(1/2)`: the Jacobian and the factor `t = l s` against the three
  -- rescaled powers.
  have hl3 : (l : ℂ) * (l : ℂ) * ((l : ℂ) ^ (-(1 / 2) : ℂ)) ^ 3 = (l : ℂ) ^ (1 / 2 : ℂ) := by
    rw [← Complex.cpow_nat_mul, ← pow_two, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hl0]
    norm_num
  have h := integral_comp_mul_left_Ioi' (carlsonRGIntegrand (l * x) (l * y) (l * z)) 0 hl
  rw [mul_zero] at h
  have hfun : (fun s : ℝ => carlsonRGIntegrand (l * x) (l * y) (l * z) (l * s)) =
      fun s : ℝ => (l : ℂ) * ((l : ℂ) ^ (-(1 / 2) : ℂ)) ^ 3 * carlsonRGIntegrand x y z s := by
    funext s
    simp only [carlsonRGIntegrand]
    rw [hscale, hscale, hscale, hscale_div, hscale_div, hscale_div, Complex.ofReal_mul]
    ring
  rw [carlsonRG_def, carlsonRG_def, ← h, hfun, integral_const_mul, Complex.real_smul, ← hl3]
  ring

/-! ### Diagonal value -/

/-- **The diagonal value of `R_G`**: `R_G(x, x, x) = x^(1/2)` for `x` in the slit plane. -/
@[simp]
theorem carlsonRG_self {x : ℂ} (hx : x ∈ slitPlane) : carlsonRG x x x = x ^ (1 / 2 : ℂ) := by
  have hmem (t : ℝ) (ht : 0 ≤ t) : (t : ℂ) + x ∈ slitPlane :=
    TauCeti.ofReal_add_mem_slitPlane hx ht
  have hx0 : x ≠ 0 := Complex.slitPlane_ne_zero hx
  -- `-6x (t + x)^(-1/2) + 2x² (t + x)^(-3/2)` is an antiderivative of `3x t (t + x)^(-5/2)`.
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -6 * x * ((t : ℂ) + x) ^ (-((1 / 2 : ℝ) : ℂ)) +
          2 * x ^ 2 * ((t : ℂ) + x) ^ (-((3 / 2 : ℝ) : ℂ)))
        (carlsonRGIntegrand x x x t) t := by
    intro t ht
    have hd (s : ℂ) := (((hasDerivAt_id (t : ℂ)).add_const x).cpow_const (c := s)
      (hmem t ht)).comp_ofReal
    have h := ((hd (-((1 / 2 : ℝ) : ℂ))).const_mul (-6 * x)).add
      ((hd (-((3 / 2 : ℝ) : ℂ))).const_mul (2 * x ^ 2))
    simp only [id] at h
    convert h using 1
    unfold carlsonRGIntegrand
    have hne := Complex.slitPlane_ne_zero (hmem t ht)
    -- Write every power of `w = t + x` through `u = w^(-1/2)`, using `u² = w⁻¹`.
    set w : ℂ := (t : ℂ) + x with hw
    set u : ℂ := w ^ (-(1 / 2) : ℂ) with hu
    have hu2 : u ^ 2 = w⁻¹ := by
      rw [hu, ← Complex.cpow_nat_mul, ← Complex.cpow_neg_one]
      norm_num
    have hp3 : w ^ (-((1 / 2 : ℝ) : ℂ) - 1) = u ^ 3 := by
      rw [hu, ← Complex.cpow_nat_mul]
      norm_num
    have hp5 : w ^ (-((3 / 2 : ℝ) : ℂ) - 1) = u ^ 5 := by
      rw [hu, ← Complex.cpow_nat_mul]
      norm_num
    have ht' : (t : ℂ) = w - x := by rw [hw]; ring
    have hu2' : u ^ 2 * w = 1 := by rw [hu2, inv_mul_cancel₀ hne]
    rw [hp3, hp5, div_eq_mul_inv, ← hu2]
    push_cast
    linear_combination (3 * x * u ^ 5) * ht' + (3 * x * u ^ 3) * hu2'
  have hlim : Tendsto (fun t : ℝ => -6 * x * ((t : ℂ) + x) ^ (-((1 / 2 : ℝ) : ℂ)) +
      2 * x ^ 2 * ((t : ℂ) + x) ^ (-((3 / 2 : ℝ) : ℂ))) atTop (𝓝 0) := by
    simpa using
      ((Complex.tendsto_ofReal_add_cpow_neg x (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
        (-6 * x)).add
      ((Complex.tendsto_ofReal_add_cpow_neg x (by norm_num : (0 : ℝ) < 3 / 2)).const_mul
        (2 * x ^ 2))
  rw [carlsonRG_def, integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_carlsonRGIntegrand (Or.inl hx) (Or.inl hx) (Or.inl hx)) hlim]
  -- The value at `t = 0` is `-6 x · x^(-1/2) + 2 x² · x^(-3/2) = -4 x^(1/2)`.
  have h1 : x * x ^ (-((1 / 2 : ℝ) : ℂ)) = x ^ (1 / 2 : ℂ) := by
    conv_lhs => enter [1]; rw [← Complex.cpow_one x]
    rw [← Complex.cpow_add _ _ hx0]
    norm_num
  have h2 : x ^ 2 * x ^ (-((3 / 2 : ℝ) : ℂ)) = x ^ (1 / 2 : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hx0]
    norm_num
  simp only [Complex.ofReal_zero, zero_add]
  linear_combination (3 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2

/-! ### Two zero arguments -/

private theorem carlsonRGIntegrand_zero_zero_eq (z : ℂ) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    carlsonRGIntegrand 0 0 z t =
      z * (((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)) := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  rw [carlsonRGIntegrand_def]
  simp only [add_zero, zero_div, zero_add]
  rw [Complex.cpow_neg_half_mul_self (t : ℂ), div_eq_mul_inv z,
    ← Complex.cpow_neg_half_mul_self ((t : ℂ) + z)]
  linear_combination (z * (((t : ℂ) + z) ^ (-(1 / 2) : ℂ)) ^ 3) * inv_mul_cancel₀ ht0

/-- At two zero arguments, `R_G(0, 0, z)` reduces to `(z / 2) R_F(z, z, z)` for every `z : ℂ`. -/
theorem carlsonRG_zero_zero_eq_mul_carlsonRF (z : ℂ) :
    carlsonRG 0 0 z = z / 2 * carlsonRF z z z := by
  rw [carlsonRG_def, carlsonRF_def,
    setIntegral_congr_fun measurableSet_Ioi (fun _ ht => carlsonRGIntegrand_zero_zero_eq z ht),
    integral_const_mul]
  ring

/-- **Convergence of `R_G` with two zero arguments.** For `z ∈ slitPlane ∪ {0}`, the integrand of
`carlsonRG 0 0 z` is integrable on `(0, ∞)`. -/
theorem integrableOn_carlsonRGIntegrand_zero_zero {z : ℂ} (hz : z ∈ slitPlane ∪ {0}) :
    IntegrableOn (carlsonRGIntegrand 0 0 z) (Ioi 0) := by
  refine IntegrableOn.congr_fun ?_ (fun _ ht => (carlsonRGIntegrand_zero_zero_eq z ht).symm)
    measurableSet_Ioi
  rcases hz with hz | hz
  · exact (integrableOn_carlsonRF_integrand (Or.inl hz) hz hz).const_mul z
  · simp [Set.mem_singleton_iff.mp hz]

/-- **Full-domain convergence of `R_G`.** Unlike `R_F`, `R_D`, and `R_J`, the defining integral of
`carlsonRG x y z` converges absolutely on `(0, ∞)` for every triple `x, y, z ∈ slitPlane ∪ {0}`,
regardless of how many arguments vanish. -/
theorem integrableOn_carlsonRGIntegrand_of_mem_union {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane ∪ {0}) :
    IntegrableOn (carlsonRGIntegrand x y z) (Ioi 0) := by
  rcases hy with hy | hy
  · rcases hz with hz | hz
    · exact integrableOn_carlsonRGIntegrand hx (Or.inl hy) (Or.inl hz)
    · rw [Set.mem_singleton_iff.mp hz]
      rcases hx with hx | hx
      · rw [carlsonRGIntegrand_comm_right, carlsonRGIntegrand_comm_left]
        exact integrableOn_carlsonRGIntegrand (Or.inr rfl) (Or.inl hx) (Or.inl hy)
      · rw [Set.mem_singleton_iff.mp hx, carlsonRGIntegrand_comm_right]
        exact integrableOn_carlsonRGIntegrand_zero_zero (Or.inl hy)
  · rw [Set.mem_singleton_iff.mp hy]
    rcases hx with hx | hx
    · rcases hz with hz | hz
      · rw [carlsonRGIntegrand_comm_left]
        exact integrableOn_carlsonRGIntegrand (Or.inr rfl) (Or.inl hx) (Or.inl hz)
      · rw [Set.mem_singleton_iff.mp hz, carlsonRGIntegrand_comm_left,
          carlsonRGIntegrand_comm_right]
        exact integrableOn_carlsonRGIntegrand_zero_zero (Or.inl hx)
    · rw [Set.mem_singleton_iff.mp hx]
      exact integrableOn_carlsonRGIntegrand_zero_zero hz

/-- **Two-zero value of `R_G`** (DLMF 19.20.4): `R_G(0, 0, z) = z^(1/2) / 2` for
`z ∈ slitPlane ∪ {0}`. -/
theorem carlsonRG_zero_zero {z : ℂ} (hz : z ∈ slitPlane ∪ {0}) :
    carlsonRG 0 0 z = z ^ (1 / 2 : ℂ) / 2 := by
  rw [carlsonRG_zero_zero_eq_mul_carlsonRF]
  rcases hz with hz | hz
  · rw [carlsonRF_self hz, ← Complex.cpow_neg_half_mul_eq_cpow_half]
    ring
  · simp [Set.mem_singleton_iff.mp hz]

/-- `simp` form of `carlsonRG_zero_zero` for `z ∈ slitPlane`. -/
@[simp]
theorem carlsonRG_zero_zero_of_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) :
    carlsonRG 0 0 z = z ^ (1 / 2 : ℂ) / 2 :=
  carlsonRG_zero_zero (Or.inl hz)

/-- At the origin, `R_G(0, 0, 0) = 0`. -/
@[simp]
theorem carlsonRG_zero_zero_zero : carlsonRG 0 0 0 = 0 := by
  simp [carlsonRG_zero_zero (Or.inr rfl)]

/-! ### Reduction to `R_F` and `R_D` -/

/-- Antiderivative on `(0, ∞)` for the linear combination of the `R_G`, `R_F`, and `R_D`
integrands in `two_mul_carlsonRG_eq`. -/
private noncomputable def carlsonRGPrimitive (x y z : ℂ) (t : ℝ) : ℂ :=
  -(((x + y) * (t : ℂ) + x * y) * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ))

private theorem carlsonRGPrimitive_zero (x y z : ℂ) :
    carlsonRGPrimitive x y z 0 =
      -(x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) * z ^ (-(1 / 2) : ℂ)) := by
  rw [carlsonRGPrimitive, ← Complex.cpow_neg_half_mul_eq_cpow_half x,
    ← Complex.cpow_neg_half_mul_eq_cpow_half y]
  simp only [Complex.ofReal_zero, mul_zero, zero_add]
  ring

private theorem continuousWithinAt_carlsonRGPrimitive {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    ContinuousWithinAt (carlsonRGPrimitive x y z) (Ici 0) 0 := by
  -- Use `(t + x)^(-1/2) * (t + x) = (t + x)^(1/2)` to isolate the non-singular `(t + x)^(1/2)`
  -- term at `x = 0`, leaving `x * t * (t + x)^(-1/2)` which vanishes identically when `x = 0`.
  have hfun : carlsonRGPrimitive x y z = fun t : ℝ =>
      -((y * ((t : ℂ) + x) ^ (1 / 2 : ℂ) + x * (t : ℂ) * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)) := by
    funext t
    rw [carlsonRGPrimitive, ← Complex.cpow_neg_half_mul_eq_cpow_half ((t : ℂ) + x)]
    ring
  have hxt : ContinuousOn (fun t : ℝ => x * (t : ℂ) * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)) (Ici 0) := by
    rcases hx with hx | hx
    · exact (continuousOn_const.mul Complex.continuous_ofReal.continuousOn).mul
        (TauCeti.continuousOn_ofReal_add_cpow_Ici hx _)
    · simp [Set.mem_singleton_iff.mp hx, continuousOn_const]
  have hre : 0 < (1 / 2 : ℂ).re := by simp
  have hcont : ContinuousOn (carlsonRGPrimitive x y z) (Ici 0) := by
    rw [hfun]
    exact ((((continuousOn_const.mul (TauCeti.continuousOn_ofReal_add_cpow_Ici_of_re_pos hx
      hre)).add hxt).mul (TauCeti.continuousOn_ofReal_add_cpow_Ici hy _)).mul
      (TauCeti.continuousOn_ofReal_add_cpow_Ici hz _)).neg
  exact hcont 0 self_mem_Ici

private theorem tendsto_carlsonRGPrimitive_atTop {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    Tendsto (carlsonRGPrimitive x y z) atTop (𝓝 0) := by
  have hr : (-(1 / 2) : ℝ) ≤ 0 := by norm_num
  obtain ⟨Cx, hCx⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hx hr
  obtain ⟨Cy, hCy⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow (Or.inl hy) hr
  obtain ⟨Cz, hCz⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow (Or.inl hz) hr
  have hCx0 : 0 ≤ Cx := by simpa using (norm_nonneg _).trans (hCx 1 one_pos)
  have hCy0 : 0 ≤ Cy := by simpa using (norm_nonneg _).trans (hCy 1 one_pos)
  push_cast at hCx hCy hCz
  set M := (‖x + y‖ + ‖x * y‖) * Cx * Cy * Cz
  have h0 : Tendsto (fun t : ℝ => M * t ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul M
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlin : ‖(x + y) * (t : ℂ) + x * y‖ ≤ (‖x + y‖ + ‖x * y‖) * t := by
    calc ‖(x + y) * (t : ℂ) + x * y‖
        ≤ ‖(x + y) * (t : ℂ)‖ + ‖x * y‖ := norm_add_le _ _
      _ = ‖x + y‖ * t + ‖x * y‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
      _ ≤ (‖x + y‖ + ‖x * y‖) * t := by nlinarith [norm_nonneg (x * y)]
  have hexp : (-(1 / 2) : ℝ) + -(1 / 2) = -1 := by norm_num
  have htinv : t * (t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ)) = 1 := by
    rw [← Real.rpow_add ht0, hexp, Real.rpow_neg_one, mul_inv_cancel₀ ht0.ne']
  rw [carlsonRGPrimitive, norm_neg, norm_mul, norm_mul, norm_mul]
  calc _ ≤ (‖x + y‖ + ‖x * y‖) * t * (Cx * t ^ (-(1 / 2) : ℝ)) *
        (Cy * t ^ (-(1 / 2) : ℝ)) * (Cz * t ^ (-(1 / 2) : ℝ)) := by
        gcongr
        exacts [hCx t ht0, hCy t ht0, hCz t ht0]
    _ = M * (t * (t ^ (-(1 / 2) : ℝ) * t ^ (-(1 / 2) : ℝ))) * t ^ (-(1 / 2) : ℝ) := by ring
    _ = M * t ^ (-(1 / 2) : ℝ) := by rw [htinv, mul_one]

private theorem hasDerivAt_carlsonRGPrimitive {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    HasDerivAt (carlsonRGPrimitive x y z)
      ((1 / 2 : ℂ) * carlsonRGIntegrand x y z t -
        z / 2 * (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)) +
        (x - z) * (y - z) / 2 *
          (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
            ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z)⁻¹)) t := by
  have hmx : (t : ℂ) + x ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane_of_mem_union hx ht
  have hmy : (t : ℂ) + y ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane hy (le_of_lt ht)
  have hmz : (t : ℂ) + z ∈ slitPlane := TauCeti.ofReal_add_mem_slitPlane hz (le_of_lt ht)
  have hd {w : ℂ} (hw : (t : ℂ) + w ∈ slitPlane) :
      HasDerivAt (fun s : ℝ => ((s : ℂ) + w) ^ (-(1 / 2) : ℂ))
        (-(1 / 2 : ℂ) * (((t : ℂ) + w) ^ (-(1 / 2) : ℂ)) ^ 3) t := by
    have h := (((hasDerivAt_id (t : ℂ)).add_const w).cpow_const (c := (-(1 / 2) : ℂ))
      hw).comp_ofReal
    simp only [id] at h
    convert h using 1
    rw [← Complex.cpow_nat_mul]
    norm_num
  have hlin : HasDerivAt (fun s : ℝ => (x + y) * (s : ℂ) + x * y) (x + y) t := by
    simpa using (((hasDerivAt_id (t : ℂ)).const_mul (x + y)).add_const (x * y)).comp_ofReal
  convert ((((hlin.fun_mul (hd hmx)).fun_mul (hd hmy)).fun_mul (hd hmz)).neg) using 1
  · rfl -- Pointwise negation on functions.
  · rw [carlsonRGIntegrand_def]
    -- Write each reciprocal `(t + w)⁻¹` as `u_w ^ 2`, where `u_w = (t + w)^(-1/2)`.
    set ux : ℂ := ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)
    set uy : ℂ := ((t : ℂ) + y) ^ (-(1 / 2) : ℂ)
    set uz : ℂ := ((t : ℂ) + z) ^ (-(1 / 2) : ℂ)
    have hinv {w : ℂ} : ((t : ℂ) + w)⁻¹ = (((t : ℂ) + w) ^ (-(1 / 2) : ℂ)) ^ 2 := by
      rw [sq, Complex.cpow_neg_half_mul_self]
    have hux : ux ^ 2 * ((t : ℂ) + x) = 1 := by
      rw [← hinv, inv_mul_cancel₀ (Complex.slitPlane_ne_zero hmx)]
    have huy : uy ^ 2 * ((t : ℂ) + y) = 1 := by
      rw [← hinv, inv_mul_cancel₀ (Complex.slitPlane_ne_zero hmy)]
    have huz : uz ^ 2 * ((t : ℂ) + z) = 1 := by
      rw [← hinv, inv_mul_cancel₀ (Complex.slitPlane_ne_zero hmz)]
    rw [div_eq_mul_inv x, div_eq_mul_inv y, div_eq_mul_inv z, hinv, hinv, hinv]
    linear_combination
      -(1 / 2 * y * ux * uy * uz) * hux -
      (1 / 2 * x * ux * uy * uz) * huy -
      (1 / 2 * (x + y - z) * ux * uy * uz) * huz

/-- **Reduction of `R_G` to `R_F` and `R_D`** (DLMF 19.21.10): for `x ∈ slitPlane ∪ {0}` and
`y, z ∈ slitPlane`,
`2 R_G(x, y, z) = z R_F(x, y, z) - ((x - z)(y - z) / 3) R_D(x, y, z) + x^(1/2) y^(1/2) z^(-1/2)`.
By symmetry of `R_G`, `R_F`, and `R_D` in `(x, y)`, either of `x` and `y` may vanish, while `z`
must lie in `slitPlane`. -/
theorem two_mul_carlsonRG_eq {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    2 * carlsonRG x y z =
      z * carlsonRF x y z - (x - z) * (y - z) / 3 * carlsonRD x y z +
        x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) * z ^ (-(1 / 2) : ℂ) := by
  have hRG := (integrableOn_carlsonRGIntegrand hx (Or.inl hy) (Or.inl hz)).const_mul (1 / 2 : ℂ)
  have hRF := (integrableOn_carlsonRF_integrand hx hy hz).const_mul (z / 2)
  have hRJ := (integrableOn_carlsonRJ_integrand hx hy hz hz).const_mul ((x - z) * (y - z) / 2)
  have hsub : IntegrableOn (fun t : ℝ => (1 / 2 : ℂ) * carlsonRGIntegrand x y z t -
      z / 2 * (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ))) (Ioi 0) := hRG.sub hRF
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuousWithinAt_carlsonRGPrimitive hx hy hz)
    (fun _ ht => hasDerivAt_carlsonRGPrimitive hx hy hz ht)
    (hsub.add hRJ)
    (tendsto_carlsonRGPrimitive_atTop hx hy hz)
  rw [integral_add hsub hRJ, integral_sub hRG hRF, integral_const_mul,
    integral_const_mul, integral_const_mul, carlsonRGPrimitive_zero, sub_neg_eq_add, zero_add]
    at hftc
  rw [carlsonRG_def, carlsonRF_def, carlsonRD_def, carlsonRJ_def]
  linear_combination hftc

/-! ### Real arguments -/

/-- **`R_G` is positive at real arguments**: for real `x, y ≥ 0` and `z > 0`, `R_G(x, y, z)` is a
positive real number (in the order `ComplexOrder`, so its imaginary part is `0`). By symmetry,
up to two of the three arguments may vanish. -/
theorem carlsonRG_pos {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) :
    0 < carlsonRG x y z := by
  set f : ℝ → ℝ := fun t => (t + x) ^ (-(1 / 2) : ℝ) * (t + y) ^ (-(1 / 2) : ℝ) *
    (t + z) ^ (-(1 / 2) : ℝ) * (x / (t + x) + y / (t + y) + z / (t + z)) * t with hf
  have heq : EqOn (carlsonRGIntegrand x y z) (fun t => ((f t : ℝ) : ℂ)) (Ioi 0) :=
    fun t ht => by
      have ht : (0 : ℝ) < t := ht
      simp only [carlsonRGIntegrand, hf, Complex.ofReal_mul, Complex.ofReal_div,
        Complex.ofReal_add, Complex.ofReal_cpow (by positivity : 0 ≤ t + x),
        Complex.ofReal_cpow (by positivity : 0 ≤ t + y),
        Complex.ofReal_cpow (by positivity : 0 ≤ t + z)]
      -- After `push_cast` the two sides differ only in how the exponent `-(1 / 2)` is cast.
      push_cast
      ring
  have hint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_carlsonRGIntegrand (TauCeti.ofReal_mem_slitPlane_union_zero hx)
      (TauCeti.ofReal_mem_slitPlane_union_zero hy)
      (Or.inl (ofReal_mem_slitPlane.mpr hz))).congr_fun heq measurableSet_Ioi
    simpa using h.re
  have hpos (t : ℝ) (ht : t ∈ Ioi 0) : 0 < f t := by
    have : (0 : ℝ) < t := ht
    simp only [hf]
    positivity
  have hI : 0 < ∫ t in Ioi (0 : ℝ), f t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => (hpos t ht).le)) hint]
    refine lt_of_lt_of_le ?_ (measure_mono fun t ht => ⟨(hpos t ht).ne', ht⟩ :
      volume (Ioi (0 : ℝ)) ≤ volume (Function.support f ∩ Ioi 0))
    simp
  rw [carlsonRG_def, setIntegral_congr_fun measurableSet_Ioi heq, integral_complex_ofReal]
  exact mul_pos (by norm_num) (Complex.zero_lt_real.mpr hI)

end Complex
