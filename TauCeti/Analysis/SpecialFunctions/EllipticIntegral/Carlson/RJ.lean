/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Carlson's symmetric elliptic integrals of the third kind and `R_D`

This file defines Carlson's symmetric elliptic integral of the third kind (DLMF 19.16.2)

`R_J(x, y, z, p) = (3/2) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2) (t + p)⁻¹ dt`

for complex `x, y, z, p`, with the principal branch of each factor `(t + x) ^ (-1/2 : ℂ)`, together
with its degenerate case `R_D(x, y, z) = R_J(x, y, z, z)` (DLMF 19.16.5), a symmetric integral of
the second kind. In Carlson's normal form of Legendre's integrals, `R_D` carries the incomplete
integral of the second kind and `R_J` the incomplete integral of the third kind.

The integral defining `R_J` converges absolutely when `x, y, z` lie in `Complex.slitPlane ∪ {0}`,
at most one of them is `0`, and `p ∈ Complex.slitPlane`. Since `R_J` is symmetric in its first
three arguments, the convergence theorem `TauCeti.Complex.integrableOn_carlsonRJ_integrand` is
stated with the possibly vanishing argument in the first position. Outside this domain `carlsonRJ`
is a totalized value of a divergent integral and carries no meaning.

## Main results

* `TauCeti.Complex.carlsonRJ`, `TauCeti.Complex.carlsonRD` — the integrals `R_J` and `R_D`.
* `TauCeti.Complex.integrableOn_carlsonRJ_integrand` — absolute convergence of the defining
  integral.
* `TauCeti.Complex.carlsonRJ_comm_left`, `TauCeti.Complex.carlsonRJ_comm_right` — `R_J` is
  symmetric in its first three arguments; `TauCeti.Complex.carlsonRD_comm` — `R_D` is symmetric
  in its first two.
* `TauCeti.Complex.carlsonRD_eq_integral` — the defining integral of `R_D`,
  `(3/2) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2) dt` (DLMF 19.16.5).
* `TauCeti.Complex.carlsonRJ_ofReal_mul`, `TauCeti.Complex.carlsonRD_ofReal_mul` — homogeneity of
  degree `-3/2` under positive real scaling.
* `TauCeti.Complex.carlsonRJ_self`, `TauCeti.Complex.carlsonRD_self` — the diagonal values
  `R_J(x, x, x, x) = R_D(x, x, x) = x^(-3/2)`.
* `TauCeti.Complex.carlsonRJ_pos`, `TauCeti.Complex.carlsonRD_pos` — `R_J` and `R_D` are positive
  real numbers at nonnegative real arguments, at most one of the symmetric ones zero.

## References

* NIST *Digital Library of Mathematical Functions*, §19.16, <https://dlmf.nist.gov/19.16>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
* B. C. Carlson, Numerical computation of real or complex elliptic integrals, *Numer. Algorithms*
  10 (1995), 13–26.

B. Braams' `lean-codes` (<https://github.com/bjbraams/lean-codes>) formalizes Carlson's book,
including `R_J` and `R_D`, on top of Carlson's general `R`-function, a Dirichlet average over a
simplex. This file instead works directly from the integral definition above and is not ported
from it.
-/

public section

open MeasureTheory Set Filter Topology
open Complex (slitPlane mem_slitPlane_iff ofReal_mem_slitPlane)
open scoped ComplexOrder

namespace TauCeti.Complex

/-- **Carlson's symmetric elliptic integral of the third kind** (DLMF 19.16.2):
`R_J(x, y, z, p) = (3/2) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2) (t + p)⁻¹ dt`, with
principal complex powers of each factor.

The integral converges when `x, y, z ∈ slitPlane ∪ {0}` with at most one of them `0` and
`p ∈ slitPlane` (`integrableOn_carlsonRJ_integrand`); elsewhere the value is a totalized junk
value. -/
noncomputable def carlsonRJ (x y z p : ℂ) : ℂ :=
  (3 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
    ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹

/-- **Carlson's symmetric elliptic integral of the second kind** `R_D(x, y, z) = R_J(x, y, z, z)`
(DLMF 19.16.5). Its integral form
`(3/2) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2) dt` is `carlsonRD_eq_integral`. -/
noncomputable def carlsonRD (x y z : ℂ) : ℂ :=
  carlsonRJ x y z z

/-- The defining integral of `carlsonRJ`. -/
theorem carlsonRJ_def (x y z p : ℂ) :
    carlsonRJ x y z p = (3 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹ :=
  (rfl)

/-- `carlsonRD` is the degenerate case `R_D(x, y, z) = R_J(x, y, z, z)` of `carlsonRJ`. -/
theorem carlsonRD_def (x y z : ℂ) : carlsonRD x y z = carlsonRJ x y z z :=
  (rfl)

/-! ### Bounds on the factors of the integrand -/

/-- The norm of the principal power `w ^ (-1/2)` is `‖w‖ ^ (-1/2)`. -/
private theorem norm_cpow_neg_half (w : ℂ) : ‖w ^ (-(1 / 2) : ℂ)‖ = ‖w‖ ^ (-(1 / 2) : ℝ) := by
  simpa using Complex.norm_cpow_real w (-(1 / 2))

/-- Adding a nonnegative real number keeps a point of the slit plane in the slit plane. -/
private theorem ofReal_add_mem_slitPlane_of_nonneg {x : ℂ} (hx : x ∈ slitPlane) {t : ℝ}
    (ht : 0 ≤ t) : (t : ℂ) + x ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hx ⊢
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_add]
  exact hx.imp (fun h => by linarith) id

/-- Adding a positive real number moves a point of `slitPlane ∪ {0}` into the slit plane. -/
private theorem ofReal_add_mem_slitPlane_of_mem_union {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) {t : ℝ}
    (ht : 0 < t) : (t : ℂ) + x ∈ slitPlane := by
  rcases hx with hx | hx
  · exact ofReal_add_mem_slitPlane_of_nonneg hx ht.le
  · rw [mem_singleton_iff.mp hx, add_zero]
    exact ofReal_mem_slitPlane.mpr ht

/-- For `x ∈ slitPlane ∪ {0}`, the factor `(t + x)^(-1/2)` is `O(t^(-1/2))` for `t > 0`. -/
private theorem exists_norm_cpow_le_rpow {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) :
    ∃ C, 0 < C ∧ ∀ t : ℝ, 0 < t → ‖((t : ℂ) + x) ^ (-(1 / 2) : ℂ)‖ ≤ C * t ^ (-(1 / 2) : ℝ) := by
  rcases hx with hx | hx
  · obtain ⟨c, hc, h⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hx
    refine ⟨c ^ (-(1 / 2) : ℝ), by positivity, fun t ht => ?_⟩
    have h1 : c * t ≤ ‖(t : ℂ) + x‖ := by
      have : c * (1 + t) ≤ ‖x + (t : ℂ)‖ := h x (Metric.mem_ball_self hc) ⟨t, ht.le⟩
      rw [add_comm]
      nlinarith
    rw [norm_cpow_neg_half, ← Real.mul_rpow hc.le ht.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  · refine ⟨1, one_pos, fun t ht => ?_⟩
    rw [mem_singleton_iff.mp hx, add_zero, norm_cpow_neg_half, Complex.norm_real,
      Real.norm_of_nonneg ht.le, one_mul]

/-- For `y ∈ slitPlane`, the factor `(t + y)^(-1/2)` is bounded for `t ≥ 0`. -/
private theorem exists_norm_cpow_le {y : ℂ} (hy : y ∈ slitPlane) :
    ∃ C, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ‖((t : ℂ) + y) ^ (-(1 / 2) : ℂ)‖ ≤ C := by
  obtain ⟨c, hc, h⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hy
  refine ⟨c ^ (-(1 / 2) : ℝ), by positivity, fun t ht => ?_⟩
  have h1 : c ≤ ‖(t : ℂ) + y‖ := by
    have : c * (1 + t) ≤ ‖y + (t : ℂ)‖ := h y (Metric.mem_ball_self hc) ⟨t, ht⟩
    rw [add_comm]
    nlinarith
  rw [norm_cpow_neg_half]
  exact Real.rpow_le_rpow_of_nonpos hc h1 (by norm_num)

/-- For `p ∈ slitPlane`, the factor `(t + p)⁻¹` is `O((1 + t)⁻¹)` for `t ≥ 0`. -/
private theorem exists_norm_inv_le {p : ℂ} (hp : p ∈ slitPlane) :
    ∃ C, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ‖((t : ℂ) + p)⁻¹‖ ≤ C * (1 + t)⁻¹ := by
  obtain ⟨c, hc, h⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hp
  refine ⟨c⁻¹, inv_pos.mpr hc, fun t ht => ?_⟩
  have h1 : c * (1 + t) ≤ ‖(t : ℂ) + p‖ := by
    rw [add_comm (t : ℂ)]
    exact h p (Metric.mem_ball_self hc) ⟨t, ht⟩
  rw [norm_inv, ← mul_inv]
  exact inv_anti₀ (by positivity) h1

/-- For `x ∈ slitPlane ∪ {0}`, the factor `(t + x)^(-1/2)` is continuous for `t > 0`. -/
private theorem continuousOn_cpow {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ)) (Ioi 0) := fun _ ht =>
  ((Complex.continuous_ofReal.add continuous_const).continuousAt.cpow continuousAt_const
    (ofReal_add_mem_slitPlane_of_mem_union hx ht)).continuousWithinAt

/-- For `p ∈ slitPlane`, the factor `(t + p)⁻¹` is continuous for `t > 0`. -/
private theorem continuousOn_inv {p : ℂ} (hp : p ∈ slitPlane) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) + p)⁻¹) (Ioi 0) := fun _ ht =>
  ((Complex.continuous_ofReal.add continuous_const).continuousAt.inv₀
    (Complex.slitPlane_ne_zero (ofReal_add_mem_slitPlane_of_nonneg hp (le_of_lt ht)))
    ).continuousWithinAt

/-- The comparison function `t^(-1/2) (1 + t)⁻¹` is integrable on `(0, ∞)`: it is `O(t^(-1/2))`
near `0` and `O(t^(-3/2))` near `∞`. -/
private theorem integrableOn_rpow_neg_half_mul_one_add_inv :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2) : ℝ) * (1 + t)⁻¹) (Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(1 / 2) : ℝ) * (1 + t)⁻¹) (Ioi 0) := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    have h1 : ContinuousAt (fun t : ℝ => 1 + t) t := continuousAt_const.add continuousAt_id
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl ht.ne')).mul
      (h1.inv₀ (by linarith))).continuousWithinAt
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (r := -(1 / 2)) (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    refine h.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    rw [Real.norm_of_nonneg (by positivity)]
    calc t ^ (-(1 / 2) : ℝ) * (1 + t)⁻¹ ≤ t ^ (-(1 / 2) : ℝ) * 1 := by
          gcongr
          exact inv_le_one_of_one_le₀ (by linarith)
      _ = t ^ (-(1 / 2) : ℝ) := mul_one _
  · refine (integrableOn_Ioi_rpow_of_lt (a := -(3 / 2)) (by norm_num) one_pos).mono'
      ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := one_pos.trans ht
    rw [Real.norm_of_nonneg (by positivity)]
    calc t ^ (-(1 / 2) : ℝ) * (1 + t)⁻¹ ≤ t ^ (-(1 / 2) : ℝ) * t ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one]
          gcongr
          linarith
      _ = t ^ (-(3 / 2) : ℝ) := by
          rw [← Real.rpow_add ht0]
          norm_num

/-! ### Convergence -/

/-- **Convergence of `R_J`.** The integrand of `carlsonRJ x y z p` is integrable on `(0, ∞)` when
`x ∈ slitPlane ∪ {0}` and `y, z, p ∈ slitPlane`. By symmetry of the integrand in `x, y, z` this
covers every argument triple in `slitPlane ∪ {0}` with at most one zero entry. -/
theorem integrableOn_carlsonRJ_integrand {x y z p : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) (Ioi 0) := by
  -- The first factor is `O(t^(-1/2))`, the next two are bounded and the last is `O((1 + t)⁻¹)`.
  obtain ⟨Cx, hCx0, hCx⟩ := exists_norm_cpow_le_rpow hx
  obtain ⟨Cy, hCy0, hCy⟩ := exists_norm_cpow_le hy
  obtain ⟨Cz, hCz0, hCz⟩ := exists_norm_cpow_le hz
  obtain ⟨Cp, hCp0, hCp⟩ := exists_norm_inv_le hp
  have hcont := (((continuousOn_cpow hx).mul (continuousOn_cpow (Or.inl hy))).mul
    (continuousOn_cpow (Or.inl hz))).mul (continuousOn_inv hp)
  refine (integrableOn_rpow_neg_half_mul_one_add_inv.const_mul (Cx * Cy * Cz * Cp)).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht : (0 : ℝ) < t := ht
  rw [norm_mul, norm_mul, norm_mul]
  calc _ ≤ Cx * t ^ (-(1 / 2) : ℝ) * Cy * Cz * (Cp * (1 + t)⁻¹) := by
        gcongr
        exacts [hCx t ht, hCy t ht.le, hCz t ht.le, hCp t ht.le]
    _ = _ := by ring

/-! ### Symmetry -/

/-- `R_J` is symmetric in its first two arguments. -/
theorem carlsonRJ_comm_left (x y z p : ℂ) : carlsonRJ x y z p = carlsonRJ y x z p := by
  simp only [carlsonRJ_def]
  congr 2
  funext t
  ring

/-- `R_J` is symmetric in its second and third arguments. Together with `carlsonRJ_comm_left`,
`R_J` is symmetric in its first three arguments. -/
theorem carlsonRJ_comm_right (x y z p : ℂ) : carlsonRJ x y z p = carlsonRJ x z y p := by
  simp only [carlsonRJ_def]
  congr 2
  funext t
  ring

/-- `R_D` is symmetric in its first two arguments. -/
theorem carlsonRD_comm (x y z : ℂ) : carlsonRD x y z = carlsonRD y x z :=
  carlsonRJ_comm_left x y z z

/-- The product of `w ^ (-1/2)` and `w⁻¹` is `w ^ (-3/2)`, including at `w = 0`. -/
private theorem cpow_neg_half_mul_inv (w : ℂ) : w ^ (-(1 / 2) : ℂ) * w⁻¹ = w ^ (-(3 / 2) : ℂ) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hw]
    norm_num

/-- **The integral form of `R_D`** (DLMF 19.16.5):
`R_D(x, y, z) = (3/2) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2) dt`. -/
theorem carlsonRD_eq_integral (x y z : ℂ) :
    carlsonRD x y z = (3 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) := by
  rw [carlsonRD_def, carlsonRJ_def]
  congr 2
  funext t
  rw [mul_assoc _ (((t : ℂ) + z) ^ (-(1 / 2) : ℂ)), cpow_neg_half_mul_inv]

/-! ### Homogeneity -/

/-- **Homogeneity of `R_J`.** For real `l > 0`,
`R_J(l x, l y, l z, l p) = l^(-3/2) R_J(x, y, z, p)`. No hypothesis on `x, y, z, p` is needed: the
substitution `t = l s` identifies the two integrals whether or not they converge. -/
theorem carlsonRJ_ofReal_mul {l : ℝ} (hl : 0 < l) (x y z p : ℂ) :
    carlsonRJ (l * x) (l * y) (l * z) (l * p) = (l : ℂ) ^ (-(3 / 2) : ℂ) * carlsonRJ x y z p := by
  have hl0 : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
  have hscale (s : ℝ) (w : ℂ) : (((l * s : ℝ) : ℂ) + l * w) ^ (-(1 / 2) : ℂ) =
      (l : ℂ) ^ (-(1 / 2) : ℂ) * ((s : ℂ) + w) ^ (-(1 / 2) : ℂ) := by
    rw [Complex.ofReal_mul, ← mul_add, TauCeti.ofReal_mul_cpow hl.le]
  have hscale_inv (s : ℝ) (w : ℂ) :
      (((l * s : ℝ) : ℂ) + l * w)⁻¹ = (l : ℂ)⁻¹ * ((s : ℂ) + w)⁻¹ := by
    rw [Complex.ofReal_mul, ← mul_add, mul_inv]
  have hl3 : ((l : ℂ) ^ (-(1 / 2) : ℂ)) ^ 3 = (l : ℂ) ^ (-(3 / 2) : ℂ) := by
    rw [← Complex.cpow_nat_mul]
    norm_num
  have h := integral_comp_mul_left_Ioi' (fun t : ℝ => ((t : ℂ) + l * x) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + l * y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + l * z) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + l * p)⁻¹) 0 hl
  rw [mul_zero] at h
  have hfun : (fun s : ℝ => (((l * s : ℝ) : ℂ) + l * x) ^ (-(1 / 2) : ℂ) *
      (((l * s : ℝ) : ℂ) + l * y) ^ (-(1 / 2) : ℂ) * (((l * s : ℝ) : ℂ) + l * z) ^ (-(1 / 2) : ℂ) *
        (((l * s : ℝ) : ℂ) + l * p)⁻¹) =
      fun s : ℝ => (l : ℂ) ^ (-(3 / 2) : ℂ) * (l : ℂ)⁻¹ * (((s : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((s : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((s : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((s : ℂ) + p)⁻¹) := by
    funext s
    rw [hscale, hscale, hscale, hscale_inv, ← hl3]
    ring
  rw [carlsonRJ_def, carlsonRJ_def, ← h, hfun, integral_const_mul, Complex.real_smul]
  field_simp

/-- **Homogeneity of `R_D`.** For real `l > 0`, `R_D(l x, l y, l z) = l^(-3/2) R_D(x, y, z)`. -/
theorem carlsonRD_ofReal_mul {l : ℝ} (hl : 0 < l) (x y z : ℂ) :
    carlsonRD (l * x) (l * y) (l * z) = (l : ℂ) ^ (-(3 / 2) : ℂ) * carlsonRD x y z :=
  carlsonRJ_ofReal_mul hl x y z z

/-! ### Diagonal values -/

/-- **The diagonal value of `R_J`**: `R_J(x, x, x, x) = x^(-3/2)` for `x` in the slit plane. -/
theorem carlsonRJ_self {x : ℂ} (hx : x ∈ slitPlane) : carlsonRJ x x x x = x ^ (-(3 / 2) : ℂ) := by
  have hmem (t : ℝ) (ht : 0 ≤ t) : (t : ℂ) + x ∈ slitPlane :=
    ofReal_add_mem_slitPlane_of_nonneg hx ht
  -- `-(2/3) (t + x)^(-3/2)` is an antiderivative of `(t + x)^(-5/2)` on `[0, ∞)`.
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -(2 / 3) * ((t : ℂ) + x) ^ (-(3 / 2) : ℂ))
        (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + x)⁻¹) t := by
    intro t ht
    have h := ((((hasDerivAt_id (t : ℂ)).add_const x).cpow_const (c := (-(3 / 2) : ℂ))
      (hmem t ht)).comp_ofReal).const_mul (-(2 / 3) : ℂ)
    simp only [id] at h
    convert h using 1
    have hne := Complex.slitPlane_ne_zero (hmem t ht)
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hne, ← Complex.cpow_add _ _ hne,
      ← Complex.cpow_add _ _ hne,
      show (-(1 / 2) : ℂ) + -(1 / 2) + -(1 / 2) + -1 = -(3 / 2) - 1 by norm_num]
    ring
  have hlim : Tendsto (fun t : ℝ => -(2 / 3) * ((t : ℂ) + x) ^ (-(3 / 2) : ℂ)) atTop (𝓝 0) := by
    obtain ⟨c, hc, h⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hx
    have hnorm : Tendsto (fun t : ℝ => ‖(t : ℂ) + x‖) atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_
        ((tendsto_atTop_add_const_left atTop 1 tendsto_id).const_mul_atTop hc)
      filter_upwards [eventually_ge_atTop 0] with t ht
      rw [add_comm (t : ℂ)]
      exact h x (Metric.mem_ball_self hc) ⟨t, ht⟩
    have h0 : Tendsto (fun t : ℝ => ‖((t : ℂ) + x) ^ (-(3 / 2) : ℂ)‖) atTop (𝓝 0) := by
      have hcpow (w : ℂ) : ‖w ^ (-(3 / 2) : ℂ)‖ = ‖w‖ ^ (-(3 / 2) : ℝ) := by
        simpa using Complex.norm_cpow_real w (-(3 / 2))
      simp only [hcpow]
      exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp hnorm
    rw [show (0 : ℂ) = -(2 / 3) * 0 by simp]
    exact (tendsto_zero_iff_norm_tendsto_zero.mpr h0).const_mul _
  rw [carlsonRJ_def, integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_carlsonRJ_integrand (Or.inl hx) hx hx hx) hlim]
  simp only [Complex.ofReal_zero, zero_add]
  ring

/-- **The diagonal value of `R_D`**: `R_D(x, x, x) = x^(-3/2)` for `x` in the slit plane. -/
theorem carlsonRD_self {x : ℂ} (hx : x ∈ slitPlane) : carlsonRD x x x = x ^ (-(3 / 2) : ℂ) :=
  carlsonRJ_self hx

/-! ### Real arguments -/

/-- A nonnegative real number lies in `slitPlane ∪ {0}`. -/
private theorem ofReal_mem_slitPlane_union_zero {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) ∈ slitPlane ∪ {0} := by
  rcases hx.eq_or_lt with h | h
  · exact Or.inr (by simp [← h])
  · exact Or.inl (ofReal_mem_slitPlane.mpr h)

/-- At a positive real base, the principal power `(t + w) ^ (-1/2)` is the real one. -/
private theorem ofReal_add_cpow_neg_half {w t : ℝ} (hw : 0 ≤ w) (ht : 0 < t) :
    ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) = (((t + w) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (by linarith)]
  push_cast
  rfl

/-- **`R_J` is positive at real arguments**: for real `x ≥ 0` and `y, z, p > 0`, `R_J(x, y, z, p)`
is a positive real number (in the order `ComplexOrder`, so its imaginary part is `0`). By symmetry,
any one of the first three arguments may be the one that vanishes. -/
theorem carlsonRJ_pos {x y z p : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    0 < carlsonRJ x y z p := by
  set f : ℝ → ℝ := fun t => (t + x) ^ (-(1 / 2) : ℝ) * (t + y) ^ (-(1 / 2) : ℝ) *
    (t + z) ^ (-(1 / 2) : ℝ) * (t + p)⁻¹ with hf
  have heq : EqOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) (fun t => ((f t : ℝ) : ℂ)) (Ioi 0) :=
    fun t ht => by
      simp only [hf, ofReal_add_cpow_neg_half hx ht, ofReal_add_cpow_neg_half hy.le ht,
        ofReal_add_cpow_neg_half hz.le ht, Complex.ofReal_mul, Complex.ofReal_inv,
        Complex.ofReal_add]
  have hint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_carlsonRJ_integrand (ofReal_mem_slitPlane_union_zero hx)
      (ofReal_mem_slitPlane.mpr hy) (ofReal_mem_slitPlane.mpr hz)
      (ofReal_mem_slitPlane.mpr hp)).congr_fun heq measurableSet_Ioi
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
  rw [carlsonRJ_def, setIntegral_congr_fun measurableSet_Ioi heq, integral_complex_ofReal,
    show (3 / 2 : ℂ) * ((∫ t in Ioi (0 : ℝ), f t : ℝ) : ℂ) =
      ((3 / 2 * ∫ t in Ioi (0 : ℝ), f t : ℝ) : ℂ) by push_cast; ring]
  exact Complex.zero_lt_real.mpr (by positivity)

/-- **`R_D` is positive at real arguments**: for real `x ≥ 0` and `y, z > 0`, `R_D(x, y, z)` is a
positive real number (in the order `ComplexOrder`). By symmetry, either of the first two arguments
may be the one that vanishes. -/
theorem carlsonRD_pos {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    0 < carlsonRD x y z :=
  carlsonRJ_pos hx hy hz hz

end TauCeti.Complex
