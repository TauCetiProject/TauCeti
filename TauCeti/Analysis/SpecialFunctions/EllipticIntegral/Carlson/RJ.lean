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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Beta
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
three arguments, the convergence theorem `Complex.integrableOn_carlsonRJ_integrand` is stated with
the possibly vanishing argument in the first position. This is the domain on which the API below
is supported; wherever the integrand fails to be integrable, the Bochner integral is totalized to
`0`, and so is `carlsonRJ`.

## Main results

* `Complex.carlsonRJ`, `Complex.carlsonRD` — the integrals `R_J` and `R_D`.
* `Complex.integrableOn_carlsonRJ_integrand` — absolute convergence of the defining
  integral.
* `Complex.carlsonRJ_comm_left`, `Complex.carlsonRJ_comm_right` — `R_J` is
  symmetric in its first three arguments; `Complex.carlsonRD_comm` — `R_D` is symmetric
  in its first two.
* `Complex.carlsonRD_eq_integral` — the defining integral of `R_D`,
  `(3/2) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2) dt` (DLMF 19.16.5).
* `Complex.carlsonRJ_ofReal_mul`, `Complex.carlsonRD_ofReal_mul` — homogeneity of
  degree `-3/2` under positive real scaling.
* `Complex.carlsonRJ_self`, `Complex.carlsonRD_self` — the diagonal values
  `R_J(x, x, x, x) = R_D(x, x, x) = x^(-3/2)`.
* `Complex.carlsonRJ_pos`, `Complex.carlsonRD_pos` — `R_J` and `R_D` are positive
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
open scoped ComplexOrder

namespace Complex

/-- **Carlson's symmetric elliptic integral of the third kind** (DLMF 19.16.2):
`R_J(x, y, z, p) = (3/2) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-1/2) (t + p)⁻¹ dt`, with
principal complex powers of each factor.

The integral converges when `x, y, z ∈ slitPlane ∪ {0}` with at most one of them `0` and
`p ∈ slitPlane` (`integrableOn_carlsonRJ_integrand`). This is the supported domain; where the
integrand is not integrable, the value is the totalized Bochner integral `0`. -/
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

/-! ### Convergence -/

/-- **Convergence of `R_J`.** The integrand of `carlsonRJ x y z p` is integrable on `(0, ∞)` when
`x ∈ slitPlane ∪ {0}` and `y, z, p ∈ slitPlane`. By symmetry of the integrand in `x, y, z` this
covers every argument triple in `slitPlane ∪ {0}` with at most one zero entry. -/
theorem integrableOn_carlsonRJ_integrand {x y z p : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) (hp : p ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) (Ioi 0) := by
  -- The first factor is `O(t^(-1/2))`, the next two are bounded and the last is `O((1 + t)⁻¹)`.
  obtain ⟨Cx, hCx⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hx (r := -(1 / 2))
    (by norm_num)
  obtain ⟨Cy, hCy⟩ := TauCeti.exists_norm_ofReal_add_cpow_le hy (r := -(1 / 2)) (by norm_num)
  obtain ⟨Cz, hCz⟩ := TauCeti.exists_norm_ofReal_add_cpow_le hz (r := -(1 / 2)) (by norm_num)
  obtain ⟨Cp, hCp0, hCp⟩ := TauCeti.exists_norm_inv_ofReal_add_le hp
  push_cast at hCx hCy hCz
  have hcpow {w : ℂ} (hw : w ∈ slitPlane ∪ {0}) :
      ContinuousOn (fun t : ℝ => ((t : ℂ) + w) ^ (-(1 / 2) : ℂ)) (Ioi 0) := fun _ ht =>
    ((continuous_ofReal.add continuous_const).continuousAt.cpow continuousAt_const
      (TauCeti.ofReal_add_mem_slitPlane_of_mem_union hw ht)).continuousWithinAt
  have hinv : ContinuousOn (fun t : ℝ => ((t : ℂ) + p)⁻¹) (Ioi 0) := fun _ ht =>
    ((continuous_ofReal.add continuous_const).continuousAt.inv₀
      (slitPlane_ne_zero (TauCeti.ofReal_add_mem_slitPlane hp (le_of_lt ht)))
      ).continuousWithinAt
  have hcont := (((hcpow hx).mul (hcpow (Or.inl hy))).mul (hcpow (Or.inl hz))).mul hinv
  -- The majorant `t^(-1/2) (1 + t)⁻¹` is Euler's second beta integrand with `a = b = 1/2`.
  have hmaj : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2) : ℝ) * (1 + t)⁻¹) (Ioi 0) := by
    have h := TauCeti.integrableOn_rpow_mul_one_add_rpow (a := 1 / 2) (b := 1 / 2)
      (by norm_num) (by norm_num)
    norm_num [Real.rpow_neg_one] at h
    exact h
  refine (hmaj.const_mul (Cx * Cy * Cz * Cp)).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht : (0 : ℝ) < t := ht
  have h1 := hCx t ht
  have h2 := hCy t ht.le
  have h3 := hCz t ht.le
  have h12 := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have h123 := mul_le_mul h12 h3 (norm_nonneg _) ((by positivity : (0 : ℝ) ≤ _).trans h12)
  rw [norm_mul, norm_mul, norm_mul]
  calc _ ≤ Cx * t ^ (-(1 / 2) : ℝ) * Cy * Cz * (Cp * (1 + t)⁻¹) :=
        mul_le_mul h123 (hCp t ht.le) (norm_nonneg _) ((by positivity : (0 : ℝ) ≤ _).trans h123)
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

/-- **The integral form of `R_D`** (DLMF 19.16.5):
`R_D(x, y, z) = (3/2) ∫₀^∞ (t + x)^(-1/2) (t + y)^(-1/2) (t + z)^(-3/2) dt`. -/
theorem carlsonRD_eq_integral (x y z : ℂ) :
    carlsonRD x y z = (3 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
      ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + z) ^ (-(3 / 2) : ℂ) := by
  rw [carlsonRD_def, carlsonRJ_def]
  congr 2
  funext t
  rw [mul_assoc _ (((t : ℂ) + z) ^ (-(1 / 2) : ℂ)), TauCeti.cpow_mul_inv (by norm_num)]
  norm_num

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
@[simp]
theorem carlsonRJ_self {x : ℂ} (hx : x ∈ slitPlane) : carlsonRJ x x x x = x ^ (-(3 / 2) : ℂ) := by
  have hmem (t : ℝ) (ht : 0 ≤ t) : (t : ℂ) + x ∈ slitPlane :=
    TauCeti.ofReal_add_mem_slitPlane hx ht
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
      ← Complex.cpow_add _ _ hne]
    norm_num
    ring
  have hlim : Tendsto (fun t : ℝ => -(2 / 3) * ((t : ℂ) + x) ^ (-(3 / 2) : ℂ)) atTop (𝓝 0) := by
    obtain ⟨c, hc, h⟩ := TauCeti.exists_pos_forall_mem_ball_mul_one_add_le_norm_add hx
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
    simpa only [mul_zero] using (tendsto_zero_iff_norm_tendsto_zero.mpr h0).const_mul (-(2 / 3) : ℂ)
  rw [carlsonRJ_def, integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_carlsonRJ_integrand (Or.inl hx) hx hx hx) hlim]
  simp only [Complex.ofReal_zero, zero_add]
  ring

/-- **The diagonal value of `R_D`**: `R_D(x, x, x) = x^(-3/2)` for `x` in the slit plane. -/
@[simp]
theorem carlsonRD_self {x : ℂ} (hx : x ∈ slitPlane) : carlsonRD x x x = x ^ (-(3 / 2) : ℂ) :=
  carlsonRJ_self hx

/-! ### Real arguments -/

/-- **`R_J` is positive at real arguments**: for real `x ≥ 0` and `y, z, p > 0`, `R_J(x, y, z, p)`
is a positive real number (in the order `ComplexOrder`, so its imaginary part is `0`). By symmetry,
any one of the first three arguments may be the one that vanishes. -/
theorem carlsonRJ_pos {x y z p : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) (hp : 0 < p) :
    0 < carlsonRJ x y z p := by
  set f : ℝ → ℝ := fun t => (t + x) ^ (-(1 / 2) : ℝ) * (t + y) ^ (-(1 / 2) : ℝ) *
    (t + z) ^ (-(1 / 2) : ℝ) * (t + p)⁻¹ with hf
  -- At a positive real base, the principal power `(t + w) ^ (-1/2)` is the real one.
  have hcpow {w t : ℝ} (hw : 0 ≤ w) (ht : 0 < t) :
      ((t : ℂ) + w) ^ (-(1 / 2) : ℂ) = (((t + w) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by linarith)]
    push_cast
    rfl
  have heq : EqOn (fun t : ℝ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + z) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + p)⁻¹) (fun t => ((f t : ℝ) : ℂ)) (Ioi 0) :=
    fun t ht => by
      simp only [hf, hcpow hx ht, hcpow hy.le ht, hcpow hz.le ht, Complex.ofReal_mul,
        Complex.ofReal_inv, Complex.ofReal_add]
  have hint : IntegrableOn f (Ioi 0) := by
    have h := (integrableOn_carlsonRJ_integrand (TauCeti.ofReal_mem_slitPlane_union_zero hx)
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
  rw [carlsonRJ_def, setIntegral_congr_fun measurableSet_Ioi heq, integral_complex_ofReal]
  norm_num [Complex.pos_iff, hI]

/-- **`R_D` is positive at real arguments**: for real `x ≥ 0` and `y, z > 0`, `R_D(x, y, z)` is a
positive real number (in the order `ComplexOrder`). By symmetry, either of the first two arguments
may be the one that vanishes. -/
theorem carlsonRD_pos {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    0 < carlsonRD x y z :=
  carlsonRJ_pos hx hy hz hz

end Complex
