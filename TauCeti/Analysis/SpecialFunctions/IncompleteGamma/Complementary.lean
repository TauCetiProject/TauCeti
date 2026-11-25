/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper
import TauCeti.Analysis.Complex.RealIdentity

/-!
# The complementary relation of the incomplete Gamma functions

For `z` in the slit plane and `a ∉ −ℕ`, the lower and upper incomplete Gamma functions add up to
Euler's Gamma function, `γ(a, z) + Γ(a, z) = Γ(a)` (DLMF 8.2.3). In the regularized form
`Q(a, z) = Γ(a, z) / Γ(a)` it holds for every `a`. The derivative and the differential equation
of `γ(a, ·)` on the slit plane follow from those of `Γ(a, ·)`.

## Main results

* `Complex.regularizedGammaQ_eq_upperIncompleteGamma_div`: `Q(a, z) = Γ(a, z)/Γ(a)` for every
  `a`, with Mathlib's entire reciprocal of `Γ` (DLMF 8.2.4–8.2.5);
* `Complex.upperIncompleteGamma_add_lowerIncompleteGamma`: `Γ(a, z) + γ(a, z) = Γ(a)` for
  `a ∉ −ℕ` (DLMF 8.2.3);
* `Complex.hasDerivAt_lowerIncompleteGamma`, `Complex.deriv_lowerIncompleteGamma`:
  `∂γ(a, z)/∂z = z^{a−1} e^{−z}` on the slit plane for `a ∉ −ℕ` (DLMF 8.8.13);
* `Complex.lowerIncompleteGamma_ode`: DLMF 8.2.12 for `γ(a, ·)`.

## Implementation notes

For `0 < Re a` and `x ≥ 0`, Tau Ceti's `Complex.partialGamma_add_upperIncompleteGamma` splits
Euler's integral into Mathlib's `Complex.partialGamma a x`, which is `γ(a, x)` by
`Complex.lowerIncompleteGamma_ofReal_eq_partialGamma`, and the tail `Γ(a, x)`. Both sides being
holomorphic on the slit plane (`Complex.analyticOnNhd_upperIncompleteGamma`,
`Complex.analyticOnNhd_lowerIncompleteGamma`), the relation extends from the positive axis to the
slit plane by `AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq`. It then extends to every `a` in
the form `Q(a, z) = Γ(a)⁻¹ Γ(a, z)` by the identity theorem in `a`, both sides being entire.
The derivative and the differential equation of `γ(a, ·)` are those of `Γ(a) − Γ(a, ·)`.

## References

* NIST Digital Library of Mathematical Functions, §§8.2, 8.8, <https://dlmf.nist.gov/8.2>.

The proofs are new; the statements follow DLMF.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace Complex

/-- **DLMF 8.2.4–8.2.5**: `Q(a, z) = Γ(a, z) / Γ(a)` on the slit plane, for every `a`. At
`a ∈ −ℕ` both sides vanish: `Γ(a)⁻¹` is Mathlib's entire reciprocal. -/
theorem regularizedGammaQ_eq_upperIncompleteGamma_div (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    regularizedGammaQ a z = upperIncompleteGamma a z / Gamma a := by
  -- for `0 < Re a`, the relation `Γ(a, z) + γ(a, z) = Γ(a)` holds on the positive axis, hence on
  -- the slit plane by the identity theorem in `z`
  have hpos {b : ℂ} (hb : 0 < b.re) :
      upperIncompleteGamma b z + lowerIncompleteGamma b z = Gamma b := by
    refine ((analyticOnNhd_upperIncompleteGamma b).add
      (analyticOnNhd_lowerIncompleteGamma b)).eqOn_slitPlane_of_ofReal_pos_eq analyticOnNhd_const
        (fun x hx => ?_) hz
    rw [Pi.add_apply, lowerIncompleteGamma_ofReal_eq_partialGamma b hb hx.le, add_comm,
      partialGamma_add_upperIncompleteGamma hb hx.le]
  -- both sides are entire in `a` and agree on `0 < Re a`
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hQ : AnalyticOnNhd ℂ (fun b => regularizedGammaQ b z) univ := fun b _ =>
    ((differentiable_const 1).sub (differentiable_regularizedGamma_left hz0)).analyticAt b
      |>.congr (.of_forall fun b => (regularizedGammaQ_def b z).symm)
  have hR : AnalyticOnNhd ℂ (fun b => upperIncompleteGamma b z / Gamma b) univ := fun b _ =>
    ((differentiable_upperIncompleteGamma_left hz).mul differentiable_one_div_Gamma).analyticAt b
      |>.congr (.of_forall fun b => (div_eq_mul_inv _ _).symm)
  refine congrFun (hQ.eq_of_eventuallyEq hR (z₀ := 1) ?_) a
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (by simp : (0 : ℝ) < (1 : ℂ).re)] with b hb
  have hG := Gamma_ne_zero_of_re_pos hb
  have h := hpos hb
  rw [lowerIncompleteGamma_def] at h
  rw [regularizedGammaQ_def, eq_div_iff hG]
  linear_combination -h

/-- **DLMF 8.2.3**: `Γ(a, z) + γ(a, z) = Γ(a)` on the slit plane, for `a ∉ −ℕ`. -/
theorem upperIncompleteGamma_add_lowerIncompleteGamma {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n)
    (hz : z ∈ slitPlane) :
    upperIncompleteGamma a z + lowerIncompleteGamma a z = Gamma a := by
  have h := regularizedGammaQ_eq_upperIncompleteGamma_div a hz
  rw [regularizedGammaQ_def, eq_div_iff (Gamma_ne_zero ha)] at h
  rw [← h, lowerIncompleteGamma_def]
  ring

/-- Near a point of the slit plane, `γ(a, ·) = Γ(a) − Γ(a, ·)` for `a ∉ −ℕ`. -/
private theorem lowerIncompleteGamma_eventuallyEq {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ}
    (hz : z ∈ slitPlane) :
    lowerIncompleteGamma a =ᶠ[𝓝 z] fun w => Gamma a - upperIncompleteGamma a w :=
  eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw => by
    rw [← upperIncompleteGamma_add_lowerIncompleteGamma ha hw]
    ring

/-- **DLMF 8.8.13** for `γ`: on the slit plane, `γ(a, ·)` has derivative `z^{a−1} e^{−z}` for
`a ∉ −ℕ`. -/
theorem hasDerivAt_lowerIncompleteGamma (a : ℂ) (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ}
    (hz : z ∈ slitPlane) :
    HasDerivAt (lowerIncompleteGamma a) (z ^ (a - 1) * cexp (-z)) z := by
  simpa using ((hasDerivAt_upperIncompleteGamma hz a).const_sub (Gamma a)).congr_of_eventuallyEq
    (lowerIncompleteGamma_eventuallyEq ha hz)

/-- **DLMF 8.8.13** for `γ` and `deriv`: on the slit plane, `∂γ(a, z)/∂z = z^{a−1} e^{−z}` for
`a ∉ −ℕ`. -/
@[simp]
theorem deriv_lowerIncompleteGamma (a : ℂ) (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ}
    (hz : z ∈ slitPlane) :
    deriv (lowerIncompleteGamma a) z = z ^ (a - 1) * cexp (-z) :=
  (hasDerivAt_lowerIncompleteGamma a ha hz).deriv

/-- **DLMF 8.2.12** for `γ`: on the slit plane, `w = γ(a, ·)` satisfies
`w'' + (1 + (1 − a)/z) w' = 0`. At `a ∈ −ℕ`, `γ(a, ·)` is Mathlib's junk value `0`. -/
theorem lowerIncompleteGamma_ode (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (deriv (lowerIncompleteGamma a)) z +
      (1 + (1 - a) / z) * deriv (lowerIncompleteGamma a) z = 0 := by
  by_cases ha : ∀ n : ℕ, a ≠ -n
  · -- `γ(a, ·) = Γ(a) − Γ(a, ·)` near `z`, so this is the negative of 8.2.12 for `Γ(a, ·)`
    have hd : deriv (lowerIncompleteGamma a) =ᶠ[𝓝 z] fun w => -deriv (upperIncompleteGamma a) w :=
      (lowerIncompleteGamma_eventuallyEq ha hz).deriv.trans
        (.of_forall fun _ => deriv_const_sub _)
    rw [hd.deriv_eq, hd.eq_of_nhds, deriv.fun_neg]
    linear_combination -upperIncompleteGamma_ode a hz
  · push Not at ha
    obtain ⟨n, rfl⟩ := ha
    simp

end Complex
