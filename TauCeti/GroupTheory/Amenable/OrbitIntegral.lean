/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# Integrals of translation orbits in `UCB` and invariant means

Let `μ` be a measure on a topological group `G` and `h` an integrable real function on `G`. For
`f` in `TauCeti.UCB G` the orbit map `y ↦ L_y f`, with `(L_y f)(x) = f (y⁻¹ * x)`, is continuous
for the supremum norm, so the `UCB G`-valued Bochner integral

```text
∫ y, h y • L_y f ∂μ  ∈  UCB G
```

is defined. It is the function `x ↦ ∫ y, h y * f (y⁻¹ * x) ∂μ`, the convolution of `h` with `f`,
and its supremum norm is at most `(∫ ‖h‖) * ‖f‖`; it is nonnegative when `h` and `f` are. Since a
mean is a continuous linear functional, it commutes with the integral:
`m (∫ y, h y • L_y f ∂μ) = ∫ y, h y * m (L_y f) ∂μ`. For a left-invariant mean the integrand is
`h y * m f`, so

```text
m (∫ y, h y • L_y f ∂μ) = (∫ y, h y ∂μ) * m f.
```

In particular a left-invariant mean does not see convolution of a function in `UCB G` with a
kernel of integral one. This is the identity `m (h ⋆ ψ) = m ψ` used to extend an invariant mean
on `UCB G` to an invariant mean on `L∞` of a Haar measure, by smoothing `L∞` functions into
`UCB G`.

No σ-finiteness of `μ` and no second countability of `G` is assumed. The measure is only asked to
be inner regular for compact sets on sets of finite measure, as every regular measure is; for
instance a Haar measure of a locally compact group, which need not be σ-finite. An integrable `h`
lives on a σ-finite set, which up to a null set is a countable union of compact sets, and the
orbit map has separable image on each of them
(`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_smul`).

## Main results

* `TauCeti.UCB.integrable_smul_leftTranslation`: the orbit integrand `y ↦ h y • L_y f` is
  integrable.
* `TauCeti.UCB.integral_smul_leftTranslation_apply`: the orbit integral is the convolution
  `x ↦ ∫ y, h y * f (y⁻¹ * x) ∂μ`.
* `TauCeti.UCB.norm_integral_smul_leftTranslation_le`: its norm is at most `(∫ ‖h‖) * ‖f‖`.
* `TauCeti.UCB.integral_smul_leftTranslation_nonneg`: it is nonnegative when `h` and `f` are.
* `TauCeti.Mean.apply_integral_smul_leftTranslation`: a mean commutes with the orbit integral.
* `TauCeti.Mean.IsLeftInvariant.apply_integral_smul_leftTranslation`: a left-invariant mean takes
  the value `(∫ h) * m f` at the orbit integral.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G, proof of
  Theorem G.3.1.
-/

public section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  {μ : Measure G} {h : G → ℝ}

namespace UCB

/-- The norm of the orbit integral `∫ y, h y • L_y f ∂μ` is at most `(∫ ‖h‖) * ‖f‖`, for every
function `h` and every measure `μ`. -/
theorem norm_integral_smul_leftTranslation_le (f : UCB G) :
    ‖∫ y, h y • leftTranslation y f ∂μ‖ ≤ (∫ y, ‖h y‖ ∂μ) * ‖f‖ := by
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  simp_rw [norm_smul, LinearIsometryEquiv.norm_map, integral_mul_const]

variable [BorelSpace G] [μ.InnerRegularCompactLTTop]

/-- For an integrable `h`, the orbit integrand `y ↦ h y • L_y f` is integrable in `UCB G`. -/
theorem integrable_smul_leftTranslation (hh : Integrable h μ) (f : UCB G) :
    Integrable (fun y => h y • leftTranslation y f) μ := by
  refine (hh.norm.mul_const ‖f‖).mono'
    (hh.aefinStronglyMeasurable.aestronglyMeasurable_smul (continuous_leftTranslation_apply f))
    (.of_forall fun y => ?_)
  rw [norm_smul, LinearIsometryEquiv.norm_map]

end UCB

namespace Mean

variable [BorelSpace G] [μ.InnerRegularCompactLTTop]

/-- A mean commutes with the orbit integral: `m (∫ y, h y • L_y f ∂μ) = ∫ y, h y * m (L_y f) ∂μ`.
-/
theorem apply_integral_smul_leftTranslation (m : Mean G) (hh : Integrable h μ) (f : UCB G) :
    m (∫ y, h y • UCB.leftTranslation y f ∂μ) = ∫ y, h y * m (UCB.leftTranslation y f) ∂μ := by
  rw [← coe_toContinuousLinearMap,
    ← ContinuousLinearMap.integral_comp_comm _ (UCB.integrable_smul_leftTranslation hh f)]
  simp only [map_smul, smul_eq_mul]

/-- A left-invariant mean takes the value `(∫ h) * m f` at the orbit integral
`∫ y, h y • L_y f ∂μ`. In particular it takes the value `m f` when `h` has integral one. -/
theorem IsLeftInvariant.apply_integral_smul_leftTranslation {m : Mean G} (hm : m.IsLeftInvariant)
    (hh : Integrable h μ) (f : UCB G) :
    m (∫ y, h y • UCB.leftTranslation y f ∂μ) = (∫ y, h y ∂μ) * m f := by
  simp only [m.apply_integral_smul_leftTranslation hh, hm.apply_leftTranslation,
    integral_mul_const]

end Mean

namespace UCB

variable [BorelSpace G] [μ.InnerRegularCompactLTTop]

/-- The orbit integral `∫ y, h y • L_y f ∂μ` is the convolution
`x ↦ ∫ y, h y * f (y⁻¹ * x) ∂μ`, evaluated at every point. -/
theorem integral_smul_leftTranslation_apply (hh : Integrable h μ) (f : UCB G) (x : G) :
    ((∫ y, h y • leftTranslation y f ∂μ : UCB G) : G →ᵇ ℝ) x =
      ∫ y, h y * (f : G →ᵇ ℝ) (y⁻¹ * x) ∂μ := by
  simpa only [Mean.eval_apply, leftTranslation_apply] using
    (Mean.eval G x).apply_integral_smul_leftTranslation hh f

/-- The orbit integral `∫ y, h y • L_y f ∂μ` is nonnegative when `h` is almost everywhere
nonnegative and `f` is nonnegative. -/
theorem integral_smul_leftTranslation_nonneg (hh : Integrable h μ) (hh₀ : 0 ≤ᵐ[μ] h) {f : UCB G}
    (hf : 0 ≤ f) : 0 ≤ ∫ y, h y • leftTranslation y f ∂μ := by
  refine le_def.2 fun x => ?_
  rw [integral_smul_leftTranslation_apply hh, ZeroMemClass.coe_zero,
    BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hh₀] with y hy
  exact mul_nonneg hy (le_def.1 hf _)

end UCB

end TauCeti
