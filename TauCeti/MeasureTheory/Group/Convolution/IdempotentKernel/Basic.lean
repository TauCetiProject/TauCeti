/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.Convolution.RightRegularIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral

/-!
# Idempotent kernels

An **idempotent kernel** on a group `G` with a measure `μ` is a continuous integrable
`e : G → ℂ` with `e g⁻¹ = conj (e g)`, `e 1 ≠ 0` and

```text
∫ z, e z * e ((z * x)⁻¹ * y) ∂μ = e x⁻¹ / e 1 * e y
```

for all `x` and `y`. In terms of convolution the last identity reads
`e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e`: the compression by `e` of every point mass `δ_x` is a multiple
of `e`, so that the corner cut out by `e` in the convolution algebra is spanned by `e`, the
defining property of a minimal idempotent. This is a statement about the convolution algebra,
not about the rank of the operator `ρ(e)` of `TauCeti.rightRegularIntegral`, which need not be
one: for a coefficient of an infinite-dimensional discrete series, `ρ(e)` has infinite rank.
Taking `x = 1` shows `e ⋆ e = e`, and evaluating at `y = 1`, with `e 1⁻¹ = conj (e 1)`, gives
`e 1 = ∫ ‖e‖²`, a positive real number. On the operator side, `ρ(e)` is idempotent and
`ρ(e) R_x ρ(e) = (e x⁻¹ / e 1) • ρ(e)` for the right translations `R_x`. The normalized
coefficients `deg_π · conj ⟨π(g) v, v⟩` of a unit vector `v` in an integrable discrete series
representation `π` are the basic examples.

## Main definitions

* `TauCeti.IsIdempotentKernel e μ`: `e` is an idempotent kernel.

## Main results

* `TauCeti.IsIdempotentKernel.integral_mul_inv_mul`: an idempotent kernel satisfies `e ⋆ e = e`.
* `TauCeti.IsIdempotentKernel.apply_one_eq_integral_norm_sq`,
  `TauCeti.IsIdempotentKernel.integral_norm_sq_pos`: `e 1 = ∫ ‖e‖² > 0`.
* `TauCeti.IsIdempotentKernel.isIdempotentElem_rightRegularIntegral`: `ρ(e)` is idempotent.
* `TauCeti.IsIdempotentKernel.rightRegularIntegral_compContinuous_mulRight_rightRegularIntegral`:
  `ρ(e) R_x ρ(e) = (e x⁻¹ / e 1) • ρ(e)`.

## Provenance

The notion is that of `New.IsIdempotentKernel` (file
`src/Lib/General/Measure/IdempotentKernel.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), the idempotent
kernel of roadmap ShortGRH/HolomorphicDiscreteSeriesOfUnitaryGroups §2.8.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction ComplexConjugate

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

/-- An **idempotent kernel** on a group `G` with a measure `μ`: a continuous integrable
`e : G → ℂ` with `e g⁻¹ = conj (e g)`, `e 1 ≠ 0` and
`∫ z, e z * e ((z * x)⁻¹ * y) ∂μ = e x⁻¹ / e 1 * e y` for all `x` and `y`. In terms of
convolution the last identity reads `e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e`: the compression by `e` of
every point mass is a multiple of `e`, so that `e` is a minimal idempotent of the convolution
algebra (`TauCeti.IsIdempotentKernel.integral_mul_inv_mul`). This is not a statement about the
rank of the operator `TauCeti.rightRegularIntegral e μ`. -/
structure IsIdempotentKernel (e : G → ℂ) (μ : Measure G) : Prop where
  /-- An idempotent kernel is continuous. -/
  continuous : Continuous e
  /-- An idempotent kernel is integrable. -/
  integrable : Integrable e μ
  /-- An idempotent kernel is hermitian: `e g⁻¹ = conj (e g)`. -/
  apply_inv (g : G) : e g⁻¹ = conj (e g)
  /-- An idempotent kernel does not vanish at `1`. -/
  apply_one_ne_zero : e 1 ≠ 0
  /-- The minimal idempotence identity `e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e`. -/
  integral_mul_mul_inv_mul (x y : G) : ∫ z, e z * e ((z * x)⁻¹ * y) ∂μ = e x⁻¹ / e 1 * e y

namespace IsIdempotentKernel

variable {e : G → ℂ} {μ : Measure G}

/-- **An idempotent kernel is idempotent for convolution**: `∫ z, e z * e (z⁻¹ * y) ∂μ = e y`. -/
@[simp]
theorem integral_mul_inv_mul (he : IsIdempotentKernel e μ) (y : G) :
    ∫ z, e z * e (z⁻¹ * y) ∂μ = e y := by
  simpa [div_self he.apply_one_ne_zero] using he.integral_mul_mul_inv_mul 1 y

/-- The value of an idempotent kernel at `1` is the square of its `L²` norm:
`e 1 = ∫ ‖e‖²`. -/
theorem apply_one_eq_integral_norm_sq (he : IsIdempotentKernel e μ) :
    e 1 = ((∫ z, ‖e z‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal, ← he.integral_mul_inv_mul 1]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [he.apply_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The value of an idempotent kernel at `1` is a positive real number: `0 < ∫ ‖e‖²`. -/
theorem integral_norm_sq_pos (he : IsIdempotentKernel e μ) : 0 < ∫ z, ‖e z‖ ^ 2 ∂μ := by
  refine (integral_nonneg fun z => by positivity).lt_of_ne fun h => he.apply_one_ne_zero ?_
  rw [he.apply_one_eq_integral_norm_sq, ← h, Complex.ofReal_zero]

/-- An idempotent kernel is square integrable. -/
theorem memLp_two (he : IsIdempotentKernel e μ) : MemLp e 2 μ :=
  (memLp_two_iff_integrable_sq_norm he.integrable.aestronglyMeasurable).2 <|
    Integrable.of_integral_ne_zero he.integral_norm_sq_pos.ne'

variable [IsTopologicalGroup G] [FirstCountableTopology G] [BorelSpace G] [MeasurableMul₂ G]
  [μ.IsMulLeftInvariant] [SFinite μ]

/-- The operator `ρ(e)` of an idempotent kernel is idempotent. -/
theorem isIdempotentElem_rightRegularIntegral (he : IsIdempotentKernel e μ) :
    IsIdempotentElem (rightRegularIntegral e μ) :=
  TauCeti.isIdempotentElem_rightRegularIntegral (Eventually.of_forall he.integral_mul_inv_mul)

/-- **The sandwich law of an idempotent kernel**: `ρ(e) R_x ρ(e) = (e x⁻¹ / e 1) • ρ(e)` for the
right translation `(R_x F)(y) = F (y * x)`, the operator form of `e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e`.
-/
theorem rightRegularIntegral_compContinuous_mulRight_rightRegularIntegral
    (he : IsIdempotentKernel e μ) (F : G →ᵇ ℂ) (x : G) :
    rightRegularIntegral e μ ((rightRegularIntegral e μ F).compContinuous
        (ContinuousMap.mulRight x)) = (e x⁻¹ / e 1) • rightRegularIntegral e μ F := by
  have he' : Integrable (fun g => e (x⁻¹ * g)) μ := he.integrable.comp_mul_left x⁻¹
  -- Right translation by `x` of `ρ(e) F` is `ρ` of the left translate `e (x⁻¹ * ·)`.
  have hR : (rightRegularIntegral e μ F).compContinuous (ContinuousMap.mulRight x) =
      rightRegularIntegral (fun g => e (x⁻¹ * g)) μ F := by
    ext y
    rw [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mulRight,
      rightRegularIntegral_apply_mul he.integrable, rightRegularIntegral_apply he']
  ext y
  rw [hR, rightRegularIntegral_rightRegularIntegral_apply he.integrable he',
    smul_apply,
    rightRegularIntegral_apply he.integrable, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [← mul_assoc, ← mul_inv_rev, he.integral_mul_mul_inv_mul]

end IsIdempotentKernel

end TauCeti
