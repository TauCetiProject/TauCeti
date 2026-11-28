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

for all `x` and `y`. The predicate is stated for an arbitrary measure `μ`, and so are its
consequences that only use the identity: taking `x = 1` gives `∫ z, e z * e (z⁻¹ * y) ∂μ = e y`,
and evaluating that at `y = 1`, with `e 1⁻¹ = conj (e 1)`, gives `e 1 = ∫ ‖e‖²`, a positive real
number.

The reading of the identity in the convolution algebra needs `μ` to be a left Haar measure. Then
`(f ⋆ g) y = ∫ z, f z * g (z⁻¹ * y) ∂μ` is the associative convolution of `L¹(G, μ)`, and
`(δ_x ⋆ g) y = g (x⁻¹ * y)` for the point mass `δ_x`, so the identity reads
`e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e` and its case `x = 1` reads `e ⋆ e = e`: the compression by `e`
of every point mass is a multiple of `e`, so that the corner cut out by `e` in the convolution
algebra is spanned by `e`, the defining property of a minimal idempotent. For a measure that is
not left invariant the integral `∫ z, f z * g (z⁻¹ * y) ∂μ` need not be associative in `f` and
`g`, and the identity carries no such meaning. Minimal idempotence is a statement about the
convolution algebra, not about the rank of the operator `ρ(e)` of `TauCeti.rightRegularIntegral`,
which need not be one: for a coefficient of an infinite-dimensional discrete series, `ρ(e)` has
infinite rank.

On the operator side, for a first-countable topological group `G` with `BorelSpace G` and
`MeasurableMul₂ G` and an s-finite left-invariant measure `μ`, `ρ(e)` is idempotent and
`ρ(e) R_x ρ(e) = (e x⁻¹ / e 1) • ρ(e)` for the right translations `R_x`; both laws go through
`TauCeti.rightRegularIntegral_rightRegularIntegral_apply`, which uses the left invariance. The
normalized coefficients `deg_π · conj ⟨π(g) v, v⟩` of a unit vector `v` in an integrable discrete
series representation `π`, with a Haar measure `μ`, are the basic examples.

## Main definitions

* `TauCeti.IsIdempotentKernel e μ`: `e` is an idempotent kernel.

## Main results

* `TauCeti.IsIdempotentKernel.integral_mul_inv_mul`: `∫ z, e z * e (z⁻¹ * y) ∂μ = e y` for any
  `μ`, which is `e ⋆ e = e` when `μ` is a left Haar measure.
* `TauCeti.IsIdempotentKernel.apply_one_eq_integral_norm_sq`,
  `TauCeti.IsIdempotentKernel.integral_norm_sq_pos`: `e 1 = ∫ ‖e‖² > 0`, for any `μ`.
* `TauCeti.IsIdempotentKernel.isIdempotentElem_rightRegularIntegral`: `ρ(e)` is idempotent, for
  an s-finite left-invariant `μ`.
* `TauCeti.IsIdempotentKernel.rightRegularIntegral_compContinuous_mulRight_rightRegularIntegral`:
  `ρ(e) R_x ρ(e) = (e x⁻¹ / e 1) • ρ(e)`, for an s-finite left-invariant `μ`.

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
`∫ z, e z * e ((z * x)⁻¹ * y) ∂μ = e x⁻¹ / e 1 * e y` for all `x` and `y`. The predicate is
stated for an arbitrary measure `μ`. When `μ` is a left Haar measure, the last identity reads
`e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e` in the convolution algebra `L¹(G, μ)`, whose case `x = 1` is
`e ⋆ e = e` (`TauCeti.IsIdempotentKernel.integral_mul_inv_mul`): the compression by `e` of every
point mass is a multiple of `e`, so that `e` is a minimal idempotent of that algebra. Without left
invariance the convolution integral need not be associative and this reading is not available.
Minimal idempotence is not a statement about the rank of the operator
`TauCeti.rightRegularIntegral e μ`. -/
structure IsIdempotentKernel (e : G → ℂ) (μ : Measure G) : Prop where
  /-- An idempotent kernel is continuous. -/
  continuous : Continuous e
  /-- An idempotent kernel is integrable. -/
  integrable : Integrable e μ
  /-- An idempotent kernel is hermitian: `e g⁻¹ = conj (e g)`. -/
  apply_inv (g : G) : e g⁻¹ = conj (e g)
  /-- An idempotent kernel does not vanish at `1`. -/
  apply_one_ne_zero : e 1 ≠ 0
  /-- The identity `∫ z, e z * e ((z * x)⁻¹ * y) ∂μ = e x⁻¹ / e 1 * e y`; when `μ` is a left
  Haar measure it is the minimal idempotence `e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e`. -/
  integral_mul_mul_inv_mul (x y : G) : ∫ z, e z * e ((z * x)⁻¹ * y) ∂μ = e x⁻¹ / e 1 * e y

namespace IsIdempotentKernel

variable {e : G → ℂ} {μ : Measure G}

/-- The case `x = 1` of the defining identity of an idempotent kernel:
`∫ z, e z * e (z⁻¹ * y) ∂μ = e y`, for any measure `μ`. When `μ` is a left Haar measure, this is
**the idempotence `e ⋆ e = e` in the convolution algebra**. -/
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

/-- The operator `ρ(e)` of an idempotent kernel is idempotent, for an s-finite left-invariant
measure `μ`. -/
theorem isIdempotentElem_rightRegularIntegral (he : IsIdempotentKernel e μ) :
    IsIdempotentElem (rightRegularIntegral e μ) :=
  TauCeti.isIdempotentElem_rightRegularIntegral (Eventually.of_forall he.integral_mul_inv_mul)

/-- **The sandwich law of an idempotent kernel**: `ρ(e) R_x ρ(e) = (e x⁻¹ / e 1) • ρ(e)` for the
right translation `(R_x F)(y) = F (y * x)` and an s-finite left-invariant measure `μ`, the operator
form of `e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e`. -/
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
