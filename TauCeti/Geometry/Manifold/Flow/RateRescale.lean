/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
public import Mathlib.Order.Hom.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.IntegralCurve.Reparam
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Rescaling a vector field to a bounded rate along a function

Let `v` be a vector field and `f` a real function on a manifold `M`. The negative gradient of a
proper function bounded below need not be complete: for `f x = x² + x⁴` on `ℝ` with the Euclidean
metric, the trajectories escape to infinity in finite backward time
(`TauCeti.Geometry.Manifold.Morse.Examples.IncompleteGradient`). Rescaling `v` by the positive
function `(1 + df(v)²)⁻¹` repairs this. The rescaled field
`TauCeti.rateRescale I f v = (1 + df(v)²)⁻¹ • v` has the same zeros as `v`
(`TauCeti.rateRescale_eq_zero_iff`), and `f` changes along it in the same direction as along `v`
(`TauCeti.mvfderiv_rateRescale_lt_zero_iff`, `TauCeti.mvfderiv_rateRescale_nonpos_iff`), but at
rate at most `1 / 2` (`TauCeti.abs_mvfderiv_rateRescale_le`). So a pseudo-gradient of `f`
rescales to a pseudo-gradient of `f`. It is as regular as `v` when `f` has one more derivative
(`TauCeti.contMDiff_rateRescale`).

When `f` is proper, the bounded rate confines each trajectory of the rescaled field to a compact
set `f⁻¹ [f x - T / 2, f x + T / 2]` up to time `T`, so the rescaled field is complete
(`TauCeti.isCompleteVectorField_rateRescale`), with no lower bound on `f` and no completeness of
any metric. Its trajectories trace those of `v` with a change of time: every global integral curve
of `v` becomes one of the rescaled field after an order automorphism of `ℝ`
(`IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_rateRescale`). So a pseudo-gradient of a
proper function on a noncompact manifold rescales to a complete pseudo-gradient, whose trajectories
are defined for all time.

## Main definitions

* `TauCeti.rateRescale I f v`: the vector field `(1 + df(v)²)⁻¹ • v`.

## Main results

* `TauCeti.rateRescale_eq_zero_iff`: the rescaled field has the zeros of `v`.
* `TauCeti.mvfderiv_rateRescale`: `df` of the rescaled field is `df(v) / (1 + df(v)²)`.
* `TauCeti.abs_mvfderiv_rateRescale_le`: this rate is at most `1 / 2` in absolute value.
* `TauCeti.contMDiff_rateRescale`: the rescaled field is `C^n` when `v` is `C^n` and `f` is
  `C^(n+1)`.
* `TauCeti.isCompleteVectorField_rateRescale`: for proper `f`, the rescaled field is complete.
* `IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_rateRescale`: global integral curves of
  `v` reparametrize to integral curves of the rescaled field.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, proof of Theorem 3.1, where the gradient is rescaled by `1 / ‖grad f‖²` on a compact
  region so that its flow is defined there.
-/

public section

noncomputable section

open Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → ℝ} {v : (x : M) → TangentSpace I x} {x : M}

variable (I) in
/-- The **rescaling of a vector field `v` to a bounded rate along `f`**: the field
`(1 + df(v)²)⁻¹ • v`. It is a positive multiple of `v`, along which `f` changes at rate at most
`1 / 2` (`TauCeti.abs_mvfderiv_rateRescale_le`). -/
def rateRescale (f : M → ℝ) (v : (x : M) → TangentSpace I x) (x : M) : TangentSpace I x :=
  (1 + mvfderiv I f x (v x) ^ 2)⁻¹ • v x

theorem rateRescale_apply (x : M) :
    rateRescale I f v x = (1 + mvfderiv I f x (v x) ^ 2)⁻¹ • v x :=
  (rfl)

/-- The rescaling factor `(1 + df(v)²)⁻¹` is positive. -/
private theorem inv_one_add_mvfderiv_sq_pos (x : M) : 0 < (1 + mvfderiv I f x (v x) ^ 2)⁻¹ := by
  positivity

/-- The rescaled field vanishes exactly where `v` does. -/
@[simp]
theorem rateRescale_eq_zero_iff : rateRescale I f v x = 0 ↔ v x = 0 := by
  rw [rateRescale_apply, smul_eq_zero, or_iff_right (inv_one_add_mvfderiv_sq_pos x).ne']

/-- The derivative of `f` along the rescaled field is `df(v) / (1 + df(v)²)`. -/
theorem mvfderiv_rateRescale (x : M) :
    mvfderiv I f x (rateRescale I f v x) =
      mvfderiv I f x (v x) / (1 + mvfderiv I f x (v x) ^ 2) := by
  rw [rateRescale_apply, map_smul, smul_eq_mul, div_eq_inv_mul]

/-- `f` strictly decreases along the rescaled field exactly where it does along `v`. -/
theorem mvfderiv_rateRescale_lt_zero_iff :
    mvfderiv I f x (rateRescale I f v x) < 0 ↔ mvfderiv I f x (v x) < 0 := by
  rw [mvfderiv_rateRescale, div_lt_iff₀ (by positivity), zero_mul]

/-- `f` does not increase along the rescaled field exactly where it does not along `v`. -/
theorem mvfderiv_rateRescale_nonpos_iff :
    mvfderiv I f x (rateRescale I f v x) ≤ 0 ↔ mvfderiv I f x (v x) ≤ 0 := by
  rw [mvfderiv_rateRescale, div_le_iff₀ (by positivity), zero_mul]

/-- **`f` changes at rate at most `1 / 2` along the rescaled field**, since `2 |a| ≤ 1 + a²`. -/
theorem abs_mvfderiv_rateRescale_le (x : M) :
    |mvfderiv I f x (rateRescale I f v x)| ≤ 1 / 2 := by
  rw [mvfderiv_rateRescale, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + _),
    div_le_iff₀ (by positivity), ← sq_abs (mvfderiv I f x (v x))]
  nlinarith [sq_nonneg (|mvfderiv I f x (v x)| - 1)]

/-- **The rescaled field is as regular as `v`** when `f` has one more derivative. -/
theorem contMDiff_rateRescale [IsManifold I 1 M] {n : WithTop ℕ∞}
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f)
    (hv : ContMDiff I I.tangent n (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    ContMDiff I I.tangent n (fun x ↦ (⟨x, rateRescale I f v x⟩ : TangentBundle I M)) := by
  have hdf : ContMDiff I 𝓘(ℝ) n fun x ↦ mvfderiv I f x (v x) :=
    (hf.contMDiff_mvfderiv_apply le_rfl).comp hv
  have hfactor : ContDiff ℝ n fun a : ℝ ↦ (1 + a ^ 2)⁻¹ :=
    (contDiff_const.add (contDiff_id.pow 2)).inv fun a ↦ by positivity
  exact (hfactor.comp_contMDiff hdf).smul_section hv

/-- **For a proper function, the rescaled field is complete.** Along it `f` changes at rate at
most `1 / 2`, so each trajectory stays in a compact preimage of `f` on each bounded time window
(`TauCeti.isCompleteVectorField_of_isProperMap_of_abs_mvfderiv_le`). Neither a lower bound on `f`
nor completeness of a metric is needed. -/
theorem isCompleteVectorField_rateRescale [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]
    (hf : IsProperMap f) (hf₂ : ContMDiff I 𝓘(ℝ) 2 f)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    IsCompleteVectorField (rateRescale I f v) :=
  isCompleteVectorField_of_isProperMap_of_abs_mvfderiv_le (contMDiff_rateRescale hf₂ hv) hf
    (hf₂.mdifferentiable (by norm_num)) abs_mvfderiv_rateRescale_le

end TauCeti

namespace IsMIntegralCurve

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {f : M → ℝ} {v : (x : M) → TangentSpace I x} {γ : ℝ → M}

/-- **Integral curves of `v` reparametrize to integral curves of the rescaled field.** If `γ` is a
global integral curve of a continuous field `v` and `f` is `C¹`, then `γ ∘ ψ` is an integral curve
of `TauCeti.rateRescale I f v` for an order automorphism `ψ` of `ℝ` fixing `0`. So it has the
image of `γ`, run in the same direction, with the same limits at `±∞`. -/
theorem exists_orderIso_isMIntegralCurve_comp_rateRescale (hγ : IsMIntegralCurve γ v)
    (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hv : ContMDiff I I.tangent 0 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧ IsMIntegralCurve (γ ∘ ψ) (TauCeti.rateRescale I f v) := by
  have hdf : Continuous fun x ↦ mvfderiv I f x (v x) :=
    ((hf.contMDiff_mvfderiv_apply (by norm_num)).comp hv).continuous
  exact hγ.exists_orderIso_isMIntegralCurve_comp
    ((continuous_const.add ((hdf.comp hγ.continuous).pow 2)).inv₀ fun t ↦
      (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')
    (fun t ↦ TauCeti.inv_one_add_mvfderiv_sq_pos (γ t))
    (fun t ↦ inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _)))
    fun t ↦ TauCeti.rateRescale_apply (γ t)

end IsMIntegralCurve
