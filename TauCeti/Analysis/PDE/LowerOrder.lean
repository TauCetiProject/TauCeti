/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Lower-order pointwise forms for divergence-form PDEs

For a divergence-form operator `L u = -∂ⱼ(aⁱʲ ∂ᵢ u) + bⁱ ∂ᵢ u + c u`, the principal matrix
coefficient lives in `TauCeti.Analysis.PDE.UniformEllipticity`. This file records the two
lower-order pointwise forms:

* `u ↦ b(x) · ∇u`, the first-order drift form `driftForm (b x)`;
* `u ↦ c(x) u`, the zeroth-order mass form `massForm (c x)`.

Boundedness of the coefficients is not given its own predicate: following Mathlib, a result
that needs a bound states it inline, as `∀ x ∈ Ω, ‖b x‖ ≤ β`, and the energy-form estimates in
`TauCeti.Analysis.PDE.EnergyForm` and `TauCeti.Analysis.PDE.CoerciveEnergy` take their bounds
in that shape.

## Main declarations

* `TauCeti.PDE.driftForm`, `TauCeti.PDE.massForm`: the pointwise lower-order forms.
* `TauCeti.PDE.norm_driftForm_apply_le` and `TauCeti.PDE.opNorm_driftForm_le`.
* `TauCeti.PDE.norm_massForm_apply_le` and `TauCeti.PDE.opNorm_massForm_le`.
* Bound-by-a-constant and radius-restricted variants for both forms.
-/

public section

namespace TauCeti

namespace PDE

open scoped InnerProductSpace

variable {n : Type*} [Fintype n]

/-- The pointwise first-order drift form `(u, ξ) ↦ ⟪b, ξ⟫ u`. -/
noncomputable def driftForm (b : EuclideanSpace ℝ n) :
    ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ n) ℝ (innerSL ℝ b)

/-- The pointwise zeroth-order mass form `(u, v) ↦ c u v`. -/
noncomputable def massForm (c : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  c • ContinuousLinearMap.mul ℝ ℝ

/-- Applying the drift form is the scalar product with the drift coefficient times `u`. -/
@[simp]
lemma driftForm_apply (b : EuclideanSpace ℝ n) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    driftForm b u ξ = ⟪b, ξ⟫_ℝ * u := by
  rw [driftForm, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]

/-- Applying the mass form is multiplication by the mass coefficient. -/
@[simp]
lemma massForm_apply (c u v : ℝ) :
    massForm c u v = c * u * v := by
  rw [massForm, smul_apply, smul_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring

/-! ## Drift form bounds -/

/-- The drift form is bounded by the norm of the drift coefficient. -/
lemma norm_driftForm_apply_le (b : EuclideanSpace ℝ n) (u : ℝ)
    (ξ : EuclideanSpace ℝ n) :
    ‖driftForm b u ξ‖ ≤ ‖b‖ * ‖u‖ * ‖ξ‖ := by
  rw [driftForm_apply, norm_mul]
  calc
    ‖⟪b, ξ⟫_ℝ‖ * ‖u‖ ≤ (‖b‖ * ‖ξ‖) * ‖u‖ := by
      gcongr
      exact norm_inner_le_norm b ξ
    _ = ‖b‖ * ‖u‖ * ‖ξ‖ := by ring

/-- If the drift coefficient is bounded by `β`, then the drift form is bounded by `β`. -/
lemma norm_driftForm_apply_le_of_norm_le {b : EuclideanSpace ℝ n} {β : ℝ}
    (hb : ‖b‖ ≤ β) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    ‖driftForm b u ξ‖ ≤ β * ‖u‖ * ‖ξ‖ := by
  exact (norm_driftForm_apply_le b u ξ).trans <| by
    gcongr

grind_pattern norm_driftForm_apply_le_of_norm_le =>
  ‖b‖ ≤ β, driftForm b u ξ

/-- The operator norm of the drift form is bounded by the norm of the drift coefficient. -/
lemma opNorm_driftForm_le (b : EuclideanSpace ℝ n) :
    ‖driftForm b‖ ≤ ‖b‖ := by
  refine (driftForm b).opNorm_le_bound₂ (norm_nonneg b) ?_
  intro u ξ
  exact norm_driftForm_apply_le b u ξ

/-- If the drift coefficient is bounded by `β`, then the drift form has operator norm at
most `β`. -/
lemma opNorm_driftForm_le_of_norm_le {b : EuclideanSpace ℝ n} {β : ℝ} (hb : ‖b‖ ≤ β) :
    ‖driftForm b‖ ≤ β :=
  (opNorm_driftForm_le b).trans hb

grind_pattern opNorm_driftForm_le_of_norm_le =>
  ‖b‖ ≤ β, ‖driftForm b‖

/-- Radius-restricted drift estimate from a coefficient bound. -/
lemma norm_driftForm_apply_le_of_norm_le_of_le {b : EuclideanSpace ℝ n}
    {β R S : ℝ} (hb : ‖b‖ ≤ β) {u : ℝ} {ξ : EuclideanSpace ℝ n}
    (hu : ‖u‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖driftForm b u ξ‖ ≤ β * R * S :=
  (driftForm b).le_of_opNorm₂_le_of_le (opNorm_driftForm_le_of_norm_le hb) hu hξ

grind_pattern norm_driftForm_apply_le_of_norm_le_of_le =>
  ‖b‖ ≤ β, ‖u‖ ≤ R, ‖ξ‖ ≤ S, driftForm b u ξ

/-! ## Mass form bounds -/

/-- The mass form is bounded by the norm of the mass coefficient. -/
lemma norm_massForm_apply_le (c u v : ℝ) :
    ‖massForm c u v‖ ≤ ‖c‖ * ‖u‖ * ‖v‖ := by
  rw [massForm_apply, norm_mul, norm_mul]

/-- If the mass coefficient is bounded by `γ`, then the mass form is bounded by `γ`. -/
lemma norm_massForm_apply_le_of_norm_le {c γ : ℝ} (hc : ‖c‖ ≤ γ) (u v : ℝ) :
    ‖massForm c u v‖ ≤ γ * ‖u‖ * ‖v‖ := by
  exact (norm_massForm_apply_le c u v).trans <| by
    gcongr

grind_pattern norm_massForm_apply_le_of_norm_le =>
  ‖c‖ ≤ γ, massForm c u v

/-- The operator norm of the mass form is bounded by the norm of the mass coefficient. -/
lemma opNorm_massForm_le (c : ℝ) :
    ‖massForm c‖ ≤ ‖c‖ := by
  refine (massForm c).opNorm_le_bound₂ (norm_nonneg c) ?_
  intro u v
  exact norm_massForm_apply_le c u v

/-- If the mass coefficient is bounded by `γ`, then the mass form has operator norm at
most `γ`. -/
lemma opNorm_massForm_le_of_norm_le {c γ : ℝ} (hc : ‖c‖ ≤ γ) :
    ‖massForm c‖ ≤ γ :=
  (opNorm_massForm_le c).trans hc

grind_pattern opNorm_massForm_le_of_norm_le =>
  ‖c‖ ≤ γ, ‖massForm c‖

/-- Radius-restricted mass estimate from a coefficient bound. -/
lemma norm_massForm_apply_le_of_norm_le_of_le {c γ R S : ℝ} (hc : ‖c‖ ≤ γ)
    {u v : ℝ} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ S) :
    ‖massForm c u v‖ ≤ γ * R * S :=
  (massForm c).le_of_opNorm₂_le_of_le (opNorm_massForm_le_of_norm_le hc) hu hv

grind_pattern norm_massForm_apply_le_of_norm_le_of_le =>
  ‖c‖ ≤ γ, ‖u‖ ≤ R, ‖v‖ ≤ S, massForm c u v

end PDE

end TauCeti
