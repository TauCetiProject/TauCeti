/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.LowerOrder

/-!
# Bounds for lower-order pointwise PDE forms

This file records the elementary boundedness API for the pointwise lower-order forms used
in divergence-form energy estimates:

* `driftForm b`, the bilinear form `(u, ξ) ↦ ⟪b, ξ⟫ u`;
* `massForm c`, the bilinear form `(u, v) ↦ c u v`.

The estimates are deliberately pointwise and finite-dimensional. They are the standalone
lower-order pieces of Lane D's boundedness bookkeeping for the weak energy form, before the
later Sobolev-space integration layer is available.

## Main declarations

* `TauCeti.PDE.norm_driftForm_apply_le` and `TauCeti.PDE.opNorm_driftForm_le`.
* `TauCeti.PDE.norm_massForm_apply_le` and `TauCeti.PDE.opNorm_massForm_le`.
* Bound-by-a-constant and radius-restricted variants for both forms.
-/

public section

namespace TauCeti

namespace PDE

open scoped InnerProductSpace

variable {n : Type*} [Fintype n]

/-! ## Drift form -/

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

/-- Radius-restricted drift estimate from a coefficient bound. -/
lemma norm_driftForm_apply_le_of_norm_le_of_le {b : EuclideanSpace ℝ n}
    {β R S : ℝ} (hb : ‖b‖ ≤ β) {u : ℝ} {ξ : EuclideanSpace ℝ n}
    (hu : ‖u‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖driftForm b u ξ‖ ≤ β * R * S :=
  (driftForm b).le_of_opNorm₂_le_of_le (opNorm_driftForm_le_of_norm_le hb) hu hξ

/-! ## Mass form -/

/-- The mass form is bounded by the norm of the mass coefficient. -/
lemma norm_massForm_apply_le (c u v : ℝ) :
    ‖massForm c u v‖ ≤ ‖c‖ * ‖u‖ * ‖v‖ := by
  rw [massForm_apply, norm_mul, norm_mul]

/-- If the mass coefficient is bounded by `γ`, then the mass form is bounded by `γ`. -/
lemma norm_massForm_apply_le_of_norm_le {c γ : ℝ} (hc : ‖c‖ ≤ γ) (u v : ℝ) :
    ‖massForm c u v‖ ≤ γ * ‖u‖ * ‖v‖ := by
  exact (norm_massForm_apply_le c u v).trans <| by
    gcongr

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

/-- Radius-restricted mass estimate from a coefficient bound. -/
lemma norm_massForm_apply_le_of_norm_le_of_le {c γ R S : ℝ} (hc : ‖c‖ ≤ γ)
    {u v : ℝ} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ S) :
    ‖massForm c u v‖ ≤ γ * R * S :=
  (massForm c).le_of_opNorm₂_le_of_le (opNorm_massForm_le_of_norm_le hc) hu hv

end PDE

end TauCeti
