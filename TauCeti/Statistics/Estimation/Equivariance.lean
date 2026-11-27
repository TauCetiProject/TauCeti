/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Location-equivariant estimators

An estimator `δ : ℝ^ι → ℝ` on samples indexed by `ι` is *location equivariant* if shifting every
observation by `a` shifts the estimate by `a`: `δ (x + a·1) = δ x + a`. At `θ = 0`, the
squared-error risk of the Pitman estimator is at most that of every square-integrable
location-equivariant estimator (`TauCeti.pitmanEstimator_risk_zero_le_of_equivariant`); the
theorem compares the risks at `θ = 0` only.

## Main definitions

* `TauCeti.IsLocationEquivariant δ`: `δ (x + a·1) = δ x + a` for all `x` and `a`.

## Main results

* `TauCeti.IsLocationEquivariant.apply_sub_const`: the subtraction form of the definition.
* `TauCeti.IsLocationEquivariant.nonempty`: location-equivariant estimators exist only for
  nonempty samples.
-/

public section

namespace TauCeti

variable {ι : Type*}

/-- An estimator `δ` on samples indexed by `ι` is **location equivariant** if shifting every
observation by `a` shifts the estimate by `a`. -/
def IsLocationEquivariant (δ : (ι → ℝ) → ℝ) : Prop :=
  ∀ x a, δ (fun i ↦ x i + a) = δ x + a

/-- Unfolding `TauCeti.IsLocationEquivariant`. -/
theorem isLocationEquivariant_iff {δ : (ι → ℝ) → ℝ} :
    IsLocationEquivariant δ ↔ ∀ x a, δ (fun i ↦ x i + a) = δ x + a :=
  Iff.rfl

/-- A location-equivariant estimator commutes with subtracting a constant from every
observation. -/
theorem IsLocationEquivariant.apply_sub_const {δ : (ι → ℝ) → ℝ} (h : IsLocationEquivariant δ)
    (x : ι → ℝ) (a : ℝ) : δ (fun i ↦ x i - a) = δ x - a := by
  simpa only [← sub_eq_add_neg] using h x (-a)

/-- A location-equivariant estimator exists only for a nonempty sample: on the empty sample the
shift by `1` changes nothing. -/
theorem IsLocationEquivariant.nonempty {δ : (ι → ℝ) → ℝ} (h : IsLocationEquivariant δ) :
    Nonempty ι := by
  by_contra hι
  have : IsEmpty ι := not_nonempty_iff.1 hι
  have h1 := h 0 1
  rw [Subsingleton.elim (fun i ↦ (0 : ι → ℝ) i + 1) 0] at h1
  linarith

end TauCeti
