/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# Complex linear and complex antilinear covectors

On a complex normed space `E`, the complex antilinear real covectors are the continuous real
linear maps `η : E → ℂ` with `η (i • v) = -(i • η v)`. Complex conjugation `φ ↦ conj ∘ φ` is a
real linear bijection from the complex linear covectors `E →L[ℂ] ℂ` onto them.

## Main declarations

* `TauCeti.antilinearCovectors E`: the complex antilinear real covectors on `E`.
* `TauCeti.conjCovector`, `TauCeti.conjCovectorEquiv`: conjugation of complex covectors, a real
  linear equivalence onto the complex antilinear covectors.
* `TauCeti.range_conjCovector`, `TauCeti.mem_antilinearCovectors_iff_existsUnique`: every
  complex antilinear covector is the conjugate of a unique complex linear covector.
-/

public section

open scoped ComplexConjugate

noncomputable section

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex antilinear real covectors on a complex normed space `E`: the continuous real
linear maps `η : E → ℂ` with `η (i • v) = -(i • η v)`. -/
def antilinearCovectors : Submodule ℝ (E →L[ℝ] ℂ) where
  carrier := {η | ∀ v, η (Complex.I • v) = -(Complex.I • η v)}
  add_mem' {η η'} hη hη' v := by
    simp [hη v, hη' v]
    ring
  zero_mem' v := by simp
  smul_mem' c η hη v := by
    simp [hη v]
    ring

variable {E}

theorem mem_antilinearCovectors_iff {η : E →L[ℝ] ℂ} :
    η ∈ antilinearCovectors E ↔ ∀ v, η (Complex.I • v) = -(Complex.I • η v) :=
  Iff.rfl

variable (E) in
/-- The complex conjugate `v ↦ conj (φ v)` of a complex covector `φ`, as a real covector. It is
complex antilinear (`TauCeti.conjCovector_mem_antilinearCovectors`). -/
def conjCovector : (E →L[ℂ] ℂ) →ₗ[ℝ] E →L[ℝ] ℂ where
  toFun φ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (φ.restrictScalars ℝ)
  map_add' φ ψ := by ext; simp
  map_smul' c φ := by ext; simp

@[simp]
theorem conjCovector_apply (φ : E →L[ℂ] ℂ) (v : E) : conjCovector E φ v = conj (φ v) :=
  (rfl)

/-- The conjugate of a complex covector is complex antilinear. -/
theorem conjCovector_mem_antilinearCovectors (φ : E →L[ℂ] ℂ) :
    conjCovector E φ ∈ antilinearCovectors E := fun v ↦ by
  simp

/-- Conjugation of complex covectors is injective. -/
theorem conjCovector_injective : Function.Injective (conjCovector E) := fun φ ψ h ↦ by
  ext v
  simpa using congrArg (fun η : E →L[ℝ] ℂ ↦ conj (η v)) h

private theorem conjAntilinear_aux (η : antilinearCovectors E) (v : E) :
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (η : E →L[ℝ] ℂ) (Complex.I • v) =
      Complex.I • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (η : E →L[ℝ] ℂ) v := by
  simp [mem_antilinearCovectors_iff.1 η.2 v]

/-- The conjugate `v ↦ conj (η v)` of a complex antilinear covector, a complex linear covector. -/
private def conjAntilinear (η : antilinearCovectors E) : E →L[ℂ] ℂ :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (η : E →L[ℝ] ℂ)).complexOfMapISmul (conjAntilinear_aux η)

private theorem conjAntilinear_apply (η : antilinearCovectors E) (v : E) :
    conjAntilinear η v = conj ((η : E →L[ℝ] ℂ) v) :=
  congrFun (ContinuousLinearMap.coe_complexOfMapISmul _ (conjAntilinear_aux η)) v

variable (E) in
/-- Complex conjugation is a real linear equivalence between the complex linear covectors on `E`
and the complex antilinear ones. -/
def conjCovectorEquiv : (E →L[ℂ] ℂ) ≃ₗ[ℝ] antilinearCovectors E where
  toFun φ := ⟨conjCovector E φ, conjCovector_mem_antilinearCovectors φ⟩
  map_add' φ ψ := Subtype.ext (map_add _ φ ψ)
  map_smul' c φ := Subtype.ext (map_smul _ c φ)
  invFun := conjAntilinear
  left_inv φ := by ext v; simp [conjAntilinear_apply]
  right_inv η := by ext v; simp [conjAntilinear_apply]

@[simp]
theorem coe_conjCovectorEquiv_apply (φ : E →L[ℂ] ℂ) :
    (conjCovectorEquiv E φ : E →L[ℝ] ℂ) = conjCovector E φ :=
  (rfl)

@[simp]
theorem conjCovectorEquiv_symm_apply_apply (η : antilinearCovectors E) (v : E) :
    (conjCovectorEquiv E).symm η v = conj ((η : E →L[ℝ] ℂ) v) :=
  conjAntilinear_apply η v

/-- The complex antilinear covectors are exactly the conjugates of the complex linear ones. -/
theorem range_conjCovector : LinearMap.range (conjCovector E) = antilinearCovectors E := by
  refine le_antisymm ?_ fun η hη ↦ ⟨(conjCovectorEquiv E).symm ⟨η, hη⟩, ?_⟩
  · rintro _ ⟨φ, rfl⟩
    exact conjCovector_mem_antilinearCovectors φ
  · exact congrArg Subtype.val ((conjCovectorEquiv E).apply_symm_apply ⟨η, hη⟩)

/-- A real covector is complex antilinear exactly when it is the conjugate of a unique complex
linear covector. -/
theorem mem_antilinearCovectors_iff_existsUnique {η : E →L[ℝ] ℂ} :
    η ∈ antilinearCovectors E ↔ ∃! φ : E →L[ℂ] ℂ, conjCovector E φ = η := by
  refine ⟨fun hη ↦ ?_, fun ⟨φ, hφ, _⟩ ↦ hφ ▸ conjCovector_mem_antilinearCovectors φ⟩
  rw [← range_conjCovector] at hη
  obtain ⟨φ, rfl⟩ := hη
  exact ⟨φ, rfl, fun ψ h ↦ conjCovector_injective h⟩


end TauCeti
