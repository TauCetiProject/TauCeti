/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Clearing denominators in the image of a linear map

Pulling Mathlib's `multiple_mem_span_of_mem_localization_span` back along an injective linear map
clears denominators in a localized span; conversely, the localizing elements act invertibly on the
localized span, so this characterizes membership in it. This applies to arbitrary spanning sets in
modules, including lifts of a basis along an injective algebra map.

## Main results

* `LinearMap.apply_mem_span_image_iff_exists_smul_mem_span`: an injective linear map sends an
  element into the localized span of the image of a set if and only if a multiple of that element
  by a denominator lies in the original span.
-/

public section

namespace LinearMap

variable {A K B L : Type*} [CommSemiring A] [CommSemiring K] [Algebra A K]
  [AddCommMonoid B] [AddCommMonoid L] [Module A B] [Module A L] [Module K L]
  [IsScalarTower A K L]

/-- An injective linear map sends `x` into the span over a localization of the image of `s` if
and only if a multiple of `x` by an element of the localizing submonoid lies in the original span
of `s`. -/
theorem apply_mem_span_image_iff_exists_smul_mem_span {f : B →ₗ[A] L} (hf : Function.Injective f)
    (M : Submonoid A) [IsLocalization M K] {s : Set B} {x : B} :
    f x ∈ Submodule.span K (f '' s) ↔ ∃ a ∈ M, a • x ∈ Submodule.span A s := by
  refine ⟨fun hx ↦ ?_, fun ⟨a, ha, hax⟩ ↦ ?_⟩
  · obtain ⟨⟨a, ha⟩, hax⟩ := multiple_mem_span_of_mem_localization_span M K (f '' s) (f x) hx
    refine ⟨a, ha, (Submodule.apply_mem_span_image_iff_mem_span hf).mp ?_⟩
    simpa only [map_smul, Submonoid.smul_def] using hax
  · have h := Submodule.span_le_restrictScalars A K (f '' s)
      (Submodule.apply_mem_span_image_of_mem_span f hax)
    rw [Submodule.restrictScalars_mem, map_smul, ← algebraMap_smul K a (f x)] at h
    exact (Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units K ⟨a, ha⟩)).mp h

end LinearMap

end
