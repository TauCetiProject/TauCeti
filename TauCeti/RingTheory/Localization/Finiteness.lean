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
clears denominators in a localized span. This applies to arbitrary spanning sets in modules,
including lifts of a basis along an injective algebra map.

## Main results

* `LinearMap.exists_smul_mem_span_of_apply_mem_span_image`: if an injective linear map sends an
  element into the localized span of the image of a set, a multiple of that element by a
  denominator lies in the original span.
-/

public section

namespace LinearMap

variable {A K B L : Type*} [CommSemiring A] [CommSemiring K] [Algebra A K]
  [AddCommMonoid B] [AddCommMonoid L] [Module A B] [Module A L] [Module K L]
  [IsScalarTower A K L]

/-- If an injective linear map sends `x` into the span over a localization of the image of `s`,
then a multiple of `x` by an element of the localizing submonoid lies in the original span
of `s`. -/
theorem exists_smul_mem_span_of_apply_mem_span_image (f : B →ₗ[A] L) (hf : Function.Injective f)
    (M : Submonoid A) [IsLocalization M K] (s : Set B) (x : B)
    (hx : f x ∈ Submodule.span K (f '' s)) :
    ∃ a ∈ M, a • x ∈ Submodule.span A s := by
  obtain ⟨⟨a, ha⟩, hax⟩ := multiple_mem_span_of_mem_localization_span M K (f '' s) (f x) hx
  refine ⟨a, ha, (Submodule.apply_mem_span_image_iff_mem_span hf).mp ?_⟩
  simpa only [map_smul, Submonoid.smul_def] using hax

end LinearMap

end
