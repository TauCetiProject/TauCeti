/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finiteness and clearing denominators under localization

Pulling Mathlib's `multiple_mem_span_of_mem_localization_span` back along an injective linear map
clears denominators in a localized span; conversely, the localizing elements act invertibly on the
localized span, so this characterizes membership in it. This applies to arbitrary spanning sets in
modules, including lifts of a basis along an injective algebra map.

Finiteness of a module is local on `Spec R` (Mathlib's `Module.Finite.of_localizationSpan`). In
the form recorded here, it suffices to find, around every closed point of `Spec R`, a basic open
`D(r)` over which the module is finite.

## Main results

* `LinearMap.apply_mem_span_image_iff_exists_smul_mem_span`: an injective linear map sends an
  element into the localized span of the image of a set if and only if a multiple of that element
  by a denominator lies in the original span.
* `Module.Finite.of_forall_isMaximal_exists_notMem`: a module is finite as soon as every maximal
  ideal `q` avoids some `r` such that the localization `M_r` is a finite `R_r`-module.
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

namespace Module.Finite

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- **Finiteness is local around closed points.** If every maximal ideal `q` of `R` avoids an
element `r` such that the localization `M_r` is a finite `R_r`-module, then `M` is a finite
`R`-module. -/
theorem of_forall_isMaximal_exists_notMem
    (H : ∀ q : Ideal R, q.IsMaximal →
      ∃ r ∉ q, Module.Finite (Localization.Away r) (LocalizedModule.Away r M)) :
    Module.Finite R M := by
  -- The elements `r` with `M_r` finite generate the unit ideal: no maximal ideal contains them.
  refine of_localizationSpan
    {r | Module.Finite (Localization.Away r) (LocalizedModule.Away r M)} ?_ fun r ↦ r.2
  by_contra h
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ h
  obtain ⟨r, hrq, hr⟩ := H q hq
  exact hrq (hle (Ideal.subset_span hr))

end Module.Finite

end
