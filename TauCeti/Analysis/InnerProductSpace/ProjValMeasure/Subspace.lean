/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The range of a projection-valued measure, as a subspace

For a `TauCeti.ProjValMeasure` and a measurable set, the range of the attached
projection, packaged as a submodule, together with the membership and
idempotence facts that make it usable.

**Moved here from `DavisKahan/SpectralTheory/PVMSubspace.lean` on 2026-07-31.**
Its docstring said the declarations *intentionally live in the DKPS bridge
namespace*, and that was true when they were adapters over `Spectra.ProjValMeasure`
from outside.  The structure was repointed to `TauCeti.ProjValMeasure` on
2026-07-28 and now lives in this directory, so the adapters sit beside the thing
they adapt rather than in a bridge that no longer bridges anything.

## Provenance

* **Original repository:** Davis--Kahan/DKPS formalization (Kitware, Inc.).
* **Original module:** `DavisKahan/SpectralTheory/PVMSubspace.lean`, moved here on
  2026-07-31 when the structure it adapts had already been repointed from
  `Spectra.ProjValMeasure` to `TauCeti.ProjValMeasure` (2026-07-28).
* **Original authors / copyright / licence:** Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* **Extraction class:** *moved, not restated.*  No statement, signature, proof,
  attribute, declaration name or namespace changed; the move is a file boundary
  and the imports it forces.
* **Spectra influence:** none remaining.  The declarations were adapters over
  `Spectra.ProjValMeasure` when they were written; the structure underneath is
  `TauCeti`'s own, and the `ForTauCeti` import firewall admits only Mathlib,
  `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The range of a measurable projection from a Spectra projection-valued
measure, packaged as a submodule. -/
@[expose]
noncomputable def pvmRangeSubspace (P : TauCeti.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) : Submodule ℂ H :=
  (P.proj B hB).range

/-- The subspace attached to a projection-valued measure is the range of its projection. -/
@[simp]
theorem pvmRangeSubspace_eq_range (P : TauCeti.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    pvmRangeSubspace P B hB = (P.proj B hB).range :=
  rfl

/-- Every projected vector belongs to the corresponding range subspace. -/
theorem pvmProjection_mem_rangeSubspace (P : TauCeti.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    P.proj B hB x ∈ pvmRangeSubspace P B hB := by
  exact ⟨x, rfl⟩

/-- A vector in the range of a PVM projection is fixed by that projection. -/
theorem pvmProjection_eq_self_of_mem_rangeSubspace
    (P : TauCeti.ProjValMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) {x : H}
    (hx : x ∈ pvmRangeSubspace P B hB) :
    P.proj B hB x = x := by
  rcases hx with ⟨y, rfl⟩
  change P.proj B hB (P.proj B hB y) = P.proj B hB y
  simpa only [mul_apply_eq_comp] using
    congrArg (fun T : H →L[ℂ] H => T y) (P.proj_idem B hB)

/-- Membership in a PVM range is equivalent to being fixed by the
projection. -/
theorem mem_pvmRangeSubspace_iff (P : TauCeti.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    x ∈ pvmRangeSubspace P B hB ↔ P.proj B hB x = x := by
  constructor
  · exact pvmProjection_eq_self_of_mem_rangeSubspace P B hB
  · intro hx
    exact ⟨x, hx⟩

/-- The range of a measurable PVM projection is complete. -/
noncomputable instance pvmRangeSubspace_completeSpace
    (P : TauCeti.ProjValMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) :
    CompleteSpace (pvmRangeSubspace P B hB) := by
  change CompleteSpace (P.proj B hB).range
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (P.proj_idem B hB)).completeSpace_coe

/-- The range of a measurable PVM projection admits an orthogonal
projection. -/
noncomputable instance pvmRangeSubspace_hasOrthogonalProjection
    (P : TauCeti.ProjValMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) :
    (pvmRangeSubspace P B hB).HasOrthogonalProjection := by
  change (P.proj B hB).range.HasOrthogonalProjection
  exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (show IsIdempotentElem (P.proj B hB) from P.proj_idem B hB)

/-- The PVM projection is the Mathlib star projection onto its range. -/
theorem pvmProjection_eq_starProjection_rangeSubspace
    (P : TauCeti.ProjValMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) :
    P.proj B hB = (pvmRangeSubspace P B hB).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact pvmProjection_mem_rangeSubspace P B hB x
  · intro y hy
    have hyfix : P.proj B hB y = y :=
      pvmProjection_eq_self_of_mem_rangeSubspace P B hB hy
    rw [← hyfix]
    have hadj := ContinuousLinearMap.adjoint_inner_right
      (P.proj B hB) (x - P.proj B hB x) y
    rw [← ContinuousLinearMap.star_eq_adjoint,
      (P.isSelfAdjoint_proj B hB).star_eq] at hadj
    rw [hadj, map_sub,
      pvmProjection_eq_self_of_mem_rangeSubspace P B hB
        (pvmProjection_mem_rangeSubspace P B hB x), sub_self, inner_zero_left]

end TauCeti
