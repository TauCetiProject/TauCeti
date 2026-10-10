/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sylvester.Bound

/-! # The bounded Sylvester operator

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `df036cd`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).

Moved from
`ForTauCeti/Analysis/InnerProductSpace/SylvesterOperator.lean` to
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Operator.lean`.  The `Sylvester/`
directory already held `Basic`, `Interval`, `SpectralDistance` and `Internal/`, while
six siblings of the same family used a flat `Sylvester*` prefix in the directory above;
one family now has one convention.  Path change and import repoint only — no statement,
signature, proof, attribute, declaration name or namespace changed.
-/

public section


/-! The Sylvester operator is a statement about composition, so it is declared
over normed spaces rather than inner product spaces: nothing here, and nothing
proved about it downstream, uses an inner product.  Consumers that do work in a
Hilbert space are unaffected, since `InnerProductSpace.toNormedSpace` supplies
the instance. -/

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousLinearMap

/-- The Sylvester operator `X ↦ A X - X B`. -/
@[expose]
def sylvesterOperator (A : F →L[𝕜] F) (B : E →L[𝕜] E)
    (X : E →L[𝕜] F) : E →L[𝕜] F :=
  A ∘L X - X ∘L B

/-- The Sylvester operator `X ↦ A X - X B`, bundled as a continuous linear map.

`sylvesterOperator` is its underlying function.  The bundled form is what lets
the Sylvester operator be *called* injective, bounded below, or invertible:
those are statements about an operator, not about a family of values.  It is a
difference of the two one-sided composition maps, each of which is continuous
and linear in `X`. -/
@[expose]
noncomputable def sylvesterOperatorL (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    (E →L[𝕜] F) →L[𝕜] (E →L[𝕜] F) :=
  compL 𝕜 E F F A - (compL 𝕜 E E F).flip B

/-- Applying the bundled Sylvester operator is applying the formula. -/
@[simp]
theorem sylvesterOperatorL_apply (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X : E →L[𝕜] F) :
    sylvesterOperatorL A B X = A ∘L X - X ∘L B :=
  (rfl)

/-- The bundled and unbundled Sylvester operators agree, definitionally.  Stated
so the two cannot drift apart. -/
theorem coe_sylvesterOperatorL (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    ⇑(sylvesterOperatorL A B) = sylvesterOperator A B :=
  rfl

/-- The Sylvester operator sends `0` to `0`. -/
@[simp] theorem sylvesterOperator_zero
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    sylvesterOperator A B (0 : E →L[𝕜] F) = 0 := by
  simp [sylvesterOperator]

/-- The Sylvester operator is additive. -/
theorem sylvesterOperator_add
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X Y : E →L[𝕜] F) :
    sylvesterOperator A B (X + Y) =
      sylvesterOperator A B X + sylvesterOperator A B Y := by
  simp only [sylvesterOperator, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp]
  abel

/-- The Sylvester operator commutes with subtraction. -/
theorem sylvesterOperator_sub
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X Y : E →L[𝕜] F) :
    sylvesterOperator A B (X - Y) =
      sylvesterOperator A B X - sylvesterOperator A B Y := by
  simp only [sylvesterOperator, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp]
  abel

/-- The Sylvester operator is homogeneous. -/
theorem sylvesterOperator_smul
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (c : 𝕜) (X : E →L[𝕜] F) :
    sylvesterOperator A B (c • X) = c • sylvesterOperator A B X := by
  ext x
  simp [sylvesterOperator, smul_sub]

/-- Elementary operator-norm bound. -/
theorem norm_sylvesterOperator_le
    (A : F →L[𝕜] F) (B : E →L[𝕜] E) (X : E →L[𝕜] F) :
    ‖sylvesterOperator A B X‖ ≤ (‖A‖ + ‖B‖) * ‖X‖ := by
  calc
    ‖sylvesterOperator A B X‖ ≤ ‖A ∘L X‖ + ‖X ∘L B‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖X‖ + ‖X‖ * ‖B‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le A X)
        (ContinuousLinearMap.opNorm_comp_le X B)
    _ = (‖A‖ + ‖B‖) * ‖X‖ := by ring

end ContinuousLinearMap
