/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# Alternatization of a continuous bilinear map

A continuous bilinear map `B : E →L[𝕜] E →L[𝕜] F` has the alternatization
`(v₀, v₁) ↦ B v₀ v₁ - B v₁ v₀`, a continuous alternating map in two arguments. This file packages
that operation as the continuous linear map `ContinuousAlternatingMap.alternatizeBilinCLM 𝕜 E F`
from bilinear maps to alternating two-forms: `E →L[𝕜] F` is identified with the continuous
alternating maps in one argument and Mathlib's `ContinuousAlternatingMap.alternatizeUncurryFinCLM`
is applied. Being a continuous linear map, the operator transports smoothness, so a smooth family
of bilinear maps has a smooth alternatization. As in Mathlib's `alternatizeUncurryFin`, no factor
`2⁻¹` is built in, so the construction is available over every normed field.

## Main declarations

* `TauCeti.ContinuousAlternatingMap.alternatizeBilinCLM`: the alternatization of continuous
  bilinear maps, as a continuous linear map into the continuous alternating two-forms.
* `TauCeti.ContinuousAlternatingMap.alternatizeBilinCLM_apply`: it evaluates to
  `B (v 0) (v 1) - B (v 1) (v 0)`.
-/

public section

namespace TauCeti

namespace ContinuousAlternatingMap

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The alternatization `B ↦ ((v₀, v₁) ↦ B v₀ v₁ - B v₁ v₀)` of a continuous bilinear map, as a
continuous linear map into the continuous alternating two-forms. It is Mathlib's
`ContinuousAlternatingMap.alternatizeUncurryFinCLM` in one alternating argument, precomposed with
the identification of `E →L[𝕜] F` with the continuous alternating maps in one argument. -/
noncomputable def alternatizeBilinCLM : (E →L[𝕜] E →L[𝕜] F) →L[𝕜] E [⋀^Fin 2]→L[𝕜] F :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F).comp
    (ContinuousLinearMap.compL 𝕜 E (E →L[𝕜] F) (E [⋀^Fin 1]→L[𝕜] F)
      ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := 𝕜) (E := E) (F := F)
        (0 : Fin 1)).toContinuousLinearEquiv : (E →L[𝕜] F) →L[𝕜] E [⋀^Fin 1]→L[𝕜] F))

variable {𝕜 E F}

/-- The alternatization of a continuous bilinear map `B` evaluates on `v : Fin 2 → E` to
`B (v 0) (v 1) - B (v 1) (v 0)`. -/
@[simp]
lemma alternatizeBilinCLM_apply (B : E →L[𝕜] E →L[𝕜] F) (v : Fin 2 → E) :
    alternatizeBilinCLM 𝕜 E F B v = B (v 0) (v 1) - B (v 1) (v 0) := by
  simp [alternatizeBilinCLM, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_two, Fin.removeNth, Fin.succAbove, sub_eq_add_neg]

end ContinuousAlternatingMap

end TauCeti

end
