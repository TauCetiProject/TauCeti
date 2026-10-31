/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Analysis.Normed.Operator.DunfordPettis.Basic
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact

/-!
# The Dunford–Pettis property of reflexive spaces

A reflexive space has the Dunford–Pettis property only when it is finite-dimensional. On a
reflexive space the identity is weakly compact, so under the Dunford–Pettis property it maps the
weakly compact closed unit ball to a norm-compact set, and Riesz's theorem applies. Conversely,
every operator out of a finite-dimensional space is compact, hence Dunford–Pettis.

Since Hilbert spaces are uniformly convex, and hence reflexive by the Milman–Pettis theorem, an
infinite-dimensional Hilbert space does not have the Dunford–Pettis property. Together with `c₀`
(`ZeroAtInftyContinuousMap.hasDunfordPettisProperty`) and `ℓ¹`
(`lp.hasDunfordPettisProperty_one`), which do, this separates the property from reflexivity.

## Main results

* `TauCeti.hasDunfordPettisProperty_of_finiteDimensional`: a finite-dimensional space has the
  Dunford–Pettis property.
* `TauCeti.hasDunfordPettisProperty_iff_finiteDimensional`: a reflexive space has the
  Dunford–Pettis property iff it is finite-dimensional.
* `TauCeti.hasDunfordPettisProperty_iff_finiteDimensional_of_innerProductSpace`: a Hilbert space
  has the Dunford–Pettis property iff it is finite-dimensional.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §5.4.
-/

public section

open Function Metric NormedSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A finite-dimensional normed space has the Dunford–Pettis property: every operator out of it is
compact. -/
theorem hasDunfordPettisProperty_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    HasDunfordPettisProperty 𝕜 E := by
  have := FiniteDimensional.proper_rclike 𝕜 E
  exact hasDunfordPettisProperty_def.2 fun _ _ _ _ T _ ↦
    (isCompactOperator_of_locallyCompactSpace_rng T).isDunfordPettis

/-- A reflexive normed space has the Dunford–Pettis property iff it is finite-dimensional. -/
theorem hasDunfordPettisProperty_iff_finiteDimensional
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) :
    HasDunfordPettisProperty 𝕜 E ↔ FiniteDimensional 𝕜 E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ hasDunfordPettisProperty_of_finiteDimensional⟩
  -- The identity is weakly compact, hence Dunford–Pettis, so it maps the weakly compact closed
  -- unit ball to a norm-compact set.
  have hid := ContinuousLinearMap.isWeaklyCompact_id_iff.2 hE
  have hball := ContinuousLinearMap.isDunfordPettis_iff_forall_isCompact_image.1
    (h.isDunfordPettis hid) (closedBall 0 1)
    (surjective_inclusionInDoubleDual_iff_isCompact_toWeakSpace_closedBall.1 hE)
  exact FiniteDimensional.of_isCompact_closedBall₀ 𝕜 one_pos (by simpa using hball)

/-- A Hilbert space has the Dunford–Pettis property iff it is finite-dimensional. In particular an
infinite-dimensional Hilbert space does not have the Dunford–Pettis property. -/
theorem hasDunfordPettisProperty_iff_finiteDimensional_of_innerProductSpace {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] :
    HasDunfordPettisProperty 𝕜 H ↔ FiniteDimensional 𝕜 H := by
  -- A Hilbert space is uniformly convex, hence reflexive by the Milman–Pettis theorem.
  let : NormedSpace ℝ H := .restrictScalars ℝ 𝕜 H
  have := InnerProductSpace.toInnerProductSpaceable 𝕜 (E := H)
  exact hasDunfordPettisProperty_iff_finiteDimensional
    surjective_inclusionInDoubleDual_of_uniformConvexSpace

end TauCeti
