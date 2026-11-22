/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SelfAdjoint
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Borel structure and volume on self-adjoint matrix subspaces

`TauCeti.Analysis.Matrix.SelfAdjoint` equips `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)`
with the ambient Frobenius norm and real inner product. This file adds its Borel measurable
structure, so that the subspace carries `volume` from `measureSpaceOfInnerProductSpace`, and shows
that `Matrix.UnitaryGroup.selfAdjointConj` preserves `volume`.

## Main declarations

* `TauCeti.selfAdjointMatrixBorelSpace`.
* `Matrix.UnitaryGroup.measurePreserving_selfAdjointConj_volume`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti
section instances
variable (p : ℕ) (𝕜 : Type*) [RCLike 𝕜]

attribute [local instance] selfAdjointMatrixNormedAddCommGroup selfAdjointMatrixInnerProductSpace

/-- Borel measurable structure on the self-adjoint matrix subspace over `𝕜`. -/
theorem selfAdjointMatrixBorelSpace [MeasurableSpace 𝕜] [BorelSpace 𝕜] :
    BorelSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)) := Subtype.borelSpace _

namespace SelfAdjointMatrix
attribute [scoped instance] selfAdjointMatrixBorelSpace
end SelfAdjointMatrix
end instances
end TauCeti

open scoped TauCeti.SelfAdjointMatrix

namespace Matrix.UnitaryGroup

/-- Unitary conjugation preserves Frobenius `volume` on the self-adjoint matrix subspace. -/
theorem measurePreserving_selfAdjointConj_volume {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace 𝕜]
    [BorelSpace 𝕜] {p : ℕ} (U : Matrix.unitaryGroup (Fin p) 𝕜) :
    MeasurePreserving (selfAdjointConj U) volume volume := (selfAdjointConj U).measurePreserving

end Matrix.UnitaryGroup
