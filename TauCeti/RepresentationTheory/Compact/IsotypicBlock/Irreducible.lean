/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.TraceCoefficient.Basic

/-!
# Irreducibility of the Peter-Weyl blocks

Each Peter-Weyl block is an irreducible representation of `G × G` under left and right
translation. The trace-coefficient equivalence identifies this action with the two-sided
endomorphism action of its irreducible model. Thus the summands of the equivariant Peter-Weyl
Hilbert sum are themselves irreducible, even for infinite compact groups.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Chapter III.
* `TauCeti.biLinHomEquivPeterWeylBlock`: the equivariant trace-coefficient comparison.
-/

public section

namespace TauCeti

variable {𝕜 G : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The Peter-Weyl block of an irreducible model is irreducible for the biregular action of
`G × G`. This does not require a skeleton of the unitary dual or finiteness of `G`. -/
theorem isIrreducible_peterWeylBlockRep (model : IrrepModel 𝕜 G) :
    (peterWeylBlockRep model).toRepresentation.IsIrreducible := by
  let e := biLinHomEquivPeterWeylBlock model
  apply Representation.isIrreducible_of_linearEquiv e.toContinuousLinearEquiv.toLinearEquiv
    (ρ := (model.rep.biLinHom model.rep).toRepresentation)
  · intro p T
    exact congr($(e.isIntertwining p) T)
  · exact _root_.ContRepresentation.isIrreducible_biLinHom model.rep model.rep
      model.isIrreducible model.isIrreducible

end TauCeti
