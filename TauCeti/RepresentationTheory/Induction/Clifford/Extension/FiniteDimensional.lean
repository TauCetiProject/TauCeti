/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Reconstruction

/-!
# Finite-dimensional Clifford reconstruction

A finite-dimensional right-commutant multiplicity module reconstructs to a
finite-dimensional representation of the inertia group. If the prescribed
normal-subgroup representation `A` is simple, the converse holds as well, and

`dim_k reconstruction = dim_{End(A)ᵐᵒᵖ} multiplicity * dim_k A`.

The dimension over the full commutant is essential over nonsplitting fields.
No scalar-Schur, Maschke, or finiteness assumption on the inertia quotient is used.
The bundled reconstruction retains the existing action on the balanced tensor,
rather than choosing coordinates or a second action.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace FDRep

open CategoryTheory TauCeti TauCeti.CliffordExtension

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  {M : Type u} [AddCommGroup M] [Module k M] [Module (End A)ᵐᵒᵖ M]
  [IsScalarTower k (End A)ᵐᵒᵖ M] [Module.Finite k M]
  (s : (groupExtension A).Section) (hs : s 1 = 1)
  (U : CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M)

/-- The finite-dimensional inertia representation reconstructed from a finite
right-commutant module with the opposite/inverse Clifford semilinear action.
Simplicity of `A` is not needed. The abbreviation retains the concrete balanced
tensor carrier, so the existing pure-tensor action lemmas apply directly. -/
noncomputable abbrev cliffordReconstructionFDRep : FDRep k (inertia A) :=
  FDRep.of (cliffordReconstructionRepresentation A s hs U)

/-- The dimension of bundled reconstruction over an arbitrary coefficient field. -/
theorem finrank_cliffordReconstructionFDRep [Simple A] :
    Module.finrank k (cliffordReconstructionFDRep A s hs U) =
      Module.finrank (End A)ᵐᵒᵖ M * Module.finrank k A := by
  let : Module.Finite (End A)ᵐᵒᵖ M := Module.Finite.of_restrictScalars_finite k _ _
  exact finrank_balancedTensorProduct A

end FDRep
