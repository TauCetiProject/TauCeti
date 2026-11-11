/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Cosemisimple
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Isotypic
public import Mathlib.Algebra.DirectSum.Module

/-!
# The simple coefficient decomposition of a linearly reductive coalgebra

A linearly reductive coalgebra over a field is the internal direct sum of its distinct
simple coefficient spaces. No algebraic-closure assumption is needed: over a nonsplit
field these are the actual coefficient spaces, not tensors over a presumed scalar
endomorphism ring. The index consists of subspaces, so isomorphic simple comodules do
not contribute duplicate summands.

Spanning comes from the finite-dimensional simple right coideals of the regular
comodule. Independence follows by identifying coefficient spaces with the isotypic
components for the convolution dual. For a coordinate Hopf algebra this is the
coefficient-block decomposition of the algebraic regular representation.

## References

* M. Sweedler, *Hopf Algebras* (1969), cosemisimple coalgebras.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 12.
-/

public noncomputable section

namespace TauCeti.Coalgebra.IsLinearlyReductive

universe u v

variable {k : Type u} [Field k]
  {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]

attribute [local instance] Comodule.convolutionModule

/-- A linearly reductive coalgebra is spanned by its distinct simple coefficient spaces. -/
theorem sSup_simpleCoefficientSubmodules_eq_top (hC : IsLinearlyReductive.{u, v, u} k C) :
    sSup (Comodule.simpleCoefficientSubmodules k C) = ⊤ := by
  rw [eq_top_iff, ← hC.iSup_matrixCoefficientSubmodule_eq_top]
  refine iSup_le fun S ↦ iSup_le fun hS ↦ ?_
  have : IsSimpleModule (WithConv (C →ₗ[k] k)) S :=
    S.isSimpleModule_convolution_iff_isAtom.mpr hS
  have : IsSimpleOrder (Subcomodule k C S) :=
    Comodule.isSimpleModule_convolution_iff.mp inferInstance
  exact le_sSup Comodule.matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules

/-- The distinct simple coefficient spaces give an internal direct sum decomposition
of a linearly reductive coalgebra, over an arbitrary field. -/
theorem isInternal_simpleCoefficientSubmodules (hC : IsLinearlyReductive.{u, v, u} k C) :
    DirectSum.IsInternal
      (fun P : Comodule.simpleCoefficientSubmodules k C ↦ (P.1 : Submodule k C)) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (sSupIndep_iff _).mp Comodule.sSupIndep_simpleCoefficientSubmodules
  · rw [← sSup_eq_iSup', hC.sSup_simpleCoefficientSubmodules_eq_top]

end TauCeti.Coalgebra.IsLinearlyReductive
