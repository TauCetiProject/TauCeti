/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Isotypic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Regular

/-!
# Linearly reductive coalgebras are cosemisimple

Over a linearly reductive coalgebra every comodule is the sum of its simple subcomodules, by
`TauCeti.Coalgebra.IsLinearlyReductive.sSup_atoms_eq_top`. Applied to the regular comodule,
this says that a linearly reductive coalgebra is cosemisimple: it is the sum of its simple right
coideals, and hence it is spanned by the matrix coefficients of its simple comodules. Since the
coefficient spaces of the simple right coideals are independent
(`TauCeti.Comodule.sSupIndep_matrixCoefficientSubmodule_image_isAtom`), the coalgebra is their
internal direct sum. For the coordinate Hopf algebra `O(G)` of a linearly reductive affine group,
this is the algebraic Peter--Weyl decomposition of `O(G)` into the coefficient spaces of
irreducible representations; two simple right coideals give the same summand exactly when they
are isomorphic (`TauCeti.Comodule.matrixCoefficientSubmodule_eq_iff`).

## Main declarations

* `TauCeti.Coalgebra.IsLinearlyReductive.iSup_matrixCoefficientSubmodule_eq_top`: **a linearly
  reductive coalgebra is spanned by the matrix coefficients of its simple subcomodules.**
* `TauCeti.Coalgebra.IsLinearlyReductive.isInternal_matrixCoefficientSubmodule`: **a linearly
  reductive coalgebra is the internal direct sum of the coefficient spaces of its simple right
  coideals.**

## References

* M. Sweedler, *Hopf Algebras* (1969), on cosemisimple coalgebras.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 12 (linearly reductive groups).
-/

public section

namespace TauCeti

universe u v

namespace Coalgebra.IsLinearlyReductive

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- **A linearly reductive coalgebra is cosemisimple:** it is spanned by the matrix coefficients
of its simple subcomodules, that is, of its simple right coideals. Each of these is
finite-dimensional by `TauCeti.Subcomodule.finite_of_isAtom`. -/
theorem iSup_matrixCoefficientSubmodule_eq_top (hC : IsLinearlyReductive.{u, v, u} k C) :
    ⨆ (S : Subcomodule k C C) (_ : IsAtom S),
      Comodule.matrixCoefficientSubmodule (R := k) (C := C) (M := S) = ⊤ := by
  rw [eq_top_iff, ← Subcomodule.top_toSubmodule (R := k) (C := C) (M := C),
    ← hC.sSup_atoms_eq_top, Subcomodule.sSup_toSubmodule]
  exact iSup_le fun S ↦
    S.1.toSubmodule_le_matrixCoefficientSubmodule.trans (le_iSup₂_of_le S.1 S.2 le_rfl)

/-- **The algebraic Peter--Weyl decomposition.** A linearly reductive coalgebra is the internal
direct sum of the distinct coefficient spaces of its simple right coideals. -/
theorem isInternal_matrixCoefficientSubmodule (hC : IsLinearlyReductive.{u, v, u} k C) :
    DirectSum.IsInternal fun P : (fun S : Subcomodule k C C ↦
        Comodule.matrixCoefficientSubmodule (R := k) (C := C) (M := S)) '' {S | IsAtom S} ↦
      (P : Submodule k C) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ((sSupIndep_iff _).mp Comodule.sSupIndep_matrixCoefficientSubmodule_image_isAtom) ?_
  rw [← sSup_eq_iSup', sSup_image]
  exact hC.iSup_matrixCoefficientSubmodule_eq_top

end Coalgebra.IsLinearlyReductive

end TauCeti
