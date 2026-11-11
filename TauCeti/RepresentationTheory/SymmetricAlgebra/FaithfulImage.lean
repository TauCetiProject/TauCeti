/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quotient
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic
import TauCeti.RepresentationTheory.Dual

/-!
# Polynomial invariants of a faithful quotient

Removing a normal subgroup acting trivially does not change the invariant subalgebra of the
symmetric algebra, including its grading. This applies both to a representation and to its
contragredient action on polynomial functions. In particular, the faithful representation of
`G ⧸ ker ρ` has exactly the original polynomial invariants. The kernel acts trivially even on
the entire polynomial algebra, not just on its invariant subalgebra.
-/

public section

namespace Representation

variable {R G M : Type*} [CommSemiring R] [Group G] [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M) (S : Subgroup G) [S.Normal] [IsTrivial (ρ.comp S.subtype)]

/-- Removing a trivially acting normal subgroup preserves the invariant subalgebra of `Sym M`,
as a subalgebra of the same ambient graded algebra. -/
@[simp]
theorem symmetricAlgebraInvariants_ofQuotient :
    (ρ.ofQuotient S).symmetricAlgebraInvariants = ρ.symmetricAlgebraInvariants := by
  exact ((ρ.ofQuotient S).symmetricAlgebraInvariants_comp_of_surjective _
    (QuotientGroup.mk'_surjective S)).symm.trans
      (congrArg symmetricAlgebraInvariants (ρ.ofQuotient_comp_mk' S))

/-- Removing a trivially acting normal subgroup preserves the polynomial invariant algebra
`Sym(M*)^G`, with its original coefficient and dual-module structures and its grading. -/
@[simp]
theorem symmetricAlgebraInvariants_dual_ofQuotient :
    (ρ.ofQuotient S).dual.symmetricAlgebraInvariants = ρ.dual.symmetricAlgebraInvariants := by
  have h : (ρ.ofQuotient S).dual.comp (QuotientGroup.mk' S) = ρ.dual := by
    rw [← dual_comp, ρ.ofQuotient_comp_mk']
  exact ((ρ.ofQuotient S).dual.symmetricAlgebraInvariants_comp_of_surjective _
    (QuotientGroup.mk'_surjective S)).symm.trans (congrArg symmetricAlgebraInvariants h)

end Representation
