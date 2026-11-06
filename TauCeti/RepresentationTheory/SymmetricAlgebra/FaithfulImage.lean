/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quotient
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic

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
theorem symmetricAlgebraInvariants_ofQuotient :
    (ρ.ofQuotient S).symmetricAlgebraInvariants = ρ.symmetricAlgebraInvariants := by
  have h : (ρ.ofQuotient S).comp (QuotientGroup.mk' S) = ρ := by
    ext g x
    simp
  exact ((ρ.ofQuotient S).symmetricAlgebraInvariants_comp_of_surjective _
    (QuotientGroup.mk'_surjective S)).symm.trans (congrArg symmetricAlgebraInvariants h)

/-- Removing a trivially acting normal subgroup preserves the polynomial invariant algebra
`Sym(M*)^G`, with its original coefficient and dual-module structures and its grading. -/
theorem symmetricAlgebraInvariants_dual_ofQuotient :
    (ρ.ofQuotient S).dual.symmetricAlgebraInvariants = ρ.dual.symmetricAlgebraInvariants := by
  have h : (ρ.ofQuotient S).dual.comp (QuotientGroup.mk' S) = ρ.dual := by
    ext g ℓ x
    simp [dual_apply, ← QuotientGroup.mk_inv, Module.Dual.transpose_apply]
  exact ((ρ.ofQuotient S).dual.symmetricAlgebraInvariants_comp_of_surjective _
    (QuotientGroup.mk'_surjective S)).symm.trans (congrArg symmetricAlgebraInvariants h)

/-- The kernel of the original representation acts trivially on every polynomial function.
Thus its action on the invariant algebra is also trivial. -/
theorem symmetricAlgebra_dual_apply_of_mem_ker {g : G} (hg : g ∈ ρ.ker)
    (p : SymmetricAlgebra R (Module.Dual R M)) : ρ.dual.symmetricAlgebra g p = p := by
  have hinv : ρ g⁻¹ = 1 := ρ.ker.inv_mem hg
  have hdual : ρ.dual g = 1 := by
    ext ℓ x
    simp [dual_apply, hinv, Module.End.one_eq_id, Module.Dual.transpose_apply]
  have hg' : g ∈ ρ.dual.symmetricAlgebra.ker := by
    rw [ker_symmetricAlgebra]
    exact hdual
  exact LinearMap.congr_fun hg' p

end Representation
