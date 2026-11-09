/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Action
public import TauCeti.GroupTheory.GroupExtension.Cohomology

/-!
# Complements and the class of the quotient extension

An abelian normal subgroup `N` of `G` has a complement exactly when the class of the
quotient extension in `H²(G ⧸ N, N)` vanishes. The coefficient action is conjugation,
not an arbitrary action on `N`. No finiteness assumption on `G` is needed.

The class is presented by the factor set of any normalized section; its independence
of that section is `TauCeti.GroupExtension.cohomologyClass_factorSet_eq`. The comparison
uses `Subgroup.quotientSplittingEquiv` and the splitting criterion
`TauCeti.FactorSet.nonempty_splitting_iff_cohomologyClass_eq_zero` for factor sets.

For the extension-class interpretation, see K. S. Brown, *Cohomology of Groups*,
Chapter IV, §3.
-/

public section

namespace Subgroup

open scoped IsMulCommutative

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [IsMulCommutative N]

attribute [local instance] quotientConjugationAction

/-- An abelian normal subgroup has a complement if and only if the class of its quotient
extension vanishes, for the quotient conjugation action and any normalized section. -/
theorem exists_complement_iff_cohomologyClass_eq_zero
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (∃ D : Subgroup G, N.IsComplement' D) ↔
      (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
        0 := by
  rw [N.exists_isComplement'_iff_nonempty_splitting_quotientExtension]
  exact (TauCeti.GroupExtension.factorSetToGroupExtensionEquiv σ hσ
    N.quotientExtension_inducesAction).nonempty_splitting_iff.symm.trans
      TauCeti.FactorSet.nonempty_splitting_iff_cohomologyClass_eq_zero

end Subgroup
