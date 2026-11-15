/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.Perm.FinThree.Basic
import TauCeti.GroupTheory.Perm.AlternatingCharacter

/-!
# Quotient conjugation action and vanishing extension class for `S₃` over `A₃`

For the normal alternating subgroup `A₃ = alternatingGroup (Fin 3)` of `S₃ = Equiv.Perm (Fin 3)`:

* Under `Subgroup.quotientConjugationAction`, the nontrivial coset of `S₃ ⧸ A₃` acts on `A₃` by
  inversion (`TauCeti.quotientConjugationAction_alternatingGroup_smul_of_ne_one`).
* For any normalized section of `1 → A₃ → S₃ → S₃ ⧸ A₃ → 1`, the factor-set class in
  `H²(S₃ ⧸ A₃, A₃)` vanishes
  (`TauCeti.cohomologyClass_factorSet_alternatingGroup_fin_three_eq_zero`).
-/

public section

open scoped IsMulCommutative

namespace TauCeti

attribute [local instance] Subgroup.quotientConjugationAction

/-- Under `Subgroup.quotientConjugationAction`, the nontrivial coset of `S₃ ⧸ A₃` acts on `A₃`
by inversion, independently of the chosen representative. -/
theorem quotientConjugationAction_alternatingGroup_smul_of_ne_one
    {q : Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)} (hq : q ≠ 1)
    (m : alternatingGroup (Fin 3)) :
    q • m = m⁻¹ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hg : g ∉ alternatingGroup (Fin 3) := by
    rwa [← QuotientGroup.eq_one_iff]
  rw [Subgroup.quotientConjugationAction_mk_smul]
  exact (MonoidHom.id (alternatingGroup (Fin 3))).map_conjNormal_alternatingGroup_eq_inv hg m

/-- For any normalized section of `1 → A₃ → S₃ → S₃ ⧸ A₃ → 1`, the factor-set class in
`H²(S₃ ⧸ A₃, A₃)` vanishes. -/
theorem cohomologyClass_factorSet_alternatingGroup_fin_three_eq_zero
    (σ : (alternatingGroup (Fin 3)).quotientExtension.Section) (hσ : σ 1 = 1) :
    (GroupExtension.factorSet σ hσ
      (alternatingGroup (Fin 3)).quotientExtension_inducesAction).cohomologyClass = 0 :=
  ((alternatingGroup (Fin 3)).exists_complement_iff_cohomologyClass_eq_zero σ hσ).mp
    ⟨_, isComplement'_alternatingGroup_stabilizer_perm_fin_three 0⟩

end TauCeti
