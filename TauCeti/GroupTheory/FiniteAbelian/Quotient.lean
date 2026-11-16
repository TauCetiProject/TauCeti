/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Cyclic quotients separating subgroups of abelian groups

If `A` is a subgroup of finite index of an abelian group and `B` is a subgroup not contained in
`A`, there is a cyclic quotient in which the image of `A` is trivial and the image of `B` is
nontrivial. Applied to two successive steps of a filtration of a finite abelian group, this
detects a strict decrease in a cyclic quotient.

The construction uses Mathlib's character-separation theorem
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` for the finite quotient by `A`: a
character valued in the units of an algebraic closure of `ℚ` kills `A` but not an element of
`B`. The quotient by its kernel is finite and embeds in the units of a field, so it is cyclic.
-/

public section

namespace TauCeti

/-- Non-containment of a subgroup of an abelian group in a subgroup of finite index is detected
by a cyclic quotient: if `B` is not contained in the finite-index subgroup `A`, some subgroup `H`
with cyclic quotient contains `A` but not `B`. -/
theorem exists_isCyclic_quotient_of_not_le {G : Type*} [CommGroup G]
    {A B : Subgroup G} [A.FiniteIndex] (h : ¬B ≤ A) :
    ∃ H : Subgroup G, A ≤ H ∧ ¬B ≤ H ∧ IsCyclic (G ⧸ H) := by
  obtain ⟨b, hb, hbA⟩ := IsConcreteLE.not_le_iff_exists.1 h
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G ⧸ A)
    (AlgebraicClosure ℚ) (a := (b : G ⧸ A)) (by rwa [ne_eq, QuotientGroup.eq_one_iff])
  let f : G →* (AlgebraicClosure ℚ)ˣ := φ.comp (QuotientGroup.mk' A)
  have hA : A ≤ f.ker := fun a ha ↦ by
    simp [f, MonoidHom.mem_ker, (QuotientGroup.eq_one_iff a).2 ha]
  have : f.ker.FiniteIndex := Subgroup.finiteIndex_of_le hA
  exact ⟨f.ker, hA, fun hB ↦ hφ (hB hb),
    isCyclic_of_injective_ringHom ((Units.coeHom _).comp (QuotientGroup.kerLift f))
      (Units.val_injective.comp (QuotientGroup.kerLift_injective f))⟩

end TauCeti
