/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Cyclic quotients separating subgroups of finite abelian groups

If `A < B` are subgroups of a finite abelian group, there is a cyclic quotient in which the
image of `A` is trivial and the image of `B` is nontrivial. Applied to two successive filtration
steps, this detects a strict decrease in a cyclic quotient.

The construction uses Mathlib's character-separation theorem
`CommGroup.forall_monoidHom_apply_eq_one_iff`: a character valued in the units of an
algebraic closure of `ℚ` kills `A` but not an element of `B`. Its finite image is cyclic.
-/

public section

namespace TauCeti

/-- A strict inclusion of subgroups of a finite abelian group is detected by a cyclic quotient:
the smaller subgroup is killed, but the larger one is not. -/
theorem exists_isCyclic_quotient_of_lt {G : Type*} [CommGroup G] [Finite G]
    {A B : Subgroup G} (h : A < B) :
    ∃ H : Subgroup G, A ≤ H ∧ ¬B ≤ H ∧ IsCyclic (G ⧸ H) := by
  classical
  obtain ⟨b, hb, hbA⟩ := IsConcreteLE.exists_of_lt h
  obtain ⟨f, hA, hf⟩ : ∃ f : G →* (AlgebraicClosure ℚ)ˣ,
      (∀ a ∈ A, f a = 1) ∧ f b ≠ 1 := by
    simpa only [not_forall, not_imp, exists_prop] using
      (mt (CommGroup.forall_monoidHom_apply_eq_one_iff (AlgebraicClosure ℚ) A b).1 hbA)
  have hB : ¬B ≤ f.ker := fun hB ↦ hf (hB hb)
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : IsCyclic f.range := inferInstance
  have hcyc : IsCyclic (G ⧸ f.ker) :=
    isCyclic_of_injective (QuotientGroup.quotientKerEquivRange f).toMonoidHom
      (QuotientGroup.quotientKerEquivRange f).injective
  exact ⟨f.ker, fun a ha ↦ hA a ha, hB, hcyc⟩

end TauCeti
