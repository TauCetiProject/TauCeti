/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Cyclic quotients separating subgroups of finite abelian groups

If `A < B` are subgroups of a finite abelian group, there is a cyclic quotient in which the
image of `A` is trivial and the image of `B` is nontrivial. Applied to two successive filtration
steps, this detects a strict decrease in a cyclic quotient.

The construction uses Mathlib's finite abelian structure theorem
`CommGroup.equiv_prod_multiplicative_zmod_of_finite` on `G / A`: a nonidentity element has a
nonidentity coordinate in one of the cyclic factors.
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
  have hbq : (QuotientGroup.mk' A) b ≠ 1 := by
    intro heq
    exact hbA ((QuotientGroup.eq_one_iff b).1 heq)
  obtain ⟨ι, _, n, _, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite (G ⧸ A)
  obtain ⟨i, hi⟩ : ∃ i, e ((QuotientGroup.mk' A) b) i ≠ 1 := by
    by_contra! heq
    apply hbq
    apply e.injective
    exact funext fun j ↦ (heq j).trans (congrFun (map_one e) j).symm
  let f : G →* Multiplicative (ZMod (n i)) :=
    ((Pi.evalMonoidHom (fun j ↦ Multiplicative (ZMod (n j))) i).comp e.toMonoidHom).comp
      (QuotientGroup.mk' A)
  have hf : f b ≠ 1 := hi
  have hA : A ≤ f.ker := by
    intro a ha
    simp [f, (QuotientGroup.eq_one_iff a).2 ha]
  have hB : ¬B ≤ f.ker := fun hB ↦ hf (hB hb)
  have : IsCyclic f.range := inferInstance
  have hcyc : IsCyclic (G ⧸ f.ker) :=
    isCyclic_of_injective (QuotientGroup.quotientKerEquivRange f).toMonoidHom
      (QuotientGroup.quotientKerEquivRange f).injective
  exact ⟨f.ker, hA, hB, hcyc⟩

end TauCeti
