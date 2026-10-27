/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.OuterAut
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Commutant

/-!
# The canonical outer action on a Clifford commutant

Let `A` be a representation of a normal subgroup `N`, with inertia group `T`.
The canonical Clifford group acts on `CategoryTheory.End A` by algebra
automorphisms. Kernel units act by inner conjugation, so this action descends to
a canonical homomorphism from `T/N` to the outer algebra automorphism group.

Every choice of a section of the Clifford extension recovers this same outer
action. Thus the automorphisms in its noncommutative crossed system determine
an action modulo inner automorphisms, without requiring them to form an action
before passage to the quotient. For a simple representation over a field the
endomorphism algebra is the actual Schur division algebra; no scalar-Schur
assumption is imposed here.

## References

G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985).
-/

public section

namespace FDRep

open CategoryTheory TauCeti TauCeti.CliffordExtension

universe u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)

/-- The commutant action of a kernel unit is an inner algebra automorphism. -/
theorem commutantAction_inl_mem_innerAlgAut (d : (End A)ˣ) :
    commutantAction (inl A d) ∈ innerAlgAut k (End A) := by
  refine (mem_innerAlgAut_iff k (End A) _).mpr ⟨d, fun f ↦ ?_⟩
  simp

section Field

variable {K : Type u} [Field K] (A : FDRep K N)

private theorem ker_rightHom_le_cliffordOuterAction_ker :
    (rightHom A).ker ≤
      ((QuotientGroup.mk' (innerAlgAut K (End A))).comp commutantAction).ker := by
  rw [← range_inl_eq_ker_rightHom]
  rintro _ ⟨d, rfl⟩
  exact (QuotientGroup.eq_one_iff _).mpr (commutantAction_inl_mem_innerAlgAut A d)

/-- The canonical action of the inertia quotient on the commutant modulo inner automorphisms. -/
noncomputable def cliffordOuterAction : Quotient A →* OuterAlgAut K (End A) :=
  (rightHom A).liftOfSurjective (rightHom_surjective A)
    ⟨(QuotientGroup.mk' (innerAlgAut K (End A))).comp commutantAction,
      ker_rightHom_le_cliffordOuterAction_ker A⟩

/-- The outer action pulls back to the given Clifford commutant action modulo inner conjugation. -/
@[simp]
theorem cliffordOuterAction_rightHom (c : Carrier A) :
    cliffordOuterAction A (rightHom A c) = QuotientGroup.mk (commutantAction c) :=
  (rightHom A).liftOfRightInverse_comp_apply _ _ _ c

/-- The action on an inertia class is represented by conjugation by any implementing operator. -/
@[simp]
theorem cliffordOuterAction_mk (p : implementers A) :
    cliffordOuterAction A (QuotientGroup.mk p.1.1) = QuotientGroup.mk (implementerConj p) := by
  simpa only [rightHom_mk, commutantAction_mk] using
    cliffordOuterAction_rightHom A (QuotientGroup.mk p : Carrier A)

/-- Any section of the Clifford extension represents the canonical outer action. -/
theorem cliffordOuterAction_section (s : (groupExtension A).Section) (q : Quotient A) :
    cliffordOuterAction A q = QuotientGroup.mk (commutantAction (s q)) := by
  have hq : rightHom A (s q) = q := by
    simpa only [groupExtension_rightHom] using s.rightHom_section q
  exact (congrArg (cliffordOuterAction A) hq).symm.trans (cliffordOuterAction_rightHom A (s q))

/-- Two sections induce the same automorphisms modulo inner conjugation. -/
theorem mk_commutantAction_section_eq (s t : (groupExtension A).Section) (q : Quotient A) :
    (QuotientGroup.mk (commutantAction (s q)) : OuterAlgAut K (End A)) =
      QuotientGroup.mk (commutantAction (t q)) := by
  rw [← cliffordOuterAction_section A s q, ← cliffordOuterAction_section A t q]

/-- The pullback along the canonical Clifford projection uniquely determines the outer action. -/
theorem cliffordOuterAction_unique (f : Quotient A →* OuterAlgAut K (End A))
    (hf : ∀ c : Carrier A, f (rightHom A c) = QuotientGroup.mk (commutantAction c)) :
    f = cliffordOuterAction A := by
  apply MonoidHom.ext
  intro q
  obtain ⟨c, rfl⟩ := rightHom_surjective A q
  rw [hf, cliffordOuterAction_rightHom]

end Field

end FDRep
