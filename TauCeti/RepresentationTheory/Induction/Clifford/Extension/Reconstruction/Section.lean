/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Reconstruction.Basic
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Section

/-!
# Section independence of Clifford reconstruction

Transporting a multiplicity action along the opposite-inverse section-change algebra
isomorphism leaves its reconstructed inertia action unchanged. Both actions use the
same right-commutant module and the same balanced tensor product. Thus this is equality
of representations, with no choices of tensor coordinates or scalar-Schur hypothesis.

The extended action of the canonical Clifford group is already independent of the section:
the inverse section difference in a new basis operator cancels the change in its kernel
coordinate. Balanced tensor descent then gives independence of reconstruction, including
for infinite-dimensional multiplicity modules and infinite inertia quotients.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
* The section-change algebra map `FDRep.cliffordMultiplicityAlgebraEquiv` and
  the extension lift `GroupExtension.Section.lift`.
-/

public section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension TauCeti.GroupExtension

attribute [local instance] endModule

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  (s t : (groupExtension A).Section) (hs : s 1 = 1) (ht : t 1 = 1)
  {M : Type w} [AddCommGroup M] [Module k M] [Module (End A)ᵐᵒᵖ M]
  [IsScalarTower k (End A)ᵐᵒᵖ M]
  (U : CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv M)

/-- Transport a multiplicity action from section `s` to section `t` by restricting
its algebra action along the opposite-inverse section-change isomorphism. -/
noncomputable def cliffordReconstructionSectionAction :
    CrossedSystem.SemilinearAction (cliffordCrossedSystem A t ht).opInv M :=
  CrossedSystem.SemilinearAction.ofAlgHom
    (U.toAlgHom.comp (cliffordMultiplicityAlgebraEquiv A s t hs ht).toAlgHom)
    (fun d => by simp)

/-- The new section operator is the old operator followed by inverse right
multiplication by the section difference. -/
@[simp]
theorem cliffordReconstructionSectionAction_operator (q : Quotient A) (m : M) :
    (cliffordReconstructionSectionAction A s t hs ht U).operator q m =
      op (↑(sectionDiff t s q)⁻¹ : End A) • U.operator q m := by
  simp [cliffordReconstructionSectionAction]

/-- The transported action extends to exactly the original algebra action composed
with the section-change map, on every algebra element. -/
@[simp]
theorem cliffordReconstructionSectionAction_toAlgHom :
    (cliffordReconstructionSectionAction A s t hs ht U).toAlgHom =
      U.toAlgHom.comp (cliffordMultiplicityAlgebraEquiv A s t hs ht).toAlgHom := by
  apply CrossedSystem.Algebra.algHom_ext <;> intro x <;>
    simp [cliffordReconstructionSectionAction]

/-- On ordinary crossed-product modules, section transport is restriction of scalars
along the section-change algebra isomorphism, on the original additive carrier. -/
theorem cliffordReconstructionSectionAction_module :
    (cliffordReconstructionSectionAction A s t hs ht U).module =
      letI := U.module
      Module.compHom M (cliffordMultiplicityAlgebraEquiv A s t hs ht).toRingHom := by
  apply Module.ext'
  intro a m
  rw [CrossedSystem.SemilinearAction.module_smul,
    cliffordReconstructionSectionAction_toAlgHom]
  rfl

/-- Transport through a section change does not change the extended action of the
canonical Clifford group. This holds before balanced tensor descent. -/
theorem cliffordReconstructionMultiplicityRepresentation_sectionAction :
    cliffordReconstructionMultiplicityRepresentation A t ht
        (cliffordReconstructionSectionAction A s t hs ht U) =
      cliffordReconstructionMultiplicityRepresentation A s hs U := by
  apply t.hom_ext
  · intro d
    ext m
    simp only [groupExtension_inl, cliffordReconstructionMultiplicityRepresentation_inl]
  · intro q
    ext m
    rw [cliffordReconstructionMultiplicityRepresentation_section,
      cliffordReconstructionSectionAction_operator]
    have hq : t q = inl A (sectionDiff t s q) * s q := by
      simpa only [GroupExtension.Section.gauge_apply, groupExtension_inl] using
        congrArg (fun a : (groupExtension A).Section => a q) (s.gauge_sectionDiff t).symm
    rw [hq, map_mul, mul_apply_eq_comp,
      cliffordReconstructionMultiplicityRepresentation_section,
      cliffordReconstructionMultiplicityRepresentation_inl]

/-- Changing the Clifford section and transporting the multiplicity action along
its algebra isomorphism leaves the entire reconstructed inertia representation equal.
In particular the comparison fixes every balanced pure tensor. -/
theorem cliffordReconstructionRepresentation_sectionAction :
    cliffordReconstructionRepresentation A t ht
        (cliffordReconstructionSectionAction A s t hs ht U) =
      cliffordReconstructionRepresentation A s hs U := by
  apply MonoidHom.ext
  intro g
  obtain ⟨p, rfl⟩ := projection_surjective A g
  apply BalancedTensorProduct.hom_ext
  intro m x
  simp only [cliffordReconstructionRepresentation_projection_tmul,
    cliffordReconstructionMultiplicityRepresentation_sectionAction]

end FDRep
