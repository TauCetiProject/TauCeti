/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.Conj
public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Commutant

/-!
# Changing the representation in a Clifford extension

An isomorphism `e : A ≅ B` of representations of a normal subgroup transports an
implementing pair `(t, U)` to `(t, e U e⁻¹)`. It identifies the diagonal copies of the
normal subgroup and hence induces an isomorphism of the canonical Clifford groups.
The resulting maps preserve both the inclusion of commutant units and the projection
to the inertia quotient. They also intertwine the actions on the full endomorphism
algebras. Thus the Clifford extension and its commutant action depend on the
representation only up to isomorphism, including over nonsplitting fields.

The construction uses Mathlib's `QuotientGroup.congr` and `CategoryTheory.Iso.conj`.

## References

G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985).
-/

public section

namespace CategoryTheory.Iso

open TauCeti TauCeti.CliffordExtension

universe u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]
  {N : Subgroup G} [N.Normal] {A B C : FDRep k N}

private noncomputable def implementersMap (e : A ≅ B) : implementers A →* implementers B where
  toFun p := ⟨(MulEquiv.subgroupCongr (inertia_congr e) p.1.1,
    (FDRep.isoToLinearEquiv e).symm.trans (p.1.2.trans (FDRep.isoToLinearEquiv e))), by
    rw [mem_implementers_iff]
    intro n x
    simpa [FDRep.Iso.conj_ρ e, LinearEquiv.conj_apply] using
      congrArg (FDRep.isoToLinearEquiv e)
        ((mem_implementers_iff A _).mp p.2 n ((FDRep.isoToLinearEquiv e).symm x))⟩
  map_one' := by
    ext <;> simp
  map_mul' p q := by
    ext <;> simp

/-- Isomorphic normal-subgroup representations have isomorphic groups of implementing pairs. -/
noncomputable def cliffordImplementersEquiv (e : A ≅ B) : implementers A ≃* implementers B where
  __ := implementersMap e
  invFun := implementersMap e.symm
  left_inv p := by
    ext <;> simp [implementersMap]
  right_inv p := by
    ext <;> simp [implementersMap]

/-- Transport preserves the underlying inertia element. -/
@[simp]
theorem cliffordImplementersEquiv_fst (e : A ≅ B) (p : implementers A) :
    ((e.cliffordImplementersEquiv p).1.1 : G) = (p.1.1 : G) := (rfl)

/-- The transported implementing operator is conjugation by the given linear equivalence. -/
@[simp]
theorem cliffordImplementersEquiv_snd_apply (e : A ≅ B) (p : implementers A) (x : B) :
    (e.cliffordImplementersEquiv p).1.2 x =
      FDRep.isoToLinearEquiv e (p.1.2 ((FDRep.isoToLinearEquiv e).symm x)) := (rfl)

/-- The inverse of a transported implementing operator is the conjugated inverse. -/
@[simp]
theorem cliffordImplementersEquiv_snd_symm_apply (e : A ≅ B) (p : implementers A) (x : B) :
    (e.cliffordImplementersEquiv p).1.2.symm x =
      FDRep.isoToLinearEquiv e (p.1.2.symm ((FDRep.isoToLinearEquiv e).symm x)) := (rfl)

/-- Transport by the identity leaves implementing pairs unchanged. -/
@[simp]
theorem refl_cliffordImplementersEquiv :
    (Iso.refl A).cliffordImplementersEquiv = MulEquiv.refl (implementers A) := by
  apply MulEquiv.ext
  intro p
  ext <;> simp

/-- Transport of implementing pairs respects composition of representation isomorphisms. -/
@[simp]
theorem trans_cliffordImplementersEquiv (e : A ≅ B) (f : B ≅ C) :
    (e ≪≫ f).cliffordImplementersEquiv =
      e.cliffordImplementersEquiv.trans f.cliffordImplementersEquiv := by
  apply MulEquiv.ext
  intro p
  ext <;> simp

/-- The inverse transport is given by the inverse representation isomorphism. -/
@[simp]
theorem symm_cliffordImplementersEquiv (e : A ≅ B) :
    e.symm.cliffordImplementersEquiv = e.cliffordImplementersEquiv.symm := by
  apply MulEquiv.ext
  intro p
  rfl

/-- The diagonal normal-subgroup action is preserved by transport. -/
@[simp]
theorem cliffordImplementersEquiv_diagonal (e : A ≅ B) (n : N) :
    e.cliffordImplementersEquiv (diagonal A n) = diagonal B n := by
  apply implementers.ext
  · simp
  · intro x
    simpa [cliffordImplementersEquiv_snd_apply] using
      LinearMap.congr_fun (FDRep.Iso.conj_ρ e n) x |>.symm

private theorem map_diagonal_range (e : A ≅ B) :
    (diagonal A).range.map e.cliffordImplementersEquiv = (diagonal B).range := by
  rw [MonoidHom.map_range]
  congr 1
  apply MonoidHom.ext
  intro n
  exact cliffordImplementersEquiv_diagonal e n

/-- An isomorphism of normal-subgroup representations identifies their canonical Clifford groups. -/
noncomputable def cliffordExtensionEquiv (e : A ≅ B) : Carrier A ≃* Carrier B :=
  QuotientGroup.congr _ _ e.cliffordImplementersEquiv (map_diagonal_range e)

/-- Transport of a Clifford class is represented by the conjugated implementing pair. -/
@[simp]
theorem cliffordExtensionEquiv_mk (e : A ≅ B) (p : implementers A) :
    e.cliffordExtensionEquiv (QuotientGroup.mk p) =
      QuotientGroup.mk (e.cliffordImplementersEquiv p) := (rfl)

/-- The identity representation isomorphism induces the identity Clifford isomorphism. -/
@[simp]
theorem refl_cliffordExtensionEquiv :
    (Iso.refl A).cliffordExtensionEquiv = MulEquiv.refl (Carrier A) := by
  apply MulEquiv.ext
  intro c
  refine QuotientGroup.induction_on c fun p ↦ ?_
  simp only [cliffordExtensionEquiv_mk, refl_cliffordImplementersEquiv, MulEquiv.refl_apply]
  -- The remaining constructors are the same quotient map, viewed in Carrier A and its definition.
  rfl

/-- Clifford transport respects composition of representation isomorphisms. -/
@[simp]
theorem trans_cliffordExtensionEquiv (e : A ≅ B) (f : B ≅ C) :
    (e ≪≫ f).cliffordExtensionEquiv = e.cliffordExtensionEquiv.trans f.cliffordExtensionEquiv := by
  apply MulEquiv.ext
  intro c
  rw [MulEquiv.trans_apply]
  refine QuotientGroup.induction_on c fun p ↦ ?_
  simp only [cliffordExtensionEquiv_mk, trans_cliffordImplementersEquiv, MulEquiv.trans_apply]
  -- Carrier C and its defining quotient have the same quotient constructor.
  rfl

/-- The inverse representation isomorphism induces the inverse Clifford isomorphism. -/
@[simp]
theorem symm_cliffordExtensionEquiv (e : A ≅ B) :
    e.symm.cliffordExtensionEquiv = e.cliffordExtensionEquiv.symm := by
  apply MulEquiv.ext
  intro c
  apply e.cliffordExtensionEquiv.injective
  have h := DFunLike.congr_fun (trans_cliffordExtensionEquiv e.symm e) c
  simpa using h.symm

/-- Isomorphic representations have canonically identified inertia quotients. -/
noncomputable def cliffordExtensionQuotientEquiv (e : A ≅ B) :
    CliffordExtension.Quotient A ≃* CliffordExtension.Quotient B :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (inertia_congr e)) (by
    rw [Subgroup.map_equiv_eq_comap_symm]
    ext t
    simp [Subgroup.mem_comap, Subgroup.mem_subgroupOf])

/-- The induced inertia quotient map keeps the underlying group element. -/
@[simp]
theorem cliffordExtensionQuotientEquiv_mk (e : A ≅ B) (t : inertia A) :
    e.cliffordExtensionQuotientEquiv (QuotientGroup.mk t) =
      QuotientGroup.mk (MulEquiv.subgroupCongr (inertia_congr e) t) := (rfl)

/-- The identity representation isomorphism induces the identity inertia quotient isomorphism. -/
@[simp]
theorem refl_cliffordExtensionQuotientEquiv :
    (Iso.refl A).cliffordExtensionQuotientEquiv =
      MulEquiv.refl (CliffordExtension.Quotient A) := by
  apply MulEquiv.ext
  intro c
  refine QuotientGroup.induction_on c fun t ↦ ?_
  simp only [cliffordExtensionQuotientEquiv_mk, MulEquiv.refl_apply]
  apply congrArg QuotientGroup.mk
  exact Subtype.ext (MulEquiv.subgroupCongr_apply _ _)

/-- Inertia quotient transport respects composition of representation isomorphisms. -/
@[simp]
theorem trans_cliffordExtensionQuotientEquiv (e : A ≅ B) (f : B ≅ C) :
    (e ≪≫ f).cliffordExtensionQuotientEquiv =
      e.cliffordExtensionQuotientEquiv.trans f.cliffordExtensionQuotientEquiv := by
  apply MulEquiv.ext
  intro c
  rw [MulEquiv.trans_apply]
  refine QuotientGroup.induction_on c fun t ↦ ?_
  simp only [cliffordExtensionQuotientEquiv_mk]
  apply congrArg QuotientGroup.mk
  exact Subtype.ext (by simp)

/-- The inverse representation isomorphism induces the inverse inertia quotient isomorphism. -/
@[simp]
theorem symm_cliffordExtensionQuotientEquiv (e : A ≅ B) :
    e.symm.cliffordExtensionQuotientEquiv = e.cliffordExtensionQuotientEquiv.symm := by
  apply MulEquiv.ext
  intro c
  apply e.cliffordExtensionQuotientEquiv.injective
  have h := DFunLike.congr_fun (trans_cliffordExtensionQuotientEquiv e.symm e) c
  simpa using h.symm

/-- The Clifford isomorphism commutes with projection to the inertia quotient. -/
@[simp]
theorem rightHom_cliffordExtensionEquiv (e : A ≅ B) (c : Carrier A) :
    rightHom B (e.cliffordExtensionEquiv c) = e.cliffordExtensionQuotientEquiv (rightHom A c) := by
  refine QuotientGroup.induction_on c fun p ↦ ?_
  simp only [cliffordExtensionEquiv_mk, rightHom_mk, cliffordExtensionQuotientEquiv_mk]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  simp

/-- Transport of a kernel unit agrees with conjugation of its equivariant endomorphism. -/
@[simp]
theorem cliffordImplementersEquiv_kernelLift (e : A ≅ B) (d : (End A)ˣ) :
    e.cliffordImplementersEquiv (kernelLift A d) =
      kernelLift B (Units.map e.conj.toMonoidHom d) := by
  apply implementers.ext
  · simp
  · intro x
    simp only [cliffordImplementersEquiv_snd_apply, kernelLift_snd_apply,
      Units.coe_map, MulEquiv.coe_toMonoidHom]
    exact (FDRep.Iso.conj_apply_asHom_apply e _ x).symm

/-- The Clifford isomorphism carries the inclusion of commutant units to the inclusion
of conjugated commutant units. -/
theorem cliffordExtensionEquiv_inl (e : A ≅ B) (d : (End A)ˣ) :
    e.cliffordExtensionEquiv (inl A d) = inl B (Units.map e.conj.toMonoidHom d) := by
  rw [inl_apply, inl_apply, cliffordExtensionEquiv_mk, cliffordImplementersEquiv_kernelLift]

/-- Changing the representation intertwines the full commutant algebra actions. -/
theorem conjAlgEquiv_commutantAction (e : A ≅ B) (c : Carrier A) (f : End A) :
    e.conjAlgEquiv k (commutantAction c f) =
      commutantAction (e.cliffordExtensionEquiv c) (e.conjAlgEquiv k f) := by
  refine QuotientGroup.induction_on c fun p ↦ ?_
  simp only [cliffordExtensionEquiv_mk, commutantAction_mk, conjAlgEquiv_apply]
  apply End.ext
  ext x
  rw [FDRep.Iso.conj_apply_asHom_apply, implementerConj_apply, implementerConj_apply,
    FDRep.Iso.conj_apply_asHom_apply]
  simp

end CategoryTheory.Iso
