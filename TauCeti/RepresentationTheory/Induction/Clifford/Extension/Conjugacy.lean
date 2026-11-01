/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Splitting
public import Mathlib.GroupTheory.GroupExtension.Basic
public import TauCeti.RepresentationTheory.AsModule

/-!
# Isomorphisms of inertia extensions and conjugacy of splittings

An ordinary action of the inertia group extending a specified normal-subgroup action
corresponds to a splitting of the canonical Clifford extension. Two such actions are
isomorphic exactly when their splittings are conjugate by a unit of the actual
normal-subgroup endomorphism algebra. Thus the splitting correspondence also classifies
extensions up to isomorphism, without identifying the commutant with the scalar field.

The comparison uses the implementing pairs and the action/splitting correspondence in
`TauCeti.CliffordExtension`. It applies over every field, including nonsplitting fields,
and needs neither simplicity nor finiteness of the ambient group.

## References

G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985),
the extension problem in Clifford theory.
-/

public section

namespace FDRep

open CategoryTheory TauCeti TauCeti.CliffordExtension

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)

private theorem mk_eq_splitting_iff (s : (groupExtension A).Splitting)
    (p : implementers A) :
    (QuotientGroup.mk p : Carrier A) = s (QuotientGroup.mk p.1.1) ↔
      ∀ x, p.1.2 x = representationOfSplitting A s p.1.1 x := by
  conv_lhs => rw [← splittingOfRepresentation_representationOfSplitting A s]
  exact mk_eq_splittingOfRepresentation_iff A _ _ p

private theorem exists_implementer_splitting (s : (groupExtension A).Splitting)
    (g : inertia A) :
    ∃ p : implementers A, p.1.1 = g ∧
      (QuotientGroup.mk p : Carrier A) = s (QuotientGroup.mk g) ∧
      ∀ x, p.1.2 x = representationOfSplitting A s g x := by
  obtain ⟨p, ⟨hp, hc⟩, _⟩ := existsUnique_implementer A g (s (QuotientGroup.mk g))
    (by simpa only [groupExtension_rightHom] using (s.rightHom_splitting _).symm)
  have hp' : p.1.1 = g := by simpa only [projection_apply] using hp
  exact ⟨p, hp', hc, fun x => by
    rw [← hp']
    exact (mk_eq_splitting_iff A s p).mp (by simpa only [hp'] using hc) x⟩

/-- Conjugating a Clifford splitting by a commutant unit corresponds exactly to
intertwining its recovered inertia action by that unit. -/
theorem clifford_splitting_eq_conj_iff (s t : (groupExtension A).Splitting) (d : (End A)ˣ) :
    (∀ q, s q = inl A d * t q * (inl A d)⁻¹) ↔
      ∀ g x, representationOfSplitting A s g (d.val.asHom.hom.hom.hom x) =
        d.val.asHom.hom.hom.hom (representationOfSplitting A t g x) := by
  simp only [← kernelLift_snd_apply]
  constructor
  · intro h g x
    obtain ⟨p, hp, hc, hρ⟩ := exists_implementer_splitting A t g
    let p' := kernelLift A d * p * (kernelLift A d)⁻¹
    have hp' : p'.1.1 = g := by simp [p', hp]
    have hc' : (QuotientGroup.mk p' : Carrier A) = s (QuotientGroup.mk p'.1.1) := by
      rw [hp', h]
      simp only [p', QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← inl_apply, hc]
      rfl
    have hv := (mk_eq_splitting_iff A s p').mp hc' ((kernelLift A d).1.2 x)
    -- Multiplication of implementing pairs composes their linear equivalences.
    rw [hp'] at hv
    simp only [p', Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv,
      LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at hv
    simpa only [hρ] using hv.symm
  · intro h q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨p, hp, hc, hρ⟩ := exists_implementer_splitting A t g
    let p' := kernelLift A d * p * (kernelLift A d)⁻¹
    have hp' : p'.1.1 = g := by simp [p', hp]
    have hc' : (QuotientGroup.mk p' : Carrier A) = s (QuotientGroup.mk p'.1.1) := by
      apply (mk_eq_splitting_iff A s p').mpr
      intro x
      have hv := h g ((kernelLift A d).1.2.symm x)
      rw [hp']
      simp only [p', Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv,
        LinearEquiv.mul_apply, LinearEquiv.coe_inv]
      simpa only [hρ, LinearEquiv.apply_symm_apply] using hv.symm
    rw [hp'] at hc'
    rw [← hc']
    simp only [p', QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← inl_apply, hc]
    rfl

/-- Two splittings of the canonical Clifford extension are kernel-conjugate exactly
when their recovered representations of the inertia group are isomorphic. -/
theorem clifford_isConj_iff_nonempty_iso (s t : (groupExtension A).Splitting) :
    (groupExtension A).IsConj s t ↔
      Nonempty (FDRep.of (representationOfSplitting A s) ≅
        FDRep.of (representationOfSplitting A t)) := by
  simp only [GroupExtension.IsConj, funext_iff, groupExtension_inl,
    clifford_splitting_eq_conj_iff, nonempty_fdRepIso_iff, FDRep.of_ρ']
  simp only [← kernelLift_snd_apply]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨(Representation.Equiv.mk (kernelLift A d).1.2
      (fun g => LinearMap.ext (fun x => (hd g x).symm))).symm⟩
  · rintro ⟨e⟩
    let f := e.symm
    have hf (g : inertia A) (x : A) :
        f.toLinearEquiv (representationOfSplitting A t g x) =
          representationOfSplitting A s g (f.toLinearEquiv x) :=
      LinearMap.congr_fun (f.toIntertwiningMap.isIntertwining' g) x
    have hn (n : N) (x : A) : f.toLinearEquiv (A.ρ n x) = A.ρ n (f.toLinearEquiv x) := by
      have hs : representationOfSplitting A s (Subgroup.inclusion (le_inertia A) n) =
          A.ρ n := DFunLike.congr_fun (representationOfSplitting_comp A s) n
      have ht : representationOfSplitting A t (Subgroup.inclusion (le_inertia A) n) =
          A.ρ n := DFunLike.congr_fun (representationOfSplitting_comp A t) n
      simpa only [hs, ht] using
        hf (Subgroup.inclusion (le_inertia A) n) x
    let p : implementers A := ⟨(1, f.toLinearEquiv), by
      simpa only [mem_implementers_iff, Subgroup.coe_one, map_one, MulAut.one_apply] using hn⟩
    have hp : p ∈ (kernelLift A).range := by
      rw [range_kernelLift_eq_ker_projection]
      simp only [MonoidHom.mem_ker, projection_apply]
      rfl
    obtain ⟨d, hd⟩ := hp
    refine ⟨d, fun g x => ?_⟩
    rw [hd]
    exact (hf g x).symm

/-- Ordinary inertia actions extending the same specified `N`-action are isomorphic
exactly when their associated Clifford splittings are conjugate by `End_N(A)ˣ`. -/
theorem clifford_splittingOfRepresentation_isConj_iff
    (σ τ : Representation k (inertia A) A)
    (hσ : σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ)
    (hτ : τ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ) :
    (groupExtension A).IsConj (splittingOfRepresentation A σ hσ)
      (splittingOfRepresentation A τ hτ) ↔ Nonempty (FDRep.of σ ≅ FDRep.of τ) := by
  rw [clifford_isConj_iff_nonempty_iso, representationOfSplitting_splittingOfRepresentation,
    representationOfSplitting_splittingOfRepresentation]

/-- Isomorphism classes of inertia actions extending the specified `N`-action correspond
bijectively to kernel-conjugacy classes of splittings of its canonical Clifford extension. -/
noncomputable def cliffordExtensionConjClassesEquiv :
    Quotient ((isIsomorphicSetoid (FDRep k (inertia A))).comap
      (fun σ : {σ : Representation k (inertia A) A //
        σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ} => FDRep.of σ.val)) ≃
      (groupExtension A).ConjClasses :=
  Quotient.congr (extensionSplittingEquiv A) (fun σ τ => by
    -- The native setoids have no characteristic simp lemmas for these relations.
    change Nonempty (FDRep.of σ.val ≅ FDRep.of τ.val) ↔
      (groupExtension A).IsConj ((extensionSplittingEquiv A) σ) ((extensionSplittingEquiv A) τ)
    rw [extensionSplittingEquiv_apply, extensionSplittingEquiv_apply]
    exact (clifford_splittingOfRepresentation_isConj_iff A σ.val τ.val σ.prop τ.prop).symm)

/-- The class correspondence sends an action to the class of its associated splitting. -/
@[simp]
theorem cliffordExtensionConjClassesEquiv_mk
    (σ : {σ : Representation k (inertia A) A //
      σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ}) :
    cliffordExtensionConjClassesEquiv A (Quotient.mk _ σ) =
      Quotient.mk _ (splittingOfRepresentation A σ.val σ.prop) := by
  exact congrArg (Quotient.mk _) (extensionSplittingEquiv_apply A σ)

/-- The inverse class correspondence recovers the action of the chosen splitting. -/
@[simp]
theorem cliffordExtensionConjClassesEquiv_symm_mk (s : (groupExtension A).Splitting) :
    (cliffordExtensionConjClassesEquiv A).symm (Quotient.mk _ s) =
      Quotient.mk _ ⟨representationOfSplitting A s, representationOfSplitting_comp A s⟩ := by
  apply (cliffordExtensionConjClassesEquiv A).injective
  have h := (cliffordExtensionConjClassesEquiv A).apply_symm_apply
    (Quotient.mk _ s : (groupExtension A).ConjClasses)
  rw [cliffordExtensionConjClassesEquiv_mk,
    splittingOfRepresentation_representationOfSplitting]
  exact h

end FDRep
