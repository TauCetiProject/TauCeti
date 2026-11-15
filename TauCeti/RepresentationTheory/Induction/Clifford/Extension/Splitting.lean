/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Basic

/-!
# Splittings of the Clifford extension

The canonical Clifford extension splits exactly when the specified normal-subgroup action
extends to an ordinary action of its inertia group on the same vector space. More precisely,
`TauCeti.CliffordExtension.extensionSplittingEquiv` identifies these actions with homomorphic
sections of the canonical Clifford extension. No scalar-Schur, simplicity, algebraic-closure,
or finite-group hypothesis is needed.

An implementing pair is uniquely determined by its inertia element and its class in the
Clifford quotient. This allows a splitting to recover actual operators, rather than merely
operators modulo the original normal-subgroup action. Conversely, an extended action gives
implementing pairs whose quotient map kills that diagonal action.

The constructions use the implementing group and diagonal quotient in
`TauCeti.CliffordExtension`, and Mathlib's quotient-group universal property.

## References

G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985).
-/

public section

namespace TauCeti.CliffordExtension

universe u v

variable {k : Type u} {G : Type v} [Group G] {N : Subgroup G} [N.Normal]

section Field

variable [Field k] (A : FDRep k N)

private noncomputable def splittingLift (s : (groupExtension A).Splitting)
    (t : inertia A) : implementers A :=
  (existsUnique_implementer A t (s (QuotientGroup.mk t))
    (by simpa only [groupExtension_rightHom] using (s.rightHom_splitting _).symm)).choose

private theorem splittingLift_spec (s : (groupExtension A).Splitting) (t : inertia A) :
    projection A (splittingLift A s t) = t ∧
      QuotientGroup.mk (splittingLift A s t) = s (QuotientGroup.mk t) :=
  (existsUnique_implementer A t (s (QuotientGroup.mk t))
    (by simpa only [groupExtension_rightHom] using (s.rightHom_splitting _).symm)).choose_spec.1

private noncomputable def splittingLiftHom (s : (groupExtension A).Splitting) :
    inertia A →* implementers A where
  toFun := splittingLift A s
  map_one' := by
    apply implementer_ext A
    · rw [(splittingLift_spec A s 1).1, map_one]
    · rw [(splittingLift_spec A s 1).2, QuotientGroup.mk_one, map_one, QuotientGroup.mk_one]
      rfl
  map_mul' t u := by
    apply implementer_ext A
    · simp only [map_mul, (splittingLift_spec A s (t * u)).1,
        (splittingLift_spec A s t).1, (splittingLift_spec A s u).1]
    · simp only [QuotientGroup.mk_mul, map_mul, (splittingLift_spec A s (t * u)).2,
        (splittingLift_spec A s t).2, (splittingLift_spec A s u).2]
      rfl

private theorem splittingLift_diagonal (s : (groupExtension A).Splitting) (n : N) :
    splittingLiftHom A s (Subgroup.inclusion (le_inertia A) n) = diagonal A n := by
  apply implementer_ext A
  · simpa only [splittingLiftHom, MonoidHom.coe_mk, OneHom.coe_mk, projection_apply,
      diagonal_fst] using (splittingLift_spec A s (Subgroup.inclusion (le_inertia A) n)).1
  · simp only [splittingLiftHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [(splittingLift_spec A s _).2]
    have hn : (QuotientGroup.mk (Subgroup.inclusion (le_inertia A) n) : Quotient A) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr n.2
    have hd : (QuotientGroup.mk (diagonal A n) : Carrier A) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨n, rfl⟩
    rw [hn, map_one, hd]
    rfl

/-- The ordinary inertia action recovered from a splitting of the Clifford extension. -/
noncomputable def representationOfSplitting (s : (groupExtension A).Splitting) :
    Representation k (inertia A) A :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (((MonoidHom.snd _ _).comp (implementers A).subtype).comp (splittingLiftHom A s))

/-- The recovered inertia action restricts to the specified `N`-action. -/
@[simp]
theorem representationOfSplitting_comp (s : (groupExtension A).Splitting) :
    (representationOfSplitting A s).comp (Subgroup.inclusion (le_inertia A)) = A.ρ := by
  ext n x
  simpa [representationOfSplitting] using
    congrArg (fun p : implementers A => p.1.2 x) (splittingLift_diagonal A s n)

private noncomputable def implementerHom (σ : Representation k (inertia A) A)
    (hσ : σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ) :
    inertia A →* implementers A :=
  let r : inertia A →* (A ≃ₗ[k] A) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k A).toMonoidHom.comp σ.toHomUnits
  (MonoidHom.id _).prod r |>.codRestrict (implementers A) (fun t => by
    rw [mem_implementers_iff]
    intro n x
    have hn : Subgroup.inclusion (le_inertia A) (MulAut.conjNormal (t : G) n) =
        t * Subgroup.inclusion (le_inertia A) n * t⁻¹ := Subtype.ext rfl
    simp [r, ← hσ, hn, map_mul])

private theorem implementerHom_diagonal (σ : Representation k (inertia A) A)
    (hσ : σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ) (n : N) :
    implementerHom A σ hσ (Subgroup.inclusion (le_inertia A) n) = diagonal A n := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · simp [implementerHom, diagonal_fst]
  · ext x
    rw [diagonal_snd_apply]
    simpa [implementerHom] using LinearMap.congr_fun (DFunLike.congr_fun hσ n) x

private theorem implementerHom_ker (σ : Representation k (inertia A) A)
    (hσ : σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ) :
    N.subgroupOf (inertia A) ≤
      ((QuotientGroup.mk' (diagonal A).range).comp (implementerHom A σ hσ)).ker := by
  intro t ht
  let n : N := ⟨t, Subgroup.mem_subgroupOf.mp ht⟩
  have ht' : t = Subgroup.inclusion (le_inertia A) n :=
    Subtype.ext (Subgroup.coe_inclusion (le_inertia A) n).symm
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ht', implementerHom_diagonal]
  exact (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨n, rfl⟩)

private noncomputable def quotientOfRepresentation (σ : Representation k (inertia A) A)
    (hσ : σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ) :
    Quotient A →* Carrier A :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp (implementerHom A σ hσ))
    (implementerHom_ker A σ hσ)

private theorem quotientOfRepresentation_mk (σ : Representation k (inertia A) A)
    (hσ : σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ) (t : inertia A) :
    quotientOfRepresentation A σ hσ (QuotientGroup.mk t) =
      QuotientGroup.mk (implementerHom A σ hσ t) := (rfl)

/-- An ordinary extension of the specified `N`-action gives a splitting of the Clifford group. -/
noncomputable def splittingOfRepresentation (σ : Representation k (inertia A) A)
    (hσ : σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ) :
    (groupExtension A).Splitting where
  __ := quotientOfRepresentation A σ hσ
  rightInverse_rightHom q := by
    refine QuotientGroup.induction_on q fun t => ?_
    rw [MonoidHom.toFun_eq_coe, groupExtension_rightHom, quotientOfRepresentation_mk,
      rightHom_mk]
    rfl

/-- The action recovered from a splitting is the operator of its implementing pair.
The quotient-class hypothesis pins the pair over the specified inertia element. -/
theorem representationOfSplitting_apply (s : (groupExtension A).Splitting)
    (p : implementers A)
    (hp : (QuotientGroup.mk p : Carrier A) = s (QuotientGroup.mk (projection A p)))
    (x : A) : representationOfSplitting A s (projection A p) x = p.1.2 x := by
  have he : splittingLiftHom A s (projection A p) = p :=
    implementer_ext A (splittingLift_spec A s _).1
      ((splittingLift_spec A s _).2.trans hp.symm)
  simpa [representationOfSplitting] using congrArg (fun q : implementers A => q.1.2 x) he

/-- The splitting associated to an extended action has exactly its operators as representatives. -/
@[simp]
theorem mk_eq_splittingOfRepresentation_iff (σ : Representation k (inertia A) A)
    (hσ : σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ) (p : implementers A) :
    (QuotientGroup.mk p : Carrier A) =
        splittingOfRepresentation A σ hσ (QuotientGroup.mk p.1.1) ↔
      ∀ x, p.1.2 x = σ p.1.1 x := by
  rw [← projection_apply A p]
  have hs : splittingOfRepresentation A σ hσ (QuotientGroup.mk (projection A p)) =
      QuotientGroup.mk (implementerHom A σ hσ (projection A p)) :=
    quotientOfRepresentation_mk A σ hσ _
  rw [hs]
  constructor
  · intro hc x
    have he : p = implementerHom A σ hσ (projection A p) :=
      implementer_ext A (by simp [implementerHom]) hc
    simpa [implementerHom] using congrArg (fun q : implementers A => q.1.2 x) he
  · intro h
    congr 1
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · simp [implementerHom, projection_apply]
    · ext x
      simpa [implementerHom] using h x

/-- Recovering the action from its associated splitting returns the original action. -/
@[simp]
theorem representationOfSplitting_splittingOfRepresentation
    (σ : Representation k (inertia A) A)
    (hσ : σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ) :
    representationOfSplitting A (splittingOfRepresentation A σ hσ) = σ := by
  ext t x
  let p := implementerHom A σ hσ t
  have hp : projection A p = t := by simp [p, projection_apply, implementerHom]
  have hc : (QuotientGroup.mk p : Carrier A) =
      splittingOfRepresentation A σ hσ (QuotientGroup.mk (projection A p)) := by
    rw [projection_apply]
    exact (mk_eq_splittingOfRepresentation_iff A σ hσ p).mpr (by simp [p, implementerHom])
  simpa [p, implementerHom, hp] using
    representationOfSplitting_apply A (splittingOfRepresentation A σ hσ) p hc x

/-- Passing from a splitting to its recovered action and back returns the splitting. -/
@[simp]
theorem splittingOfRepresentation_representationOfSplitting
    (s : (groupExtension A).Splitting) :
    splittingOfRepresentation A (representationOfSplitting A s)
      (representationOfSplitting_comp A s) = s := by
  apply DFunLike.ext
  intro q
  refine QuotientGroup.induction_on q fun t => ?_
  let p := splittingLift A s t
  have hp : projection A p = t := (splittingLift_spec A s t).1
  have hc : (QuotientGroup.mk p : Carrier A) = s (QuotientGroup.mk t) :=
    (splittingLift_spec A s t).2
  have he := (mk_eq_splittingOfRepresentation_iff A (representationOfSplitting A s)
    (representationOfSplitting_comp A s) p).mpr fun x => by
      simpa only [projection_apply] using
        (representationOfSplitting_apply A s p (by simpa only [hp] using hc) x).symm
  rw [← projection_apply A p, hp] at he
  exact he.symm.trans hc

/-- Ordinary inertia actions extending the specified `N`-action correspond to splittings of
its canonical Clifford extension. The underlying vector space and the `N`-action are fixed. -/
noncomputable def extensionSplittingEquiv :
    {σ : Representation k (inertia A) A //
      σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ} ≃ (groupExtension A).Splitting where
  toFun σ := splittingOfRepresentation A σ.1 σ.2
  invFun s := ⟨representationOfSplitting A s, representationOfSplitting_comp A s⟩
  left_inv σ := Subtype.ext (representationOfSplitting_splittingOfRepresentation A σ.1 σ.2)
  right_inv := splittingOfRepresentation_representationOfSplitting A

@[simp]
theorem extensionSplittingEquiv_apply
    (σ : {σ : Representation k (inertia A) A //
      σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ}) :
    extensionSplittingEquiv A σ = splittingOfRepresentation A σ.1 σ.2 := (rfl)

@[simp]
theorem extensionSplittingEquiv_symm_apply (s : (groupExtension A).Splitting) :
    (extensionSplittingEquiv A).symm s =
      ⟨representationOfSplitting A s, representationOfSplitting_comp A s⟩ := (rfl)

/-- The canonical Clifford extension splits exactly when the given `N`-representation extends
ordinarily to its inertia group, without any scalar-endomorphism hypothesis. -/
theorem nonempty_splitting_iff :
    Nonempty (groupExtension A).Splitting ↔
      ∃ σ : Representation k (inertia A) A,
        σ.comp (Subgroup.inclusion (le_inertia A)) = A.ρ := by
  constructor
  · rintro ⟨s⟩
    exact ⟨representationOfSplitting A s, representationOfSplitting_comp A s⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨splittingOfRepresentation A σ hσ⟩

end Field

end TauCeti.CliffordExtension
