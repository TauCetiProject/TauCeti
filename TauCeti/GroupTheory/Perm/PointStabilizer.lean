/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Permutations of the complement of a point

`Fin.permStabilizerEquiv i` identifies permutations of `Fin n` with the stabilizer of
`i : Fin (n + 1)`. The other points are labelled in increasing order by `i.succAbove`.
This gives an explicit coordinate convention for restricting representations of a symmetric
group to a point stabilizer.
-/

public section

namespace Fin

/-- Permutations of the complement of `i`, labelled by `i.succAbove`, form its stabilizer. -/
noncomputable def permStabilizerEquiv {n : ℕ} (i : Fin (n + 1)) :
    Equiv.Perm (Fin n) ≃* MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) i := by
  let f : Equiv.Perm (Fin n) →*
      MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) i :=
    (Equiv.Perm.extendDomainHom (finSuccAboveEquiv i)).codRestrict _ fun σ =>
      Equiv.Perm.extendDomain_apply_not_subtype σ _ (by simp)
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro σ τ h
    exact Equiv.Perm.extendDomainHom_injective _ (congrArg Subtype.val h)
  · intro σ
    have hfix : σ.val i = i := σ.property
    obtain ⟨τ, hτ⟩ := (Equiv.Perm.subtypeEquivSubtypePerm
      (fun j : Fin (n + 1) => j ≠ i)).surjective ⟨σ.val, by simpa using hfix⟩
    refine ⟨(finSuccAboveEquiv i).symm.permCongr τ, Subtype.ext ?_⟩
    apply Equiv.ext
    intro j
    by_cases hj : j = i
    · subst j
      simpa [f, Equiv.Perm.extendDomainHom, hfix] using
        (Equiv.Perm.extendDomain_apply_not_subtype
          ((finSuccAboveEquiv i).symm.permCongr τ) (finSuccAboveEquiv i)
          (by simp) : _ = i)
    · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hj
      have ht := congrArg (fun e => e.val (i.succAbove a)) hτ
      simp only [Equiv.Perm.subtypeEquivSubtypePerm, Equiv.coe_fn_mk] at ht
      rw [Equiv.Perm.ofSubtype_apply_of_mem τ (i.succAbove_ne a)] at ht
      simpa [f, Equiv.Perm.extendDomainHom, ← finSuccAboveEquiv_apply,
        Equiv.Perm.extendDomain_apply_subtype] using ht

/-- The underlying permutation extends the permutation of the complement by fixing `i`. -/
@[simp]
theorem coe_permStabilizerEquiv {n : ℕ} (i : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    (i.permStabilizerEquiv σ : Equiv.Perm (Fin (n + 1))) =
      Equiv.Perm.extendDomainHom (finSuccAboveEquiv i) σ := (rfl)

/-- On the complement, the stabilizer equivalence uses the increasing labelling. -/
@[simp↓]
theorem permStabilizerEquiv_apply_succAbove {n : ℕ} (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    (i.permStabilizerEquiv σ : Equiv.Perm (Fin (n + 1))) (i.succAbove j) =
      i.succAbove (σ j) := by
  simpa only [coe_permStabilizerEquiv, Equiv.Perm.extendDomainHom,
    MonoidHom.coe_mk, OneHom.coe_mk, finSuccAboveEquiv_apply] using
    Equiv.Perm.extendDomain_apply_image σ (finSuccAboveEquiv i) j

/-- Recovering a permutation of the complement commutes with the increasing labelling. -/
@[simp]
theorem succAbove_permStabilizerEquiv_symm_apply {n : ℕ} (i : Fin (n + 1))
    (σ : MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) i) (j : Fin n) :
    i.succAbove (i.permStabilizerEquiv.symm σ j) = σ.val (i.succAbove j) := by
  rw [← permStabilizerEquiv_apply_succAbove, MulEquiv.apply_symm_apply]

end Fin
