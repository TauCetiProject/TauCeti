/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI

/-!
# Splitting off one factor of a free product

For a family of monoids `M : ι → Type*` and an index `i`, the indexed free product `∗ⱼ Mⱼ` is the
free product of `Mᵢ` and of the indexed free product of the other factors.

## Main definitions

* `Monoid.CoprodI.ofCoprodNe`: the homomorphism `Mᵢ ∗ (∗_{j ≠ i} Mⱼ) →* ∗ⱼ Mⱼ` induced by the
  inclusions of the factors.
* `Monoid.CoprodI.equivCoprodNe`: the isomorphism `∗ⱼ Mⱼ ≃* Mᵢ ∗ (∗_{j ≠ i} Mⱼ)`, whose inverse is
  `ofCoprodNe`.

## Main results

* `Monoid.CoprodI.ofCoprodNe_bijective`: `ofCoprodNe` is bijective.
-/

public section

open Function
open scoped Monoid.Coprod

namespace Monoid.CoprodI

variable {ι : Type*} (M : ι → Type*) [∀ i, Monoid (M i)] (i : ι)

/-- The homomorphism from the free product of `M i` and of the indexed free product of the other
factors to the indexed free product of all the factors. -/
def ofCoprodNe : M i ∗ (CoprodI fun j : {j // j ≠ i} ↦ M j) →* CoprodI M :=
  Coprod.lift of (lift fun j ↦ of (i := j.1))

theorem ofCoprodNe_def : ofCoprodNe M i = Coprod.lift of (lift fun j ↦ of (i := j.1)) :=
  (rfl)

@[simp]
theorem ofCoprodNe_comp_inl : (ofCoprodNe M i).comp Coprod.inl = of :=
  Coprod.lift_comp_inl _ _

@[simp]
theorem ofCoprodNe_comp_inr : (ofCoprodNe M i).comp Coprod.inr = lift fun j ↦ of (i := j.1) :=
  Coprod.lift_comp_inr _ _

@[simp]
theorem ofCoprodNe_inl (m : M i) : ofCoprodNe M i (Coprod.inl m) = of m :=
  Coprod.lift_apply_inl _ _ m

@[simp]
theorem ofCoprodNe_inr (x : CoprodI fun j : {j // j ≠ i} ↦ M j) :
    ofCoprodNe M i (Coprod.inr x) = lift (fun j ↦ of (i := j.1)) x :=
  Coprod.lift_apply_inr _ _ x

theorem ofCoprodNe_inr_of (j : {j // j ≠ i}) (m : M j) :
    ofCoprodNe M i (Coprod.inr (of m)) = of (i := j.1) m := by
  simp

section DecidableEq

variable [DecidableEq ι]

/-- An indexed free product is the free product of any one of its factors and of the indexed free
product of the others: `M i` goes to the left factor and each `M j`, `j ≠ i`, to the right one. -/
def equivCoprodNe : CoprodI M ≃* M i ∗ (CoprodI fun j : {j // j ≠ i} ↦ M j) :=
  MonoidHom.toMulEquiv
    (lift fun j ↦ if h : j = i then h ▸ Coprod.inl
      else Coprod.inr.comp (of (M := fun j : {j // j ≠ i} ↦ M j) (i := ⟨j, h⟩)))
    (ofCoprodNe M i)
    (ext_hom _ _ fun j ↦ by
      by_cases h : j = i
      · subst h; ext m; simp
      · ext m; simp [h])
    (Coprod.hom_ext (by ext m; simp) (ext_hom _ _ fun j ↦ by ext m; simp [j.2]))

@[simp]
theorem equivCoprodNe_of_self (m : M i) : equivCoprodNe M i (of m) = Coprod.inl m := by
  simp [equivCoprodNe]

@[simp]
theorem equivCoprodNe_of_ne {j : ι} (hj : j ≠ i) (m : M j) :
    equivCoprodNe M i (of m) = Coprod.inr (of (i := ⟨j, hj⟩) m) := by
  simp [equivCoprodNe, hj]

@[simp]
theorem coe_equivCoprodNe_symm : ⇑(equivCoprodNe M i).symm = ofCoprodNe M i :=
  (rfl)

end DecidableEq

/-- An indexed free product is the free product of any one of its factors and of the indexed free
product of the others. -/
theorem ofCoprodNe_bijective : Bijective (ofCoprodNe M i) := by
  classical
  simpa using (equivCoprodNe M i).symm.bijective

end Monoid.CoprodI
