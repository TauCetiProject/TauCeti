/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Complexity

/-!
# Complexity and realization of first-order formulas

Mathlib's `FirstOrder.Language.BoundedFormula.iSup` and `FirstOrder.Language.BoundedFormula.iInf`
form the disjunction and conjunction of a finite family of formulas. This file shows that both are
quantifier-free when every member of the family is.

In an algebraic language, every atomic formula holds in a subsingleton structure: atomic
formulas can only assert equality of terms.

Translating a formula along a language homomorphism (`FirstOrder.Language.LHom.onBoundedFormula`)
keeps it atomic, quantifier-free or universal, and quantifying all bound variables of a universal
formula (`FirstOrder.Language.BoundedFormula.alls`) gives a universal formula. These let universal
sentences of a language be read in an extension by constants.
-/

public section

namespace FirstOrder.Language.BoundedFormula.IsQF

variable {L : Language} {α β : Type*} {n : ℕ}

/-- A finite disjunction of quantifier-free formulas is quantifier-free. -/
theorem iSup [Finite β] {f : β → L.BoundedFormula α n} (hf : ∀ b, (f b).IsQF) :
    (BoundedFormula.iSup f).IsQF := by
  -- Mirror the Fintype.ofFinite instance chosen by BoundedFormula.iSup;
  -- its finite-connective goal then reduces to the corresponding list fold.
  let _ := Fintype.ofFinite β
  suffices ∀ l : List β, (l.map f).foldr (· ⊔ ·) ⊥ |>.IsQF from this _
  intro l
  induction l with
  | nil => exact isQF_bot
  | cons b l ih => exact (hf b).sup ih

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
theorem iInf [Finite β] {f : β → L.BoundedFormula α n} (hf : ∀ b, (f b).IsQF) :
    (BoundedFormula.iInf f).IsQF := by
  -- Mirror the Fintype.ofFinite instance chosen by BoundedFormula.iInf;
  -- its finite-connective goal then reduces to the corresponding list fold.
  let _ := Fintype.ofFinite β
  suffices ∀ l : List β, (l.map f).foldr (· ⊓ ·) ⊤ |>.IsQF from this _
  intro l
  induction l with
  | nil => exact top
  | cons b l ih => exact (hf b).inf ih

end FirstOrder.Language.BoundedFormula.IsQF

namespace FirstOrder.Language.BoundedFormula

open FirstOrder

/-- Every atomic formula over an algebraic language holds in a subsingleton structure. -/
theorem realize_of_isAtomic_subsingleton {L : Language} [L.IsAlgebraic]
    {G α : Type*} [Subsingleton G] [L.Structure G]
    {n : ℕ} {φ : L.BoundedFormula α n} (hφ : φ.IsAtomic)
    (v : α → G) (xs : Fin n → G) : φ.Realize v xs := by
  cases hφ with
  | equal _ _ => exact Subsingleton.elim _ _
  | rel r _ => exact isEmptyElim r

variable {L L' : Language} {α : Type*} {n : ℕ} {φ : L.BoundedFormula α n}

/-- Translating an atomic formula along a language homomorphism gives an atomic formula. -/
theorem IsAtomic.onBoundedFormula (h : φ.IsAtomic) (ϕ : L →ᴸ L') :
    (ϕ.onBoundedFormula φ).IsAtomic := by
  cases h with
  | equal t₁ t₂ => exact IsAtomic.equal _ _
  | rel R ts => exact IsAtomic.rel _ _

/-- Translating a quantifier-free formula along a language homomorphism gives a quantifier-free
formula. -/
theorem IsQF.onBoundedFormula (h : φ.IsQF) (ϕ : L →ᴸ L') :
    (ϕ.onBoundedFormula φ).IsQF := by
  induction h with
  | falsum => exact IsQF.falsum
  | of_isAtomic h => exact (h.onBoundedFormula ϕ).isQF
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

/-- Translating a universal formula along a language homomorphism gives a universal formula. -/
theorem IsUniversal.onBoundedFormula (h : φ.IsUniversal) (ϕ : L →ᴸ L') :
    (ϕ.onBoundedFormula φ).IsUniversal := by
  induction h with
  | of_isQF h => exact (h.onBoundedFormula ϕ).isUniversal
  | all _ ih => exact ih.all

/-- Universally quantifying all bound variables of a universal formula gives a universal
formula. -/
theorem IsUniversal.alls (h : φ.IsUniversal) : φ.alls.IsUniversal := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih h.all

end FirstOrder.Language.BoundedFormula
