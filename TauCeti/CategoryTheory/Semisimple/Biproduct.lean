/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Semisimple.Multiplicity

/-!
# Simple multiplicities of finite biproducts

Simple decomposition multiplicities are additive on arbitrary finite biproducts. This extends the
binary additivity of `simpleMultiplicities_biprod` and provides the finite-sum formula needed to
construct additive invariants from simple multiplicities.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The simple multiplicities of a finite biproduct are the sums of the multiplicities of its
summands. -/
@[simp]
theorem simpleMultiplicities_biproduct {ι : Type*} [Fintype ι] (X : ι → C) :
    simpleMultiplicities (⨁ X) = ∑ i, simpleMultiplicities (X i) := by
  classical
  revert X
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ X : ι → C,
      simpleMultiplicities (⨁ X) = ∑ i, simpleMultiplicities (X i))
    ?_ ?_ ?_ ι
  · intro α β _ e hα X
    let : Fintype α := Fintype.ofEquiv β e.symm
    rw [simpleMultiplicities_eq_of_iso
      (biproduct.whiskerEquiv e fun _ => Iso.refl _).symm, hα]
    exact e.sum_comp fun b => simpleMultiplicities (X b)
  · intro X
    rw [(simpleMultiplicities_eq_zero_iff _).2 ((IsZero.iff_id_eq_zero _).2
      (biproduct.hom_ext _ _ fun j => j.elim))]
    simp
  · intro α _ hα X
    rw [simpleMultiplicities_eq_of_iso (biproductOptionIso X),
      simpleMultiplicities_biprod, hα, Fintype.sum_option]

end TauCeti
