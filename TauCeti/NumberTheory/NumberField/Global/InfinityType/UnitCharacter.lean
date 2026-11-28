/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import TauCeti.NumberTheory.NumberField.Global.InfinityType.Basic

import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# Algebraic infinity types on integer units

An algebraic infinity type restricts its embedding monomial to a character on the units of
the ring of integers. Constant types give the trivial character over a totally imaginary
field, where every integer unit has field norm one.
-/

public noncomputable section

open NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields.AlgebraicInfinityType

variable {K : Type*} [Field K] [NumberField K]

/-- The embedding monomial restricted to the units of the ring of integers. -/
def unitCharacter (n : AlgebraicInfinityType K) : (𝓞 K)ˣ →* ℂˣ :=
  n.embeddingCharacter.comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

/-- The unit character is obtained by restricting the embedding character along the inclusion
of the integer units into the field units. -/
theorem unitCharacter_def (n : AlgebraicInfinityType K) :
    n.unitCharacter =
      n.embeddingCharacter.comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom) :=
  (rfl)

/-- Evaluate the unit character as the product of the individual embedding powers. -/
@[simp]
theorem coe_unitCharacter_apply (n : AlgebraicInfinityType K) (u : (𝓞 K)ˣ) :
    (n.unitCharacter u : ℂ) = ∏ σ : K →+* ℂ, σ (u : K) ^ n σ := by
  simp [unitCharacter_def, coe_embeddingCharacter_apply]

/-- The zero algebraic infinity type gives the trivial unit character. -/
@[simp]
theorem unitCharacter_zero : unitCharacter (0 : AlgebraicInfinityType K) = 1 := by
  simp only [unitCharacter_def, embeddingCharacter_zero, MonoidHom.one_comp]

/-- Adding algebraic infinity types multiplies their unit characters. -/
@[simp]
theorem unitCharacter_add (n m : AlgebraicInfinityType K) :
    (n + m).unitCharacter = n.unitCharacter * m.unitCharacter := by
  simp only [unitCharacter_def, embeddingCharacter_add, MonoidHom.mul_comp]

/-- Negating an algebraic infinity type inverts its unit character. -/
@[simp]
theorem unitCharacter_neg (n : AlgebraicInfinityType K) :
    (-n).unitCharacter = n.unitCharacter⁻¹ := by
  simp only [unitCharacter_def, embeddingCharacter_neg, MonoidHom.inv_comp]

/-- Constant algebraic infinity types are trivial on the integer units of a totally imaginary
field. -/
theorem unitCharacter_eq_one_of_constant [IsTotallyComplex K] (n : AlgebraicInfinityType K)
    {a : ℤ} (hn : ∀ σ, n σ = a) : n.unitCharacter = 1 := by
  ext u
  have hpos := norm_pos_of_isTotallyPositive (NumberField.Units.coe_ne_zero u) (by simp)
  have hnorm := (abs_of_pos hpos).symm.trans (NumberField.Units.norm K u)
  simp only [coe_unitCharacter_apply, hn, MonoidHom.one_apply, Units.val_one]
  have hprod : (∏ σ : K →+* ℂ, σ (u : K)) = 1 := calc
    _ = ∏ σ : K →ₐ[ℚ] ℂ, σ (u : K) :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun _ ↦ rfl)
    _ = 1 := by rw [← Algebra.norm_eq_prod_embeddings, hnorm, map_one]
  rw [Finset.prod_zpow, hprod, one_zpow]

end TauCeti.GlobalNumberFields.AlgebraicInfinityType
