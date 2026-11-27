/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel
import TauCeti.LinearAlgebra.Unimodular.Card
import TauCeti.RingTheory.StableRange.Commutative

/-!
# Congruence subgroup indices under products of quotient rings

A finite quotient ring has stable range at most one. Its unimodular rows and units split
over a product decomposition, so the indices of `GL2K1` and `GL2K0` multiply over the factors.
-/

public section

namespace TauCeti

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The index of `K₁(I)` for a finite product of quotient rings is the product of the factor
indices. The ambient rings of the factors may differ from `A`. -/
theorem GL2K1.index_eq_prod_of_quotientEquivPi [Finite (A ⧸ I)] {ι : Type*} [Fintype ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] (J : ∀ i, Ideal (B i))
    (e : A ⧸ I ≃+* ∀ i, B i ⧸ J i) :
    (GL2K1 I).index = ∏ i, (GL2K1 (J i)).index := by
  have hfin (i : ι) : Finite (B i ⧸ J i) :=
    Finite.of_surjective _ ((Function.surjective_eval i).comp e.surjective)
  rw [GL2K1.index_eq_card I (hasStableRangeLE_one_of_finite_maximalSpectrum _),
    ← Module.card_isUnimodular_congr (Fin 2) e, Module.card_isUnimodular_pi]
  exact Finset.prod_congr rfl fun i _ ↦
    (GL2K1.index_eq_card (J i) (hasStableRangeLE_one_of_finite_maximalSpectrum _)).symm

private theorem card_units_mul_index_GL2K0 :
    Nat.card (A ⧸ I)ˣ * (GL2K0 I).index = (GL2K1 I).index := by
  rw [← GL2K1.relIndex_GL2K0_eq_card_units, Subgroup.relIndex_mul_index (GL2K1.le_GL2K0 I)]

/-- A product decomposition of the finite quotient ring makes the level index the product
of the indices for its factors. The ambient rings of the factors may differ from `A`. -/
theorem GL2K0.index_eq_prod_of_quotientEquivPi [Finite (A ⧸ I)] {ι : Type*} [Fintype ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] (J : ∀ i, Ideal (B i))
    (e : A ⧸ I ≃+* ∀ i, B i ⧸ J i) :
    (GL2K0 I).index = ∏ i, (GL2K0 (J i)).index := by
  have hu : Nat.card (A ⧸ I)ˣ = ∏ i, Nat.card (B i ⧸ J i)ˣ := by
    rw [Nat.card_congr ((Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits).toEquiv, Nat.card_pi]
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (A ⧸ I)ˣ))
  calc
    Nat.card (A ⧸ I)ˣ * (GL2K0 I).index = (GL2K1 I).index := card_units_mul_index_GL2K0 I
    _ = ∏ i, (GL2K1 (J i)).index := GL2K1.index_eq_prod_of_quotientEquivPi I J e
    _ = Nat.card (A ⧸ I)ˣ * ∏ i, (GL2K0 (J i)).index := by
      simp only [hu, ← Finset.prod_mul_distrib, card_units_mul_index_GL2K0]

end TauCeti
