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

For finite quotient rings, stable range at most one identifies the cosets of `GL2K1` and
`GL2K0` with unimodular rows and projective points. Unimodular rows and units split over a
product decomposition, so the indices multiply over the factors. For infinite quotients,
the lower unipotent matrices give infinitely many cosets and both natural-number indices
are zero.
-/

public section

namespace TauCeti

variable {A : Type*} [CommRing A] (I : Ideal A)

open Matrix

private theorem index_GL2K0_eq_zero [Infinite (A ⧸ I)] : (GL2K0 I).index = 0 := by
  let lift := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  let g (x : A ⧸ I) := transvectionUnit (one_ne_zero : (1 : Fin 2) ≠ 0) (lift x)
  have hrow (x : A ⧸ I) : bottomRowMod I (g x) = ![x, 1] := by
    have hlift : Ideal.Quotient.mk I (lift x) = x :=
      Function.rightInverse_surjInv Ideal.Quotient.mk_surjective x
    funext j
    fin_cases j <;> simp [g, bottomRowMod_apply, coe_transvectionUnit_eq_one_add_single, hlift]
  rw [Subgroup.index_eq_card,
    ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]
  have : Infinite (Quotient (QuotientGroup.rightRel (GL2K0 I))) :=
    Infinite.of_injective (fun x ↦ Quotient.mk _ (g x)) fun x y h ↦ by
      obtain ⟨u, hu⟩ := GL2K0.rightRel_iff.mp (Quotient.exact h)
      rw [hrow, hrow] at hu
      exact eq_of_smul_vecCons_one_eq (a := (u : A ⧸ I)) (by simpa only [Units.smul_def] using hu)
  exact Nat.card_eq_zero_of_infinite

private theorem index_GL2K1_eq_zero [Infinite (A ⧸ I)] : (GL2K1 I).index = 0 :=
  eq_zero_of_zero_dvd (index_GL2K0_eq_zero I ▸ Subgroup.index_dvd_of_le (GL2K1.le_GL2K0 I))

/-- The index of `K₁(I)` is the `Nat.card` of the unimodular rows of `(A ⧸ I)²`.
Both sides are zero when `A ⧸ I` is infinite. -/
theorem GL2K1.index_eq_card :
    (GL2K1 I).index = Nat.card {v : Fin 2 → A ⧸ I // Module.IsUnimodular (A ⧸ I) v} := by
  cases finite_or_infinite (A ⧸ I)
  · rw [Subgroup.index_eq_card,
      ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _),
      Nat.card_congr (GL2K1.rightCosetEquiv I (hasStableRangeLE_one_of_finite_maximalSpectrum _))]
  · have := Module.infinite_orbitQuotient_unimodular_fin_two (A ⧸ I)
    have : Infinite {v : Fin 2 → A ⧸ I // Module.IsUnimodular (A ⧸ I) v} := by
      simpa only [Module.mem_unimodularSubMulAction] using
        (Infinite.of_surjective _ (Quotient.mk_surjective
          (s := MulAction.orbitRel (A ⧸ I)ˣ
            (Module.unimodularSubMulAction (A ⧸ I) (Fin 2 → A ⧸ I)))))
    rw [index_GL2K1_eq_zero I, Nat.card_eq_zero_of_infinite]

/-- The index of `K₀(I)` is the `Nat.card` of the projective line `ℙ¹(A ⧸ I)`.
Both sides are zero when `A ⧸ I` is infinite. -/
theorem GL2K0.index_eq_card :
    (GL2K0 I).index = Nat.card (MulAction.orbitRel.Quotient (A ⧸ I)ˣ
      (Module.unimodularSubMulAction (A ⧸ I) (Fin 2 → A ⧸ I))) := by
  cases finite_or_infinite (A ⧸ I)
  · rw [Subgroup.index_eq_card,
      ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _),
      Nat.card_congr (GL2K0.rightCosetEquiv I (hasStableRangeLE_one_of_finite_maximalSpectrum _))]
  · have := Module.infinite_orbitQuotient_unimodular_fin_two (A ⧸ I)
    rw [index_GL2K0_eq_zero I, Nat.card_eq_zero_of_infinite]

/-- The index of `K₁(I)` is the product of the factor indices under a finite product decomposition
of `A ⧸ I`. If the quotient ring is infinite, some factor is infinite and both sides are zero. -/
theorem GL2K1.index_eq_prod_of_quotientEquivPi {ι : Type*} [Fintype ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] (J : ∀ i, Ideal (B i))
    (e : A ⧸ I ≃+* ∀ i, B i ⧸ J i) :
    (GL2K1 I).index = ∏ i, (GL2K1 (J i)).index := by
  rw [GL2K1.index_eq_card I, ← Module.card_isUnimodular_congr (Fin 2) e,
    Module.card_isUnimodular_pi]
  exact Finset.prod_congr rfl fun i _ ↦ (GL2K1.index_eq_card (J i)).symm

private theorem card_units_mul_index_GL2K0 :
    Nat.card (A ⧸ I)ˣ * (GL2K0 I).index = (GL2K1 I).index := by
  rw [← GL2K1.relIndex_GL2K0_eq_card_units, Subgroup.relIndex_mul_index (GL2K1.le_GL2K0 I)]

/-- The index of `K₀(I)` is the product of the factor indices under a finite product decomposition
of `A ⧸ I`. If the quotient ring is infinite, some factor is infinite and both sides are zero. -/
theorem GL2K0.index_eq_prod_of_quotientEquivPi {ι : Type*} [Fintype ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] (J : ∀ i, Ideal (B i))
    (e : A ⧸ I ≃+* ∀ i, B i ⧸ J i) :
    (GL2K0 I).index = ∏ i, (GL2K0 (J i)).index := by
  classical
  by_cases h : Finite (A ⧸ I)
  · have hu : Nat.card (A ⧸ I)ˣ = ∏ i, Nat.card (B i ⧸ J i)ˣ := by
      rw [Nat.card_congr ((Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits).toEquiv,
        Nat.card_pi]
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (A ⧸ I)ˣ))
    calc
      Nat.card (A ⧸ I)ˣ * (GL2K0 I).index = (GL2K1 I).index := card_units_mul_index_GL2K0 I
      _ = ∏ i, (GL2K1 (J i)).index := GL2K1.index_eq_prod_of_quotientEquivPi I J e
      _ = Nat.card (A ⧸ I)ˣ * ∏ i, (GL2K0 (J i)).index := by
        simp only [hu, ← Finset.prod_mul_distrib, card_units_mul_index_GL2K0]
  · have := not_finite_iff_infinite.mp h
    have ⟨i, hi⟩ : ∃ i, Infinite (B i ⧸ J i) := by
      by_contra! hfin
      exact h (Finite.of_equiv _ e.symm.toEquiv)
    rw [index_GL2K0_eq_zero I, Finset.prod_eq_zero (Finset.mem_univ i) (index_GL2K0_eq_zero (J i))]

end TauCeti
