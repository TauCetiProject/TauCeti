/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Exponent
public import TauCeti.NumberTheory.NumberField.FixedField
public import TauCeti.RingTheory.DedekindDomain.Different.Tower

/-!
# The different exponent in a fixed field

For a finite Galois extension `L/K`, the coefficient of the different of a fixed field `Lᴴ/K`
at the prime below `Q` is determined by how many elements of each ramification group at `Q`
lie outside `H`. The ramification index of `Q` over that prime clears the denominator in this
formula. It follows from Hilbert's different formula and transitivity of the different.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §§1–2.
-/

public section

open IsDedekindDomain IntermediateField NumberField

open scoped NumberField

namespace IsDedekindDomain.HeightOneSpectrum

open TauCeti

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **The different exponent of a fixed field from its permutation action.** The ramification
index over the selected prime of `Lᴴ` times its different exponent is the sum, over the lower
ramification groups at `Q`, of the numbers of elements outside `H`. -/
theorem ramificationIdx_mul_multiplicity_differentIdeal_fixedField
    (w : HeightOneSpectrum (𝓞 L)) (H : Subgroup (L ≃ₐ[K] L)) :
    w.asIdeal.ramificationIdx (𝓞 ↥(fixedField H)) *
        multiplicity (w.under (𝓞 ↥(fixedField H))).asIdeal
          (differentIdeal (𝓞 K) (𝓞 ↥(fixedField H))) =
      ∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) -
        Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ⊓ H :
          Subgroup (L ≃ₐ[K] L))) := by
  let E := fixedField H
  let : IsScalarTower K ↥E L := E.isScalarTower_mid'
  let : IsGalois ↥E L := IsGalois.of_fixed_field L H
  let u := w.under (𝓞 ↥E)
  have hTower := multiplicity_differentIdeal_tower (A := 𝓞 K) u w
  have hK := w.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one
    (K := K)
  have hE := w.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one
    (K := ↥E)
  let _ : FaithfulSMul (L ≃ₐ[K] L) (𝓞 L) := IsGaloisGroup.faithful (𝓞 K)
  obtain ⟨N, hN⟩ := Ideal.exists_forall_ramificationGroup_eq_bot
    (G := L ≃ₐ[K] L) w.isPrime.ne_top
  have hOutside : Function.HasFiniteSupport (fun i : ℕ ↦
      Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) -
      Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ⊓ H :
        Subgroup (L ≃ₐ[K] L))) := by
    refine (Set.finite_Iio N).subset ?_
    intro i hi
    by_contra hlt
    have hiN : N ≤ i := Nat.le_of_not_lt hlt
    have hzero : Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) -
        Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ⊓ H :
          Subgroup (L ≃ₐ[K] L)) = 0 := by
      rw [hN i hiN]
      simp
    exact hi hzero
  have hFixed : Function.HasFiniteSupport (fun i : ℕ ↦
      Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ⊓ H :
        Subgroup (L ≃ₐ[K] L)) - 1) := by
    refine (Set.finite_Iio N).subset ?_
    intro i hi
    by_contra hlt
    have hiN : N ≤ i := Nat.le_of_not_lt hlt
    have hzero : Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ⊓ H :
        Subgroup (L ≃ₐ[K] L)) - 1 = 0 := by
      rw [hN i hiN]
      simp
    exact hi hzero
  have hSum :
      (∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) - 1)) =
      (∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ⊓ H :
        Subgroup (L ≃ₐ[K] L)) - 1)) +
      (∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) -
        Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ⊓ H :
          Subgroup (L ≃ₐ[K] L)))) := by
    rw [← finsum_add_distrib hFixed hOutside]
    apply finsum_congr
    intro i
    have hle : Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ⊓ H :
        Subgroup (L ≃ₐ[K] L)) ≤
        Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective inf_le_left)
    have hpos : 0 < Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ⊓ H :
        Subgroup (L ≃ₐ[K] L)) := Nat.card_pos
    omega
  have hE' : multiplicity w.asIdeal (differentIdeal (𝓞 ↥E) (𝓞 L)) =
      ∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup (L ≃ₐ[K] L) i ⊓ H :
        Subgroup (L ≃ₐ[K] L)) - 1) := by
    rw [hE]
    apply finsum_congr
    intro i
    simpa only [Ideal.ramificationGroup_def] using
      congrArg (fun n : ℕ => n - 1)
        (Ideal.card_inertia_fixedField_eq_card_inf (w.asIdeal ^ (i + 1)) H)
  rw [hK, hE'] at hTower
  rw [hSum] at hTower
  exact (Nat.add_left_cancel hTower).symm

end IsDedekindDomain.HeightOneSpectrum

end
