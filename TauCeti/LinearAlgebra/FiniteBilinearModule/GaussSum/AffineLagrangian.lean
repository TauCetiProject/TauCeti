/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum

/-!
# Gauss sums on a translate of a bilinear Lagrangian

Let `H` be a Lagrangian for the polar pairing of a finite quadratic module. If the quadratic
form is constant on `a + H`, its Gauss sum is `#H · expCircle (q(a))`. The subgroup need not
be isotropic for the quadratic form. The phase on its translate records the characteristic
norm in the discriminant form of the even sublattice of an odd unimodular lattice.

The character-averaging argument follows
`TauCeti.FiniteQuadraticModule.gaussSum_restrict_orthogonalComplement`.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public section

namespace TauCeti.FiniteQuadraticModule

variable {A : FiniteQuadraticModule} {H : AddSubgroup A} (a : A)

private theorem quadratic_add_of_constantOn_coset
    (ha : ∀ h : H, A.quadratic (a + h) = A.quadratic a) (x : A) (h : H) :
    A.quadratic (x + h) =
      A.quadratic x + A.toFiniteBilinearModule.pairing (x - a) h := by
  have hp (y : A) : A.quadratic (y + h) = A.quadratic y + A.quadratic h +
      A.toFiniteBilinearModule.pairing y h := by
    rw [← polar_eq_pairing, QuadraticMap.polar]
    abel
  have hh : A.quadratic h + A.toFiniteBilinearModule.pairing a h = 0 := by
    apply add_left_cancel (a := A.quadratic a)
    simpa only [hp, add_assoc, add_zero] using ha h
  have hb : A.toFiniteBilinearModule.pairing (x - a) h =
      A.toFiniteBilinearModule.pairing x h - A.toFiniteBilinearModule.pairing a h := by
    rw [A.toFiniteBilinearModule.pairing_comm, map_sub,
      A.toFiniteBilinearModule.pairing_comm h x,
      A.toFiniteBilinearModule.pairing_comm h a]
  rw [hp, eq_neg_of_add_eq_zero_left hh, hb]
  abel

private theorem sum_expCircle_pairing_sub [Fintype H]
    [DecidablePred (· ∈ H)]
    (hH : A.toFiniteBilinearModule.IsLagrangian H) (x : A) :
    ∑ h : H, expCircle (A.toFiniteBilinearModule.pairing (x - a) h) =
      if x - a ∈ H then (Nat.card H : ℂ) else 0 := by
  classical
  have h := CharacterModule.sum_expCircle
    (A.toFiniteBilinearModule.pairingRestrict H (x - a))
  simp only [FiniteBilinearModule.pairingRestrict_apply] at h
  rw [h, Nat.card_eq_fintype_card]
  refine if_congr ?_ rfl rfl
  rw [← AddMonoidHom.mem_ker, FiniteBilinearModule.pairingRestrict_ker,
    ← (A.toFiniteBilinearModule.isLagrangian_def H).mp hH]

private theorem sum_expCircle_translate_filter [Fintype A]
    [DecidablePred (· ∈ H)]
    (ha : ∀ h : H, A.quadratic (a + h) = A.quadratic a) :
    ∑ x : A, (if x ∈ H then expCircle (A.quadratic (a + x)) else 0) =
      (Nat.card H : ℂ) * expCircle (A.quadratic a) := by
  classical
  have ht := Finset.sum_subtype
    (F := inferInstanceAs (Fintype H)) (p := fun x : A ↦ x ∈ H)
    (Finset.univ.filter (fun x : A ↦ x ∈ H)) (by simp)
    (fun x : A ↦ expCircle (A.quadratic (a + x)))
  rw [← Finset.sum_filter, ht]
  simp [ha, Nat.card_eq_fintype_card]

/-- If the quadratic form is constant on a translate of a Lagrangian for its polar pairing,
the Gauss sum is the subgroup's order times the exponential of that constant. -/
theorem gaussSum_eq_natCard_mul_expCircle_of_bilinear_isLagrangian
    (hH : A.toFiniteBilinearModule.IsLagrangian H)
    (ha : ∀ h : H, A.quadratic (a + h) = A.quadratic a) :
    A.gaussSum = (Nat.card H : ℂ) * expCircle (A.quadratic a) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype A
  have hcard : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hshift (h : H) : ∑ x, expCircle (A.quadratic (x + h)) = A.gaussSum := by
    rw [gaussSum_eq_sum]
    exact Equiv.sum_comp (Equiv.addRight (h : A)) (fun x ↦ expCircle (A.quadratic x))
  apply mul_left_cancel₀ hcard
  calc (Nat.card H : ℂ) * A.gaussSum
      = ∑ h : H, ∑ x, expCircle (A.quadratic (x + h)) := by
        simp [hshift, Nat.card_eq_fintype_card]
    _ = ∑ x, expCircle (A.quadratic x) *
          ∑ h : H, expCircle (A.toFiniteBilinearModule.pairing (x - a) h) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ ↦ ?_
        rw [quadratic_add_of_constantOn_coset a ha, AddChar.map_add_eq_mul]
    _ = ∑ x, expCircle (A.quadratic x) *
          (if x - a ∈ H then (Nat.card H : ℂ) else 0) := by
        simp_rw [sum_expCircle_pairing_sub a hH]
    _ = (Nat.card H : ℂ) * ((Nat.card H : ℂ) * expCircle (A.quadratic a)) := by
        rw [← Equiv.sum_comp (Equiv.addLeft a)]
        simp only [Equiv.coe_addLeft, add_sub_cancel_left]
        rw [← sum_expCircle_translate_filter a ha, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        split_ifs <;> simp [mul_comm]

end TauCeti.FiniteQuadraticModule
