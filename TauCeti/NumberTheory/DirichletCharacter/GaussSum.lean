/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import TauCeti.NumberTheory.DirichletCharacter.Conductor

/-!
# Primitive Dirichlet Gauss sums in characteristic zero

This file extends the Gauss-sum API from finite fields to primitive Dirichlet characters of an
arbitrary level. For a primitive character `χ` and a primitive additive character `e` of
`ZMod N`, the product of the Gauss sums for `(χ, e)` and `(χ⁻¹, e⁻¹)` is `N`. For a
quadratic character this gives the familiar square formula
`gaussSum χ e ^ 2 = χ (-1) * N`.

The characteristic-zero specialization `gaussSumOfPrimitiveRoot χ hζ` uses the additive
character defined by a primitive root of unity `ζ`. Its Galois action is χ⁻¹ applied to the
cyclotomic character, so its stabilizer is the kernel of χ. This is the form needed to identify
quadratic subfields of cyclotomic fields.

The Gauss-sum identities are classical; see K. Ireland and M. Rosen, *A Classical Introduction to
Modern Number Theory*, Chapter 6.
-/

public section

open AddChar

namespace DirichletCharacter

/-! ### Gauss sums of primitive Dirichlet characters -/

/-- The Gauss sums of a primitive Dirichlet character and its inverse, taken against inverse
additive characters, multiply to the level. This holds for composite levels, unlike the
finite-field result `gaussSum_mul_gaussSum_eq_card`.
-/
theorem gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter R n} (hχ : IsPrimitive χ)
    {e : AddChar (ZMod n) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = Fintype.card (ZMod n) := by
  classical
  simp only [gaussSum]
  rw [Finset.mul_sum]
  calc
    ∑ b, gaussSum χ e * (χ⁻¹ b * e⁻¹ b) =
        ∑ b, gaussSum χ (e.mulShift b) * e⁻¹ b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [gaussSum_mulShift_of_isPrimitive e hχ b]
      ring
    _ = ∑ b, ∑ a, χ a * e (b * a) * e (-b) := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [gaussSum, AddChar.mulShift_apply, AddChar.inv_apply, Finset.sum_mul]
    _ = ∑ a, χ a * ∑ b, e (b * (a - 1)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_assoc, ← e.map_add_eq_mul]
      congr 2
      ring
    _ = Fintype.card (ZMod n) := by
      simp_rw [AddChar.sum_mulShift _ he]
      rw [Finset.sum_eq_single 1]
      · simp
      · intro b _ hb
        simp [sub_eq_zero, hb]
      · simp

/-- The square of the Gauss sum of a primitive quadratic Dirichlet character is its value at
`-1` times the level. -/
theorem gaussSum_sq_of_isPrimitive_of_isQuadratic
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter R n} (hχ : IsPrimitive χ) (hquad : χ.IsQuadratic)
    {e : AddChar (ZMod n) R} (he : e.IsPrimitive) :
    gaussSum χ e ^ 2 = χ (-1) * Fintype.card (ZMod n) := by
  have hinv : χ⁻¹ = χ := hquad.inv
  have hshift : gaussSum χ⁻¹ e⁻¹ = χ (-1) * gaussSum χ e := by
    rw [hinv, e.inv_mulShift, ← Units.coe_neg_one, gaussSum_mulShift_eq, hinv]
  have hprod := gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive hχ he
  rw [hshift] at hprod
  have hsign : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]
    norm_num
  calc
    gaussSum χ e ^ 2 = 1 * gaussSum χ e ^ 2 := by rw [one_mul]
    _ = (χ (-1) * χ (-1)) * gaussSum χ e ^ 2 := by rw [hsign]
    _ = χ (-1) * (gaussSum χ e * (χ (-1) * gaussSum χ e)) := by ring
    _ = χ (-1) * Fintype.card (ZMod n) := by rw [hprod]

/-! ### Galois action in characteristic zero -/

variable {L : Type*} [Field L] [CharZero L] {N : ℕ} [NeZero N]

/-- The Gauss sum of an integer-valued Dirichlet character, formed with the additive character
defined by a primitive root of unity in a characteristic-zero field. -/
noncomputable def gaussSumOfPrimitiveRoot (χ : DirichletCharacter ℤ N) {ζ : L}
    (hζ : IsPrimitiveRoot ζ N) : L :=
  gaussSum (χ.ringHomComp (Int.castRingHom L)) (AddChar.zmodChar N hζ.pow_eq_one)

omit [CharZero L] in
/-- Expresses `gaussSumOfPrimitiveRoot` using the underlying Dirichlet Gauss sum. -/
theorem gaussSumOfPrimitiveRoot_def (χ : DirichletCharacter ℤ N) {ζ : L}
    (hζ : IsPrimitiveRoot ζ N) :
    gaussSumOfPrimitiveRoot χ hζ =
      gaussSum (χ.ringHomComp (Int.castRingHom L)) (AddChar.zmodChar N hζ.pow_eq_one) := by
  rw [gaussSumOfPrimitiveRoot]

/-- The square formula for the Gauss sum formed from a primitive root of unity. -/
theorem gaussSumOfPrimitiveRoot_sq (χ : DirichletCharacter ℤ N) (hχ : IsPrimitive χ)
    (hquad : χ.IsQuadratic) {ζ : L} (hζ : IsPrimitiveRoot ζ N) :
    gaussSumOfPrimitiveRoot χ hζ ^ 2 =
      (χ.ringHomComp (Int.castRingHom L)) (-1) * Fintype.card (ZMod N) := by
  apply gaussSum_sq_of_isPrimitive_of_isQuadratic
  · exact (isPrimitive_ringHomComp_iff χ (Int.castRingHom L) Int.cast_injective).mpr hχ
  · exact hquad.comp _
  · exact AddChar.zmodChar_primitive_of_primitive_root N hζ

/-- A Galois automorphism acts on a Dirichlet Gauss sum through the inverse character evaluated at
its cyclotomic character. -/
theorem map_gaussSumOfPrimitiveRoot (χ : DirichletCharacter ℤ N) {ζ : L}
    (hζ : IsPrimitiveRoot ζ N) (σ : L ≃ₐ[ℚ] L) :
    σ (gaussSumOfPrimitiveRoot χ hζ) =
      (χ.ringHomComp (Int.castRingHom L))⁻¹ (hζ.autToPow ℚ σ) *
        gaussSumOfPrimitiveRoot χ hζ := by
  simp only [gaussSumOfPrimitiveRoot]
  rw [gaussSum, map_sum]
  have hmap (a : ZMod N) :
      σ ((χ.ringHomComp (Int.castRingHom L)) a * AddChar.zmodChar N hζ.pow_eq_one a) =
        (χ.ringHomComp (Int.castRingHom L)) a *
          (AddChar.zmodChar N hζ.pow_eq_one).mulShift (hζ.autToPow ℚ σ) a := by
    rw [map_mul]
    simp only [MulChar.ringHomComp_apply]
    have hcast : σ ((Int.castRingHom L) (χ a)) = (Int.castRingHom L) (χ a) := by
      simp
    rw [hcast, mulShift_apply, AddChar.zmodChar_apply, AddChar.zmodChar_apply,
      map_pow, ← hζ.autToPow_spec ℚ σ, ← pow_mul]
    congr 1
    apply pow_eq_pow_of_modEq _ hζ.pow_eq_one
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  simp_rw [hmap]
  exact gaussSum_mulShift_eq _ _ _

/-- The Gauss sum attached to a primitive integer-valued Dirichlet character does not vanish in a
characteristic-zero field. -/
theorem gaussSumOfPrimitiveRoot_ne_zero (χ : DirichletCharacter ℤ N)
    (hχ : IsPrimitive χ) {ζ : L} (hζ : IsPrimitiveRoot ζ N) :
    gaussSumOfPrimitiveRoot χ hζ ≠ 0 := by
  let χL := χ.ringHomComp (Int.castRingHom L)
  let e := AddChar.zmodChar N hζ.pow_eq_one
  have hcard : (Fintype.card (ZMod N) : L) ≠ 0 := by
    rw [ZMod.card]
    exact Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hχL : IsPrimitive χL :=
    (isPrimitive_ringHomComp_iff χ (Int.castRingHom L) Int.cast_injective).mpr hχ
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root N hζ
  intro hzero
  have hprod := gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive hχL he
  have hz : gaussSum χL e = 0 := by
    simpa only [gaussSumOfPrimitiveRoot, χL, e] using hzero
  rw [hz, zero_mul] at hprod
  exact hcard hprod.symm

/-- The stabilizer of a primitive Dirichlet Gauss sum is the kernel of the character composed with
the cyclotomic character. -/
theorem stabilizer_gaussSumOfPrimitiveRoot (χ : DirichletCharacter ℤ N)
    (hχ : IsPrimitive χ) {ζ : L} (hζ : IsPrimitiveRoot ζ N) :
    MulAction.stabilizer Gal(L/ℚ) (gaussSumOfPrimitiveRoot χ hζ) =
      (χ.toUnitHom.comp (hζ.autToPow ℚ)).ker := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, MonoidHom.mem_ker,
    MonoidHom.comp_apply, map_gaussSumOfPrimitiveRoot]
  have hg := gaussSumOfPrimitiveRoot_ne_zero χ hχ hζ
  constructor
  · intro h
    have hc : (χ.ringHomComp (Int.castRingHom L))⁻¹ (hζ.autToPow ℚ σ) = 1 := by
      apply (mul_left_inj' hg).mp
      simpa using h
    rw [MulChar.inv_apply_eq_inv, MulChar.ringHomComp_apply] at hc
    have hc' := congrArg Ring.inverse hc
    have hu : IsUnit ((Int.castRingHom L) (χ (hζ.autToPow ℚ σ : ZMod N))) := by
      simpa only [MulChar.ringHomComp_apply] using
        (hζ.autToPow ℚ σ).isUnit.map (χ.ringHomComp (Int.castRingHom L))
    rw [Ring.inverse_inverse hu, Ring.inverse_one] at hc'
    rw [eq_intCast, Int.cast_eq_one] at hc'
    apply Units.ext
    simpa only [MulChar.coe_toUnitHom, Units.val_one] using hc'
  · intro h
    have hv := congrArg ((↑) : ℤˣ → ℤ) h
    simp only [MulChar.coe_toUnitHom, Units.val_one] at hv
    simp only [MulChar.inv_apply_eq_inv, MulChar.ringHomComp_apply, hv, map_one,
      Ring.inverse_one, one_mul]

end DirichletCharacter
