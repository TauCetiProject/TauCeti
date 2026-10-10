/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Cyclic
import TauCeti.Data.ZMod.UnitSquare
import TauCeti.Data.ZMod.MulCastHom
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Relations between cyclic dyadic generators of unequal exponents

For cyclic generators whose exponents differ by two, simultaneously multiplying both
odd coefficients by five preserves the quadratic form. Multiplication by four from the
smaller cyclic group to the larger one and reduction in the reverse direction make the
coordinate rotation well defined.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(h), (k).
-/

public section

namespace TauCeti.FiniteQuadraticModule

private theorem dyadicCyclic_prod_gap_two_quadratic_intCast (k : ℕ) [NeZero k]
    (θ η x y : ℤ) :
    ((dyadicCyclic k θ).prod (dyadicCyclic (k + 2) η)).quadratic
        ((x : ZMod (2 ^ k)), (y : ZMod (2 ^ (k + 2)))) =
      ZMod.toRatAddCircle (2 ^ (k + 3))
        ((4 * θ * x ^ 2 + η * y ^ 2 : ℤ) : ZMod (2 ^ (k + 3))) := by
  rw [ZMod.toRatAddCircle_intCast]
  erw [prod_quadratic, dyadicCyclic_quadratic_intCast, dyadicCyclic_quadratic_intCast]
  rw [← AddCircle.coe_add]
  congr 1
  push_cast
  rw [show k + 3 = k + 1 + 2 by omega, pow_add]
  norm_num
  field_simp
  ring

private def dyadicGapTwoRotation (k : ℕ) (a b : ℤ) :
    (ZMod (2 ^ k) × ZMod (2 ^ (k + 2))) →+
      (ZMod (2 ^ k) × ZMod (2 ^ (k + 2))) where
  toFun x :=
    ((a : ZMod (2 ^ k)) * x.1 - (b : ZMod (2 ^ k)) *
      ZMod.castHom (pow_dvd_pow 2 (by omega : k ≤ k + 2)) (ZMod (2 ^ k)) x.2,
      ZMod.mulCastHom 4 (by simp [pow_add]) x.1 + (a : ZMod (2 ^ (k + 2))) * x.2)
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> ring

private theorem dyadicGapTwoRotation_quadratic (k : ℕ) [NeZero k] (θ η a b : ℤ)
    (hsq : (a : ZMod (2 ^ (k + 3))) ^ 2 + 4 * b = 5)
    (hcoef : (θ : ZMod (2 ^ (k + 3))) * b = η)
    (x : ((dyadicCyclic k (5 * θ)).prod (dyadicCyclic (k + 2) (5 * η))).carrier) :
    ((dyadicCyclic k θ).prod (dyadicCyclic (k + 2) η)).quadratic
        (dyadicGapTwoRotation k a b x) =
      ((dyadicCyclic k (5 * θ)).prod (dyadicCyclic (k + 2) (5 * η))).quadratic x := by
  rcases x with ⟨x, y⟩
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ k) x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ (k + 2)) y
  have hrot : dyadicGapTwoRotation k a b
      ((m : ZMod (2 ^ k)), (n : ZMod (2 ^ (k + 2)))) =
    (((a * m - b * n : ℤ) : ZMod (2 ^ k)),
      ((4 * m + a * n : ℤ) : ZMod (2 ^ (k + 2)))) := by
    -- Reduce the two coordinate applications, leaving the homomorphism proof fields intact.
    apply Prod.ext
    · change (a : ZMod (2 ^ k)) * (m : ZMod (2 ^ k)) - (b : ZMod (2 ^ k)) *
          ZMod.castHom (pow_dvd_pow 2 (by omega : k ≤ k + 2)) (ZMod (2 ^ k))
            (n : ZMod (2 ^ (k + 2))) = _
      rw [map_intCast]
      push_cast
      ring
    · change ZMod.mulCastHom 4 (by simp [pow_add]) (m : ZMod (2 ^ k)) +
          (a : ZMod (2 ^ (k + 2))) * (n : ZMod (2 ^ (k + 2))) = _
      rw [ZMod.mulCastHom_intCast]
      push_cast
      ring
  erw [hrot]
  erw [dyadicCyclic_prod_gap_two_quadratic_intCast,
    dyadicCyclic_prod_gap_two_quadratic_intCast]
  congr 1
  push_cast
  rw [← hcoef]
  linear_combination
    (θ : ZMod (2 ^ (k + 3))) * (4 * (m : ZMod (2 ^ (k + 3))) ^ 2 + b * n ^ 2) * hsq

/-- Simultaneously multiplying two odd cyclic coefficients by five preserves their
orthogonal sum when their exponents differ by two, as in Nikulin's relation 1.8.2(h). -/
noncomputable def dyadicCyclicProdGapTwoIsometryFiveMul (k : ℕ) [NeZero k] {θ η : ℤ}
    (hθ : Odd θ) (hη : Odd η) :
    Isometry ((dyadicCyclic k θ).prod (dyadicCyclic (k + 2) η))
      ((dyadicCyclic k (5 * θ)).prod (dyadicCyclic (k + 2) (5 * η))) :=
  Classical.choice <| by
    have hunit (s : ℤ) (hs : Odd s) : IsUnit (s : ZMod (2 ^ (k + 3))) := by
      obtain ⟨t, rfl⟩ := hs
      convert ZMod.isUnit_two_mul_add (c := (t : ZMod (2 ^ (k + 3)))) isUnit_one using 1
      push_cast
      ring
    obtain ⟨Θ, hΘ⟩ := hunit θ hθ
    let r : ZMod (2 ^ (k + 3)) := (η : ZMod (2 ^ (k + 3))) * (Θ⁻¹ : (ZMod (2 ^ (k + 3)))ˣ)
    have hr : IsUnit r := (hunit η hη).mul (Units.isUnit Θ⁻¹)
    have hθr : (θ : ZMod (2 ^ (k + 3))) * r = η := by
      dsimp [r]
      rw [← hΘ, mul_left_comm, Units.mul_inv, mul_one]
    obtain ⟨u, hu⟩ := ZMod.exists_unit_sq_eq_five_sub_four_mul (k := k + 2) hr
    let a : ℤ := u.val.val
    let b : ℤ := r.val
    have ha : (a : ZMod (2 ^ (k + 3))) = u.val := by simp [a]
    have hb : (b : ZMod (2 ^ (k + 3))) = r := by simp [b]
    have hsq : (a : ZMod (2 ^ (k + 3))) ^ 2 + 4 * b = 5 := by
      rw [ha, hb, hu]
      ring
    have hcoef : (θ : ZMod (2 ^ (k + 3))) * b = η := by rw [hb]; exact hθr
    let g : Hom ((dyadicCyclic k (5 * θ)).prod (dyadicCyclic (k + 2) (5 * η)))
        ((dyadicCyclic k θ).prod (dyadicCyclic (k + 2) η)) :=
      { toLinearMap := (dyadicGapTwoRotation k a b).toIntLinearMap
        map_app' := fun x ↦ by
          simpa only [LinearMap.toFun_eq_coe, AddMonoidHom.coe_toIntLinearMap] using
            dyadicGapTwoRotation_quadratic k θ η a b hsq hcoef x }
    have hsource :
        ((dyadicCyclic k (5 * θ)).prod (dyadicCyclic (k + 2) (5 * η))).IsNondegenerate :=
      (isNondegenerate_prod _ _).mpr
        ⟨(isNondegenerate_dyadicCyclic_iff _ _).mpr ((by decide : Odd (5 : ℤ)).mul hθ),
          (isNondegenerate_dyadicCyclic_iff _ _).mpr ((by decide : Odd (5 : ℤ)).mul hη)⟩
    have hinj : Function.Injective g := fun x y hxy ↦
      FiniteBilinearModule.Hom.injective g.toFiniteBilinearModule hsource
        ((Hom.toFiniteBilinearModule_apply g x).trans
          (hxy.trans (Hom.toFiniteBilinearModule_apply g y).symm))
    exact ⟨(g.toIsometry ((Nat.bijective_iff_injective_and_card g).mpr ⟨hinj, rfl⟩)).symm⟩

end TauCeti.FiniteQuadraticModule
