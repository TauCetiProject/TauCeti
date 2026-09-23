/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.GroupTheory.Index

/-!
# Torsion in residue rings with power modulus

For every nonzero `p`, the subgroup of `ZMod (p ^ (k + 1))` killed by `p` is additively
equivalent to `ZMod p`.
-/

public section

namespace TauCeti

/-- The homomorphism underlying `zmodTorsionByEquiv`. -/
private def zmodTorsionByEquivHom (p k : ℕ) :
    ZMod p →+ AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ) := by
  let P : AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ) :=
    ⟨(p ^ k : ZMod (p ^ (k + 1))), AddSubgroup.torsionBy.nsmul_iff.2 (by
      simp only [nsmul_eq_mul]
      rw [mul_comm, ← pow_succ, ← Nat.cast_pow, ZMod.natCast_self])⟩
  exact ZMod.lift p ⟨zmultiplesHom _ P, by
    exact (zmultiplesHom_apply _ P (p : ℤ)).trans <|
      (natCast_zsmul P p).trans (AddSubgroup.torsionBy.nsmul P)⟩

/-- The subgroup of `ZMod (p ^ (k + 1))` killed by `p` is additively equivalent to `ZMod p`. -/
noncomputable def zmodTorsionByEquiv (p k : ℕ) [NeZero p] :
    ZMod p ≃+ AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ) := by
  let f := zmodTorsionByEquivHom p k
  have hf_inj : Function.Injective f := by
    dsimp only [f, zmodTorsionByEquivHom]
    rw [ZMod.lift_injective]
    intro m hm
    have hm' : ((m * (p : ℤ) ^ k : ℤ) : ZMod (p ^ (k + 1))) = 0 := by
      simpa [zmodTorsionByEquivHom, ZMod.lift_coe, zmultiplesHom_apply, mul_comm] using
        congrArg Subtype.val hm
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hm'
    have hp0 : (p : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne p)
    have hm'' : (p : ℤ) ^ k * p ∣ (p : ℤ) ^ k * m := by
      simpa [pow_succ, mul_comm] using hm'
    have hpm : (p : ℤ) ∣ m := by
      exact (mul_dvd_mul_iff_left hp0).mp hm''
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd m p).2 hpm
  have hf_surj : Function.Surjective f := by
    intro x
    have hx : ((p : ℤ) : ZMod (p ^ (k + 1))) * x.1 = 0 := by
      simpa only [Int.cast_smul_eq_zsmul, zsmul_eq_mul] using
        (Submodule.mem_torsionBy_iff _ _).mp x.2
    have hdiv : p ^ k ∣ x.1.val := by
      rw [← ZMod.natCast_zmod_val x.1] at hx
      simp only [Int.cast_natCast] at hx
      rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
      have hx' : p * p ^ k ∣ p * x.1.val := by
        simpa only [pow_succ, mul_comm (p ^ k)] using hx
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (NeZero.ne p))).mp hx'
    refine ⟨(((x.1.val / p ^ k : ℕ) : ℤ) : ZMod p), Subtype.ext ?_⟩
    dsimp only [f, zmodTorsionByEquivHom]
    rw [ZMod.lift_coe]
    simp only [zmultiplesHom_apply]
    rw [natCast_zsmul]
    change (x.1.val / p ^ k) • (p ^ k : ZMod (p ^ (k + 1))) = x.1
    rw [nsmul_eq_mul]
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.div_mul_cancel hdiv, ZMod.natCast_zmod_val]
  exact
    { toFun := f
      invFun := fun x ↦ Classical.choose (hf_surj x)
      left_inv := fun x ↦ hf_inj (by exact Classical.choose_spec (hf_surj (f x)))
      right_inv := fun x ↦ Classical.choose_spec (hf_surj x)
      map_add' := fun x y ↦ f.map_add x y }

/-- `zmodTorsionByEquiv` sends a residue to its multiple by `p ^ k` in the ambient residue ring. -/
@[simp]
theorem zmodTorsionByEquiv_apply_coe (p k : ℕ) [NeZero p] (x : ZMod p) :
    ((zmodTorsionByEquiv p k x : ZMod (p ^ (k + 1))) : ZMod (p ^ (k + 1))) =
      (x.val * p ^ k : ℕ) := by
  -- The equivalence uses `zmodTorsionByEquivHom` as its forward map.
  change ((zmodTorsionByEquivHom p k x :
    AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ)) : ZMod (p ^ (k + 1))) = _
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  unfold zmodTorsionByEquivHom
  dsimp only
  conv_lhs => rw [← Int.cast_natCast x.val]
  rw [ZMod.lift_coe]
  simp [zmultiplesHom_apply]

/-- Membership in the image of `zmodTorsionByEquiv` is characterized in the ambient residue ring. -/
@[simp]
theorem zmodTorsionByEquiv_apply_eq_iff (p k : ℕ) [NeZero p] (x : ZMod p)
    (y : AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ)) :
    zmodTorsionByEquiv p k x = y ↔
      (x.val * p ^ k : ℕ) = (y.1 : ZMod (p ^ (k + 1))) := by
  rw [← zmodTorsionByEquiv_apply_coe]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Subtype.ext h

/-- The inverse picks the unique residue whose multiple by `p ^ k` is the given torsion point. -/
theorem zmodTorsionByEquiv_symm_apply_eq_iff (p k : ℕ) [NeZero p]
    (y : AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ)) (x : ZMod p) :
    (zmodTorsionByEquiv p k).symm y = x ↔
      (x.val * p ^ k : ℕ) = (y.1 : ZMod (p ^ (k + 1))) := by
  change (zmodTorsionByEquiv p k).toEquiv.symm y = x ↔ _
  rw [Equiv.symm_apply_eq, eq_comm]
  exact zmodTorsionByEquiv_apply_eq_iff p k x y

end TauCeti

end
