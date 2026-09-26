/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Torsion in residue rings with power modulus

For every nonzero `p`, the subgroup of `ZMod (p ^ (k + 1))` killed by `p` is additively
equivalent to `ZMod p`. This counts the elements killed by `p` in prime-power cyclic factors,
as required by the rank-two finite-abelian criterion.
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

/-- The underlying homomorphism multiplies a residue by `p ^ k`. -/
private theorem zmodTorsionByEquivHom_apply_coe (p k : ℕ) [NeZero p] (x : ZMod p) :
    ((zmodTorsionByEquivHom p k x :
      AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ)) : ZMod (p ^ (k + 1))) =
      (x.val * p ^ k : ℕ) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  unfold zmodTorsionByEquivHom
  dsimp only
  conv_lhs => rw [← Int.cast_natCast x.val]
  rw [ZMod.lift_coe]
  simp [zmultiplesHom_apply]

/-- A point killed by `p` in `ZMod (p ^ (k + 1))` is `p ^ k` times the residue of its
representative divided by `p ^ k`: the representative is divisible by `p ^ k`, with quotient
smaller than `p`. -/
private theorem natCast_val_div_pow_mul_pow (p k : ℕ) [NeZero p]
    (y : AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ)) :
    (((((y.1.val / p ^ k : ℕ) : ZMod p).val * p ^ k : ℕ)) : ZMod (p ^ (k + 1))) = y.1 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hy : ((p : ℤ) : ZMod (p ^ (k + 1))) * y.1 = 0 := by
    simpa only [Int.cast_smul_eq_zsmul, zsmul_eq_mul] using
      (Submodule.mem_torsionBy_iff _ _).mp y.2
  rw [← ZMod.natCast_zmod_val y.1] at hy
  simp only [Int.cast_natCast] at hy
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hy
  have hy' : p * p ^ k ∣ p * y.1.val := by
    simpa only [pow_succ, mul_comm (p ^ k)] using hy
  have hdiv : p ^ k ∣ y.1.val := (Nat.mul_dvd_mul_iff_left hp).mp hy'
  have hlt : y.1.val / p ^ k < p := by
    apply (Nat.div_lt_iff_lt_mul (pow_pos hp k)).2
    simpa only [pow_succ, mul_comm] using y.1.val_lt
  rw [ZMod.val_natCast_of_lt hlt, Nat.div_mul_cancel hdiv, ZMod.natCast_zmod_val]

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
    refine ⟨(((x.1.val / p ^ k : ℕ) : ℤ) : ZMod p), Subtype.ext ?_⟩
    dsimp only [f]
    simp only [Int.cast_natCast]
    rw [zmodTorsionByEquivHom_apply_coe, natCast_val_div_pow_mul_pow]
  exact AddEquiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-- `zmodTorsionByEquiv` sends a residue to its multiple by `p ^ k` in the ambient residue ring. -/
@[simp]
theorem zmodTorsionByEquiv_apply_coe (p k : ℕ) [NeZero p] (x : ZMod p) :
    ((zmodTorsionByEquiv p k x : ZMod (p ^ (k + 1))) : ZMod (p ^ (k + 1))) =
      (x.val * p ^ k : ℕ) :=
  zmodTorsionByEquivHom_apply_coe p k x

/-- The inverse of `zmodTorsionByEquiv` divides the representative by `p ^ k`. -/
@[simp]
theorem zmodTorsionByEquiv_symm_apply (p k : ℕ) [NeZero p]
    (y : AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ)) :
    (zmodTorsionByEquiv p k).symm y = ((y.1.val / p ^ k : ℕ) : ZMod p) := by
  apply (zmodTorsionByEquiv p k).injective
  rw [(zmodTorsionByEquiv p k).apply_symm_apply]
  apply Subtype.ext
  symm
  rw [zmodTorsionByEquiv_apply_coe, natCast_val_div_pow_mul_pow]

/-- Equality with the image of a chosen residue under `zmodTorsionByEquiv` is characterized in
the ambient residue ring. -/
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
  constructor
  · intro h
    apply (zmodTorsionByEquiv_apply_eq_iff p k x y).mp
    rw [← h]
    exact (zmodTorsionByEquiv p k).apply_symm_apply y
  · intro h
    rw [← (zmodTorsionByEquiv_apply_eq_iff p k x y)] at h
    rw [← h]
    exact (zmodTorsionByEquiv p k).symm_apply_apply x

end TauCeti

end
