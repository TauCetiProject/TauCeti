/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.Index

/-!
# Prime torsion in prime-power residue rings

The subgroup of `ZMod (p ^ (k + 1))` killed by `p` is additively equivalent to `ZMod p`.
-/

public section

namespace TauCeti

namespace ZMod

/-- The subgroup of `ZMod (p ^ (k + 1))` killed by `p` is additively equivalent to `ZMod p`. -/
noncomputable def torsionByPrimeEquiv (p k : ℕ) [NeZero p] :
    ZMod p ≃+ AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ) := by
  let P : AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ) :=
    ⟨(p ^ k : ZMod (p ^ (k + 1))), AddSubgroup.torsionBy.nsmul_iff.2 (by
      simp only [nsmul_eq_mul]
      rw [mul_comm, ← pow_succ, ← Nat.cast_pow, ZMod.natCast_self])⟩
  let f : ZMod p →+ AddSubgroup.torsionBy (ZMod (p ^ (k + 1))) (p : ℤ) :=
    ZMod.lift p ⟨zmultiplesHom _ P, by
      exact (zmultiplesHom_apply _ P (p : ℤ)).trans <|
        (natCast_zsmul P p).trans (AddSubgroup.torsionBy.nsmul P)⟩
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · dsimp only [f]
    rw [ZMod.lift_injective]
    intro m hm
    have hm' : ((m * (p : ℤ) ^ k : ℤ) : ZMod (p ^ (k + 1))) = 0 := by
      simpa [P, ZMod.lift_coe, zmultiplesHom_apply, mul_comm] using congrArg Subtype.val hm
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hm'
    have hp0 : (p : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne p)
    have hm'' : (p : ℤ) ^ k * p ∣ (p : ℤ) ^ k * m := by
      simpa [pow_succ, mul_comm] using hm'
    have hpm : (p : ℤ) ∣ m := by
      exact (mul_dvd_mul_iff_left hp0).mp hm''
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd m p).2 hpm
  · intro x
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
    dsimp only [f]
    rw [ZMod.lift_coe]
    simp only [zmultiplesHom_apply]
    rw [natCast_zsmul]
    change (x.1.val / p ^ k) • (p ^ k : ZMod (p ^ (k + 1))) = x.1
    rw [nsmul_eq_mul]
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.div_mul_cancel hdiv, ZMod.natCast_zmod_val]

end ZMod

end TauCeti

end
