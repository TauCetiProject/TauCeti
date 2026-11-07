/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Torsion in residue rings

For nonzero `m` and `n`, the subgroup of `ZMod (m * n)` killed by `m` is additively equivalent to
`ZMod m`, by multiplication by `n` (`TauCeti.zmodTorsionByEquiv`). With `m = p` and `n = p ^ k`
this counts the elements killed by `p` in the prime-power cyclic factor `ZMod (p * p ^ k)`, as
required by the rank-two finite-abelian criterion.

For every nonzero `p`, an element of `ZMod (p ^ (n + 1))` is killed by `p` exactly when it is the
reduction of a multiple of `p ^ n` (`ZMod.zsmul_eq_zero_iff_exists_eq_pow_mul`). In the first
nontrivial case, an element of `ZMod (p ^ 2)` is killed by `p` exactly when it reduces to `0`
modulo `p` (`ZMod.cast_eq_zero_iff_natCast_mul_eq_zero`); this is what prevents a character of
order `p` from lifting modulo `p ^ 2`.
-/

public section

/-- An element of `ZMod (p ^ 2)` reduces to `0` modulo `p` exactly when it is killed by `p`. -/
theorem ZMod.cast_eq_zero_iff_natCast_mul_eq_zero {p : ℕ} [NeZero p] {u : ZMod (p ^ 2)} :
    (ZMod.cast u : ZMod p) = 0 ↔ (p : ZMod (p ^ 2)) * u = 0 := by
  rw [← ZMod.natCast_zmod_val u, ZMod.cast_natCast (dvd_pow_self p two_ne_zero), ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff,
    ← Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (NeZero.ne p)), ← sq]

/-- An element of `ZMod (p ^ (n + 1))` is killed by `p` exactly when it is the reduction of a
multiple of `p ^ n`. -/
theorem ZMod.zsmul_eq_zero_iff_exists_eq_pow_mul {p n : ℕ} [NeZero p] {x : ZMod (p ^ (n + 1))} :
    (p : ℤ) • x = 0 ↔ ∃ t : ℤ, x = (((p : ℤ) ^ n * t : ℤ) : ZMod (p ^ (n + 1))) := by
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective x
  rw [zsmul_eq_mul, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow, pow_succ,
    mul_comm ((p : ℤ) ^ n), Int.mul_dvd_mul_iff_left (by exact_mod_cast NeZero.ne p)]
  refine ⟨fun ⟨t, ht⟩ ↦ ⟨t, by rw [ht]⟩, fun ⟨t, ht⟩ ↦ ?_⟩
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, Nat.cast_pow, pow_succ] at ht
  exact (dvd_sub_right (dvd_mul_right _ _)).mp ((dvd_mul_right _ _).trans ht)

namespace TauCeti

/-- The homomorphism underlying `zmodTorsionByEquiv`: multiplication by `n`. -/
private def zmodTorsionByEquivHom (m n : ℕ) :
    ZMod m →+ AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ) :=
  ZMod.lift m ⟨zmultiplesHom _ ⟨(n : ZMod (m * n)), AddSubgroup.torsionBy.nsmul_iff.2 <| by
      rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_self]⟩,
    (natCast_zsmul _ m).trans (AddSubgroup.torsionBy.nsmul _)⟩

/-- The underlying homomorphism sends the residue of an integer `t` to the residue of `t * n`. -/
private theorem zmodTorsionByEquivHom_intCast_coe (m n : ℕ) (t : ℤ) :
    (zmodTorsionByEquivHom m n t : ZMod (m * n)) = ((t * n : ℤ) : ZMod (m * n)) := by
  simp [zmodTorsionByEquivHom, ZMod.lift_coe, zmultiplesHom_apply]

/-- The representative of an element of `ZMod (m * n)` killed by `m` is divisible by `n`. -/
private theorem dvd_val_of_mem_torsionBy {m n : ℕ} [NeZero m] [NeZero n] {y : ZMod (m * n)}
    (hy : y ∈ AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ)) : n ∣ y.val := by
  rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_eq_mul, ← ZMod.natCast_zmod_val y, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff] at hy
  exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (NeZero.ne m))).mp hy

/-- Multiplication by `n` is a bijection from `ZMod m` onto the `m`-torsion of `ZMod (m * n)`. -/
private theorem zmodTorsionByEquivHom_bijective (m n : ℕ) [NeZero m] [NeZero n] :
    Function.Bijective (zmodTorsionByEquivHom m n) := by
  refine ⟨(ZMod.lift_injective m).2 fun t ht ↦ ?_, fun y ↦ ?_⟩
  · have ht' : ((t * n : ℤ) : ZMod (m * n)) = 0 := by
      simpa [zmultiplesHom_apply] using congrArg Subtype.val ht
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul,
      mul_dvd_mul_iff_right (by exact_mod_cast NeZero.ne n)] at ht'
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd t m).2 ht'
  · refine ⟨((y.1.val / n : ℕ) : ℤ), Subtype.ext ?_⟩
    rw [zmodTorsionByEquivHom_intCast_coe, ← Nat.cast_mul, Int.cast_natCast,
      Nat.div_mul_cancel (dvd_val_of_mem_torsionBy y.2), ZMod.natCast_zmod_val]

/-- For nonzero `m` and `n`, the subgroup of `ZMod (m * n)` killed by `m` is additively
equivalent to `ZMod m`, by multiplication by `n`. -/
noncomputable def zmodTorsionByEquiv (m n : ℕ) [NeZero m] [NeZero n] :
    ZMod m ≃+ AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ) :=
  AddEquiv.ofBijective (zmodTorsionByEquivHom m n) (zmodTorsionByEquivHom_bijective m n)

/-- `zmodTorsionByEquiv` sends a residue to its multiple by `n` in the ambient residue ring. -/
@[simp]
theorem zmodTorsionByEquiv_apply_coe (m n : ℕ) [NeZero m] [NeZero n] (x : ZMod m) :
    (zmodTorsionByEquiv m n x : ZMod (m * n)) = (x.val * n : ℕ) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  simpa [zmodTorsionByEquiv] using zmodTorsionByEquivHom_intCast_coe m n x.val

/-- The inverse of `zmodTorsionByEquiv` divides the representative by `n`. -/
@[simp]
theorem zmodTorsionByEquiv_symm_apply (m n : ℕ) [NeZero m] [NeZero n]
    (y : AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ)) :
    (zmodTorsionByEquiv m n).symm y = ((y.1.val / n : ℕ) : ZMod m) := by
  refine (AddEquiv.symm_apply_eq _).2 (Subtype.ext ?_)
  rw [zmodTorsionByEquiv_apply_coe, ZMod.val_natCast, ← Nat.mul_mod_mul_right, ZMod.natCast_mod,
    Nat.div_mul_cancel (dvd_val_of_mem_torsionBy y.2), ZMod.natCast_zmod_val]

/-- Equality with the image of a chosen residue under `zmodTorsionByEquiv` is characterized in
the ambient residue ring. -/
theorem zmodTorsionByEquiv_apply_eq_iff (m n : ℕ) [NeZero m] [NeZero n] (x : ZMod m)
    (y : AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ)) :
    zmodTorsionByEquiv m n x = y ↔ (x.val * n : ℕ) = (y : ZMod (m * n)) := by
  rw [Subtype.ext_iff, zmodTorsionByEquiv_apply_coe]

/-- The inverse picks the unique residue whose multiple by `n` is the given torsion point. -/
theorem zmodTorsionByEquiv_symm_apply_eq_iff (m n : ℕ) [NeZero m] [NeZero n]
    (y : AddSubgroup.torsionBy (ZMod (m * n)) (m : ℤ)) (x : ZMod m) :
    (zmodTorsionByEquiv m n).symm y = x ↔ (x.val * n : ℕ) = (y : ZMod (m * n)) := by
  rw [AddEquiv.symm_apply_eq, eq_comm, zmodTorsionByEquiv_apply_eq_iff]

end TauCeti

end
