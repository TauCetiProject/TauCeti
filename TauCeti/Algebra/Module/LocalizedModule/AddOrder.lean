/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Additive orders in modules over `ℤ[1/m]`

On a module over `ℤ[1/m] = Localization.Away m`, multiplication by `m` is injective, since `m` is
a unit of `ℤ[1/m]`. So it preserves additive orders, and the additive order of an element of
finite order is prime to `m`. An element killed by a nonzero scalar of `ℤ[1/m]` is killed by a
nonzero integer, after clearing denominators, so it has finite order prime to `m`. Hence its order
is invertible in every commutative ring in which `m = 0`. This is what makes the torsion part of a
uniquely `m`-divisible abelian group invisible to homology with coefficients in which `m = 0`.

## Main results

* `TauCeti.isUnit_addOrderOf_of_smul_eq_zero`: in a `ℤ[1/m]`-module, an element killed by a
  nonzero scalar has finite additive order prime to `m`, hence a unit of any commutative ring in
  which `m = 0`.
-/

public section

namespace TauCeti

/-- **Orders of torsion elements of a `ℤ[1/m]`-module.** An element of a `ℤ[1/m]`-module killed by
a nonzero scalar has finite additive order prime to `m`. So its order is a unit of every
commutative ring `k` in which `m = 0`. -/
theorem isUnit_addOrderOf_of_smul_eq_zero {k : Type*} [CommRing k] {m : ℤ} (hmk : (m : k) = 0)
    {M : Type*} [AddCommGroup M] [Module (Localization.Away m) M] {x : M}
    {r : Localization.Away m} (hr : r ≠ 0) (hx : r • x = 0) : IsUnit (addOrderOf x : k) := by
  have hu : IsUnit (m : Localization.Away m) :=
    by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away m) m
  -- `m ≠ 0`, since `ℤ[1/0]` is the zero ring
  have hm : m ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, isUnit_zero_iff] at hu
    exact hr (by rw [← mul_one r, ← hu, mul_zero])
  -- clearing the denominator of `r` gives a nonzero integer `a` killing `x`
  obtain ⟨j, a, ha⟩ := IsLocalization.Away.surj m r
  rw [eq_intCast, eq_intCast] at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero] at ha
    exact hr ((hu.pow j).mul_left_eq_zero.1 ha)
  have hax : a • x = 0 := by
    rw [← Int.cast_smul_eq_zsmul (Localization.Away m) a x, ← ha, mul_comm, mul_smul, hx,
      smul_zero]
  have hd : addOrderOf x ≠ 0 := fun h ↦ ha0 <| by
    simpa [h] using addOrderOf_dvd_iff_zsmul_eq_zero.2 hax
  -- multiplication by `|m|` is injective, so it preserves the order of `x`
  have hn : IsUnit (m.natAbs : Localization.Away m) := by
    have := isUnit_of_dvd_unit (map_dvd (Int.castRingHom (Localization.Away m))
      (Int.natAbs_dvd.2 (dvd_refl m))) (by simpa using hu)
    simpa using this
  have hord : addOrderOf ((m.natAbs : Localization.Away m) • x) = addOrderOf x :=
    addOrderOf_injective (DistribSMul.toAddMonoidHom M _)
      (fun _ _ h ↦ hn.smul_left_cancel.1 h) x
  rw [Nat.cast_smul_eq_nsmul, addOrderOf_nsmul' x (Int.natAbs_ne_zero.2 hm),
    Nat.div_eq_self] at hord
  have hcop : (addOrderOf x).Coprime m.natAbs := hord.resolve_left hd
  -- `|m|` vanishes in `k`, so the order of `x`, being coprime to it, is a unit of `k`
  have hnk : (m.natAbs : k) = 0 := by
    obtain ⟨c, hc⟩ := Int.dvd_natAbs.2 (dvd_refl m)
    rw [← Int.cast_natCast, hc, Int.cast_mul, hmk, zero_mul]
  simpa [hnk, isCoprime_zero_right] using hcop.cast (R := k)

end TauCeti
