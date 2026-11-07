/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Height.Basic
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Formal group laws of finite height over separably closed fields

Let `F` be a commutative formal group law of finite height `h` over a field `K` of
characteristic `p`, so that `[p]_F(T) = a T ^ (p ^ h) + ⋯` with `a ≠ 0`. The homothety `T ↦ u T`
turns `a` into `1` whenever `u ^ (p ^ h - 1) = a`
(`FormalGroup.coeff_nsmulSeries_homothety_smul_eq_one`). Since `p ^ h - 1` is `-1` in `K`, the
polynomial `X ^ (p ^ h - 1) - a` is separable, so over a separably closed field such a `u`
exists. This is the normalization in degree `p ^ h` in Lazard's classification of formal group
laws over separably closed fields by their height.

## Main results

* `FormalGroup.exists_coeff_nsmulSeries_homothety_smul_eq_one`: over a separably closed field, a
  homothety makes the leading coefficient of the `p`-series equal to one.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* A. Fröhlich, *Formal Groups*, Lecture Notes in Mathematics 74, Springer (1968), Chapter III.
-/

public section

namespace FormalGroup

/-- **Normalizing the leading coefficient of the `p`-series over a separably closed field.** Over
a separably closed field of characteristic `p`, a commutative formal group law `F` of finite
height `h` becomes, after the homothety `T ↦ u T` by a suitable unit `u`, a formal group law
whose `p`-series has leading term `T ^ (p ^ h)`. -/
theorem exists_coeff_nsmulSeries_homothety_smul_eq_one {K : Type*} [Field K] [IsSepClosed K]
    {p : ℕ} [hp : Fact p.Prime] [CharP K p] (F : FormalGroup K) [F.IsComm] {h : ℕ}
    (hF : F.height p = h) :
    ∃ u : Kˣ, PowerSeries.coeff (p ^ h)
      ((TauCeti.FormalCoordinate.homothety u • F).nsmulSeries p) = 1 := by
  set a := PowerSeries.coeff (p ^ h) (F.nsmulSeries p)
  have ha : a ≠ 0 := F.coeff_nsmulSeries_ne_zero_of_height_eq hF
  have hh : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr (F.ne_zero_of_height_eq_natCast hF)
  have hq : 1 < p ^ h := Nat.one_lt_pow (by omega) hp.out.one_lt
  -- `p ^ h - 1` is `-1` in `K`, so `X ^ (p ^ h - 1) - a` is separable and has a root `z`
  have : NeZero ((p ^ h - 1 : ℕ) : K) := ⟨by
    rw [Nat.cast_sub hq.le, Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega), Nat.cast_one,
      zero_sub, neg_ne_zero]
    exact one_ne_zero⟩
  obtain ⟨z, hz⟩ := IsSepClosed.exists_pow_nat_eq a (p ^ h - 1)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact ha (by rw [← hz, zero_pow (by omega)])
  exact ⟨Units.mk0 z hz0, F.coeff_nsmulSeries_homothety_smul_eq_one hF _ hz⟩

end FormalGroup
