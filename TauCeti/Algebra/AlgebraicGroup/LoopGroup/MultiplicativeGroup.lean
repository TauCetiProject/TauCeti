/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LoopGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.CongruenceSubgroup
import Mathlib.Algebra.DualNumber

/-!
# Loops in the multiplicative group

For the multiplicative group `𝔾ₘ`, with coordinate Hopf algebra `k[T, T⁻¹]`, the identification
`TauCeti.MultiplicativeGroup.pointsMulEquiv` of points with units gives `LG(R) = R⸨t⸩ˣ` and
`L⁺G(R) = R⟦t⟧ˣ`, and under it the congruence subgroup `K_N(R)` is the group of units of the
form `1 + t ^ N f` with `f ∈ R⟦t⟧`. For `N ≥ 1` every such series is a unit, so
`K_N(R) = 1 + t ^ N R⟦t⟧`, while `K_0(R) = R⟦t⟧ˣ`.

Over a field `R` every loop has the form `a t ^ n u` with `a ∈ Rˣ`, `n ∈ ℤ` and `u ∈ K_1(R)`: this
is the valuation of `R⸨t⸩`. Over a nonreduced ring the description fails. If `ε ≠ 0` is
nilpotent, `1 + ε t⁻¹` is a unit of `R⸨t⸩`, but it is not `t ^ n` times a unit of `R⟦t⟧` for any
`n`, that is, not `t ^ n` times a positive loop; for `R = ℚ[ε] ⧸ (ε²)` its inverse is
`1 - ε t⁻¹`. So the loop group of `𝔾ₘ` is not the
functor `R ↦ Rˣ × ℤ × K_1(R)`, and it has to be defined on all commutative algebras by its
points.

## Main results

* `TauCeti.MultiplicativeGroup.mem_congruenceSubgroup_span_X_pow_iff`: a positive loop of `𝔾ₘ`
  lies in `K_N(R)` exactly when its unit is `1 + t ^ N f` for some `f ∈ R⟦t⟧`.
* `TauCeti.MultiplicativeGroup.exists_eq_single_mul_ofPowerSeries`: over a field, every loop of
  `𝔾ₘ` is `a t ^ n u` with `u ∈ K_1(R)`.
* `TauCeti.MultiplicativeGroup.exists_pointsMulEquiv_eq_one_add_single_neg_one` and
  `TauCeti.MultiplicativeGroup.not_exists_eq_single_mul_ofPowerSeries`: for a nonzero nilpotent
  `ε`, the unit `1 + ε t⁻¹` of `R⸨t⸩` is a loop of `𝔾ₘ` that is not `t ^ n` times a positive
  loop.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge Stud. Adv. Math. 103 (2007),
  §1.3.1, p. 19.
-/

public section

open HahnSeries PowerSeries WithConv
open scoped LaurentPolynomial

universe u w

-- The coefficientwise `k`-algebra structure on Laurent series, as in `CommAlgCat.laurentSeries`.
attribute [local instance 1100] HahnSeries.instAlgebra

namespace TauCeti

namespace MultiplicativeGroup

variable {k : Type u} [CommRing k]

/-- The loop group of `𝔾ₘ` is the unit group of Laurent series: `LG(R) = R⸨t⸩ˣ`. -/
noncomputable example (R : CommAlgCat.{w} k) :
    (HopfAlgebra.loopGroup k k[T;T⁻¹]).obj R ≃* (LaurentSeries R)ˣ :=
  pointsMulEquiv

/-- The positive loop group of `𝔾ₘ` is the unit group of power series: `L⁺G(R) = R⟦t⟧ˣ`. -/
noncomputable example (R : CommAlgCat.{w} k) :
    (HopfAlgebra.positiveLoopGroup k k[T;T⁻¹]).obj R ≃* (PowerSeries R)ˣ :=
  pointsMulEquiv

variable {R : Type w} [CommRing R] [Algebra k R]

/-- **Congruence subgroups of `𝔾ₘ`.** A positive loop of `𝔾ₘ` lies in `K_N(R)` exactly when the
unit of `R⟦t⟧` it represents is `1 + t ^ N f` for some `f ∈ R⟦t⟧`. -/
theorem mem_congruenceSubgroup_span_X_pow_iff {N : ℕ} {x : WithConv (k[T;T⁻¹] →ₐ[k] R⟦X⟧)} :
    x ∈ HopfAlgebra.congruenceSubgroup k k[T;T⁻¹] (Ideal.span {(X : R⟦X⟧) ^ N}) ↔
      ∃ f : R⟦X⟧, ((pointsMulEquiv x : R⟦X⟧ˣ) : R⟦X⟧) = 1 + X ^ N * f := by
  rw [mem_congruenceSubgroup_iff, Ideal.mem_span_singleton]
  exact ⟨fun ⟨f, hf⟩ ↦ ⟨f, by rw [← hf, add_sub_cancel]⟩,
    fun ⟨f, hf⟩ ↦ ⟨f, by rw [hf, add_sub_cancel_left]⟩⟩

/-- **Loops of `𝔾ₘ` over a field.** Over a field `R`, every loop of `𝔾ₘ` is `a t ^ n u` for a
unit `a` of `R`, an integer `n` and a positive loop `u ∈ K_1(R)`: the unit `x` of `R⸨t⸩` it
represents is `a t ^ n u` with `n` the order of `x` and `a` its leading coefficient. -/
theorem exists_eq_single_mul_ofPowerSeries {R : Type w} [Field R] [Algebra k R]
    (g : WithConv (k[T;T⁻¹] →ₐ[k] LaurentSeries R)) :
    ∃ (a : Rˣ) (n : ℤ) (u : WithConv (k[T;T⁻¹] →ₐ[k] R⟦X⟧)),
      u ∈ HopfAlgebra.congruenceSubgroup k k[T;T⁻¹] (Ideal.span {(X : R⟦X⟧) ^ 1}) ∧
        ((pointsMulEquiv g : (LaurentSeries R)ˣ) : LaurentSeries R) =
          single n (a : R) * ofPowerSeries ℤ R (pointsMulEquiv u : R⟦X⟧ˣ) := by
  set x : LaurentSeries R := (pointsMulEquiv g).val
  have hx : x ≠ 0 := (pointsMulEquiv g).ne_zero
  -- The leading coefficient `a` of `x` is the constant coefficient of its power series part.
  have ha : x.coeff x.order ≠ 0 := coeff_order_eq_zero.not.2 hx
  set a : Rˣ := Units.mk0 _ ha
  set q : R⟦X⟧ := PowerSeries.C (a⁻¹ : R) * x.powerSeriesPart
  have hq : constantCoeff q = 1 := by
    rw [map_mul, constantCoeff_C, ← coeff_zero_eq_constantCoeff_apply,
      LaurentSeries.powerSeriesPart_coeff, Nat.cast_zero, add_zero]
    exact a.inv_mul
  have hqu : IsUnit q := isUnit_iff_constantCoeff.2 (hq ▸ isUnit_one)
  refine ⟨a, x.order, pointsMulEquiv.symm hqu.unit, ?_, ?_⟩
  · rw [mem_congruenceSubgroup_span_X_pow_iff, MulEquiv.apply_symm_apply, IsUnit.unit_spec]
    have hq₁ : constantCoeff (q - 1) = 0 := by rw [map_sub, hq, map_one, sub_self]
    obtain ⟨f, hf⟩ := X_dvd_iff.2 hq₁
    exact ⟨f, by rw [pow_one, ← hf, add_sub_cancel]⟩
  · rw [MulEquiv.apply_symm_apply, IsUnit.unit_spec, map_mul, ofPowerSeries_C, HahnSeries.C_apply,
      ← mul_assoc, single_mul_single, add_zero, mul_inv_cancel₀ a.ne_zero]
    exact (LaurentSeries.single_order_mul_powerSeriesPart x).symm

variable (k) in
/-- For nilpotent `ε`, the Laurent series `1 + ε t⁻¹` is a unit of `R⸨t⸩`, hence a loop of `𝔾ₘ`. -/
theorem exists_pointsMulEquiv_eq_one_add_single_neg_one {ε : R} (hε : IsNilpotent ε) :
    ∃ g : WithConv (k[T;T⁻¹] →ₐ[k] LaurentSeries R),
      ((pointsMulEquiv g : (LaurentSeries R)ˣ) : LaurentSeries R) = 1 + single (-1) ε := by
  obtain ⟨m, hm⟩ := hε
  have hu : IsUnit (1 + single (-1) ε : LaurentSeries R) :=
    IsNilpotent.isUnit_one_add ⟨m, by rw [single_pow, hm, single_eq_zero]⟩
  exact ⟨pointsMulEquiv.symm hu.unit, by rw [MulEquiv.apply_symm_apply, IsUnit.unit_spec]⟩

/-- **The valuation description fails over nonreduced rings.** For a nonzero nilpotent `ε`, the
loop `1 + ε t⁻¹` of `𝔾ₘ` is not `t ^ n` times a positive loop for any integer `n`; in particular
it is not `a t ^ n u` with `a ∈ Rˣ` and `u ∈ K_1(R)`. -/
theorem not_exists_eq_single_mul_ofPowerSeries {ε : R} (hε₀ : ε ≠ 0) (hε : IsNilpotent ε)
    {g : WithConv (k[T;T⁻¹] →ₐ[k] LaurentSeries R)}
    (hg : ((pointsMulEquiv g : (LaurentSeries R)ˣ) : LaurentSeries R) = 1 + single (-1) ε) :
    ¬ ∃ (n : ℤ) (u : WithConv (k[T;T⁻¹] →ₐ[k] R⟦X⟧)),
      ((pointsMulEquiv g : (LaurentSeries R)ˣ) : LaurentSeries R) =
        single n 1 * ofPowerSeries ℤ R (pointsMulEquiv u : R⟦X⟧ˣ) := by
  rintro ⟨n, u, h⟩
  rw [hg] at h
  have : Nontrivial R := ⟨⟨ε, 0, hε₀⟩⟩
  set p : R⟦X⟧ := (pointsMulEquiv u).val
  have hcoeff (m : ℤ) : (1 + single (-1) ε : LaurentSeries R).coeff m =
      if m - n < 0 then 0 else PowerSeries.coeff (m - n).natAbs p := by
    rw [h, coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  have hunit : IsUnit (constantCoeff p) := (pointsMulEquiv u).isUnit.map _
  rcases lt_or_ge n 0 with hn | hn
  · -- The coefficient of `t ^ n` is the unit `p(0)`; it is `0` or the nilpotent `ε`.
    have hn' := hcoeff n
    simp only [sub_self, lt_irrefl, ite_false, Int.natAbs_zero, coeff_zero_eq_constantCoeff_apply,
      coeff_add, HahnSeries.coeff_one, hn.ne, zero_add, coeff_single] at hn'
    split_ifs at hn' with h1
    · exact hε.not_isUnit (hn' ▸ hunit)
    · exact not_isUnit_zero (hn' ▸ hunit)
  · -- The coefficient of `t⁻¹` is `ε ≠ 0`, but `t ^ n p` has no pole.
    have h1 := hcoeff (-1)
    have hneg : -1 - n < 0 := by omega
    have hne : (-1 : ℤ) ≠ 0 := by omega
    simp only [hneg, ite_true, coeff_add, HahnSeries.coeff_one, hne, ite_false, zero_add,
      coeff_single_same] at h1
    exact hε₀ h1

/-- Over the dual numbers `ℚ[ε] ⧸ (ε²)`, the hypotheses of
`not_exists_eq_single_mul_ofPowerSeries` hold for `ε`, and the inverse of `1 + ε t⁻¹` is
`1 - ε t⁻¹`. -/
example : (DualNumber.eps : DualNumber ℚ) ≠ 0 ∧ IsNilpotent (DualNumber.eps : DualNumber ℚ) ∧
    (1 + single (-1) DualNumber.eps : LaurentSeries (DualNumber ℚ)) *
      (1 - single (-1) DualNumber.eps) = 1 := by
  refine ⟨fun h ↦ (one_ne_zero : (1 : ℚ) ≠ 0) (by simpa using congrArg TrivSqZeroExt.snd h),
    ⟨2, by rw [sq, DualNumber.eps_mul_eps]⟩, ?_⟩
  -- `(1 + e) * (1 - e) = 1 - e ^ 2`, and `e = ε t⁻¹` squares to `0`.
  have hsq (e : LaurentSeries (DualNumber ℚ)) : (1 + e) * (1 - e) = 1 - e * e := by ring
  rw [hsq, single_mul_single, DualNumber.eps_mul_eps, single_eq_zero, sub_zero]

end MultiplicativeGroup

end TauCeti
