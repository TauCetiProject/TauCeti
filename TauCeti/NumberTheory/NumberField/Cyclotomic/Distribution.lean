/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import TauCeti.FieldTheory.Minpoly
import TauCeti.RingTheory.Norm.PowerBasis

/-!
# Norm distribution for cyclotomic numbers

For compatible primitive roots at conductors `m` and `m * p`, the norm of `1 - ζ` from
conductor `m * p` to conductor `m` has two forms, according as `p` divides `m` or not.
In the coprime case the omitted conjugate is the inverse arithmetic Frobenius of the lower
root. This is the distribution relation used in cyclotomic Euler systems.

## References

* K. Rubin, *Euler systems*, Chapter III, §2.1, equation (2), in the `1 - ζ` convention.
-/

public section

open Polynomial
open scoped IntermediateField

namespace IsCyclotomicExtension.Rat

/-- The degree between two rational cyclotomic fields is the ratio of their totients. -/
theorem finrank_eq_totient_div {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
    [Algebra K L] {m n : ℕ} [NeZero m] [NeZero n]
    [IsCyclotomicExtension {m} ℚ K] [IsCyclotomicExtension {n} ℚ L] :
    Module.finrank K L = n.totient / m.totient := by
  have hm := IsCyclotomicExtension.Rat.finrank m K
  have hn := IsCyclotomicExtension.Rat.finrank n L
  have hm0 : Module.finrank ℚ K ≠ 0 := hm ▸ (Nat.totient_pos.mpr (NeZero.pos m)).ne'
  rw [← hm, ← hn]
  exact (Module.finrank_div_finrank_cancel_left ℚ K L hm0).symm

end IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

section Relative

variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
  [Algebra K L] {m p : ℕ}
  [IsCyclotomicExtension {m} ℚ K] [IsCyclotomicExtension {m * p} ℚ L]
  {ζ : L} {η : K}

omit [IsCyclotomicExtension {m} ℚ K] in
private theorem rat_cyclotomic_step_adjoin_eq_top [NeZero m] [NeZero p]
    (hζ : IsPrimitiveRoot ζ (m * p)) : K⟮ζ⟯ = ⊤ := by
  apply IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral (NeZero.pos (m * p))).tower_top
  apply IntermediateField.toSubalgebra_injective
  rw [IntermediateField.top_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
  exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ

private theorem natDegree_minpoly_rat_cyclotomic_step [NeZero m] [NeZero p]
    (hζ : IsPrimitiveRoot ζ (m * p)) :
    (minpoly K ζ).natDegree = (m * p).totient / m.totient := by
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos (m * p))).tower_top
  rw [← IntermediateField.adjoin.finrank hint, hζ.rat_cyclotomic_step_adjoin_eq_top,
    IntermediateField.finrank_top',
    IsCyclotomicExtension.Rat.finrank_eq_totient_div (m := m) (n := m * p)]

/-- If `p ∣ m`, a primitive `(m * p)`-th root with `p`-th power `η` has relative minimal polynomial
`X ^ p - C η` over the `m`-th rational cyclotomic field. The multiplying factor `p` need not be
prime in this case. -/
theorem minpoly_eq_X_pow_sub_C_of_dvd [NeZero m]
    (hζ : IsPrimitiveRoot ζ (m * p)) (hp : p ∣ m) (hpow : ζ ^ p = algebraMap K L η) :
    minpoly K ζ = X ^ p - C η := by
  have := NeZero.mk (ne_zero_of_dvd_ne_zero (NeZero.ne m) hp)
  apply TauCeti.Algebra.minpoly_eq_X_pow_sub_C_of_pow_eq_of_natDegree_eq (NeZero.ne p) hpow
  rw [hζ.natDegree_minpoly_rat_cyclotomic_step, Nat.mul_comm m p, Nat.totient_mul_of_dvd hp,
    Nat.mul_div_cancel _ (Nat.totient_pos.mpr (NeZero.pos m))]

/-- For a prime `p ∤ m` and an inverse exponent `a` with `p * a ≡ 1 [MOD m]`, the relative minimal
polynomial at the step from `m` to `m * p` is `X ^ p - C η` with the factor `X - C (η ^ a)` removed.
Here `η` is the `p`-th power of the upper primitive root. -/
theorem minpoly_mul_X_sub_C_eq_X_pow_sub_C_of_mul_modEq_one
    (hζ : IsPrimitiveRoot ζ (m * p)) (hp : p.Prime)
    (hpow : ζ ^ p = algebraMap K L η) {a : ℕ} (ha : p * a ≡ 1 [MOD m]) :
    minpoly K ζ * (X - C (η ^ a)) = X ^ p - C η := by
  have hnd : ¬p ∣ m := fun h ↦ hp.not_dvd_one <|
    Nat.modEq_zero_iff_dvd.mp ((ha.of_dvd h).symm.trans (dvd_mul_right p a).modEq_zero_nat)
  have hm : m ≠ 0 := fun h ↦ hnd (h ▸ dvd_zero p)
  have := NeZero.mk hm
  have := NeZero.mk hp.ne_zero
  have hη : η ^ m = 1 := (algebraMap K L).injective <| by
    rw [map_pow, ← hpow, ← pow_mul, mul_comm p m, hζ.pow_eq_one, map_one]
  have hroot : (η ^ a) ^ p = η := by
    rw [← pow_mul, mul_comm a p, pow_eq_pow_of_modEq ha hη, pow_one]
  have hne : ζ ≠ algebraMap K L (η ^ a) := by
    intro he
    have hd : m * p ∣ m := (hζ.pow_eq_one_iff_dvd m).mp <| by
      rw [he, ← map_pow, pow_right_comm, hη, one_pow, map_one]
    exact (not_le_of_gt (lt_mul_of_one_lt_right (NeZero.pos m) hp.one_lt))
      (Nat.le_of_dvd (NeZero.pos m) hd)
  -- Remove the lower-field root before comparing the degree of the quotient with `minpoly`.
  obtain ⟨g, hg⟩ : X - C (η ^ a) ∣ X ^ p - C η :=
    (dvd_iff_isRoot).2 (by simp [IsRoot, hroot])
  have hmonic := monic_X_pow_sub_C η hp.ne_zero
  have hgmonic : g.Monic := (monic_X_sub_C _).of_mul_monic_left (hg ▸ hmonic)
  have hdeg : g.natDegree = p - 1 := by
    have h := congrArg natDegree hg
    rw [natDegree_X_pow_sub_C, (monic_X_sub_C _).natDegree_mul hgmonic, natDegree_X_sub_C] at h
    omega
  have hz : aeval ζ g = 0 := by
    have h := congrArg (aeval ζ) hg
    simp only [map_mul, map_sub, map_pow, aeval_X, aeval_C, hpow, sub_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr (by simpa using hne))
  have hint : IsIntegral K ζ := (hζ.isIntegral (Nat.mul_pos (NeZero.pos m) hp.pos)).tower_top
  have hmin : minpoly K ζ = g := by
    symm
    refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hgmonic (minpoly.dvd K ζ hz) ?_
    rw [hdeg, hζ.natDegree_minpoly_rat_cyclotomic_step, Nat.mul_comm m p,
      Nat.totient_mul_of_prime_of_not_dvd hp hnd, Nat.mul_div_cancel _
        (Nat.totient_pos.mpr (NeZero.pos m))]
  rw [hmin, mul_comm, ← hg]

omit [IsCyclotomicExtension {m} ℚ K] in
private theorem norm_one_sub_eq_eval_minpoly_rat_cyclotomic_step [NeZero m] [NeZero p]
    (hζ : IsPrimitiveRoot ζ (m * p)) :
    Algebra.norm K (1 - ζ) = (minpoly K ζ).eval 1 := by
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos (m * p))).tower_top
  simpa only [map_one, PowerBasis.ofAdjoinSimpleEqTop_gen] using
    PowerBasis.norm_algebraMap_sub_gen
      (PowerBasis.ofAdjoinSimpleEqTop hint hζ.rat_cyclotomic_step_adjoin_eq_top) 1

/-- Repeated-conductor distribution: if `p ∣ m`, the norm of `1 - ζ` is `1 - η`,
where `ζ` has order `m * p` and its `p`-th power is `η` in the field of conductor `m`. -/
theorem norm_one_sub_eq_of_dvd [NeZero m]
    (hζ : IsPrimitiveRoot ζ (m * p)) (hp : p ∣ m) (hpow : ζ ^ p = algebraMap K L η) :
    Algebra.norm K (1 - ζ) = 1 - η := by
  have := NeZero.mk (ne_zero_of_dvd_ne_zero (NeZero.ne m) hp)
  rw [hζ.norm_one_sub_eq_eval_minpoly_rat_cyclotomic_step, hζ.minpoly_eq_X_pow_sub_C_of_dvd hp hpow]
  simp

/-- Coprime-conductor distribution in product form, so it also holds at conductor one.
The factor `1 - η ^ a` corresponds to the omitted root of `X ^ p - C η`. -/
theorem norm_one_sub_mul_one_sub_pow_eq_of_mul_modEq_one
    (hζ : IsPrimitiveRoot ζ (m * p)) (hp : p.Prime)
    (hpow : ζ ^ p = algebraMap K L η) {a : ℕ} (ha : p * a ≡ 1 [MOD m]) :
    Algebra.norm K (1 - ζ) * (1 - η ^ a) = 1 - η := by
  have : NeZero m := ⟨by rintro rfl; simp [hp.ne_one] at ha⟩
  have := NeZero.mk hp.ne_zero
  rw [hζ.norm_one_sub_eq_eval_minpoly_rat_cyclotomic_step]
  simpa only [eval_mul, eval_sub, eval_X, eval_C, eval_pow, one_pow] using
    congrArg (eval 1) (hζ.minpoly_mul_X_sub_C_eq_X_pow_sub_C_of_mul_modEq_one hp hpow ha)

/-- At a new prime `p`, the extra factor in the norm product is the image of `1 - η` under
inverse arithmetic Frobenius, i.e., the automorphism corresponding to `p⁻¹ mod m`. -/
theorem norm_one_sub_mul_autEquivPow_symm_inv_eq [NeZero m]
    (hζ : IsPrimitiveRoot ζ (m * p)) (hp : p.Prime) (hc : p.Coprime m)
    (hpow : ζ ^ p = algebraMap K L η) :
    Algebra.norm K (1 - ζ) *
        (IsCyclotomicExtension.autEquivPow K (cyclotomic.irreducible_rat (NeZero.pos m))).symm
          (ZMod.unitOfCoprime p hc)⁻¹ (1 - η) =
      1 - η := by
  let u := ZMod.unitOfCoprime p hc
  have hη : η ^ m = 1 := (algebraMap K L).injective <| by
    rw [map_pow, ← hpow, ← pow_mul, mul_comm p m, hζ.pow_eq_one, map_one]
  have ha : p * (u⁻¹ : (ZMod m)ˣ).val.val ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val,
      ← ZMod.coe_unitOfCoprime p hc, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let e := IsCyclotomicExtension.autEquivPow K (cyclotomic.irreducible_rat (NeZero.pos m))
  have he : e.symm u⁻¹ η = η ^ (u⁻¹ : (ZMod m)ˣ).val.val := calc
    e.symm u⁻¹ η = η ^ (e (e.symm u⁻¹)).val.val :=
      IsCyclotomicExtension.autEquivPow_apply_of_pow_eq_one K _ (e.symm u⁻¹) hη
    _ = _ := by rw [MulEquiv.apply_symm_apply]
  calc
    Algebra.norm K (1 - ζ) * e.symm u⁻¹ (1 - η) =
        Algebra.norm K (1 - ζ) * (1 - η ^ (u⁻¹ : (ZMod m)ˣ).val.val) := by
      rw [map_sub (e.symm u⁻¹), map_one, he]
    _ = 1 - η := hζ.norm_one_sub_mul_one_sub_pow_eq_of_mul_modEq_one hp hpow ha

/-- Away from conductor one, the coprime-conductor norm is the quotient of `1 - η` by its
inverse arithmetic Frobenius conjugate. -/
theorem norm_one_sub_eq_div_of_coprime [NeZero m]
    (hζ : IsPrimitiveRoot ζ (m * p)) (hm : m ≠ 1) (hp : p.Prime) (hc : p.Coprime m)
    (hpow : ζ ^ p = algebraMap K L η) :
    Algebra.norm K (1 - ζ) = (1 - η) /
      (IsCyclotomicExtension.autEquivPow K (cyclotomic.irreducible_rat (NeZero.pos m))).symm
        (ZMod.unitOfCoprime p hc)⁻¹ (1 - η) := by
  have hη : IsPrimitiveRoot η m := by
    apply IsPrimitiveRoot.of_map_of_injective (f := algebraMap K L) _ (algebraMap K L).injective
    rw [← hpow]
    exact hζ.pow (Nat.mul_pos (NeZero.pos m) hp.pos) (Nat.mul_comm m p)
  have hη1 : 1 - η ≠ 0 := sub_ne_zero.mpr (hη.ne_one (lt_of_le_of_ne (NeZero.pos m) hm.symm)).symm
  exact (eq_div_iff ((map_ne_zero_iff _ (AlgEquiv.injective _)).2 hη1)).2
    (hζ.norm_one_sub_mul_autEquivPow_symm_inv_eq hp hc hpow)

end Relative

/-- The norm of `1 - ζ` in a cyclotomic extension, when the cyclotomic polynomial is irreducible.
The formula includes conductors one and two. -/
theorem norm_one_sub_eq_eval_cyclotomic {F E : Type*} [Field F] [CommRing E] [IsDomain E]
    [Algebra F E] {n : ℕ} [IsCyclotomicExtension {n} F E] {ζ : E}
    (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (cyclotomic n F)) :
    Algebra.norm F (1 - ζ) = (cyclotomic n F).eval 1 := by
  have : NeZero n := ⟨fun hn ↦ by simp [hn] at hirr⟩
  have := IsCyclotomicExtension.neZero' n F E
  simpa only [map_one, powerBasis_gen, hζ.minpoly_eq_cyclotomic_of_irreducible hirr] using
    (hζ.powerBasis F).norm_algebraMap_sub_gen 1

/-- The norm to `ℚ` of `1 - ζ` for a prime conductor is that prime, including at `2`.
This is the conductor-one distribution value. -/
theorem norm_one_sub_eq_natCast_of_prime {E : Type*} [Field E] [CharZero E]
    {p : ℕ} [IsCyclotomicExtension {p} ℚ E] {ζ : E} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) :
    Algebra.norm ℚ (1 - ζ) = (p : ℚ) := by
  have := Fact.mk hp
  rw [hζ.norm_one_sub_eq_eval_cyclotomic (cyclotomic.irreducible_rat hp.pos),
    eval_one_cyclotomic_prime]

end IsPrimitiveRoot
