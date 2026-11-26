/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.RingTheory.HahnSeries.Map
public import TauCeti.RingTheory.LaurentSeries.Ramified
import Mathlib.FieldTheory.IsSepClosed
import TauCeti.FieldTheory.IsAlgClosed.FrobeniusFixedPoints
import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Coefficientwise Frobenius on Laurent series

This file defines the arithmetic `p^f`-Frobenius automorphism
`TauCeti.coefficientFrobenius p f k : LaurentSeries k ≃+* LaurentSeries k` acting on coefficients
and fixing the uniformizer `X = HahnSeries.single 1 1`, together with its surjectivity equation
`π^d * σ^N(g) - g = y`.

## Main definitions

* `TauCeti.coefficientFrobenius`: the arithmetic `p^f`-Frobenius on `LaurentSeries k`, fixing `X`.

## Main results

* `TauCeti.coeff_coefficientFrobenius`, `TauCeti.valuation_coefficientFrobenius`: action on
  coefficients and preservation of the `X`-adic valuation.
* `TauCeti.surjective_single_mul_mapRingHom_sub_of_ne_zero`: `g ↦ X^d * τ(g) - g` is surjective
  on `LaurentSeries R` whenever `d ≠ 0`.
* `TauCeti.surjective_iterate_coefficientFrobenius_sub`: `g ↦ X^d * σ^N(g) - g` is surjective on
  `LaurentSeries k` for every `d : ℤ`, `N > 0`, and `f > 0` when `k` is algebraically closed.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), §§4.1–4.5.
-/

public section

open Finset Function
open scoped LaurentSeries

namespace TauCeti

/-! ### Coefficientwise Frobenius on Laurent series -/

section CoefficientFrobenius

/-- Arithmetic `p^f`-Frobenius on coefficients, fixing the Laurent-series uniformizer `X`. -/
noncomputable def coefficientFrobenius (p f : ℕ) [Fact p.Prime] (k : Type*) [CommSemiring k]
    [CharP k p] [PerfectRing k p] : LaurentSeries k ≃+* LaurentSeries k :=
  have : ExpChar k p := expChar_prime k p
  RingEquiv.ofRingHom
    (HahnSeries.mapRingHom (iterateFrobeniusEquiv k p f).toRingHom)
    (HahnSeries.mapRingHom (iterateFrobeniusEquiv k p f).symm.toRingHom)
    (by
      rw [← HahnSeries.mapRingHom_comp]
      ext x n
      simp)
    (by
      rw [← HahnSeries.mapRingHom_comp]
      ext x n
      simp)

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [CommSemiring k] [CharP k p] [PerfectRing k p]

/-- Applying `coefficientFrobenius` coincides with `HahnSeries.mapRingHom` of the `p^f`-Frobenius
automorphism of `k`. -/
theorem coefficientFrobenius_apply (x : LaurentSeries k) :
    coefficientFrobenius p f k x =
      have : ExpChar k p := expChar_prime k p
      HahnSeries.mapRingHom (iterateFrobeniusEquiv k p f).toRingHom x :=
  (rfl)

/-- The underlying `RingHom` of `coefficientFrobenius p f k`. -/
@[simp]
theorem toRingHom_coefficientFrobenius :
    (coefficientFrobenius p f k).toRingHom =
      have : ExpChar k p := expChar_prime k p
      HahnSeries.mapRingHom (iterateFrobeniusEquiv k p f).toRingHom :=
  (rfl)

/-- The underlying `RingHom` of `(coefficientFrobenius p f k).symm`. -/
@[simp]
theorem symm_toRingHom_coefficientFrobenius :
    (coefficientFrobenius p f k).symm.toRingHom =
      have : ExpChar k p := expChar_prime k p
      HahnSeries.mapRingHom (iterateFrobeniusEquiv k p f).symm.toRingHom :=
  (rfl)

/-- `coefficientFrobenius p f k` raises each Laurent series coefficient to the `p^f`-th power. -/
@[simp]
theorem coeff_coefficientFrobenius (x : LaurentSeries k) (n : ℤ) :
    (coefficientFrobenius p f k x).coeff n = x.coeff n ^ p ^ f := by
  have : ExpChar k p := expChar_prime k p
  rw [coefficientFrobenius_apply, HahnSeries.coeff_mapRingHom, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, iterateFrobeniusEquiv_def]

/-- Coefficients of the inverse `coefficientFrobenius` map are transformed by the inverse
`p^f`-Frobenius on `k`. -/
@[simp]
theorem coeff_coefficientFrobenius_symm (x : LaurentSeries k) (n : ℤ) :
    ((coefficientFrobenius p f k).symm x).coeff n =
      have : ExpChar k p := expChar_prime k p
      (iterateFrobeniusEquiv k p f).symm (x.coeff n) := by
  have : ExpChar k p := expChar_prime k p
  exact HahnSeries.coeff_mapRingHom (iterateFrobeniusEquiv k p f).symm.toRingHom x n

/-- Action of `coefficientFrobenius p f k` on a monomial `c * X^n`. -/
@[simp]
theorem coefficientFrobenius_single (n : ℤ) (c : k) :
    coefficientFrobenius p f k (HahnSeries.single n c) = HahnSeries.single n (c ^ p ^ f) := by
  ext m
  by_cases hm : m = n
  · subst hm; simp
  · simp [HahnSeries.coeff_single_of_ne hm, zero_pow (pow_ne_zero f (Fact.out : p.Prime).ne_zero)]

/-- `coefficientFrobenius p f k` fixes `X^n` for every `n : ℤ`. -/
theorem coefficientFrobenius_single_one (n : ℤ) :
    coefficientFrobenius p f k (HahnSeries.single n 1) = HahnSeries.single n 1 := by
  simp

/-- The `n`-th iterate of `coefficientFrobenius p f k` raises coefficients to the `(p^f)^n`-th
power. -/
theorem coeff_iterate_coefficientFrobenius (n : ℕ) (x : LaurentSeries k) (m : ℤ) :
    ((coefficientFrobenius p f k)^[n] x).coeff m = x.coeff m ^ (p ^ f) ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', coeff_coefficientFrobenius, ih, pow_succ, pow_mul]

/-- `LaurentSeries.expand` commutes with `coefficientFrobenius p f k`. -/
@[simp]
theorem expand_coefficientFrobenius (d : ℕ+) (x : LaurentSeries k) :
    _root_.LaurentSeries.expand k d (coefficientFrobenius p f k x) =
      coefficientFrobenius p f k (_root_.LaurentSeries.expand k d x) := by
  have : ExpChar k p := expChar_prime k p
  rw [_root_.LaurentSeries.expand_apply, _root_.LaurentSeries.expand_apply,
    coefficientFrobenius_apply, coefficientFrobenius_apply, HahnSeries.mapRingHom_apply,
    HahnSeries.mapRingHom_apply]
  exact (HahnSeries.map_embDomain (Int.mulOrderEmbedding d) x
    (iterateFrobeniusEquiv k p f).toRingHom).symm

/-- `LaurentSeries.contract` commutes with `coefficientFrobenius p f k`. -/
@[simp]
theorem contract_coefficientFrobenius (d : ℕ+) (x : LaurentSeries k) (r : Fin d) :
    _root_.LaurentSeries.contract d (coefficientFrobenius p f k x) r =
      coefficientFrobenius p f k (_root_.LaurentSeries.contract d x r) := by
  ext m
  simp

/-- `coefficientFrobenius p f k` preserves the `X`-adic valuation on `LaurentSeries k`. -/
@[simp]
theorem valuation_coefficientFrobenius {k : Type*} [Field k] [CharP k p] [PerfectRing k p]
    (x : LaurentSeries k) : Valued.v (coefficientFrobenius p f k x) = Valued.v x := by
  have : ExpChar k p := expChar_prime k p
  rw [coefficientFrobenius_apply, TauCeti.LaurentSeries.valuation_mapRingHom]

end CoefficientFrobenius

/-! ### Solving `X ^ d * σ(g) - g = y` on Laurent series -/

section LaurentEquation

private theorem coeff_iterate_single_mul_mapRingHom {R : Type*} [CommRing R] (τ : R ≃+* R)
    (d : ℤ) (y : LaurentSeries R) (n : ℕ) (m : ℤ) :
    ((fun g ↦ HahnSeries.single d 1 * HahnSeries.mapRingHom τ.toRingHom g)^[n] y).coeff m =
      τ^[n] (y.coeff (m - n * d)) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', HahnSeries.coeff_single_mul, one_mul, HahnSeries.coeff_mapRingHom, ih,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ← iterate_succ_apply' τ]
    congr 2
    push_cast
    ring

private theorem surjective_single_mul_mapRingHom_sub_of_pos {R : Type*} [CommRing R]
    (τ : R ≃+* R) {d : ℤ} (hd : 0 < d) :
    Surjective fun g : LaurentSeries R ↦
      HahnSeries.single d 1 * HahnSeries.mapRingHom τ.toRingHom g - g := by
  let T : LaurentSeries R →+ LaurentSeries R :=
    { toFun g := HahnSeries.single d 1 * HahnSeries.mapRingHom τ.toRingHom g
      map_zero' := by simp
      map_add' x y := by simp [mul_add] }
  have hT (g : LaurentSeries R) :
      T g = HahnSeries.single d 1 * HahnSeries.mapRingHom τ.toRingHom g := rfl
  have hTcoeff (n : ℕ) (y : LaurentSeries R) (m : ℤ) :
      (T^[n] y).coeff m = τ^[n] (y.coeff (m - n * d)) :=
    coeff_iterate_single_mul_mapRingHom τ d y n m
  have hTvanish (y : LaurentSeries R) (m : ℤ) (n : ℕ)
      (hn : Int.toNat (m - y.order) + 1 ≤ n) : (T^[n] y).coeff m = 0 := by
    rw [hTcoeff]
    have hnd : (n : ℤ) ≤ n * d := le_mul_of_one_le_right (Int.natCast_nonneg n) hd
    have hlt : m - n * d < y.order := by omega
    rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, iterate_fixed (map_zero τ) n]
  intro y
  let bound (m : ℤ) : ℕ := Int.toNat (m - y.order) + 1
  let gcoeff (m : ℤ) : R := -∑ n ∈ Finset.range (bound m), (T^[n] y).coeff m
  have hg_bdd : BddBelow gcoeff.support := by
    refine ⟨y.order, fun m hm ↦ ?_⟩
    rw [Function.mem_support] at hm
    by_contra! hlt
    apply hm
    have hb : bound m = 1 := by simp [bound]; omega
    simp [gcoeff, hb, HahnSeries.coeff_eq_zero_of_lt_order hlt]
  let g : LaurentSeries R := HahnSeries.ofSuppBddBelow gcoeff hg_bdd
  refine ⟨g, ?_⟩
  ext m
  set M := max (bound m) (bound (m - d) + 1)
  have hg_eq : g.coeff m = -∑ n ∈ Finset.range M, (T^[n] y).coeff m := by
    rw [HahnSeries.coeff_ofSuppBddBelow]
    simp only [gcoeff, neg_inj]
    exact Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun n _ hnb ↦
      hTvanish y m n (not_lt.1 (Finset.mem_range.not.1 hnb))
  have hg_shift : g.coeff (m - d) = -∑ n ∈ Finset.range M, (T^[n] y).coeff (m - d) := by
    rw [HahnSeries.coeff_ofSuppBddBelow]
    simp only [gcoeff, neg_inj]
    exact Finset.sum_subset (Finset.range_mono (Nat.le_trans (Nat.le_succ _) (le_max_right _ _)))
      fun n _ hnb ↦ hTvanish y (m - d) n (not_lt.1 (Finset.mem_range.not.1 hnb))
  have hTg : (T g).coeff m = -∑ n ∈ Finset.range M, (T^[n + 1] y).coeff m := by
    rw [hT, HahnSeries.coeff_single_mul, one_mul, HahnSeries.coeff_mapRingHom,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hg_shift, map_neg, map_sum, neg_inj]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [iterate_succ_apply', hT, HahnSeries.coeff_single_mul, one_mul, HahnSeries.coeff_mapRingHom,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  dsimp only
  rw [← hT g, HahnSeries.coeff_sub, hTg, hg_eq, neg_sub_neg, ← Finset.sum_sub_distrib,
    Finset.sum_range_sub' (fun n ↦ (T^[n] y).coeff m), iterate_zero, id_eq,
    hTvanish y m M (le_max_left _ _), sub_zero]

/-- For any ring automorphism `τ` of `R` and nonzero integer `d`, the operator
`g ↦ X ^ d * τ(g) - g` is surjective on `LaurentSeries R`. -/
theorem surjective_single_mul_mapRingHom_sub_of_ne_zero {R : Type*} [CommRing R]
    (τ : R ≃+* R) {d : ℤ} (hd : d ≠ 0) :
    Surjective fun g : LaurentSeries R ↦
      HahnSeries.single d 1 * HahnSeries.mapRingHom τ.toRingHom g - g := by
  rcases hd.lt_or_gt with hd_neg | hd_pos
  · intro y
    have hpos : 0 < -d := neg_pos.2 hd_neg
    obtain ⟨h, hh⟩ := surjective_single_mul_mapRingHom_sub_of_pos τ.symm hpos
      (-(HahnSeries.single (-d) 1 * y))
    refine ⟨HahnSeries.mapRingHom τ.symm.toRingHom h, ?_⟩
    have hcomp :
        HahnSeries.mapRingHom τ.toRingHom (HahnSeries.mapRingHom τ.symm.toRingHom h) = h := by
      rw [← RingHom.comp_apply, ← HahnSeries.mapRingHom_comp]
      simp
    have hh' : h - HahnSeries.single (-d) 1 * HahnSeries.mapRingHom τ.symm.toRingHom h =
        HahnSeries.single (-d) 1 * y := by
      linear_combination -hh
    dsimp only
    rw [hcomp]
    calc HahnSeries.single d 1 * h - HahnSeries.mapRingHom τ.symm.toRingHom h
        = HahnSeries.single d 1 * (h - HahnSeries.single (-d) 1 *
            HahnSeries.mapRingHom τ.symm.toRingHom h) := by
          rw [mul_sub, ← mul_assoc, HahnSeries.single_mul_single, add_neg_cancel, mul_one,
            HahnSeries.single_zero_one, one_mul]
      _ = HahnSeries.single d 1 * (HahnSeries.single (-d) 1 * y) := by rw [hh']
      _ = y := by
          rw [← mul_assoc, HahnSeries.single_mul_single, add_neg_cancel, mul_one,
            HahnSeries.single_zero_one, one_mul]
  · exact surjective_single_mul_mapRingHom_sub_of_pos τ hd_pos

/-- Over an algebraically closed field `k` of characteristic `p > 0`, the operator
`g ↦ X ^ d * σ^[N](g) - g` is surjective on `LaurentSeries k` for every `d : ℤ`, `N > 0`, and
`f > 0`. -/
theorem surjective_iterate_coefficientFrobenius_sub {p : ℕ} [Fact p.Prime] {f : ℕ}
    (hf : f ≠ 0) {k : Type*} [Field k] [CharP k p] [IsAlgClosed k] (N : ℕ+) (d : ℤ) :
    Surjective fun g : LaurentSeries k ↦
      HahnSeries.single d 1 * (coefficientFrobenius p f k)^[N] g - g := by
  classical
  have : ExpChar k p := expChar_prime k p
  have hfn : f * (N : ℕ) ≠ 0 := mul_ne_zero hf N.ne_zero
  let τ : k ≃+* k := iterateFrobeniusEquiv k p (f * N)
  have hτ_eq (g : LaurentSeries k) :
      (coefficientFrobenius p f k)^[N] g = HahnSeries.mapRingHom τ.toRingHom g := by
    ext m
    rw [coeff_iterate_coefficientFrobenius, HahnSeries.coeff_mapRingHom,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, iterateFrobeniusEquiv_def, ← pow_mul]
  simp_rw [hτ_eq]
  rcases eq_or_ne d 0 with rfl | hd
  · intro y
    have hq : 1 < p ^ (f * (N : ℕ)) := Nat.one_lt_pow hfn (Fact.out : p.Prime).one_lt
    choose s hs using fun m : ℤ ↦ IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C' p
      (p ^ (f * (N : ℕ))) 1 (-1) (-y.coeff m) (dvd_pow_self p hfn) hq (by simp)
    let gcoeff (m : ℤ) : k := if y.coeff m = 0 then 0 else s m
    have hg_pwo : gcoeff.support.IsPWO := by
      refine y.isPWO_support.mono fun m hm ↦ ?_
      rw [Function.mem_support] at hm
      rw [HahnSeries.mem_support]
      intro hy0
      exact hm (by simp [gcoeff, hy0])
    let g : LaurentSeries k := ⟨gcoeff, hg_pwo⟩
    refine ⟨g, ?_⟩
    ext m
    dsimp only
    rw [HahnSeries.single_zero_one, one_mul, HahnSeries.coeff_sub, HahnSeries.coeff_mapRingHom,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    have hg_coeff : g.coeff m = gcoeff m := rfl
    rw [hg_coeff]
    by_cases hym : y.coeff m = 0
    · simp [gcoeff, hym]
    · simp only [gcoeff, hym, ↓reduceIte, τ, iterateFrobeniusEquiv_def]
      linear_combination hs m
  · exact surjective_single_mul_mapRingHom_sub_of_ne_zero τ hd

end LaurentEquation

end TauCeti
