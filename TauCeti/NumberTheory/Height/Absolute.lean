/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.MahlerMeasure
public import TauCeti.NumberTheory.Height.NumberField
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.FieldTheory.IntermediateField.Adjoin.Inv
import TauCeti.NumberTheory.Height.FiniteOrder
import TauCeti.NumberTheory.NumberField.InfinitePlace.Roots
import TauCeti.RingTheory.Polynomial.GaussNorm

/-!
# The absolute height and the Mahler measure

For an algebraic number `x` of degree `d`, the Mahler measure and the absolute multiplicative Weil
height are related by `M(x) = H(x) ^ d`, equivalently `log M(x) = d · h(x)`. This file proves
this identity for elements of an arbitrary field of characteristic zero; at transcendental
elements both sides are the junk value `1`.

As a consequence, Northcott's theorem for the Mahler measure gives bounded-degree Northcott
finiteness for the absolute height: in any field of characteristic zero there are only finitely
many algebraic elements of bounded degree and bounded absolute height. The field is not required
to be a number field, so this applies in `ℂ` or in an algebraic closure of `ℚ`.

## Main results

* `TauCeti.mahlerMeasure_eq_absMulHeight₁_pow`: `M(x) = H(x) ^ d`.
* `TauCeti.log_mahlerMeasure_eq_mul_absLogHeight₁`: `log M(x) = d · h(x)`.
* `TauCeti.mahlerMeasure_inv`: `M(x⁻¹) = M(x)`.
* `TauCeti.finite_setOf_absMulHeight₁_le`: finiteness of the set of algebraic elements of degree
  at most `d` and absolute height at most `B`.

## Implementation notes

The proof averages the relative height over the conjugates. Let `L` be a number field in which
`minpoly ℚ x` splits, let `D = [L : ℚ]`, and let `a₀` be the leading coefficient of the primitive
minimal polynomial `F_x = a₀ ∏ (X - xᵢ)` over `L`. Every conjugate `xᵢ ∈ L` has relative height
`H_L(xᵢ) = H(x) ^ D`, so the product of these `d` heights is `H(x) ^ (D d)`. Computing the same
product place by place:

* at an infinite place, the conjugates are carried bijectively onto the complex roots of
  `minpoly ℚ x`, so each place contributes `∏ᵢ max(1, |xᵢ|) = M(x) / a₀`, with multiplicity;
* at a finite place `w`, Gauss's lemma for the primitive polynomial `F_x` gives
  `w(a₀) ∏ᵢ max(1, w(xᵢ)) = 1`;
* by the product formula the finite-place values of `a₀` multiply to `a₀ ^ (-D)`.

Together the product is `M(x) ^ D`, and taking `D`-th roots gives the identity. The theorem
uses the splitting field of `minpoly ℚ x` as `L`.

## References

* C. Smyth, *The Mahler measure of algebraic numbers: a survey* (2008), §1.
* X. Wu, *Diophantine geometry, week 08: arithmetic heights* (2023), §3, Lemma 3.1,
  Proposition 3.1 and Theorem 3.4.
-/

public section

open Polynomial NumberField Height Module

namespace TauCeti

variable {F : Type*} [Field F] [CharZero F]

section NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- If `minpoly ℚ x` splits in the number field `L`, then at every finite place `w` of `L` the
value of the leading coefficient `a₀` of `F_x` times the product of `max (w r) 1` over the
conjugates `r` of `x` in `L` is `1`. -/
private lemma mul_prod_aroots_max_finitePlace {x : F} (hx : IsAlgebraic ℚ x)
    (hs : ((minpoly ℚ x).map (algebraMap ℚ L)).Splits) (w : FinitePlace L) :
    w ((primitiveMinpoly x).leadingCoeff : L) *
      (((minpoly ℚ x).aroots L).map fun r ↦ max (w r) 1).prod = 1 := by
  have hmon : ((minpoly ℚ x).map (algebraMap ℚ L)).Monic := (minpoly.monic hx.isIntegral).map _
  have hcomp : Int.castRingHom L = (algebraMap ℚ L).comp (Int.castRingHom ℚ) :=
    RingHom.ext_int _ _
  have h : (primitiveMinpoly x).map (Int.castRingHom L) =
      C ((primitiveMinpoly x).leadingCoeff : L) *
        (((minpoly ℚ x).aroots L).map fun r ↦ X - C r).prod := by
    rw [hcomp, ← Polynomial.map_map, map_primitiveMinpoly hx, Polynomial.map_mul, map_C,
      aroots_def, ← hs.eq_prod_roots_of_monic hmon]
    simp
  simpa [max_comm, FinitePlace.coe_apply] using
    (isPrimitive_primitiveMinpoly x).mul_multiset_prod_max_one_eq_one (v := w.val)
      (fun a b ↦ w.add_le a b) h

/-- If `minpoly ℚ x` splits in the number field `L`, then the product of the relative heights
`H_L(r)` over the conjugates `r` of `x` in `L` is `M(x) ^ [L : ℚ]`. -/
private theorem prod_aroots_mulHeight₁_eq_mahlerMeasure_pow {x : F} (hx : IsAlgebraic ℚ x)
    (hs : ((minpoly ℚ x).map (algebraMap ℚ L)).Splits) :
    (((minpoly ℚ x).aroots L).map mulHeight₁).prod = mahlerMeasure x ^ finrank ℚ L := by
  classical
  set s := (minpoly ℚ x).aroots L
  set a : ℤ := (primitiveMinpoly x).leadingCoeff
  set P := (((minpoly ℚ x).aroots ℂ).map fun z ↦ max 1 ‖z‖).prod
  -- In characteristic zero the conjugates are distinct, so products over `s.toFinset` are
  -- products over the multiset of roots.
  have hnd : s.Nodup := nodup_roots ((minpoly.irreducible hx.isIntegral).separable.map)
  have ht (f : L → ℝ) : ∏ r ∈ s.toFinset, f r = (s.map f).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  have hfin (r : L) : (fun w : FinitePlace L ↦ max (w r) 1).HasFiniteMulSupport := by
    rcases eq_or_ne r 0 with rfl | hr
    · simp [Function.HasFiniteMulSupport]
    · exact (FinitePlace.hasFiniteMulSupport hr).max Function.hasFiniteMulSupport_one
  have ha : (a : L) ≠ 0 := Int.cast_ne_zero.mpr (leadingCoeff_primitiveMinpoly_pos x).ne'
  have hv (v : InfinitePlace L) : v (a : L) = a := by
    rw [← v.norm_embedding_eq, map_intCast, Complex.norm_intCast,
      abs_of_pos (by exact_mod_cast leadingCoeff_primitiveMinpoly_pos x)]
  -- The product formula for `a₀`: its finite-place values multiply to `a₀ ^ (-[L : ℚ])`.
  have hprod : (∏ᶠ w : FinitePlace L, w (a : L))⁻¹ = (a : ℝ) ^ finrank ℚ L := by
    rw [← eq_inv_of_mul_eq_one_left (prod_abs_eq_one ha)]
    simp [hv, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  rw [← ht]
  calc ∏ r ∈ s.toFinset, mulHeight₁ r
      = ∏ r ∈ s.toFinset, ((∏ v : InfinitePlace L, max (v r) 1 ^ v.mult) *
          ∏ᶠ w : FinitePlace L, max (w r) 1) :=
        Finset.prod_congr rfl fun r _ ↦ mulHeight₁_eq r
    _ = (∏ v : InfinitePlace L, (∏ r ∈ s.toFinset, max (v r) 1) ^ v.mult) *
          ∏ᶠ w : FinitePlace L, ∏ r ∈ s.toFinset, max (w r) 1 := by
        rw [Finset.prod_mul_distrib, Finset.prod_comm, prod_finprod_comm _ _ fun r _ ↦ hfin r]
        simp_rw [Finset.prod_pow]
    _ = (∏ v : InfinitePlace L, P ^ v.mult) * ∏ᶠ w : FinitePlace L, (w (a : L))⁻¹ := by
        congr 1
        · exact Finset.prod_congr rfl fun v _ ↦ by rw [ht, v.prod_aroots_max_one_eq hs]
        · exact finprod_congr fun w ↦ by
            rw [ht, eq_inv_of_mul_eq_one_right (mul_prod_aroots_max_finitePlace hx hs w)]
    _ = mahlerMeasure x ^ finrank ℚ L := by
        rw [finprod_inv_distrib, hprod, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq,
          ← mul_pow, mul_comm, mahlerMeasure_eq_leadingCoeff_mul_prod]

/-- If `minpoly ℚ x` splits in the number field `L`, then the product of the relative heights
`H_L(r)` over the conjugates `r` of `x` in `L` is `H(x) ^ ([L : ℚ] d)`, where `d = deg x`. -/
private theorem prod_aroots_mulHeight₁_eq_absMulHeight₁_pow {x : F} (hx : IsAlgebraic ℚ x)
    (hs : ((minpoly ℚ x).map (algebraMap ℚ L)).Splits) :
    (((minpoly ℚ x).aroots L).map mulHeight₁).prod =
      (absMulHeight₁ x ^ (minpoly ℚ x).natDegree) ^ finrank ℚ L := by
  -- Every conjugate `r` has the same absolute height as `x`, and `H_L(r) = H(r) ^ [L : ℚ]`.
  have hr (r : L) (hr : r ∈ (minpoly ℚ x).aroots L) :
      mulHeight₁ r = absMulHeight₁ x ^ finrank ℚ L := by
    have hroot : aeval r (minpoly ℚ x) = 0 := (mem_aroots.mp hr).2
    rw [absMulHeight₁_eq_of_minpoly_eq (minpoly.eq_of_irreducible_of_monic
        (minpoly.irreducible hx.isIntegral) hroot (minpoly.monic hx.isIntegral)),
      absMulHeight₁_eq_rpow, Real.rpow_inv_natCast_pow (mulHeight₁_nonneg r) finrank_pos.ne']
  rw [Multiset.map_congr rfl hr, Multiset.map_const', Multiset.prod_replicate, aroots_def,
    ← hs.natDegree_eq_card_roots, natDegree_map, ← pow_mul, ← pow_mul, mul_comm]

end NumberField

/-- **Mahler measure and absolute height.** For every element `x` of a field of characteristic
zero, `M(x) = H(x) ^ d` with `d = deg x`, the degree of `minpoly ℚ x`. For transcendental `x` this
reads `1 = 1 ^ 0`. -/
theorem mahlerMeasure_eq_absMulHeight₁_pow (x : F) :
    mahlerMeasure x = absMulHeight₁ x ^ (minpoly ℚ x).natDegree := by
  by_cases hx : IsAlgebraic ℚ x
  · let L := (minpoly ℚ x).SplittingField
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    have : NumberField L := {}
    have hs := SplittingField.splits (minpoly ℚ x)
    have h := (prod_aroots_mulHeight₁_eq_mahlerMeasure_pow hx hs).symm.trans
      (prod_aroots_mulHeight₁_eq_absMulHeight₁_pow hx hs)
    exact (pow_left_inj₀ (zero_le_one.trans (one_le_mahlerMeasure x))
      (pow_nonneg (zero_le_one.trans (one_le_absMulHeight₁ x)) _) finrank_pos.ne').mp h
  · rw [mahlerMeasure_of_not_isAlgebraic hx,
      minpoly.eq_zero (isAlgebraic_iff_isIntegral.not.mp hx), natDegree_zero, pow_zero]

/-- The logarithmic form of `mahlerMeasure_eq_absMulHeight₁_pow`: `log M(x) = d · h(x)` with
`d = deg x`. -/
theorem log_mahlerMeasure_eq_mul_absLogHeight₁ (x : F) :
    Real.log (mahlerMeasure x) = (minpoly ℚ x).natDegree * absLogHeight₁ x := by
  rw [mahlerMeasure_eq_absMulHeight₁_pow, Real.log_pow, absLogHeight₁]

/-- **Mahler measure of an inverse.** `M(x⁻¹) = M(x)` for every element `x` of a field of
characteristic zero. For `x = 0` this reads `M(0) = M(0)`, since `0⁻¹ = 0`. -/
@[simp]
theorem mahlerMeasure_inv (x : F) : mahlerMeasure x⁻¹ = mahlerMeasure x := by
  rw [mahlerMeasure_eq_absMulHeight₁_pow, mahlerMeasure_eq_absMulHeight₁_pow, absMulHeight₁_inv,
    TauCeti.minpoly.natDegree_inv]

/-- **Northcott's theorem for the absolute height.** In a field of characteristic zero there are
only finitely many algebraic elements of degree at most `d` and absolute height at most `B`. -/
theorem finite_setOf_absMulHeight₁_le (d : ℕ) (B : ℝ) :
    {x : F | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B}.Finite := by
  refine (finite_setOf_mahlerMeasure_le d (max 1 B ^ d)).subset ?_
  rintro x ⟨hx, hd, hB⟩
  refine ⟨hx, hd, ?_⟩
  rw [mahlerMeasure_eq_absMulHeight₁_pow]
  calc absMulHeight₁ x ^ (minpoly ℚ x).natDegree
      ≤ max 1 B ^ (minpoly ℚ x).natDegree := by
        gcongr
        exacts [zero_le_one.trans (one_le_absMulHeight₁ x), hB.trans (le_max_right _ _)]
    _ ≤ max 1 B ^ d := pow_le_pow_right₀ (le_max_left _ _) hd

end TauCeti
