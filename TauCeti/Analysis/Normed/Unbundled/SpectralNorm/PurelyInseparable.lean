/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.PurelyInseparable.Basic

import Mathlib.Algebra.Polynomial.Expand
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Spectral norms on purely inseparable extensions

Let `K` be an ultrametric normed field, not assumed complete or nontrivially normed, and let
`M / K` be a purely inseparable algebraic extension. Every element `x ∈ M` has a positive
characteristic-power `x ^ p ^ n` in `K`, so power-multiplicativity of `spectralNorm K M` forces
`(spectralNorm K M x) ^ p ^ n = ‖a‖` where `algebraMap K M a = x ^ p ^ n`. Consequently:

* `spectralNorm K M` is multiplicative on `M`, defining a nonarchimedean real absolute value
  `TauCeti.spectralAbsoluteValue K M` and an ultrametric normed-algebra structure on
  `WithAbs (spectralAbsoluteValue K M)`.
* In any algebraic tower `K → M → N` with `M / K` purely inseparable, the spectral norm of `N`
  over `WithAbs (spectralAbsoluteValue K M)` equals its spectral norm over `K`
  (`TauCeti.spectralNorm_withAbs_spectralAbsoluteValue`).

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.2.2 and 3.5.2.
-/

public section

namespace TauCeti

open Polynomial

section NormedField

variable {K M : Type*} [NormedField K] [IsUltrametricDist K] [Field M] [Algebra K M]

/-- If `x ^ n = algebraMap K M a` for `n ≠ 0` in an algebraic extension `M / K`, then
`spectralNorm K M x ^ n = ‖a‖`. -/
theorem spectralNorm_pow_eq_norm_of_pow_eq_algebraMap [Algebra.IsAlgebraic K M] {n : ℕ}
    (hn : n ≠ 0) {x : M} {a : K} (h : x ^ n = algebraMap K M a) :
    spectralNorm K M x ^ n = ‖a‖ := by
  rw [← isPowMul_spectralNorm x (Nat.one_le_iff_ne_zero.mpr hn), h, spectralNorm_extends]

/-- If `x ^ n = algebraMap K M a` for `n ≠ 0` in an algebraic extension `M / K`, then
`spectralNorm K M x = ‖a‖ ^ (1 / n)`. -/
theorem spectralNorm_eq_norm_rpow_of_pow_eq_algebraMap [Algebra.IsAlgebraic K M] {n : ℕ}
    (hn : n ≠ 0) {x : M} {a : K} (h : x ^ n = algebraMap K M a) :
    spectralNorm K M x = ‖a‖ ^ (1 / (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [one_div, Real.eq_rpow_inv (spectralNorm_nonneg x) (norm_nonneg a) hn', Real.rpow_natCast,
    spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hn h]

/-- On a purely inseparable extension of an ultrametric normed field, the spectral norm is
multiplicative, without completeness or nontriviality of the norm on `K`. -/
theorem spectralNorm_mul_of_isPurelyInseparable [IsPurelyInseparable K M] (x y : M) :
    spectralNorm K M (x * y) = spectralNorm K M x * spectralNorm K M y := by
  let p := ringExpChar K
  obtain ⟨m, a, ha⟩ := IsPurelyInseparable.pow_mem K p x
  obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem K p y
  set q := p ^ (m + n)
  have hq : q ≠ 0 := (pow_pos (expChar_pos K p) (m + n)).ne'
  have hxq : x ^ q = algebraMap K M (a ^ p ^ n) := by
    rw [map_pow, ha, ← pow_mul, ← pow_add]
  have hyq : y ^ q = algebraMap K M (b ^ p ^ m) := by
    rw [map_pow, hb, ← pow_mul, ← pow_add, add_comm]
  have hxyq : (x * y) ^ q = algebraMap K M (a ^ p ^ n * b ^ p ^ m) := by
    rw [mul_pow, hxq, hyq, map_mul]
  refine (pow_left_inj₀ (spectralNorm_nonneg _)
    (mul_nonneg (spectralNorm_nonneg _) (spectralNorm_nonneg _)) hq).mp ?_
  rw [mul_pow, spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hq hxyq,
    spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hq hxq,
    spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hq hyq, norm_mul]

/-- The spectral norm on a purely inseparable extension `M / K` as a real absolute value on `M`. -/
noncomputable def spectralAbsoluteValue (K M : Type*) [NormedField K] [IsUltrametricDist K]
    [Field M] [Algebra K M] [IsPurelyInseparable K M] : AbsoluteValue M ℝ where
  toFun := spectralNorm K M
  map_mul' := spectralNorm_mul_of_isPurelyInseparable
  nonneg' := spectralNorm_nonneg
  eq_zero' x := ⟨fun hx ↦ eq_zero_of_map_spectralNorm_eq_zero hx
    (Algebra.IsAlgebraic.isAlgebraic x), fun hx ↦ hx ▸ spectralNorm_zero⟩
  add_le' _ _ := isNonarchimedean_spectralNorm.add_le spectralNorm_nonneg

@[simp]
theorem spectralAbsoluteValue_apply [IsPurelyInseparable K M] (x : M) :
    spectralAbsoluteValue K M x = spectralNorm K M x :=
  (rfl)

theorem isNonarchimedean_spectralAbsoluteValue (K M : Type*) [NormedField K]
    [IsUltrametricDist K] [Field M] [Algebra K M] [IsPurelyInseparable K M] :
    IsNonarchimedean (spectralAbsoluteValue K M) :=
  isNonarchimedean_spectralNorm

instance [IsPurelyInseparable K M] : IsUltrametricDist (WithAbs (spectralAbsoluteValue K M)) :=
  (isNonarchimedean_spectralAbsoluteValue K M).isUltrametricDist_withAbs

private theorem norm_algebraMap_withAbs_spectralAbsoluteValue [IsPurelyInseparable K M] (a : K) :
    ‖algebraMap K (WithAbs (spectralAbsoluteValue K M)) a‖ = ‖a‖ := by
  rw [WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq, spectralAbsoluteValue_apply,
    spectralNorm_extends]

noncomputable instance [IsPurelyInseparable K M] :
    NormedAlgebra K (WithAbs (spectralAbsoluteValue K M)) where
  norm_smul_le a x := by
    rw [Algebra.smul_def, norm_mul, norm_algebraMap_withAbs_spectralAbsoluteValue]

end NormedField

/-- Mapping a polynomial along a norm-preserving ring homomorphism between normed fields preserves
its `spectralValue`. -/
theorem spectralValue_map_of_norm_eq {F E : Type*} [NormedField F] [NormedField E]
    (φ : F →+* E) (hφ : ∀ a, ‖φ a‖ = ‖a‖) (P : F[X]) :
    spectralValue (P.map φ) = spectralValue P := by
  have hdeg : (P.map φ).natDegree = P.natDegree := P.natDegree_map_eq_of_injective φ.injective
  unfold spectralValue
  congr 1 with n
  simp only [spectralValueTerms, hdeg, coeff_map, hφ]

private theorem spectralValue_expand_le {K M' : Type*} [NormedField K] [NormedField M']
    [Algebra K M'] (hiso : ∀ a : K, ‖algebraMap K M' a‖ = ‖a‖) {q : ℕ} (hq : 0 < q)
    {Q₀ : K[X]} {Q : M'[X]} (hdeg : Q₀.natDegree = Q.natDegree)
    (hcoeff : ∀ k, algebraMap K M' (Q₀.coeff k) = Q.coeff k ^ q) :
    spectralValue (Polynomial.expand K q Q₀) ≤ spectralValue Q := by
  refine ciSup_le fun m ↦ ?_
  rw [spectralValueTerms, natDegree_expand, hdeg]
  split_ifs with hm
  · rw [coeff_expand hq]
    split_ifs with hdvd
    · obtain ⟨k, rfl⟩ := hdvd
      have hk : k < Q.natDegree := by
        rw [mul_comm] at hm
        exact Nat.lt_of_mul_lt_mul_right hm
      rw [Nat.mul_div_cancel_left k hq]
      have hnorm : ‖Q₀.coeff k‖ = ‖Q.coeff k‖ ^ q := by
        rw [← hiso (Q₀.coeff k), hcoeff k, norm_pow]
      have hsub : ((Q.natDegree * q : ℕ) : ℝ) - ((q * k : ℕ) : ℝ) =
          (q : ℝ) * ((Q.natDegree : ℝ) - (k : ℝ)) := by
        push_cast
        ring
      have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      have hexp : (‖Q.coeff k‖ ^ q) ^ (1 / ((q : ℝ) * ((Q.natDegree : ℝ) - (k : ℝ)))) =
          ‖Q.coeff k‖ ^ (1 / ((Q.natDegree : ℝ) - (k : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        field_simp [hqR]
      rw [hnorm, hsub, hexp, ← spectralValueTerms_of_lt_natDegree Q hk]
      exact le_ciSup (spectralValueTerms_bddAbove Q) k
    · rw [norm_zero, Real.zero_rpow]
      · exact spectralValue_nonneg Q
      · refine one_div_ne_zero (sub_ne_zero.mpr ?_)
        exact_mod_cast hm.ne'
  · exact spectralValue_nonneg Q

/-- **Tower invariance of the spectral norm across a purely inseparable subextension.**
Let `K → M → N` be a tower of fields with `M / K` purely inseparable and `N / M` algebraic.
Equipping `M` with `spectralAbsoluteValue K M` through `WithAbs`, the spectral norm of `N` over
`M` coincides with its spectral norm over `K`. -/
theorem spectralNorm_withAbs_spectralAbsoluteValue {K M N : Type*} [NormedField K]
    [IsUltrametricDist K] [Field M] [Algebra K M] [IsPurelyInseparable K M]
    [Field N] [Algebra K N] [Algebra M N] [IsScalarTower K M N] [Algebra.IsAlgebraic M N]
    (y : N) :
    spectralNorm (WithAbs (spectralAbsoluteValue K M)) N y = spectralNorm K N y := by
  let M' := WithAbs (spectralAbsoluteValue K M)
  have : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.trans K M N
  have : Algebra.IsAlgebraic M' N :=
    Algebra.IsAlgebraic.ringHom_of_comp_eq (R := M) (A := N)
      (WithAbs.equiv (spectralAbsoluteValue K M)).symm.toRingHom (RingHom.id N)
      (WithAbs.equiv _).symm.injective Function.surjective_id (by ext; rfl)
  refine le_antisymm ?_ ?_
  · -- `minpoly K y`, mapped to `M'[X]`, is monic, annihilates `y`, and keeps its `spectralValue`.
    set P := minpoly K y
    have hP : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
    have hroot : aeval y (P.map (algebraMap K M')) = 0 := by
      rw [aeval_map_algebraMap, minpoly.aeval]
    calc spectralNorm M' N y = spectralAlgNorm M' N y := rfl
      _ ≤ spectralValue (P.map (algebraMap K M')) :=
          norm_root_le_spectralValue spectralAlgNorm_isPowMul isNonarchimedean_spectralNorm
            (hP.map _) hroot
      _ = spectralValue P :=
          spectralValue_map_of_norm_eq (algebraMap K M')
            norm_algebraMap_withAbs_spectralAbsoluteValue P
      _ = spectralNorm K N y := rfl
  · -- Raise `Q = minpoly M' y` to a `p ^ n`-th power whose coefficients descend to `K`.
    classical
    set Q := minpoly M' y
    have hQ : Q.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
    let p := ringExpChar K
    have : ExpChar M' p := expChar_of_injective_algebraMap (algebraMap K M').injective p
    have hex (i : ℕ) : ∃ m : ℕ, (Q.coeff i) ^ p ^ m ∈ (algebraMap K M').range := by
      obtain ⟨m, a, ha⟩ := IsPurelyInseparable.pow_mem K p (Q.coeff i).ofAbs
      refine ⟨m, a, ?_⟩
      apply WithAbs.ofAbs_injective
      rw [WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs, WithAbs.ofAbs_pow]
      exact ha
    let m_fn (i : ℕ) : ℕ := (hex i).choose
    set n : ℕ := Q.support.sup m_fn
    set q : ℕ := p ^ n
    have hq : 0 < q := pow_pos (expChar_pos K p) n
    have hmem (i : ℕ) : Q.coeff i ^ q ∈ (algebraMap K M').range := by
      by_cases hi : i ∈ Q.support
      · obtain ⟨a, ha⟩ := (hex i).choose_spec
        have hle : m_fn i ≤ n := Finset.le_sup hi
        refine ⟨a ^ p ^ (n - m_fn i), ?_⟩
        rw [map_pow, ha, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hle]
      · rw [notMem_support_iff.mp hi, zero_pow hq.ne']
        exact ⟨0, map_zero _⟩
    choose b hb using hmem
    let Q₀ : K[X] := ∑ i ∈ Q.support, monomial i (b i)
    have hQ₀_coeff (k : ℕ) : Q₀.coeff k = b k := by
      rw [finsetSum_coeff]
      simp only [coeff_monomial, Finset.sum_ite_eq']
      split_ifs with hk
      · rfl
      · symm
        apply (algebraMap K M').injective
        rw [map_zero, hb k, notMem_support_iff.mp hk, zero_pow hq.ne']
    have hQ₀_map : Q₀.map (algebraMap K M') = Q.map (iterateFrobenius M' p n) := by
      ext k
      rw [coeff_map, coeff_map, hQ₀_coeff, hb, iterateFrobenius_def]
    set R : K[X] := Polynomial.expand K q Q₀
    have hR_map : R.map (algebraMap K M') = Q ^ q := by
      calc R.map (algebraMap K M')
          = Polynomial.expand M' q (Q₀.map (algebraMap K M')) := map_expand
        _ = Polynomial.expand M' q (Q.map (iterateFrobenius M' p n)) := by rw [hQ₀_map]
        _ = (Polynomial.expand M' q Q).map (iterateFrobenius M' p n) := map_expand.symm
        _ = Q ^ q := map_iterateFrobenius_expand p Q n
    have hR_monic : R.Monic := by
      refine monic_of_injective (algebraMap K M').injective ?_
      rw [hR_map]
      exact hQ.pow q
    have hR_root : aeval y R = 0 := by
      rw [← aeval_map_algebraMap M' y R, hR_map, map_pow, minpoly.aeval, zero_pow hq.ne']
    have hdeg : Q₀.natDegree = Q.natDegree := by
      have h1 : (R.map (algebraMap K M')).natDegree = R.natDegree :=
        R.natDegree_map_eq_of_injective (algebraMap K M').injective
      rw [hR_map, hQ.natDegree_pow, natDegree_expand, mul_comm q] at h1
      exact Nat.eq_of_mul_eq_mul_right hq h1.symm
    calc spectralNorm K N y = spectralAlgNorm K N y := rfl
      _ ≤ spectralValue R :=
          norm_root_le_spectralValue spectralAlgNorm_isPowMul isNonarchimedean_spectralNorm
            hR_monic hR_root
      _ ≤ spectralValue Q :=
          spectralValue_expand_le norm_algebraMap_withAbs_spectralAbsoluteValue hq hdeg
            (fun k ↦ by rw [hQ₀_coeff, hb])
      _ = spectralNorm M' N y := rfl

end TauCeti
