/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Basic properties of polynomial spectral values and spectral norms

This file collects elementary invariance and scaling lemmas for `spectralValue` and `spectralNorm`
that do not depend on separability or completeness assumptions.

## Main results

* `RingHom.spectralValue_map_of_norm_eq`: mapping a polynomial along a norm-preserving ring
  homomorphism out of a normed ring preserves `spectralValue`.
* `Polynomial.spectralValue_expand`: expanding a polynomial by a positive factor `q` raises its
  `spectralValue` to `1 / q`.
* `RingEquiv.spectralNorm_eq_of_norm_eq`: compatible ring isomorphisms whose base map preserves
  norms preserve `spectralNorm`.
* `TauCeti.spectralNorm_pow_eq_norm_of_pow_eq_algebraMap` and
  `TauCeti.spectralNorm_eq_norm_rpow_of_pow_eq_algebraMap`: if a positive power `x ^ n` lies in the
  base field `K`, then `spectralNorm K M x ^ n` equals the base norm of `x ^ n` without requiring
  the ambient field extension `M / K` to be algebraic.
-/

public section

open Polynomial
open scoped IntermediateField

namespace RingHom

/-- Mapping a polynomial along a norm-preserving ring homomorphism out of a normed ring preserves
its `spectralValue`. -/
theorem spectralValue_map_of_norm_eq {R S : Type*} [NormedRing R] [SeminormedRing S]
    (φ : R →+* S) (hφ : ∀ a, ‖φ a‖ = ‖a‖) (P : R[X]) :
    spectralValue (P.map φ) = spectralValue P := by
  have hinj : Function.Injective φ := fun a b hab ↦ sub_eq_zero.mp <| norm_eq_zero.mp <| by
    rw [← hφ, map_sub, hab, sub_self, norm_zero]
  have hdeg : (P.map φ).natDegree = P.natDegree := P.natDegree_map_eq_of_injective hinj
  unfold spectralValue
  congr 1 with n
  simp only [spectralValueTerms, hdeg, coeff_map, hφ]

end RingHom

namespace Polynomial

/-- Expanding a polynomial by a positive factor `q` replaces its `spectralValue` by its `q`-th
root. -/
theorem spectralValue_expand {R : Type*} [SeminormedCommRing R] (P : R[X]) {q : ℕ} (hq : q ≠ 0) :
    spectralValue (expand R q P) = spectralValue P ^ (1 / (q : ℝ)) := by
  have hq_pos : 0 < q := Nat.pos_of_ne_zero hq
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hterm (k : ℕ) :
      spectralValueTerms (expand R q P) (k * q) = spectralValueTerms P k ^ (1 / (q : ℝ)) := by
    by_cases hk : k < P.natDegree
    · have hkq : k * q < (expand R q P).natDegree := by
        rw [natDegree_expand]
        exact Nat.mul_lt_mul_of_pos_right hk hq_pos
      rw [spectralValueTerms_of_lt_natDegree _ hkq, spectralValueTerms_of_lt_natDegree P hk,
        coeff_expand_mul hq_pos, natDegree_expand, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      have hsub : ((P.natDegree * q : ℕ) : ℝ) - ((k * q : ℕ) : ℝ) =
          ((P.natDegree : ℝ) - (k : ℝ)) * (q : ℝ) := by
        push_cast
        ring
      rw [hsub, one_div_mul_one_div]
    · have hkq : (expand R q P).natDegree ≤ k * q := by
        rw [natDegree_expand]
        exact Nat.mul_le_mul_right q (not_lt.mp hk)
      rw [spectralValueTerms_of_natDegree_le _ hkq,
        spectralValueTerms_of_natDegree_le P (not_lt.mp hk),
        Real.zero_rpow (one_div_ne_zero hqR)]
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun m ↦ ?_
    by_cases hm : m < (expand R q P).natDegree
    · by_cases hdvd : q ∣ m
      · obtain ⟨k, rfl⟩ := hdvd
        rw [mul_comm, hterm]
        exact Real.rpow_le_rpow (spectralValueTerms_nonneg P k)
          (le_ciSup (spectralValueTerms_bddAbove P) k) (by positivity)
      · rw [spectralValueTerms_of_lt_natDegree _ hm, coeff_expand hq_pos, ite_eq_right hdvd,
          norm_zero, Real.zero_rpow]
        · exact Real.rpow_nonneg (spectralValue_nonneg P) _
        · refine one_div_ne_zero (sub_ne_zero.mpr ?_)
          exact_mod_cast hm.ne'
    · rw [spectralValueTerms_of_natDegree_le _ (not_lt.mp hm)]
      exact Real.rpow_nonneg (spectralValue_nonneg P) _
  · refine (pow_le_pow_iff_left₀ (Real.rpow_nonneg (spectralValue_nonneg P) _)
      (spectralValue_nonneg _) hq).mp ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (spectralValue_nonneg P), one_div_mul_cancel hqR,
      Real.rpow_one]
    refine ciSup_le fun k ↦ ?_
    have hk_pow : (spectralValueTerms P k ^ (1 / (q : ℝ))) ^ q = spectralValueTerms P k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (spectralValueTerms_nonneg P k),
        one_div_mul_cancel hqR, Real.rpow_one]
    rw [← hk_pow, ← hterm]
    exact pow_le_pow_left₀ (spectralValueTerms_nonneg _ _)
      (le_ciSup (spectralValueTerms_bddAbove _) (k * q)) q

end Polynomial

namespace RingEquiv

/-- Compatible ring isomorphisms whose base map is norm-preserving preserve `spectralNorm`. -/
theorem spectralNorm_eq_of_norm_eq {K K' L L' : Type*}
    [NormedField K] [NormedField K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (e : K ≃+* K') (he : ∀ a, ‖e a‖ = ‖a‖) (g : L ≃+* L')
    (hcomp : (algebraMap K' L').comp e.toRingHom = g.toRingHom.comp (algebraMap K L)) (x : L) :
    spectralNorm K' L' (g x) = spectralNorm K L x := by
  by_cases hx : IsIntegral K x
  · have hmin : Polynomial.map (e : K →+* K') (minpoly K x) = minpoly K' (g x) :=
      minpoly.eq_of_irreducible_of_monic
        (by rw [← Polynomial.mapEquiv_apply, MulEquiv.irreducible_iff]
            exact minpoly.irreducible hx)
        (by simpa using (Polynomial.map_aeval_eq_aeval_map hcomp (minpoly K x) x).symm)
        ((minpoly.monic hx).map _)
    rw [spectralNorm, ← hmin, (e : K →+* K').spectralValue_map_of_norm_eq he, ← spectralNorm]
  · have hgx : ¬ IsIntegral K' (g x) := by
      rintro ⟨P, hPm, hP0⟩
      refine hx ⟨P.map (e.symm : K' →+* K), hPm.map _, ?_⟩
      have hcomp' : (algebraMap K L).comp e.symm.toRingHom =
          g.symm.toRingHom.comp (algebraMap K' L') := by
        ext b
        apply g.injective
        simpa [RingHom.comp_apply] using (RingHom.congr_fun hcomp (e.symm b)).symm
      rw [← Polynomial.aeval_def] at hP0 ⊢
      simpa [hP0] using (Polynomial.map_aeval_eq_aeval_map hcomp' P (g x)).symm
    rw [spectralNorm, spectralNorm, minpoly.eq_zero hx, minpoly.eq_zero hgx,
      ← Polynomial.map_zero (e : K →+* K'), (e : K →+* K').spectralValue_map_of_norm_eq he]

end RingEquiv

namespace TauCeti

section NormedField

variable {K M : Type*} [NormedField K] [IsUltrametricDist K] [Field M] [Algebra K M]

/-- If `x ^ n = algebraMap K M a` for `n ≠ 0` in a field extension `M / K`, then
`spectralNorm K M x ^ n = ‖a‖`. -/
theorem spectralNorm_pow_eq_norm_of_pow_eq_algebraMap {n : ℕ}
    (hn : n ≠ 0) {x : M} {a : K} (h : x ^ n = algebraMap K M a) :
    spectralNorm K M x ^ n = ‖a‖ := by
  have hx : IsIntegral K x :=
    ⟨X ^ n - C a, monic_X_pow_sub_C a hn, by rw [eval₂_sub, eval₂_X_pow, eval₂_C, h, sub_self]⟩
  have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
  set g := IntermediateField.AdjoinSimple.gen K x
  have hg : g ^ n = algebraMap K K⟮x⟯ a := (algebraMap K⟮x⟯ M).injective <| by
    rw [map_pow, IntermediateField.AdjoinSimple.algebraMap_gen, h,
      IsScalarTower.algebraMap_apply K K⟮x⟯ M]
  rw [← IntermediateField.AdjoinSimple.algebraMap_gen K x, ← spectralNorm.eq_of_tower,
    ← isPowMul_spectralNorm g (Nat.one_le_iff_ne_zero.mpr hn), hg, spectralNorm_extends]

/-- If `x ^ n = algebraMap K M a` for `n ≠ 0` in a field extension `M / K`, then
`spectralNorm K M x = ‖a‖ ^ (1 / n)`. -/
theorem spectralNorm_eq_norm_rpow_of_pow_eq_algebraMap {n : ℕ}
    (hn : n ≠ 0) {x : M} {a : K} (h : x ^ n = algebraMap K M a) :
    spectralNorm K M x = ‖a‖ ^ (1 / (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [one_div, Real.eq_rpow_inv (spectralNorm_nonneg x) (norm_nonneg a) hn', Real.rpow_natCast,
    spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hn h]

end NormedField

end TauCeti
