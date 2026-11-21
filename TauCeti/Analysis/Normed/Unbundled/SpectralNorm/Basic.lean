/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.Analysis.Normed.Ring.UnitBall

/-!
# Basic properties of polynomial spectral values and spectral norms

This file collects elementary vanishing, invariance, scaling, and tower-descent lemmas for
`spectralValue` and `spectralNorm` that do not depend on separability, trace, or completeness
assumptions.

In addition, over any complete ultrametric field `K` (including trivially normed fields), the
spectral norm is multiplicative on algebraic elements of any field extension `L`
(`TauCeti.spectralNorm_mul_eq`, extending Mathlib's `spectralAlgNorm_mul`), and on an algebraic
extension `L` it defines an unbundled ultrametric normed `K`-algebra structure
(`TauCeti.spectralNormedField`, adapted from Mathlib's `spectralNorm.normedField`, together with
`TauCeti.isUltrametricDist_spectralNormedField` and `TauCeti.spectralNormedAlgebra`). For any
element `x` algebraic over `K` in any field extension `L`, its spectral norm satisfies
`spectralNorm K L x ^ d = ‖a₀‖` where `d` and `a₀` are the degree and constant coefficient of
`minpoly K x` (`TauCeti.spectralNorm_pow_natDegree_minpoly_eq_norm_coeff_zero`, extending Mathlib's
`spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`). In any normed field extension of `K`, the norm
of an algebraic element coincides with the spectral norm (`TauCeti.norm_eq_spectralNorm`, extending
Mathlib's `NormedAlgebra.norm_eq_spectralNorm`), giving `‖x‖ ^ d = ‖a₀‖`
(`NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero`).

## Main results

* `TauCeti.spectralNorm_eq_zero_of_not_isAlgebraic`: the spectral norm over `K` of an element that
  is transcendental over `K` is zero.
* `RingHom.spectralValue_map_of_norm_eq`: mapping a polynomial along a norm-preserving ring
  homomorphism out of a normed ring preserves `spectralValue`.
* `Polynomial.spectralValue_C` and `Polynomial.spectralValue_one`: constant polynomials over any
  seminormed ring have spectral value `0`.
* `Polynomial.Monic.spectralValue_eq_iSup_roots` and
  `Polynomial.Monic.spectralValue_le_of_forall_aeval_eq_zero`: over an ultrametric normed field, the
  spectral value of a monic polynomial is the supremum of `spectralNorm` over its roots in
  `AlgebraicClosure K`.
* `Polynomial.Monic.spectralValue_mul`, `Polynomial.Monic.spectralValue_le_of_dvd`, and
  `Polynomial.Monic.spectralValue_prod_le`: over an ultrametric normed field, `spectralValue` takes
  products of monic polynomials to maxima, so monic divisors have smaller `spectralValue`.
* `Polynomial.spectralValue_expand`: expanding a polynomial by a positive factor `q` raises its
  `spectralValue` to `1 / q`.
* `Polynomial.spectralValue_map_iterateFrobenius_le`: mapping a polynomial over a reduced
  seminormed commutative ring by `iterateFrobenius R p n` bounds its `spectralValue` by
  `spectralValue P ^ p ^ n`.
* `AlgHom.spectralNorm_map`: `K`-algebra homomorphisms of fields preserve `spectralNorm K`.
* `RingEquiv.spectralNorm_eq_of_norm_eq`: compatible ring isomorphisms whose base map preserves
  norms preserve `spectralNorm`.
* `Module.Dual.exists_bound_spectralNorm_of_tower`: in a field tower `K → L → N`, spectral
  boundedness of every `K`-linear functional descends from `N` to `L`.
* `TauCeti.spectralNorm_pow_eq_norm_of_pow_eq_algebraMap` and
  `TauCeti.spectralNorm_eq_norm_rpow_of_pow_eq_algebraMap`: if a positive power `x ^ n` lies in the
  base field `K`, then `spectralNorm K M x ^ n` equals the base norm of `x ^ n` without requiring
  the ambient field extension `M / K` to be algebraic.
* `TauCeti.spectralNorm_eq_one_of_forall_norm_le_one`: over a trivially normed field, every nonzero
  integral element has spectral norm `1`.
* `TauCeti.spectralNorm_mul_eq`, `TauCeti.spectralNormedField`, `TauCeti.spectralNormedAlgebra`,
  and `TauCeti.norm_eq_spectralNorm`: multiplicativity on algebraic elements, unbundled normed
  field structure on algebraic extensions, and uniqueness of the norm on algebraic elements of
  normed field extensions over any complete ultrametric field.
* `TauCeti.spectralNorm_pow_natDegree_minpoly_eq_norm_coeff_zero` and
  `NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero`: `spectralNorm K L x ^ d = ‖a₀‖`
  and `‖x‖ ^ d = ‖a₀‖` for an algebraic element `x` with minimal polynomial of degree `d` and
  constant coefficient `a₀`.
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

/-- Every constant polynomial over a seminormed ring has spectral value `0`. -/
@[simp]
theorem spectralValue_C {R : Type*} [SeminormedRing R] (r : R) :
    spectralValue (C r) = 0 := by
  have h0 : spectralValueTerms (C r) = fun _ ↦ 0 :=
    _root_.funext fun n ↦ spectralValueTerms_of_natDegree_le (C r) (by simp)
  rw [spectralValue, h0, ciSup_const]

/-- The constant polynomial `1` over any seminormed ring has spectral value `0`. -/
@[simp]
theorem spectralValue_one {R : Type*} [SeminormedRing R] :
    spectralValue (1 : R[X]) = 0 := by
  rw [← map_one C, spectralValue_C]

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

open scoped Classical in
/-- Over an ultrametric normed field, the spectral value of a monic polynomial `p : K[X]` is the
supremum of `spectralNorm K (AlgebraicClosure K)` over the roots of `p` in `AlgebraicClosure K`. -/
theorem Monic.spectralValue_eq_iSup_roots {p : K[X]} (hp : p.Monic) :
    spectralValue p =
      ⨆ x : AlgebraicClosure K,
        if x ∈ (mapAlg K (AlgebraicClosure K) p).roots then
          spectralNorm K (AlgebraicClosure K) x
        else 0 := by
  let L := AlgebraicClosure K
  have hmap : mapAlg K L p = ((mapAlg K L p).roots.map fun a : L ↦ X - C a).prod := by
    have hmon : (mapAlg K L p).Monic := by
      rw [mapAlg_eq_map]
      exact hp.map _
    exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (IsAlgClosed.splits (mapAlg K L p)).natDegree_eq_card_roots.symm).symm
  simpa only [spectralAlgNorm_def] using (max_norm_root_eq_spectralValue spectralAlgNorm_isPowMul
    isNonarchimedean_spectralNorm spectralAlgNorm_one p _ hmap).symm

/-- Over an ultrametric normed field, a nonnegative bound `r` on `spectralNorm` at every root of a
monic polynomial `p : K[X]` in `AlgebraicClosure K` bounds `spectralValue p`. -/
theorem Monic.spectralValue_le_of_forall_aeval_eq_zero {p : K[X]} (hp : p.Monic) {r : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ x : AlgebraicClosure K, aeval x p = 0 → spectralNorm K (AlgebraicClosure K) x ≤ r) :
    spectralValue p ≤ r := by
  classical
  rw [hp.spectralValue_eq_iSup_roots]
  refine ciSup_le fun x ↦ ?_
  split_ifs with hx
  · have hxp : aeval x p = 0 := by
      have h0 := (mem_roots (by rw [mapAlg_eq_map]; exact (hp.map _).ne_zero)).mp hx
      rwa [mapAlg_eq_map, IsRoot.def, eval_map_algebraMap] at h0
    exact h x hxp
  · exact hr

/-- Over an ultrametric normed field, the spectral value of a product of two monic polynomials is
the maximum of their spectral values. -/
theorem Monic.spectralValue_mul {p q : K[X]} (hp : p.Monic) (hq : q.Monic) :
    spectralValue (p * q) = max (spectralValue p) (spectralValue q) := by
  have hroot {r : K[X]} (hr : r.Monic) {x : AlgebraicClosure K} (hx : aeval x r = 0) :
      spectralNorm K (AlgebraicClosure K) x ≤ spectralValue r := by
    rw [← spectralAlgNorm_def]
    exact norm_root_le_spectralValue spectralAlgNorm_isPowMul isNonarchimedean_spectralNorm hr hx
  refine le_antisymm ?_ (max_le ?_ ?_)
  · refine (hp.mul hq).spectralValue_le_of_forall_aeval_eq_zero
      (le_max_of_le_left (spectralValue_nonneg p)) fun x hx ↦ ?_
    rw [map_mul, mul_eq_zero] at hx
    rcases hx with hxp | hxq
    · exact (hroot hp hxp).trans (le_max_left _ _)
    · exact (hroot hq hxq).trans (le_max_right _ _)
  · refine hp.spectralValue_le_of_forall_aeval_eq_zero (spectralValue_nonneg _) fun x hx ↦
      hroot (hp.mul hq) (by rw [map_mul, hx, zero_mul])
  · refine hq.spectralValue_le_of_forall_aeval_eq_zero (spectralValue_nonneg _) fun x hx ↦
      hroot (hp.mul hq) (by rw [map_mul, hx, mul_zero])

/-- Over an ultrametric normed field, if a monic polynomial `p` divides a monic polynomial `q`,
then `spectralValue p ≤ spectralValue q`. -/
theorem Monic.spectralValue_le_of_dvd {p q : K[X]} (hp : p.Monic) (hq : q.Monic) (hdvd : p ∣ q) :
    spectralValue p ≤ spectralValue q := by
  obtain ⟨r, rfl⟩ := hdvd
  have hr : r.Monic := hp.of_mul_monic_left hq
  rw [hp.spectralValue_mul hr]
  exact le_max_left _ _

/-- Over an ultrametric normed field, a uniform upper bound `r ≥ 0` on the spectral values of monic
polynomials bounds the spectral value of their product. -/
theorem Monic.spectralValue_prod_le {ι : Type*} {s : Finset ι} {f : ι → K[X]}
    (hf : ∀ i ∈ s, (f i).Monic) {r : ℝ} (hr : 0 ≤ r)
    (hle : ∀ i ∈ s, spectralValue (f i) ≤ r) :
    spectralValue (∏ i ∈ s, f i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    have hfa : (f a).Monic := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, (f i).Monic := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, hfa.spectralValue_mul (monic_prod_of_monic s f hfs)]
    exact max_le (hle a (Finset.mem_insert_self a s))
      (ih hfs fun i hi ↦ hle i (Finset.mem_insert_of_mem hi))

end NormedField

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

/-- Mapping a polynomial over a reduced seminormed commutative ring by the `n`-fold Frobenius raises
its `spectralValue` to at most the `p ^ n`-th power. Reducedness keeps nilpotent leading
coefficients from lowering `natDegree`. -/
theorem spectralValue_map_iterateFrobenius_le {R : Type*} [SeminormedCommRing R] [IsReduced R]
    (P : R[X]) (p : ℕ) [ExpChar R p] (n : ℕ) :
    spectralValue (P.map (iterateFrobenius R p n)) ≤ spectralValue P ^ p ^ n := by
  set q := p ^ n
  have hq : 0 < q := expChar_pow_pos R p n
  have hdeg : (P.map (iterateFrobenius R p n)).natDegree = P.natDegree := by
    rw [natDegree_map_eq_iff, iterateFrobenius_def]
    refine Classical.or_iff_not_imp_left.mpr fun h0 ↦ ?_
    rw [leadingCoeff_eq_zero.mp (IsReduced.eq_zero _ ⟨q, not_not.mp h0⟩), natDegree_zero]
  refine ciSup_le fun k ↦ ?_
  rw [spectralValueTerms, hdeg]
  split_ifs with hk
  · have hpow : ‖(P.map (iterateFrobenius R p n)).coeff k‖ ≤ ‖P.coeff k‖ ^ q := by
      rw [coeff_map, iterateFrobenius_def]
      exact norm_pow_le' (P.coeff k) hq
    have hexp : 0 ≤ 1 / ((P.natDegree : ℝ) - (k : ℝ)) :=
      one_div_nonneg.mpr (sub_nonneg.mpr (Nat.cast_le.mpr hk.le))
    calc ‖(P.map (iterateFrobenius R p n)).coeff k‖ ^ (1 / ((P.natDegree : ℝ) - (k : ℝ)))
        ≤ (‖P.coeff k‖ ^ q) ^ (1 / ((P.natDegree : ℝ) - (k : ℝ))) :=
          Real.rpow_le_rpow (norm_nonneg _) hpow hexp
      _ = spectralValueTerms P k ^ q := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), mul_comm (q : ℝ),
            Real.rpow_mul (norm_nonneg _), Real.rpow_natCast,
            spectralValueTerms_of_lt_natDegree P hk]
      _ ≤ spectralValue P ^ q :=
          pow_le_pow_left₀ (spectralValueTerms_nonneg P k)
            (le_ciSup (spectralValueTerms_bddAbove P) k) q
  · exact pow_nonneg (spectralValue_nonneg P) q

end Polynomial

namespace AlgHom

/-- The spectral norm over `K` is invariant under `K`-algebra maps of fields. -/
theorem spectralNorm_map {K : Type*} [NormedField K] {E L : Type*} [Field E]
    [Algebra K E] [Field L] [Algebra K L] (ψ : E →ₐ[K] L) (y : E) :
    spectralNorm K L (ψ y) = spectralNorm K E y := by
  -- `spectralNorm K L y` is by definition `spectralValue (minpoly K y)`, and the injective map `ψ`
  -- preserves minimal polynomials.
  rw [spectralNorm, spectralNorm, minpoly.algHom_eq ψ ψ.injective]

end AlgHom

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

namespace Module.Dual

/-- In a tower of fields `K → L → N`, if every `K`-linear functional on `N` is bounded by
`spectralNorm K N`, then every `K`-linear functional on `L` is bounded by `spectralNorm K L`. -/
theorem exists_bound_spectralNorm_of_tower {K L : Type*} (N : Type*)
    [NormedField K] [Field L] [Algebra K L] [Field N] [Algebra K N] [Algebra L N]
    [IsScalarTower K L N]
    (hN : ∀ ψ : Module.Dual K N, ∃ C : ℝ, ∀ z, ‖ψ z‖ ≤ C * spectralNorm K N z)
    (φ : Module.Dual K L) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C * spectralNorm K L y := by
  let ι : L →ₗ[K] N := (IsScalarTower.toAlgHom K L N).toLinearMap
  have hker : LinearMap.ker ι = ⊥ := LinearMap.ker_eq_bot.mpr (algebraMap L N).injective
  obtain ⟨π, hπ⟩ := ι.exists_leftInverse_of_injective hker
  obtain ⟨C, hC⟩ := hN (φ.comp π)
  refine ⟨C, fun y ↦ ?_⟩
  have hy : (φ.comp π) (algebraMap L N y) = φ y :=
    congrArg φ (LinearMap.congr_fun hπ y)
  rw [spectralNorm.eq_of_tower (L := N) y, ← hy]
  exact hC (algebraMap L N y)

end Module.Dual

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

/-- The spectral norm of an element that is transcendental over `K` is zero, since its minimal
polynomial is `0`. -/
theorem spectralNorm_eq_zero_of_not_isAlgebraic {K L : Type*} [NormedField K] [Field L]
    [Algebra K L] {y : L} (hy : ¬ IsAlgebraic K y) : spectralNorm K L y = 0 := by
  have h0 : spectralValueTerms (0 : K[X]) = 0 :=
    funext fun n ↦ spectralValueTerms_of_natDegree_le _ (by simp)
  rw [spectralNorm, minpoly.eq_zero fun h ↦ hy h.isAlgebraic, spectralValue, h0]
  exact ciSup_const

/-- Over a trivially normed field (`∀ c : K, ‖c‖ ≤ 1`), every nonzero element integral over `K`
has spectral norm `1`. -/
theorem spectralNorm_eq_one_of_forall_norm_le_one {K L : Type*} [NormedField K] [Field L]
    [Algebra K L] (hK : ∀ c : K, ‖c‖ ≤ 1) {y : L} (hy : IsIntegral K y) (hy0 : y ≠ 0) :
    spectralNorm K L y = 1 := by
  refine le_antisymm
    ((spectralValue_le_one_iff (minpoly.monic hy)).2 fun n ↦ hK _) ?_
  have hnorm0 : ‖(minpoly K y).coeff 0‖ = 1 := by
    simpa only [RingHom.id_apply] using
      norm_map_eq_one_of_isUnit (φ := RingHom.id K) hK
        (isUnit_iff_ne_zero.2 (minpoly.coeff_zero_ne_zero hy hy0))
  have hterm : spectralValueTerms (minpoly K y) 0 = 1 := by
    rw [spectralValueTerms_of_lt_natDegree _ (minpoly.natDegree_pos hy), hnorm0, Real.one_rpow]
  exact hterm ▸ le_ciSup (spectralValueTerms_bddAbove (minpoly K y)) 0

section CompleteSpace

/-- Over any complete ultrametric field `K`, the spectral norm is multiplicative on algebraic
elements of any field extension `L`. This extends Mathlib's `spectralAlgNorm_mul` to trivially
normed `K` and pointwise algebraic elements. -/
theorem spectralNorm_mul_eq {K L : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Field L] [Algebra K L] {x y : L} (hx : IsAlgebraic K x) (hy : IsAlgebraic K y) :
    spectralNorm K L (x * y) = spectralNorm K L x * spectralNorm K L y := by
  by_cases h : ∃ c : K, 1 < ‖c‖
  · let : NontriviallyNormedField K := { non_trivial := h }
    have : FiniteDimensional K K⟮x, y⟯ :=
      IntermediateField.finiteDimensional_adjoin_pair hx.isIntegral hy.isIntegral
    let x' : K⟮x, y⟯ := ⟨x, IntermediateField.subset_adjoin K {x, y} (by simp)⟩
    let y' : K⟮x, y⟯ := ⟨y, IntermediateField.subset_adjoin K {x, y} (by simp)⟩
    have hmul : spectralNorm K K⟮x, y⟯ (x' * y') =
        spectralNorm K K⟮x, y⟯ x' * spectralNorm K K⟮x, y⟯ y' := by
      simpa only [spectralAlgNorm_def] using spectralAlgNorm_mul (K := K) (L := K⟮x, y⟯) x' y'
    rw [spectralNorm.eq_of_tower (L := L) (x' * y'), spectralNorm.eq_of_tower (L := L) x',
      spectralNorm.eq_of_tower (L := L) y', map_mul,
      IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply] at hmul
    exact hmul
  · push Not at h
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [spectralNorm_zero]
    rcases eq_or_ne y 0 with rfl | hy0
    · simp [spectralNorm_zero]
    rw [spectralNorm_eq_one_of_forall_norm_le_one h (hx.isIntegral.mul hy.isIntegral)
        (mul_ne_zero hx0 hy0),
      spectralNorm_eq_one_of_forall_norm_le_one h hx.isIntegral hx0,
      spectralNorm_eq_one_of_forall_norm_le_one h hy.isIntegral hy0, mul_one]

/-- For any element `x` algebraic over a complete ultrametric field `K` in any field extension `L`,
the spectral norm of `x` raised to the degree of its minimal polynomial equals the norm of the
constant coefficient of that polynomial. This extends Mathlib's
`spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` to trivially normed `K` and pointwise
algebraic elements. -/
theorem spectralNorm_pow_natDegree_minpoly_eq_norm_coeff_zero {K L : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Field L] [Algebra K L] {x : L}
    (hx : IsAlgebraic K x) :
    spectralNorm K L x ^ (minpoly K x).natDegree = ‖(minpoly K x).coeff 0‖ := by
  by_cases h : ∃ c : K, 1 < ‖c‖
  · let : NontriviallyNormedField K := { non_trivial := h }
    have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx.isIntegral
    set g := IntermediateField.AdjoinSimple.gen K x
    have hgen : algebraMap K⟮x⟯ L g = x := IntermediateField.AdjoinSimple.algebraMap_gen K x
    have hmin : minpoly K g = minpoly K x := by
      have := minpoly.algHom_eq (IsScalarTower.toAlgHom K K⟮x⟯ L)
        (IsScalarTower.toAlgHom K K⟮x⟯ L).injective g
      simpa only [IsScalarTower.coe_toAlgHom', hgen] using this.symm
    have hd : ((minpoly K g).natDegree : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral g)).ne'
    have hpow : spectralNorm K K⟮x⟯ g ^ (minpoly K g).natDegree = ‖(minpoly K g).coeff 0‖ := by
      rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K K⟮x⟯ g, ← Real.rpow_natCast,
        ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hd, Real.rpow_one]
    rwa [spectralNorm.eq_of_tower (L := L), hgen, hmin] at hpow
  · push Not at h
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [minpoly.zero, spectralNorm_zero]
    have hnorm0 : ‖(minpoly K x).coeff 0‖ = 1 := by
      simpa only [RingHom.id_apply] using
        norm_map_eq_one_of_isUnit (φ := RingHom.id K) h
          (isUnit_iff_ne_zero.2 (minpoly.coeff_zero_ne_zero hx.isIntegral hx0))
    rw [spectralNorm_eq_one_of_forall_norm_le_one h hx.isIntegral hx0, one_pow, hnorm0]

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

variable (K L) in
/-- An algebraic field extension `L` of any complete ultrametric field `K`, equipped with the
spectral norm as a `NormedField`. Adapted from Mathlib's `spectralNorm.normedField`, without the
`NontriviallyNormedField K` assumption. Not registered as an instance because `L` may carry its own
topology or norm. -/
@[expose, instance_reducible]
noncomputable def spectralNormedField : NormedField L :=
  { (inferInstance : Field L) with
    norm x := spectralNorm K L x
    dist x y := spectralNorm K L (x - y)
    dist_self x := by simp [sub_self, spectralNorm_zero]
    dist_comm x y := by rw [← neg_sub, spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)]
    dist_triangle x y z :=
      sub_add_sub_cancel x y z ▸ isNonarchimedean_spectralNorm.add_le spectralNorm_nonneg
    eq_of_dist_eq_zero hxy :=
      sub_eq_zero.1 (eq_zero_of_map_spectralNorm_eq_zero hxy (Algebra.IsAlgebraic.isAlgebraic _))
    dist_eq x y := by
      rw [← spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic (x - y)),
        sub_eq_add_neg, neg_add, neg_neg]
    norm_mul x y :=
      spectralNorm_mul_eq (Algebra.IsAlgebraic.isAlgebraic x) (Algebra.IsAlgebraic.isAlgebraic y)
    edist_dist x y := by rw [ENNReal.ofReal_eq_coe_nnreal] }

/-- The norm of `TauCeti.spectralNormedField K L` is `spectralNorm K L`. Not `@[simp]`: its
left-hand side also matches norms defined as the spectral norm, such as that of `PadicAlgCl p`,
where it loops with `PadicAlgCl.spectralNorm_eq`. -/
theorem norm_spectralNormedField (x : L) :
    @Norm.norm L (spectralNormedField K L).toNorm x = spectralNorm K L x :=
  (rfl)

/-- The spectral norm on `L` defines an ultrametric distance. -/
theorem isUltrametricDist_spectralNormedField (K L : Type*) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    @IsUltrametricDist L (spectralNormedField K L).toDist :=
  let := spectralNormedField K L
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y ↦ by
    simpa only [norm_spectralNormedField] using isNonarchimedean_spectralNorm x y

/-- `L` equipped with `TauCeti.spectralNormedField K L` is a `NormedAlgebra` over `K`. -/
@[expose, instance_reducible]
noncomputable def spectralNormedAlgebra (K L : Type*) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    @NormedAlgebra K L _ (spectralNormedField K L).toNormedCommRing.toNormedRing.toSeminormedRing :=
  letI := spectralNormedField K L
  { (inferInstance : Algebra K L) with
    norm_smul_le r x := by
      simpa only [norm_spectralNormedField, coe_nnNorm] using
        (spectralNorm_smul r (Algebra.IsAlgebraic.isAlgebraic x)).le }

end CompleteSpace

/-- For any element `x` algebraic over a complete ultrametric field `K` in a normed field extension
`L`, the norm of `x` coincides with `spectralNorm K L x`. This extends Mathlib's
`NormedAlgebra.norm_eq_spectralNorm` to trivially normed `K` and pointwise algebraic elements. -/
theorem norm_eq_spectralNorm (K : Type*) {L : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [NormedField L] [NormedAlgebra K L] {x : L} (hx : IsAlgebraic K x) :
    ‖x‖ = spectralNorm K L x := by
  by_cases h : ∃ c : K, 1 < ‖c‖
  · let : NontriviallyNormedField K := { non_trivial := h }
    have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx.isIntegral
    have hgen := NormedAlgebra.norm_eq_spectralNorm K (IntermediateField.AdjoinSimple.gen K x)
    rwa [AddSubgroupClass.coe_norm, IntermediateField.AdjoinSimple.coe_gen,
      spectralNorm.eq_of_tower (L := L), IntermediateField.AdjoinSimple.algebraMap_gen] at hgen
  · push Not at h
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [spectralNorm_zero]
    have : IsUltrametricDist L := .of_normedAlgebra K
    have hna : IsNonarchimedean (NormedAlgebra.toMulAlgebraNorm K L).toAlgebraNorm :=
      fun a b ↦ by
        simpa only [MulAlgebraNorm.coe_AlgebraNorm, NormedAlgebra.toMulAlgebraNorm_apply] using
          IsUltrametricDist.norm_add_le_max a b
    have hle : ∀ {y : L}, IsAlgebraic K y → ‖y‖ ≤ spectralNorm K L y := fun hy ↦ by
      simpa only [MulAlgebraNorm.coe_AlgebraNorm, NormedAlgebra.toMulAlgebraNorm_apply] using
        norm_le_spectralNorm (f := (NormedAlgebra.toMulAlgebraNorm K L).toAlgebraNorm)
          (MulRingNorm.isPowMul (NormedAlgebra.toMulAlgebraNorm K L).toMulRingNorm) hna hy
    have hxinv : IsAlgebraic K x⁻¹ := hx.inv
    have hspec : spectralNorm K L x = 1 :=
      spectralNorm_eq_one_of_forall_norm_le_one h hx.isIntegral hx0
    have hinv : ‖x⁻¹‖ ≤ 1 := (hle hxinv).trans_eq <|
      spectralNorm_eq_one_of_forall_norm_le_one h hxinv.isIntegral (inv_ne_zero hx0)
    exact (le_antisymm ((hle hx).trans_eq hspec)
      ((inv_le_one₀ (norm_pos_iff.2 hx0)).1 (norm_inv x ▸ hinv))).trans hspec.symm

end TauCeti

/-- For any element `x` algebraic over a complete ultrametric field `K` in a normed field extension
`L`, the norm of `x` raised to the degree of its minimal polynomial equals the norm of the constant
coefficient of that polynomial. -/
theorem NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero (K : Type*) {L : Type*}
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedField L]
    [NormedAlgebra K L] {x : L} (hx : IsAlgebraic K x) :
    ‖x‖ ^ (minpoly K x).natDegree = ‖(minpoly K x).coeff 0‖ := by
  rw [TauCeti.norm_eq_spectralNorm K hx,
    TauCeti.spectralNorm_pow_natDegree_minpoly_eq_norm_coeff_zero hx]
