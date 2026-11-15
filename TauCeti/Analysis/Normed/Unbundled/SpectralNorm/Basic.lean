/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# Basic properties of polynomial spectral values and spectral norms

This file collects elementary vanishing, invariance, scaling, and tower-descent lemmas for
`spectralValue` and `spectralNorm` that do not depend on separability, trace, or completeness
assumptions.

In addition, over any complete ultrametric field `K` (including trivially normed fields), the
spectral norm on an algebraic extension `L` is multiplicative (`TauCeti.spectralNorm_mul_eq`) and
defines an unbundled ultrametric normed `K`-algebra structure (`TauCeti.spectralNormedField`,
`TauCeti.isUltrametricDist_spectralNormedField`, `TauCeti.spectralNormedAlgebra`). In any algebraic
normed field extension of `K` the norm coincides with the spectral norm
(`TauCeti.norm_eq_spectralNorm`), so an element `x` whose minimal polynomial has degree `d` and
constant coefficient `a₀` satisfies `‖x‖ ^ d = ‖a₀‖`.

## Main results

* `TauCeti.spectralNorm_eq_zero_of_not_isAlgebraic`: the spectral norm over `K` of an element that
  is transcendental over `K` is zero.
* `RingHom.spectralValue_map_of_norm_eq`: mapping a polynomial along a norm-preserving ring
  homomorphism out of a normed ring preserves `spectralValue`.
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
* `TauCeti.spectralNorm_eq_one_of_forall_norm_le_one`, `TauCeti.spectralNorm_mul_eq`,
  `TauCeti.spectralNormedField`, `TauCeti.spectralNormedAlgebra`, and
  `TauCeti.norm_eq_spectralNorm`: multiplicativity, unbundled normed field structure, and
  uniqueness of the norm on algebraic extensions of any complete ultrametric field.
* `NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero`: `‖x‖ ^ d = ‖a₀‖` for `x` with
  minimal polynomial of degree `d` and constant coefficient `a₀`.
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
  have hc0 : (minpoly K y).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hy hy0
  have hnorm0 : ‖(minpoly K y).coeff 0‖ = 1 :=
    le_antisymm (hK _)
      ((inv_le_one₀ (norm_pos_iff.2 hc0)).1 (norm_inv ((minpoly K y).coeff 0) ▸ hK _))
  have hterm : spectralValueTerms (minpoly K y) 0 = 1 := by
    rw [spectralValueTerms_of_lt_natDegree _ (minpoly.natDegree_pos hy), hnorm0, Real.one_rpow]
  exact hterm ▸ le_ciSup (spectralValueTerms_bddAbove (minpoly K y)) 0

section CompleteSpace

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Over any complete ultrametric field `K`, the spectral norm on an algebraic extension `L` is
multiplicative, without requiring the norm on `K` to be nontrivial. -/
theorem spectralNorm_mul_eq (x y : L) :
    spectralNorm K L (x * y) = spectralNorm K L x * spectralNorm K L y := by
  by_cases h : ∃ c : K, 1 < ‖c‖
  · let : NontriviallyNormedField K := { non_trivial := h }
    exact spectralAlgNorm_mul x y
  · push Not at h
    rcases eq_or_ne x 0 with rfl | hx
    · simp [spectralNorm_zero]
    rcases eq_or_ne y 0 with rfl | hy
    · simp [spectralNorm_zero]
    rw [spectralNorm_eq_one_of_forall_norm_le_one h (Algebra.IsIntegral.isIntegral (x * y))
        (mul_ne_zero hx hy),
      spectralNorm_eq_one_of_forall_norm_le_one h (Algebra.IsIntegral.isIntegral x) hx,
      spectralNorm_eq_one_of_forall_norm_le_one h (Algebra.IsIntegral.isIntegral y) hy, mul_one]

variable (K L) in
/-- An algebraic field extension `L` of any complete ultrametric field `K`, equipped with the
spectral norm as a `NormedField`. Not registered as an instance because `L` may carry its own
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
    norm_mul := spectralNorm_mul_eq
    edist_dist x y := by rw [ENNReal.ofReal_eq_coe_nnreal] }

/-- The norm of `TauCeti.spectralNormedField K L` is `spectralNorm K L`. -/
@[simp]
theorem norm_spectralNormedField (x : L) :
    @Norm.norm L (spectralNormedField K L).toNorm x = spectralNorm K L x :=
  (rfl)

/-- The spectral norm on `L` defines an ultrametric distance. -/
theorem isUltrametricDist_spectralNormedField (K L : Type*) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    @IsUltrametricDist L (spectralNormedField K L).toDist :=
  let := spectralNormedField K L
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm

/-- `L` equipped with `TauCeti.spectralNormedField K L` is a `NormedAlgebra` over `K`. -/
@[expose, instance_reducible]
noncomputable def spectralNormedAlgebra (K L : Type*) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    @NormedAlgebra K L _ (spectralNormedField K L).toNormedCommRing.toNormedRing.toSeminormedRing :=
  letI := spectralNormedField K L
  { (inferInstance : Algebra K L) with
    norm_smul_le r x := (spectralNorm_smul r (Algebra.IsAlgebraic.isAlgebraic x)).le }

end CompleteSpace

/-- In an algebraic normed field extension `L` of any complete ultrametric field `K`, the norm on
`L` coincides with `spectralNorm K L`. -/
theorem norm_eq_spectralNorm (K : Type*) {L : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L] (x : L) :
    ‖x‖ = spectralNorm K L x := by
  by_cases h : ∃ c : K, 1 < ‖c‖
  · let : NontriviallyNormedField K := { non_trivial := h }
    exact NormedAlgebra.norm_eq_spectralNorm K x
  · push Not at h
    rcases eq_or_ne x 0 with rfl | hx
    · simp [spectralNorm_zero]
    have : IsUltrametricDist L := .of_normedAlgebra K
    have hle : ∀ y : L, ‖y‖ ≤ spectralNorm K L y := fun y ↦
      norm_le_spectralNorm (f := (NormedAlgebra.toMulAlgebraNorm K L).toAlgebraNorm)
        (MulRingNorm.isPowMul (NormedAlgebra.toMulAlgebraNorm K L).toMulRingNorm)
        IsUltrametricDist.norm_add_le_max (Algebra.IsAlgebraic.isAlgebraic y)
    have hspec : spectralNorm K L x = 1 :=
      spectralNorm_eq_one_of_forall_norm_le_one h (Algebra.IsIntegral.isIntegral x) hx
    have hinv : ‖x⁻¹‖ ≤ 1 := (hle x⁻¹).trans_eq <|
      spectralNorm_eq_one_of_forall_norm_le_one h (Algebra.IsIntegral.isIntegral x⁻¹)
        (inv_ne_zero hx)
    exact (le_antisymm ((hle x).trans_eq hspec)
      ((inv_le_one₀ (norm_pos_iff.2 hx)).1 (norm_inv x ▸ hinv))).trans hspec.symm

end TauCeti

/-- In an algebraic normed field extension `L` of a complete ultrametric field `K`, the norm of an
element `x` raised to the degree of its minimal polynomial is the norm of the constant coefficient
of that polynomial. -/
theorem NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero (K : Type*) {L : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedField L]
    [NormedAlgebra K L] [Algebra.IsAlgebraic K L] (x : L) :
    ‖x‖ ^ (minpoly K x).natDegree = ‖(minpoly K x).coeff 0‖ := by
  have hd : ((minpoly K x).natDegree : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne'
  rw [NormedAlgebra.norm_eq_spectralNorm K, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hd, Real.rpow_one]
