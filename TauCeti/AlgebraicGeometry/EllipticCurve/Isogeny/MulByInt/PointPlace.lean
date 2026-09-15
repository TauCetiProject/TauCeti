/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Place
-- Proof-only: membership in the ideal of a point, as a span of two polynomials.
import Mathlib.RingTheory.Polynomial.Ideal
-- Proof-only: the non-vanishing of the division polynomial off the kernel.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality
-- Proof-only: the two coordinate identities relating `P` and `n • P`.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Descent
-- Proof-only: the place of a prime, whose valuation is trivial on the constants.
import TauCeti.FieldTheory.FunctionField.AffineModel.Prime
-- Proof-only: triviality on the base survives restriction.
import TauCeti.RingTheory.Valuation.IsTrivialOn
-- Proof-only: a valuation with no pole at `x` is bounded on the coordinate ring.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.CoordinateRingIntegral
-- Proof-only: the transcendence of the affine coordinate over the base.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
-- Proof-only: normalization, which turns the restricted valuation into a surjective one.
import TauCeti.RingTheory.Valuation.Discrete.Normalize
-- Proof-only: the centre of a bounded valuation on a Dedekind domain.
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

/-!
# The place of a point restricts along `[n]` to the place of its multiple

A point `P` of `W` off the kernel of `[n]` has a place of `F(W)`, and so does `n • P`. Pulling the
first back along the function-field map of `[n]` gives a valuation of `F(W)` again, and this file
shows it is equivalent to the place of `n • P`: the points above a place, for the covering `[n]`,
are the points that `[n]` sends there.

The restricted valuation is not itself normalized, which is why the statement is an equivalence
rather than an equality. Normalizing it and taking its centre on the coordinate ring names a
height one prime, and the two division-polynomial coordinate identities put the ideal of `n • P`
inside that centre; maximality of the point ideal then forces the two to agree.

## Main results

* `TauCeti.Isogeny.isEquiv_comap_pointPlace`: the place of `P` restricted along `[n]` is
  equivalent to the place of `n • P`.
* `TauCeti.Isogeny.isEquiv_comap_pointPlace_iff`: and conversely, a place restricts to the place
  of `T` only if its point is an `[n]`-preimage of `T`, so the fibre over a place is exactly the
  preimage of its point.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], III.1.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain
open scoped Polynomial.Bivariate

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
  [IsDedekindDomain W.toAffine.CoordinateRing]

omit [W.IsElliptic] in
omit [DecidableEq F] in
private theorem mk_mem_pointPlace_iff {x y : F} (h : W.toAffine.Equation x y) (p : F[X][Y]) :
    CoordinateRing.mk W.toAffine p ∈ (CoordinateRing.pointPlace h).asIdeal ↔
      p.evalEval x y = 0 := by
  have hmap : CoordinateRing.XYIdeal W.toAffine x (C y) =
      Ideal.map (CoordinateRing.mk W.toAffine)
        (Ideal.span {C (X - C x), (Y : F[X][Y]) - C (C y)}) := by
    simp only [CoordinateRing.XYIdeal, CoordinateRing.XClass, CoordinateRing.YClass,
      ← Set.image_pair, ← Ideal.map_span]
  have hker : RingHom.ker (CoordinateRing.mk W.toAffine) =
      Ideal.span {W.toAffine.polynomial} := by
    ext q
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    exact AdjoinRoot.mk_eq_zero
  have hpoly : W.toAffine.polynomial ∈
      Ideal.span {C (X - C x), (Y : F[X][Y]) - C (C y)} :=
    mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h
  rw [CoordinateRing.pointPlace_asIdeal, hmap, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective _ AdjoinRoot.mk_surjective,
    ← RingHom.ker_eq_comap_bot, hker,
    sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hpoly),
    mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero]

omit [W.IsElliptic] in
/-- `[n]*y − y'` vanishes at `P` when `n • P = (x', y')`. -/
private theorem valuation_pointPlace_mulByIntY_sub_lt_one {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : psiFunctionField W n ≠ 0) {x' y' : F} (h' : W.toAffine.Nonsingular x' y')
    (hnP : n • Affine.Point.some x y h = Affine.Point.some x' y' h') :
    (CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField
        (mulByIntY W n - algebraMap F W.toAffine.FunctionField y') < 1 := by
  have hP0 : n • Affine.Point.some x y h ≠ 0 := by rw [hnP]; simp
  have hΨ : (W.ΨSq n).eval x ≠ 0 := eval_ΨSq_ne_zero_of_zsmul_ne_zero W h hP0
  have hψ : (W.ψ n).evalEval x y ≠ 0 := by
    intro h0
    refine hΨ ?_
    rw [← evalEval_Ψ_sq_eq_eval_ΨSq W h.left n, ← evalEval_ψ_eq_evalEval_Ψ W h.left n, h0]
    ring
  have hbne : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (CoordinateRing.mk W.toAffine ((W.ψ n) ^ 3)) ≠ 0 := by
    rw [map_pow, map_pow, ← psiFunctionField_def]; exact pow_ne_zero 3 hn
  have hrw : mulByIntY W n - algebraMap F W.toAffine.FunctionField y' =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (CoordinateRing.mk W.toAffine (W.ω n - C (C y') * (W.ψ n) ^ 3)) /
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (CoordinateRing.mk W.toAffine ((W.ψ n) ^ 3)) := by
    have hpsi3 : psiFunctionField W n ^ 3 =
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (CoordinateRing.mk W.toAffine ((W.ψ n) ^ 3)) := by
      rw [map_pow, map_pow, ← psiFunctionField_def]
    rw [mulByIntY_def, omegaFunctionField_def, hpsi3, eq_div_iff hbne, sub_mul,
      div_mul_cancel₀ _ hbne,
      IsScalarTower.algebraMap_apply F W.toAffine.CoordinateRing W.toAffine.FunctionField,
      ← map_mul, ← map_sub]
    congr 1
  have hden : (CoordinateRing.pointPlace h.left).intValuation
      (CoordinateRing.mk W.toAffine ((W.ψ n) ^ 3)) = 1 := by
    rcases eq_or_lt_of_le (HeightOneSpectrum.intValuation_le_one _
      (CoordinateRing.mk W.toAffine ((W.ψ n) ^ 3))) with heq | hlt
    · exact heq
    · exact absurd ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).1 hlt)
        (by rw [mk_mem_pointPlace_iff]; simpa [evalEval] using pow_ne_zero 3 hψ)
  rw [hrw, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap, hden, div_one]
  refine (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 ?_
  rw [mk_mem_pointPlace_iff]
  have hid := W.mul_evalEval_ψ_cube_eq_evalEval_ω_of_zsmul h h' hnP
  simp only [evalEval, eval_C, eval_sub, eval_mul, eval_pow] at hid ⊢
  rw [← hid]; ring


omit [W.IsElliptic] in
/-- `[n]*x` takes the value `x'` at `P` when `n • P = (x', y')`. -/
private theorem valuation_pointPlace_mulByIntX_sub_lt_one {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : psiFunctionField W n ≠ 0) {x' y' : F} (h' : W.toAffine.Nonsingular x' y')
    (hnP : n • Affine.Point.some x y h = Affine.Point.some x' y' h') :
    (CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField
        (mulByIntX W n - algebraMap F W.toAffine.FunctionField x') < 1 := by
  have hP0 : n • Affine.Point.some x y h ≠ 0 := by rw [hnP]; simp
  have hΨ : (W.ΨSq n).eval x ≠ 0 := eval_ΨSq_ne_zero_of_zsmul_ne_zero W h hP0
  have hbne : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (CoordinateRing.mk W.toAffine (C (W.ΨSq n))) ≠ 0 := by
    rw [← psiFunctionField_sq]; exact pow_ne_zero 2 hn
  have hrw : mulByIntX W n - algebraMap F W.toAffine.FunctionField x' =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (CoordinateRing.mk W.toAffine (C (W.Φ n - C x' * W.ΨSq n))) /
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (CoordinateRing.mk W.toAffine (C (W.ΨSq n))) := by
    rw [mulByIntX_def, phiFunctionField_def, CoordinateRing.mk_φ, psiFunctionField_sq,
      eq_div_iff hbne, sub_mul, div_mul_cancel₀ _ hbne,
      IsScalarTower.algebraMap_apply F W.toAffine.CoordinateRing W.toAffine.FunctionField,
      ← map_mul, ← map_sub]
    congr 1
    rw [C_sub, C_mul, map_sub, map_mul]
    congr 2
  have hden : (CoordinateRing.pointPlace h.left).intValuation
      (CoordinateRing.mk W.toAffine (C (W.ΨSq n))) = 1 := by
    rcases eq_or_lt_of_le (HeightOneSpectrum.intValuation_le_one _
      (CoordinateRing.mk W.toAffine (C (W.ΨSq n)))) with heq | hlt
    · exact heq
    · exact absurd ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).1 hlt)
        (by rw [mk_mem_pointPlace_iff]; simpa only [evalEval_C] using hΨ)
  rw [hrw, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap, hden, div_one]
  refine (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 ?_
  rw [mk_mem_pointPlace_iff]
  have hid := mul_eval_ΨSq_eq_eval_Φ_of_zsmul W h h' hnP
  simp only [evalEval, eval_C, eval_sub, eval_mul]
  rw [← hid]; ring



omit [DecidableEq F] [IsDedekindDomain W.toAffine.CoordinateRing] in
private theorem fieldPullback_mulByIntIsogeny_genericX {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).fieldPullback
        (algebraMap F[X] W.toAffine.FunctionField Polynomial.X) = mulByIntX W n := by
  rw [IsScalarTower.algebraMap_apply F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField,
    fieldPullback_algebraMap, mulByIntIsogeny_pullback, AdjoinRoot.algebraMap_eq,
    mulByIntPullback_X]

omit [W.IsElliptic] [DecidableEq F] in
private theorem valuation_pointPlace_mulByIntX_le_one {x y : F}
    (h : W.toAffine.Equation x y) {n : ℤ}
    (hΨ : CoordinateRing.mk W.toAffine (C (W.ΨSq n)) ∉ (CoordinateRing.pointPlace h).asIdeal) :
    (CoordinateRing.pointPlace h).valuation W.toAffine.FunctionField (mulByIntX W n) ≤ 1 := by
  have hone : (CoordinateRing.pointPlace h).intValuation
      (CoordinateRing.mk W.toAffine (C (W.ΨSq n))) = 1 := by
    rcases eq_or_lt_of_le (HeightOneSpectrum.intValuation_le_one _
      (CoordinateRing.mk W.toAffine (C (W.ΨSq n)))) with heq | hlt
    · exact heq
    · exact absurd ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).1 hlt) hΨ
  rw [mulByIntX_def, phiFunctionField_def, psiFunctionField_sq, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  rw [hone, div_one]
  exact HeightOneSpectrum.intValuation_le_one _ _

/-- Step 2: the comap of the place of `P` is at most `1` on the whole coordinate ring. -/
private theorem comap_algebraMap_coordinateRing_le_one {x y : F}
    (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) (hP : n • Affine.Point.some x y h ≠ 0)
    (r : W.toAffine.CoordinateRing) :
    (((CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField).comap
        (mulByIntIsogeny W hn).fieldPullback.toRingHom)
      (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r) ≤ 1 := by
  have : ((CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField).IsTrivialOn F :=
    TauCeti.Place.valuation_ofPrime F W.toAffine.FunctionField (CoordinateRing.pointPlace h.left) ▸
      (TauCeti.Place.ofPrime F W.toAffine.FunctionField
        (CoordinateRing.pointPlace h.left)).isTrivialOn
  refine Valuation.algebraMap_coordinateRing_le_one _ ?_ r
  rw [Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    fieldPullback_mulByIntIsogeny_genericX]
  refine valuation_pointPlace_mulByIntX_le_one W h.left ?_
  rw [mk_mem_pointPlace_iff]
  simpa only [evalEval_C] using eval_ΨSq_ne_zero_of_zsmul_ne_zero W h hP

omit [DecidableEq F] [IsDedekindDomain W.toAffine.CoordinateRing] in
/-- **`[n]*x` is not a constant.** It is the image of the transcendental affine coordinate under
an injective map, so it differs from every element of the base field. -/
private theorem mulByIntX_sub_algebraMap_ne_zero {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (x' : F) : mulByIntX W n - algebraMap F W.toAffine.FunctionField x' ≠ 0 := by
  rw [sub_ne_zero]
  intro heq
  have hinj : Function.Injective (mulByIntIsogeny W hn).fieldPullback :=
    (mulByIntIsogeny W hn).fieldPullback.toRingHom.injective
  have hX : (mulByIntIsogeny W hn).fieldPullback
      (algebraMap F[X] W.toAffine.FunctionField Polynomial.X) =
      (mulByIntIsogeny W hn).fieldPullback (algebraMap F W.toAffine.FunctionField x') := by
    rw [fieldPullback_mulByIntIsogeny_genericX, heq, AlgHom.commutes]
  have hgen := hinj hX
  rw [← WeierstrassCurve.Affine.genericX_eq_algebraMap] at hgen
  exact W.toAffine.transcendental_genericX (hgen ▸ isAlgebraic_algebraMap x')

omit [DecidableEq F] [IsDedekindDomain W.toAffine.CoordinateRing] in
/-- The pullback of `[n]` sends the class of `X - x'` to `[n]*x - x'`. -/
private theorem pullback_mulByIntIsogeny_XClass {n : ℤ} (hn : psiFunctionField W n ≠ 0) (x' : F) :
    (mulByIntIsogeny W hn).fieldPullback (algebraMap W.toAffine.CoordinateRing
        W.toAffine.FunctionField (CoordinateRing.XClass W.toAffine x')) =
      mulByIntX W n - algebraMap F W.toAffine.FunctionField x' := by
  rw [fieldPullback_algebraMap, mulByIntIsogeny_pullback, CoordinateRing.XClass,
    mulByIntPullback_mk]
  simp [evalEval]

omit [DecidableEq F] [IsDedekindDomain W.toAffine.CoordinateRing] in
/-- The pullback of `[n]` sends the class of `Y - y'` to `[n]*y - y'`. -/
private theorem pullback_mulByIntIsogeny_YClass {n : ℤ} (hn : psiFunctionField W n ≠ 0) (y' : F) :
    (mulByIntIsogeny W hn).fieldPullback (algebraMap W.toAffine.CoordinateRing
        W.toAffine.FunctionField (CoordinateRing.YClass W.toAffine (C y'))) =
      mulByIntY W n - algebraMap F W.toAffine.FunctionField y' := by
  rw [fieldPullback_algebraMap, mulByIntIsogeny_pullback, CoordinateRing.YClass,
    mulByIntPullback_mk]
  simp [evalEval]

/-- **The place of `P` restricts along `[n]` to the place of `n • P`.** -/
theorem isEquiv_comap_pointPlace {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) {x' y' : F} (h' : W.toAffine.Nonsingular x' y')
    (hnP : n • Affine.Point.some x y h = Affine.Point.some x' y' h') :
    (((CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField).comap
        (mulByIntIsogeny W hn).fieldPullback.toRingHom).IsEquiv
      ((CoordinateRing.pointPlace h'.left).valuation W.toAffine.FunctionField) := by
  have hP0 : n • Affine.Point.some x y h ≠ 0 := by rw [hnP]; simp
  set v := (CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField with hvdef
  set u := v.comap (mulByIntIsogeny W hn).fieldPullback.toRingHom with hudef
  -- an explicit element of value strictly between `0` and `1`: `[n]*x - x'` vanishes at `P`
  -- (so its value is below `1`) but is not the zero function (so its value is not `0`)
  set z := algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
    (CoordinateRing.XClass W.toAffine x') with hzdef
  have huz : u z = v (mulByIntX W n - algebraMap F W.toAffine.FunctionField x') := by
    rw [hzdef, hudef, Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      pullback_mulByIntIsogeny_XClass]
  have hz1 : u z ≠ 1 := by
    rw [huz]; exact (valuation_pointPlace_mulByIntX_sub_lt_one W h hn h' hnP).ne
  have hz0 : u z ≠ 0 := by
    rw [huz]; exact (Valuation.ne_zero_iff v).mpr (mulByIntX_sub_algebraMap_ne_zero W hn x')
  have : u.IsNontrivial := ⟨z, hz0, hz1⟩
  have hR : ∀ r : W.toAffine.CoordinateRing,
      u (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r) ≤ 1 :=
    comap_algebraMap_coordinateRing_le_one W h hn hP0
  set w := Valuation.normalization u with hwdef
  have hEq : w.IsEquiv u := Valuation.isEquiv_normalization u
  have hord : Valuation.ord u z ≠ 0 := fun h0 ↦ hz1 (by
    have hexp := (Valuation.ord_eq_iff_valuation_eq_exp_neg u ((u.ne_zero_iff).mp hz0)).mp h0
    simpa using hexp)
  have hsurj : Function.Surjective w :=
    Valuation.normalization_surjective u (Valuation.ordIndex_pos u hord).ne'
  have hRw : ∀ r : W.toAffine.CoordinateRing,
      w (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r) ≤ 1 :=
    fun r ↦ hEq.le_one_iff_le_one.mpr (hR r)
  have hlt : ∀ z : W.toAffine.FunctionField, w z < 1 ↔ u z < 1 := fun z ↦ by
    simpa using hEq.lt_iff_lt (x := z) (y := 1)
  have : w.IsNontrivial := Valuation.isNontrivial_of_surjective hsurj
  set Q := Valuation.heightOneSpectrum W.toAffine.CoordinateRing w hRw with hQdef
  have hval : Q.valuation W.toAffine.FunctionField = w :=
    Valuation.valuation_heightOneSpectrum hsurj hRw
  have hle : CoordinateRing.XYIdeal W.toAffine x' (C y') ≤ Q.asIdeal := by
    rw [CoordinateRing.XYIdeal, Ideal.span_le]
    rintro _ (rfl | rfl)
    · change CoordinateRing.XClass W.toAffine x' ∈ Q.asIdeal
      rw [hQdef, Valuation.asIdeal_heightOneSpectrum, Valuation.mem_centerIdeal, hlt, hudef,
        Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        pullback_mulByIntIsogeny_XClass]
      exact valuation_pointPlace_mulByIntX_sub_lt_one W h hn h' hnP
    · change CoordinateRing.YClass W.toAffine (C y') ∈ Q.asIdeal
      rw [hQdef, Valuation.asIdeal_heightOneSpectrum, Valuation.mem_centerIdeal, hlt, hudef,
        Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        pullback_mulByIntIsogeny_YClass]
      exact valuation_pointPlace_mulByIntY_sub_lt_one W h hn h' hnP
  have hideal : CoordinateRing.XYIdeal W.toAffine x' (C y') = Q.asIdeal :=
    (CoordinateRing.XYIdeal_isMaximal_of_equation h'.left).eq_of_le Q.isPrime.ne_top hle
  have hQ : Q = CoordinateRing.pointPlace h'.left :=
    HeightOneSpectrum.ext (by rw [CoordinateRing.pointPlace_asIdeal, ← hideal])
  rw [← hQ, hval]
  exact hEq.symm

/-- **The fibre of `[n]` over a place is exactly the `[n]`-preimage of its point.** For `P` off
the kernel of `[n]`, the place of `P` restricts along `[n]` to the place of `T` precisely when
`n • P = T`. -/
theorem isEquiv_comap_pointPlace_iff {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) {x' y' x'' y'' : F} (h' : W.toAffine.Nonsingular x' y')
    (h'' : W.toAffine.Nonsingular x'' y'')
    (hnP : n • Affine.Point.some x y h = Affine.Point.some x'' y'' h'') :
    (((CoordinateRing.pointPlace h.left).valuation W.toAffine.FunctionField).comap
        (mulByIntIsogeny W hn).fieldPullback.toRingHom).IsEquiv
      ((CoordinateRing.pointPlace h'.left).valuation W.toAffine.FunctionField) ↔
      n • Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  refine ⟨fun hab ↦ ?_, isEquiv_comap_pointPlace W h hn h'⟩
  -- both places restrict to the same one, and a height one prime is determined by its valuation
  have hb := isEquiv_comap_pointPlace W h hn h'' hnP
  have hpq : CoordinateRing.pointPlace h''.left = CoordinateRing.pointPlace h'.left :=
    HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (hb.symm.trans hab)
  obtain ⟨rfl, rfl⟩ := (CoordinateRing.pointPlace_eq_iff h''.left h'.left).mp hpq
  rw [hnP]


end TauCeti.Isogeny
end
