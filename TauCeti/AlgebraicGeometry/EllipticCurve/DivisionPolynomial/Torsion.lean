/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Eval
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul
public import TauCeti.AlgebraicGeometry.EllipticCurve.Integrality

/-!
# Integrality of odd-order and order-four torsion, under a squarefree hypothesis

The Nagell–Lutz statement is that a torsion point of an integral Weierstrass model has integral
coordinates. **This file does not prove that.** It proves the cases a squarefree hypothesis makes
accessible — odd order `n` with `(n : R)` squarefree, and order four with `(2 : R)` squarefree —
over an arbitrary unique factorisation domain `R` with fraction field `K` rather than only over
`ℤ/ℚ`. Order two is genuinely excluded: such a point need not be integral, and what is proved
instead is the denominator bound `den(x) ∣ 4`.

The bridge from the group law to polynomials is `evalEval_ψ_eq_zero_of_zsmul_eq_zero`: if
`n • P = 0` then `ψₙ` vanishes at `P`. That turns a torsion hypothesis into a polynomial root,
and the root feeds `isInteger_x_of_equation_of_is_root_of_squarefree_leadingCoeff` from
`EllipticCurve/Integrality.lean`, whose squarefree-leading-coefficient hypothesis is supplied by
Mathlib's `leadingCoeff_preΨ` (`= n`), `leadingCoeff_preΨ₄` (`= 2`) and `leadingCoeff_Ψ₂Sq`
(`= 4`). The `y`-coordinate then follows from the `x`-coordinate on the curve.

## Main results

* `WeierstrassCurve.evalEval_ψ_eq_zero_of_zsmul_eq_zero`: over a field, `n • P = 0`
  forces `ψₙ(x, y) = 0`. This is the consumer of `zsmul_eq_smulEval` that the whole
  division-polynomial development was built for.
* `WeierstrassCurve.isInteger_of_odd_prime_torsion_of_squarefree`: **the headline.** For
  an odd prime `p` with `(p : R)` squarefree, a `p`-torsion point has both coordinates in `R`.
* `WeierstrassCurve.isInteger_of_order_four_of_squarefree`: the order-four case, with
  `(2 : R)` squarefree.
* `WeierstrassCurve.den_dvd_four_of_order_two`: order two is the genuine exception — the
  coordinates need not be integral, but the denominator of `x` divides `4`.
* `WeierstrassCurve.two_nsmul_eq_zero_of_evalEval_ψ₂_eq_zero`: the converse direction at
  `n = 2`, which is what separates the order-four case from the order-two one.

## Roadmap

New mathematics: `TauCetiRoadmap/EllipticCurves/README.md:821` — "**The torsion subgroup and
Nagell–Lutz**", whose route is stated at `:830`–`:831` as "division polynomials". The roadmap asks
for the theorem over `ℚ` for both integral models; these are the UFD-level statements that
specialise to it.

## Provenance

Ported from J. Xu and D. K. Angdinata's
`projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`):
`evalEval_ψ_eq_zero_of_zsmul_eq_zero` (`:67`), `x_isInteger_of_odd_prime_torsion_squarefree`
(`:118`), `two_nsmul_eq_zero_of_ψ₂_eq_zero` (`:143`), `integrality_of_order_four_squarefree`
(`:156`), `den_dvd_of_order_two` (`:183`) and `prime_order_integrality_squarefree` (`:205`). That
file is byte-identical at `9fec8eba7652`, the revision the roadmap pins, so the citations hold at
either.

Its remaining two declarations are **already in this repository** and are called rather than
restated: `isInteger_of_root_squarefree_leading_coeff` (`:88`) is `Integrality.lean`'s
`isInteger_x_of_equation_of_is_root_of_squarefree_leadingCoeff`, and
`y_isInteger_of_x_isInteger_on_curve` (`:42`) is its `isInteger_y_of_equation_of_isInteger_x`.

Four adaptations. The source's `curveK R K W` (`PIDCurve.lean:32`) is **not ported**: it is a bare
abbreviation for `W.map (algebraMap R K)`, and Mathlib defines `W.baseChange K` to be exactly that
— `rfl`-equal — so this file uses `baseChange`, matching `Integrality.lean` and `Denominator.lean`.
Its companion `curveK_equation_iff` is then just `Affine.equation_iff` and is not needed at all.
The source's `evalEval_ψ_odd` (`EvalBridge.lean:62`) is likewise not ported: it is the one-line
composite `(evalEval_ψ_eq_evalEval_Ψ …).trans (evalEval_Ψ_odd …)`, and this repository carries
both components while declining the wrapper, so the composition is inlined at its one call site.
`evalEval_ψ_eq_zero_of_zsmul_eq_zero` drops the source's `[DecidableEq F]`, which TauCeti's
`zsmul_eq_smulEval` does not require. Finally the names are restated to describe their
conclusions: `x_isInteger_of_odd_prime_torsion_squarefree` →
`isInteger_x_of_odd_prime_torsion_of_squarefree`, `prime_order_integrality_squarefree` →
`isInteger_of_odd_prime_torsion_of_squarefree`, `integrality_of_order_four_squarefree` →
`isInteger_of_order_four_of_squarefree`, `den_dvd_of_order_two` → `den_dvd_four_of_order_two`,
`two_nsmul_eq_zero_of_ψ₂_eq_zero` → `two_nsmul_eq_zero_of_evalEval_ψ₂_eq_zero`.
-/

public section

open Polynomial

namespace WeierstrassCurve

open TauCeti.WeierstrassCurve

variable {F : Type*} [Field F] (E : WeierstrassCurve F)

/-- **A torsion point is a root of its division polynomial.** If `n • P = 0` in the Jacobian
point group, then `ψₙ` vanishes at `P`.

This is where `zsmul_eq_smulEval` is consumed: it identifies `n • P` with the class of
`(φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))`, and a Jacobian class is the point at infinity exactly when its
`Z`-coordinate vanishes. -/
theorem evalEval_ψ_eq_zero_of_zsmul_eq_zero {x y : F}
    (hns : E.toAffine.Nonsingular x y) (n : ℤ)
    (htors : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    (E.ψ n).evalEval x y = 0 := by
  have heval := zsmul_eq_smulEval E hns n
  have hzero := Jacobian.Point.zero_point (W' := E.toJacobian)
  rw [Jacobian.Point.ext_iff] at htors
  rw [heval, hzero] at htors
  exact (Jacobian.Z_eq_zero_of_equiv (Quotient.exact htors)).mpr rfl

/-- If `ψ₂` vanishes at `(x, y)` then `2 • P = 0`: the point equals its own negation, so adding
it to itself lands at infinity. Field-local — no base ring is involved. -/
theorem two_nsmul_eq_zero_of_evalEval_ψ₂_eq_zero [DecidableEq F] {x y : F}
    (hns : E.toAffine.Nonsingular x y) (hψ : E.ψ₂.evalEval x y = 0) :
    (2 : ℕ) • (Affine.Point.some _ _ hns) = 0 := by
  rw [WeierstrassCurve.ψ₂, Affine.evalEval_polynomialY] at hψ
  have hy : y = E.toAffine.negY x y := by simp only [Affine.negY]; linear_combination hψ
  rw [two_nsmul]
  exact Affine.Point.add_self_of_Y_eq hy

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
variable (W : WeierstrassCurve R)

omit [DecidableEq K] in
/-- For an **odd** `n` with `(n : R)` squarefree, an `n`-torsion point has integral
`x`-coordinate.

`ψₙ` vanishes at the point; for odd `n` that value is `preΨₙ` evaluated at `x` alone, whose
leading coefficient is `n` — squarefree by hypothesis, which is what the rational-root argument
in `Integrality.lean` needs.

Oddness is the only arithmetic input: the source states this for an odd prime, but primality is
used there solely to rule out `n = 2`, so odd composite torsion is covered by the same proof. -/
theorem isInteger_x_of_odd_torsion_of_squarefree {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    {n : ℕ} (hodd : ¬Even (n : ℤ))
    (htors : (n : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (hsf : Squarefree (n : R)) : IsLocalization.IsInteger R x := by
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero (W.baseChange K) hns (n : ℤ) htors
  have hodd_int : ¬Even (n : ℤ) := hodd
  -- The source's `evalEval_ψ_odd` is this composition; only its two halves are ported here.
  rw [(evalEval_ψ_eq_evalEval_Ψ (W.baseChange K) hns.left (n : ℤ)).trans
    (evalEval_Ψ_odd (W.baseChange K) (n : ℤ) hodd_int)] at hψ
  have hmap : (W.baseChange K).preΨ (n : ℤ) = (W.preΨ (n : ℤ)).map (algebraMap R K) :=
    WeierstrassCurve.map_preΨ ..
  rw [hmap, eval_map] at hψ
  rw [← aeval_def] at hψ
  have hsf_lc : Squarefree (W.preΨ (n : ℤ)).leadingCoeff := by
    have hn_R_ne : ((n : ℤ) : R) ≠ 0 := by rw [Int.cast_natCast]; exact hsf.ne_zero
    rw [W.leadingCoeff_preΨ hn_R_ne]
    simpa [hodd_int, Int.cast_natCast] using hsf
  exact isInteger_x_of_equation_of_is_root_of_squarefree_leadingCoeff W hns.left hψ hsf_lc

omit [DecidableEq K] in
/-- **Odd torsion is integral.** If `(n : R)` is squarefree and `P` is killed by an odd `n`, both
coordinates of `P` lie in `R`. Specialises to the odd-prime statement the Nagell–Lutz route
quotes, but needs only oddness. -/
theorem isInteger_of_odd_torsion_of_squarefree {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    {n : ℕ} (hodd : ¬Even (n : ℤ))
    (htors : (n : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (hsf : Squarefree (n : R)) :
    IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y :=
  have hx := isInteger_x_of_odd_torsion_of_squarefree W hns hodd htors hsf
  ⟨hx, isInteger_y_of_equation_of_isInteger_x W hns.left hx⟩

omit [DecidableEq K] in
/-- **Order two is the exception, and its denominator divides `4`.** A two-torsion point need not
have integral coordinates; `ψ₂` vanishing forces `Ψ₂Sq` to vanish at `x`, and that polynomial's
leading coefficient is `4`. -/
theorem den_dvd_four_of_order_two (h4_ne : (4 : R) ≠ 0) {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (h2 : (2 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    (IsFractionRing.den R x : R) ∣ (4 : R) := by
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero (W.baseChange K) hns 2 h2
  rw [WeierstrassCurve.ψ_two] at hψ
  have hΨ_zero : (W.baseChange K).Ψ₂Sq.eval x = 0 := by
    have h := evalEval_eq_of_mk_eq (W.baseChange K).toAffine hns.left
      (Affine.CoordinateRing.mk_ψ₂_sq (W := W.baseChange K))
    rw [evalEval_pow, hψ, zero_pow two_ne_zero, evalEval_C] at h
    linear_combination -h
  have hmap : (W.baseChange K).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap R K) :=
    WeierstrassCurve.map_Ψ₂Sq ..
  rw [hmap, eval_map] at hΨ_zero
  rw [← aeval_def] at hΨ_zero
  have hdvd := den_dvd_of_is_root hΨ_zero
  rwa [W.leadingCoeff_Ψ₂Sq h4_ne] at hdvd

/-- **An order-four point is integral when `(2 : R)` is squarefree.** `ψ₄` factors as
`preΨ₄ * ψ₂`; the second factor vanishing would make the point two-torsion, which `h2ne` excludes,
so the first does, and `preΨ₄` has leading coefficient `2`. -/
theorem isInteger_of_order_four_of_squarefree {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (h4 : (4 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (h2ne : (2 : ℕ) • (Affine.Point.some _ _ hns) ≠ 0)
    (hsf : Squarefree (2 : R)) :
    IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y := by
  have hψ₄ := evalEval_ψ_eq_zero_of_zsmul_eq_zero (W.baseChange K) hns 4 h4
  rw [WeierstrassCurve.ψ_four] at hψ₄
  simp only [evalEval_mul, evalEval_C] at hψ₄
  rcases mul_eq_zero.mp hψ₄ with hpreΨ | hψ₂
  · have hmap : (W.baseChange K).preΨ₄ = W.preΨ₄.map (algebraMap R K) :=
      WeierstrassCurve.map_preΨ₄ ..
    rw [hmap, eval_map] at hpreΨ
    rw [← aeval_def] at hpreΨ
    have hsf_lc : Squarefree W.preΨ₄.leadingCoeff := by
      rw [W.leadingCoeff_preΨ₄ hsf.ne_zero]; exact hsf
    have hx := isInteger_x_of_equation_of_is_root_of_squarefree_leadingCoeff W hns.left hpreΨ hsf_lc
    exact ⟨hx, isInteger_y_of_equation_of_isInteger_x W hns.left hx⟩
  · exact absurd (two_nsmul_eq_zero_of_evalEval_ψ₂_eq_zero (W.baseChange K) hns hψ₂) h2ne

end WeierstrassCurve
