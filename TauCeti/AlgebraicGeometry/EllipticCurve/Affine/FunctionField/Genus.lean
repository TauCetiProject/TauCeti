/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.FieldTheory.FunctionField.Elliptic.Basic
-- Proof-only: `degreeLT` and its basis, for the private dimension count.
import Mathlib.RingTheory.Polynomial.DegreeLT
-- Proof-only: `algebraMap_smul_eq_mul`, moving `F[X]`-scalars into the function field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint

/-!
# The function field of an elliptic curve has genus one

Let `W` be an elliptic Weierstrass curve over a field `F`, with coordinate functions `x` and `y`
and place at infinity `O`.  This file computes the Riemann–Roch spaces `L(n · O)` by hand and
reads off the two invariants of `F(W) / F` that the general theory of function fields needs:

* `F` is the **exact field of constants** of `F(W)`;
* `F(W)` has **genus one**, and is therefore an elliptic function field in the sense of
  `TauCeti.IsEllipticFunctionField`, the place at infinity being rational.

The computation is the classical one.  A function with no pole away from `O` is regular at every
height-one prime of the coordinate ring, which is a Dedekind domain, so it lies in the coordinate
ring and is `p + q y` for polynomials `p` and `q`.  At infinity the two summands have pole orders
`2 deg p` and `2 deg q + 3`; these have different parities, so they never cancel, and

`p + q y ∈ L(n · O)` exactly when `2 deg p ≤ n` and `2 deg q + 3 ≤ n`.

Counting the monomials `xⁱ` and `xʲ y` allowed by these bounds gives `ℓ(n · O) = n` for `n ≥ 1`
and `ℓ(0) = 1`.  The second value says the constants are exact; the first, compared with Riemann's
theorem in large degree, says the genus is one.  No Riemann–Roch theorem, differential or
ramification computation is used.

## Main results

* `WeierstrassCurve.Affine.mem_riemannRochSpace_natCast_zsmul_ofPoint_infinity_iff`: the
  functions in `L(n · O)` are the `p + q y` with `2 deg p ≤ n` and `2 deg q + 3 ≤ n`.
* `WeierstrassCurve.Affine.isIntegrallyClosedIn_functionField`: `F` is the exact field of
  constants of `F(W)`.
* `WeierstrassCurve.Affine.genus_functionField`: **`F(W)` has genus one.**
* `WeierstrassCurve.Affine.isEllipticFunctionField`: `F(W) / F` is an elliptic function field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 1.4.15, Theorem 1.4.17 and Proposition 6.1.3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Section III.3.
-/

public section

open Polynomial TauCeti AlgebraicGeometry IsDedekindDomain

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-! ### Pole orders at infinity -/

section PoleOrder

open scoped Classical in
/-- The value at infinity of `q y` for a nonzero polynomial `q`: a pole of order `2 deg q + 3`. -/
private theorem infinityPlace_algebraMap_mul_mk_Y {q : F[X]} (hq : q ≠ 0) :
    W.infinityPlace (algebraMap F[X] W.FunctionField q *
        algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) =
      WithZero.exp (2 * (q.natDegree : ℤ) + 3) := by
  rw [map_mul, infinityPlace_algebraMap_polynomial W hq, infinityPlace.mk_Y, ← WithZero.exp_add]

open scoped Classical in
/-- **The pole order at infinity of `p + q y`**: it is at most `n` exactly when `2 deg p ≤ n`
and `2 deg q + 3 ≤ n`.  The two summands have pole orders of different parities, so the value of
the sum is the larger of the two values. -/
private theorem infinityPlace_add_mul_mk_Y_le_exp_iff (p q : F[X]) (n : ℕ) :
    W.infinityPlace (algebraMap F[X] W.FunctionField p + algebraMap F[X] W.FunctionField q *
        algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) ≤
        WithZero.exp (n : ℤ) ↔
      2 * p.natDegree ≤ n ∧ (q = 0 ∨ 2 * q.natDegree + 3 ≤ n) := by
  rcases eq_or_ne q 0 with rfl | hq
  · rcases eq_or_ne p 0 with rfl | hp
    · simp
    · simp only [map_zero, zero_mul, add_zero, infinityPlace_algebraMap_polynomial W hp,
        WithZero.exp_le_exp, true_or, and_true]
      omega
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [map_zero, zero_add, infinityPlace_algebraMap_mul_mk_Y W hq, WithZero.exp_le_exp,
      natDegree_zero, mul_zero, zero_le, hq, false_or, true_and]
    omega
  have hne : W.infinityPlace (algebraMap F[X] W.FunctionField p) ≠
      W.infinityPlace (algebraMap F[X] W.FunctionField q *
        algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
    rw [infinityPlace_algebraMap_polynomial W hp, infinityPlace_algebraMap_mul_mk_Y W hq]
    intro h
    have := WithZero.exp_injective h
    omega
  rw [W.infinityPlace.map_add_of_distinct_val hne, max_le_iff,
    infinityPlace_algebraMap_polynomial W hp, infinityPlace_algebraMap_mul_mk_Y W hq,
    WithZero.exp_le_exp, WithZero.exp_le_exp]
  simp only [hq, false_or]
  omega

end PoleOrder

/-! ### The monomials `xⁱ` and `xʲ y` -/

/-- The `F`-linear map `(p, q) ↦ p + q y` on pairs of polynomials of degree less than `a` and
less than `b`. -/
private noncomputable def addMulMkY (a b : ℕ) :
    degreeLT F a × degreeLT F b →ₗ[F] W.FunctionField :=
  (((Algebra.linearMap F[X] W.FunctionField).restrictScalars F).comp
      (degreeLT F a).subtype).coprod
    ((LinearMap.mulRight F (algebraMap W.CoordinateRing W.FunctionField
        (CoordinateRing.mk W Y))).comp
      (((Algebra.linearMap F[X] W.FunctionField).restrictScalars F).comp (degreeLT F b).subtype))

private theorem addMulMkY_apply (a b : ℕ) (pq : degreeLT F a × degreeLT F b) :
    addMulMkY W a b pq = algebraMap F[X] W.FunctionField pq.1 +
      algebraMap F[X] W.FunctionField pq.2 *
        algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) :=
  (rfl)

/-- The image of `p • 1 + q • Y` in the function field is `p + q y`. -/
private theorem algebraMap_smul_one_add_smul_mk_Y (p q : F[X]) :
    algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W Y) =
      algebraMap F[X] W.FunctionField p + algebraMap F[X] W.FunctionField q *
        algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) := by
  rw [map_add, algebraMap_smul_eq_mul, algebraMap_smul_eq_mul, map_one, mul_one]

/-- `p + q y = 0` forces `p = q = 0`: `{1, y}` is a basis of the coordinate ring over `F[X]`. -/
private theorem addMulMkY_injective (a b : ℕ) : Function.Injective (addMulMkY W a b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ h
  rw [addMulMkY_apply, ← algebraMap_smul_one_add_smul_mk_Y] at h
  obtain ⟨rfl, rfl⟩ := CoordinateRing.smul_basis_eq_zero
    ((map_eq_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mp h)
  rfl

/-! ### The Riemann–Roch spaces `L(n · O)` -/

section RiemannRochSpace

variable [W.IsElliptic]

local instance : IsDedekindDomain W.CoordinateRing :=
  have := isIntegrallyClosed_coordinateRing W
  W.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **The Riemann–Roch spaces at infinity of an elliptic curve**: for `n : ℕ`, a function lies
in `L(n · O)` exactly when it is `p + q y` for polynomials `p` and `q` with `2 deg p ≤ n` and
`2 deg q + 3 ≤ n` (the latter read as vacuous when `q = 0`).  So `L(n · O)` is spanned by the
monomials `xⁱ` with `2i ≤ n` and `xʲ y` with `2j + 3 ≤ n`. -/
theorem mem_riemannRochSpace_natCast_zsmul_ofPoint_infinity_iff {n : ℕ} {f : W.FunctionField} :
    f ∈ riemannRochSpace ((n : ℤ) • WeilDivisor.ofPoint (Place.infinity W)) ↔
      ∃ p q : F[X], 2 * p.natDegree ≤ n ∧ (q = 0 ∨ 2 * q.natDegree + 3 ≤ n) ∧
        algebraMap F[X] W.FunctionField p + algebraMap F[X] W.FunctionField q *
          algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) = f := by
  rw [mem_riemannRochSpace_iff]
  constructor
  · intro hf
    -- Regular at every affine place, `f` lies in the coordinate ring.
    have haff (𝔭 : HeightOneSpectrum W.CoordinateRing) : 𝔭.valuation W.FunctionField f ≤ 1 := by
      have h := hf (Place.ofPrime F W.FunctionField 𝔭)
      rwa [WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_of_ne
        (Place.infinity_ne_ofPrime 𝔭).symm, mul_zero, WithZero.exp_zero,
        Place.valuation_ofPrime] at h
    obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one W.FunctionField f haff
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
    have hr := algebraMap_smul_one_add_smul_mk_Y W p q
    -- At infinity, the bound on the pole order is the bound on the degrees.
    have h := hf (Place.infinity W)
    rw [WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one, Place.valuation_infinity,
      hr, infinityPlace_add_mul_mk_Y_le_exp_iff] at h
    exact ⟨p, q, h.1, h.2, hr.symm⟩
  · rintro ⟨p, q, hp, hq, rfl⟩ P
    rcases Place.eq_infinity_or_existsUnique_eq_ofPrime P with rfl | ⟨𝔭, rfl, -⟩
    · rw [WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one,
        Place.valuation_infinity, infinityPlace_add_mul_mk_Y_le_exp_iff]
      exact ⟨hp, hq⟩
    · rw [WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_of_ne
        (Place.infinity_ne_ofPrime 𝔭).symm, mul_zero, WithZero.exp_zero,
        ← (Place.ofPrime F W.FunctionField 𝔭).mem_integers_iff,
        ← algebraMap_smul_one_add_smul_mk_Y]
      exact Place.algebraMap_mem_integers_ofPrime F W.FunctionField 𝔭 _

/-- `L(n · O)` is the image of the pairs `(p, q)` with `deg p < n / 2 + 1` and
`deg q < (n - 1) / 2`. -/
private theorem riemannRochSpace_eq_range_addMulMkY (n : ℕ) :
    riemannRochSpace ((n : ℤ) • WeilDivisor.ofPoint (Place.infinity W)) =
      LinearMap.range (addMulMkY W (n / 2 + 1) ((n - 1) / 2)) := by
  -- A polynomial has degree less than `m` exactly when it is `0` or its `natDegree` is.
  have hdeg (p : F[X]) (m : ℕ) : p ∈ degreeLT F m ↔ p = 0 ∨ p.natDegree < m := by
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    · rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt hp]
      simp [hp]
  ext f
  rw [mem_riemannRochSpace_natCast_zsmul_ofPoint_infinity_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨(⟨p, (hdeg p _).mpr (Or.inr (by omega))⟩, ⟨q, (hdeg q _).mpr ?_⟩), rfl⟩
    exact hq.imp id (fun hq ↦ by omega)
  · rintro ⟨⟨⟨p, hp⟩, ⟨q, hq⟩⟩, rfl⟩
    refine ⟨p, q, ?_, ((hdeg q _).mp hq).imp id (fun hq ↦ by omega), rfl⟩
    rcases (hdeg p _).mp hp with rfl | hp
    · simp
    · omega

/-- **`ℓ(n · O)` counted by monomials**: `n / 2 + 1` powers `xⁱ` and `(n - 1) / 2` products
`xʲ y`.  This is `n` for `n ≥ 1` and `1` for `n = 0`. -/
private theorem dim_natCast_zsmul_ofPoint_infinity (n : ℕ) :
    Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint (Place.infinity W)) = n / 2 + 1 + (n - 1) / 2 := by
  rw [Divisor.dim_def, riemannRochSpace_eq_range_addMulMkY,
    LinearMap.finrank_range_of_inj (addMulMkY_injective W _ _),
    Module.finrank_eq_card_basis (degreeLT.basisProd F _ _), Fintype.card_fin]

/-- **`F` is the exact field of constants of the function field of an elliptic curve**: the
functions without poles form the one-dimensional space `L(0)`, which is the field of constants. -/
theorem isIntegrallyClosedIn_functionField : IsIntegrallyClosedIn F W.FunctionField := by
  rw [isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one,
    ← Divisor.dim_zero W.isFunctionField]
  simpa using dim_natCast_zsmul_ofPoint_infinity W 0

/-- **The function field of an elliptic curve has genus one.**  Riemann's theorem gives
`ℓ(D) = deg D + 1 - g` for every divisor of large degree, and at `D = n · O` the left side is `n`
while `deg D = n`, the place at infinity being rational. -/
@[simp]
theorem genus_functionField : genus F W.FunctionField = 1 := by
  obtain ⟨c, hc⟩ := exists_forall_dim_eq_degree_add_one_sub_genus W.isFunctionField
    (isIntegrallyClosedIn_functionField W)
  have h := hc (((max c 1).toNat : ℤ) • WeilDivisor.ofPoint (Place.infinity W))
    (by simp [Divisor.degree_zsmul])
  rw [dim_natCast_zsmul_ofPoint_infinity, Divisor.degree_zsmul, Divisor.degree_ofPoint,
    Place.degree_infinity] at h
  omega

/-- **The function field of an elliptic curve is an elliptic function field**: it has genus one,
and the place at infinity is a divisor of degree one. -/
theorem isEllipticFunctionField : IsEllipticFunctionField F W.FunctionField :=
  (isEllipticFunctionField_iff_genus_eq_one_and_exists_place_degree_eq_one W.isFunctionField
    (isIntegrallyClosedIn_functionField W)).mpr
    ⟨genus_functionField W, Place.infinity W, Place.degree_infinity⟩

end RiemannRochSpace

end WeierstrassCurve.Affine
