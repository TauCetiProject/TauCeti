/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.RegularLocalRing.Hypersurface

/-!
# The coordinate ring of the circle

For a commutative ring `k`, `TauCeti.CircleRing k = k[x, y] ⧸ (x² + y² - 1)` is the coordinate
ring of the affine unit circle over `k`. For `k = ℝ` it is the ring of the real algebraic circle,
over which the rotation matrix `!![x, -y; y, x]` has determinant one.

A `k`-algebra map out of `CircleRing k` is the same as a point `(a, b)` with `a² + b² = 1`
(`TauCeti.CircleRing.lift`, `TauCeti.CircleRing.algHom_ext`).

When `2` is invertible in `k`, the circle is covered by the two charts `1 + x ≠ 0` and
`1 - x ≠ 0`, since `(1 + x) + (1 - x) = 2`. For `ε` with `ε² = 1`, stereographic projection from
the point `(-ε, 0)` identifies the chart `1 + εx ≠ 0` with the localization `k[t, (1 + t²)⁻¹]`:
the coordinate is `t = y / (1 + εx)`, with inverse

  `x = ε (1 - t²) / (1 + t²)`, `y = 2t / (1 + t²)`, `(1 + εx)⁻¹ = (1 + t²) / 2`.

On the overlap of the charts of `ε = 1` and `ε = -1` the two coordinates are inverse to each
other, because `y² = (1 - x)(1 + x)`.

Over a field in which `2 ≠ 0` the equation `x² + y² - 1` is irreducible, and together with its
partial derivatives `2x`, `2y` it generates the unit ideal, so the curve is smooth. By the Jacobian
criterion for plane curves (`MvPolynomial.isDedekindDomain_quotient_span_singleton`),
`CircleRing k` is then a Dedekind domain. In characteristic two the equation is the square
`(x + y + 1)²`, and the ring is not even reduced.

## Main definitions

* `TauCeti.CircleRing k`: the coordinate ring `k[x, y] ⧸ (x² + y² - 1)`.
* `TauCeti.CircleRing.x`, `TauCeti.CircleRing.y`: the two coordinate functions.
* `TauCeti.CircleRing.lift`: the `k`-algebra map sending `x, y` to a point `(a, b)` of the circle.
* `TauCeti.CircleRing.stereographicEquiv`: the chart `1 + εx ≠ 0` is `k[t, (1 + t²)⁻¹]`.
* `TauCeti.CircleRing.chartToOverlap`: the canonical map from a chart `1 + εx ≠ 0` to the overlap
  `y ≠ 0`.

## Main results

* `TauCeti.irreducible_X_zero_sq_add_X_one_sq_sub_one`: `x² + y² - 1` is irreducible over a
  domain in which `2 ≠ 0`.
* `TauCeti.CircleRing.isCoprime_one_add_x_one_sub_x`: the two charts cover the circle.
* `TauCeti.CircleRing.instIsDedekindDomain`: over a field in which `2 ≠ 0`, `CircleRing k` is a
  Dedekind domain.
* `TauCeti.CircleRing.stereographic_overlap`: on the overlap `y ≠ 0`, the two stereographic
  coordinates satisfy `t₊ · t₋ = 1`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Example 1.5.4 (the real circle ring and its rotation
  matrix).
-/

public section

open scoped Polynomial

namespace TauCeti

section Equation

open MvPolynomial

variable (k : Type*) [CommRing k]

/-- **The coordinate ring of the unit circle** `k[x, y] ⧸ (x² + y² - 1)` over `k`. -/
abbrev CircleRing : Type _ :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k)}

/-- **The circle equation is irreducible** over a domain in which `2 ≠ 0`. -/
theorem irreducible_X_zero_sq_add_X_one_sq_sub_one [IsDomain k] (h2 : (2 : k) ≠ 0) :
    Irreducible (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k) := by
  -- As a monic quadratic in `y` over `k[x]`, a factorization gives a root `a ∈ k[x]` with
  -- `a² = (1 - x)(1 + x)`. Then `x - 1` divides `a`, hence `x + 1`, which fails at `x = 1`.
  set g : k[X][X] := Polynomial.X ^ 2 + Polynomial.C (Polynomial.X ^ 2 - 1)
  have hmon : g.Monic := Polynomial.monic_X_pow_add_C _ two_ne_zero
  have hdeg : g.natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hirr : Irreducible g := by
    rw [hmon.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg.ge (by omega),
      Polynomial.roots_eq_zero_iff_not_isRoot hmon.ne_zero]
    intro a ha
    simp only [g, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at ha
    have hp : Prime (Polynomial.X - 1 : k[X]) := by
      simpa using Polynomial.prime_X_sub_C (1 : k)
    obtain ⟨b, rfl⟩ := hp.dvd_of_dvd_pow
      (show (Polynomial.X - 1 : k[X]) ∣ a ^ 2 from ⟨-(Polynomial.X + 1), by linear_combination ha⟩)
    have hb : (Polynomial.X - 1 : k[X]) * ((Polynomial.X - 1) * b ^ 2 + (Polynomial.X + 1)) = 0 :=
      by linear_combination ha
    have h1 := congrArg (Polynomial.eval 1) ((mul_eq_zero.mp hb).resolve_left hp.ne_zero)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_zero, sub_self, zero_mul,
      zero_add] at h1
    exact h2 (by linear_combination h1)
  have hf : (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k) =
      Polynomial.Bivariate.equivMvPolynomial k g := by
    simp only [g, map_add, map_pow, map_sub, map_one, Polynomial.Bivariate.equivMvPolynomial_X,
      Polynomial.Bivariate.equivMvPolynomial_C_X]
    ring
  rw [hf]
  exact (MulEquiv.irreducible_iff (Polynomial.Bivariate.equivMvPolynomial k)).mpr hirr

namespace CircleRing

variable {k}

/-- The first coordinate function `x` on the circle. -/
noncomputable def x : CircleRing k := Ideal.Quotient.mk _ (X 0)

/-- The second coordinate function `y` on the circle. -/
noncomputable def y : CircleRing k := Ideal.Quotient.mk _ (X 1)

@[simp]
theorem mk_X_zero :
    Ideal.Quotient.mk (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k)}) (X 0) = x :=
  (rfl)

@[simp]
theorem mk_X_one :
    Ideal.Quotient.mk (Ideal.span {(X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k)}) (X 1) = y :=
  (rfl)

/-- The coordinate functions satisfy the circle equation. -/
theorem x_sq_add_y_sq : (x : CircleRing k) ^ 2 + y ^ 2 = 1 := by
  have h := Ideal.Quotient.mk_singleton_self (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k)
  simp only [map_sub, map_add, map_pow, map_one, mk_X_zero, mk_X_one] at h
  linear_combination h

/-- The image of the circle equation under a ring map out of `CircleRing k`. -/
private theorem map_x_sq_add_map_y_sq {S F : Type*} [CommRing S] [FunLike F (CircleRing k) S]
    [RingHomClass F (CircleRing k) S] (f : F) : f x ^ 2 + f y ^ 2 = 1 := by
  rw [← map_pow, ← map_pow, ← map_add, x_sq_add_y_sq, map_one]

/-- The factorization `y² = (1 - x)(1 + x)`. On the overlap of the charts `1 + x ≠ 0` and
`1 - x ≠ 0` it says that the stereographic coordinates `y / (1 + x)` and `y / (1 - x)` are
inverse to each other. -/
theorem y_sq : (y : CircleRing k) ^ 2 = (1 - x) * (1 + x) := by
  linear_combination (x_sq_add_y_sq (k := k))

variable {S : Type*} [CommRing S] [Algebra k S]

/-- **The universal property of the circle.** The `k`-algebra map `CircleRing k →ₐ[k] S` sending
`x` to `a` and `y` to `b`, for a point `(a, b)` of the circle over `S`. -/
noncomputable def lift (a b : S) (h : a ^ 2 + b ^ 2 = 1) : CircleRing k →ₐ[k] S :=
  Ideal.Quotient.liftₐ _ (aeval ![a, b]) fun p hp => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [h]

@[simp]
theorem lift_x (a b : S) (h : a ^ 2 + b ^ 2 = 1) : lift a b h (x : CircleRing k) = a :=
  (Ideal.Quotient.lift_mk _ _ _).trans (by simp)

@[simp]
theorem lift_y (a b : S) (h : a ^ 2 + b ^ 2 = 1) : lift a b h (y : CircleRing k) = b :=
  (Ideal.Quotient.lift_mk _ _ _).trans (by simp)

/-- Two `k`-algebra maps out of `CircleRing k` agree as soon as they agree on `x` and `y`. -/
@[ext]
theorem algHom_ext {f g : CircleRing k →ₐ[k] S} (hx : f x = g x) (hy : f y = g y) : f = g :=
  Ideal.Quotient.algHom_ext k <| MvPolynomial.algHom_ext fun i => by
    fin_cases i
    exacts [hx, hy]

/-- **The two charts cover the circle**: when `2` is invertible, `1 + x` and `1 - x` generate
the unit ideal, their sum being `2`. -/
theorem isCoprime_one_add_x_one_sub_x (h2 : IsUnit (2 : k)) :
    IsCoprime (1 + x : CircleRing k) (1 - x) := by
  obtain ⟨u, hu⟩ := h2.map (algebraMap k (CircleRing k))
  rw [map_ofNat] at hu
  exact ⟨↑u⁻¹, ↑u⁻¹, by linear_combination (-↑u⁻¹ : CircleRing k) * hu + Units.inv_mul u⟩

/-- **The circle is a Dedekind domain** over a field in which `2 ≠ 0`. -/
instance instIsDedekindDomain {k : Type*} [Field k] [NeZero (2 : k)] :
    IsDedekindDomain (CircleRing k) := by
  -- The equation is irreducible, and with its partial derivatives `2x` and `2y` it generates
  -- the unit ideal, so the Jacobian criterion applies.
  refine MvPolynomial.isDedekindDomain_quotient_span_singleton
    (irreducible_X_zero_sq_add_X_one_sq_sub_one k two_ne_zero) ?_
  have h0 : pderiv 0 (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k) = 2 * X 0 := by
    simp [pderiv_X, mul_comm]
  have h1 : pderiv 1 (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k) = 2 * X 1 := by
    simp [pderiv_X, mul_comm]
  have hC : C (2⁻¹ : k) * 2 = (1 : MvPolynomial (Fin 2) k) := by
    rw [← map_ofNat C 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  rw [h0, h1, Ideal.eq_top_iff_one]
  have hmem : -1 * (X 0 ^ 2 + X 1 ^ 2 - 1) + (C 2⁻¹ * X 0) * (2 * X 0) +
      (C 2⁻¹ * X 1) * (2 * X 1) ∈
        Ideal.span {(X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k), 2 * X 0, 2 * X 1} := by
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;> refine Ideal.mul_mem_left _ _ ?_ <;>
      exact Ideal.subset_span (by simp)
  -- `1 = -(x² + y² - 1) + (x / 2) (2x) + (y / 2) (2y)`
  convert hmem using 1
  linear_combination (-(X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) k)) * hC

end CircleRing

end Equation

/-! ### The stereographic charts -/

namespace CircleRing

open Polynomial IsLocalization.Away

variable {k : Type*} [CommRing k] {ε : k}

/-- The image of `ε² = 1` in a `k`-algebra. -/
private theorem algebraMap_sq_eq_one {S : Type*} [CommRing S] [Algebra k S] (hε : ε ^ 2 = 1) :
    algebraMap k S ε ^ 2 = 1 := by
  rw [← map_pow, hε, map_one]

/-- When `2` is invertible in `k`, `2 * b` is a unit in a `k`-algebra if `b` is invertible. -/
private theorem isUnit_two_mul {S : Type*} [CommRing S] [Algebra k S] (h2 : IsUnit (2 : k))
    {a b : S} (h : a * b = 1) : IsUnit (2 * b) :=
  .mul (map_ofNat (algebraMap k S) 2 ▸ h2.map _) (.of_mul_eq_one_right _ h)

/-- A ring homomorphism out of `Localization.Away r` sends `invSelf r` and `algebraMap R _ r` to
elements with product `1`. -/
private theorem map_invSelf_mul_map {R S : Type*} {r : R} {F : Type*} [CommRing R] [CommRing S]
    [FunLike F (Localization.Away r) S] [RingHomClass F (Localization.Away r) S] (f : F) :
    f (invSelf r) * f (algebraMap R _ r) = 1 := by
  rw [← map_mul, mul_comm, mul_invSelf, map_one]

/-! The identities behind the two charts, for elements `E`, `T`, `w` (on the `t` side) and
`E`, `a`, `b`, `v`, `w` (on the `x, y` side) of a commutative ring. They are applied with `E` the
image of `ε`, `T` the image of `t`, `a`, `b` the images of `x`, `y`, and `v`, `w` the inverses
of `1 + εx` and `1 + t²`. -/

/-- The point `(E (1 - T²) w, 2Tw)` lies on the circle when `E² = 1` and `w = (1 + T²)⁻¹`. -/
private theorem chart_sq_add_sq {R : Type*} [CommRing R] {E T w : R} (hE : E ^ 2 = 1)
    (hw : (1 + T ^ 2) * w = 1) : (E * (1 - T ^ 2) * w) ^ 2 + (2 * T * w) ^ 2 = 1 := by
  linear_combination (w ^ 2 * (1 - T ^ 2) ^ 2) * hE + ((1 + T ^ 2) * w + 1) * hw

/-- At the point `(E (1 - T²) w, 2Tw)`, the chart function `1 + Ex` takes the value `2w`. -/
private theorem chart_one_add_mul {R : Type*} [CommRing R] {E T w : R} (hE : E ^ 2 = 1)
    (hw : (1 + T ^ 2) * w = 1) : 1 + E * (E * (1 - T ^ 2) * w) = 2 * w := by
  linear_combination (1 - T ^ 2) * w * hE - hw

/-- On the circle `a² + b² = 1` with `v = (1 + Ea)⁻¹`, the coordinate `t = bv` satisfies
`1 + t² = 2v`. -/
private theorem chart_one_add_sq {R : Type*} [CommRing R] {E a b v : R} (hE : E ^ 2 = 1)
    (hab : a ^ 2 + b ^ 2 = 1) (hv : (1 + E * a) * v = 1) : 1 + (b * v) ^ 2 = 2 * v := by
  linear_combination v ^ 2 * a ^ 2 * hE + v ^ 2 * hab + (2 * v - (1 + E * a) * v - 1) * hv

/-- On the circle `a² + b² = 1` with `v = (1 + Ea)⁻¹` and `w = (2v)⁻¹`, the coordinate `t = bv`
recovers `a = E (1 - t²) / (1 + t²)`. -/
private theorem chart_x_eq {R : Type*} [CommRing R] {E a b v w : R} (hE : E ^ 2 = 1)
    (hab : a ^ 2 + b ^ 2 = 1) (hv : (1 + E * a) * v = 1) (hw : w * (2 * v) = 1) :
    E * (1 - (b * v) ^ 2) * w = a := by
  linear_combination w * v ^ 2 * (-E) * hab + w * v ^ 2 * (2 * a + E * a ^ 2) * hE +
    w * (2 * a * v - E * ((1 + E * a) * v + 1)) * hv + a * hw

/-- The point `(ε (1 - t²) / (1 + t²), 2t / (1 + t²))` of the circle over `k[t, (1 + t²)⁻¹]`. -/
private noncomputable def toChartAux (hε : ε ^ 2 = 1) :
    CircleRing k →ₐ[k] Localization.Away (1 + X ^ 2 : k[X]) :=
  lift (algebraMap k _ ε * algebraMap k[X] _ (1 - X ^ 2) * invSelf (1 + X ^ 2 : k[X]))
    (algebraMap k[X] _ (2 * X) * invSelf (1 + X ^ 2 : k[X])) (by
      have hw := mul_invSelf (S := Localization.Away (1 + X ^ 2 : k[X])) (1 + X ^ 2 : k[X])
      simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat] at hw ⊢
      exact chart_sq_add_sq (algebraMap_sq_eq_one hε) hw)

private theorem toChartAux_x (hε : ε ^ 2 = 1) :
    toChartAux hε x =
      algebraMap k _ ε * algebraMap k[X] _ (1 - X ^ 2) * invSelf (1 + X ^ 2 : k[X]) :=
  lift_x ..

private theorem toChartAux_y (hε : ε ^ 2 = 1) :
    toChartAux hε y = algebraMap k[X] _ (2 * X) * invSelf (1 + X ^ 2 : k[X]) :=
  lift_y ..

/-- The chart function `1 + εx` becomes `2 / (1 + t²)`. -/
private theorem toChartAux_one_add_smul_x (hε : ε ^ 2 = 1) :
    toChartAux hε (1 + ε • x) = 2 * invSelf (1 + X ^ 2 : k[X]) := by
  have hw := mul_invSelf (S := Localization.Away (1 + X ^ 2 : k[X])) (1 + X ^ 2 : k[X])
  rw [map_add, map_one, map_smul, toChartAux_x, Algebra.smul_def]
  simp only [map_add, map_sub, map_pow, map_one] at hw ⊢
  exact chart_one_add_mul (algebraMap_sq_eq_one hε) hw

/-- The forward chart map `k[x, y, (1 + εx)⁻¹] → k[t, (1 + t²)⁻¹]`. -/
private noncomputable def toChart (hε : ε ^ 2 = 1) (h2 : IsUnit (2 : k)) :
    Localization.Away (1 + ε • x : CircleRing k) →ₐ[k] Localization.Away (1 + X ^ 2 : k[X]) :=
  liftAlgHom (1 + ε • x) (f := toChartAux hε) <| by
    rw [toChartAux_one_add_smul_x]
    exact isUnit_two_mul h2 (mul_invSelf _)

/-- The coordinate `t = y / (1 + εx)` of the chart, as a map `k[t] → k[x, y, (1 + εx)⁻¹]`. -/
private noncomputable def fromChartAux (ε : k) :
    k[X] →ₐ[k] Localization.Away (1 + ε • x : CircleRing k) :=
  aeval (algebraMap (CircleRing k) _ y * invSelf (1 + ε • x : CircleRing k))

/-- `(1 + εx) · (1 + εx)⁻¹ = 1`, with the chart function written out. -/
private theorem one_add_mul_mul_invSelf (ε : k) :
    (1 + algebraMap k (Localization.Away (1 + ε • x : CircleRing k)) ε *
      algebraMap (CircleRing k) _ x) * invSelf (1 + ε • x : CircleRing k) = 1 := by
  have hv := mul_invSelf (S := Localization.Away (1 + ε • x : CircleRing k))
    (1 + ε • x : CircleRing k)
  rwa [map_add, map_one, algebraMap.smul, Algebra.smul_def] at hv

/-- The function `1 + t²` becomes `2 / (1 + εx)`. -/
private theorem fromChartAux_one_add_X_sq (hε : ε ^ 2 = 1) :
    fromChartAux ε (1 + X ^ 2) = 2 * invSelf (1 + ε • x : CircleRing k) := by
  simp only [fromChartAux, map_add, map_one, map_pow, aeval_X]
  exact chart_one_add_sq (algebraMap_sq_eq_one hε) (map_x_sq_add_map_y_sq _)
    (one_add_mul_mul_invSelf ε)

/-- The inverse chart map `k[t, (1 + t²)⁻¹] → k[x, y, (1 + εx)⁻¹]`. -/
private noncomputable def fromChart (hε : ε ^ 2 = 1) (h2 : IsUnit (2 : k)) :
    Localization.Away (1 + X ^ 2 : k[X]) →ₐ[k] Localization.Away (1 + ε • x : CircleRing k) :=
  liftAlgHom (1 + X ^ 2 : k[X]) (f := fromChartAux ε) <| by
    rw [fromChartAux_one_add_X_sq hε]
    exact isUnit_two_mul h2 (mul_invSelf _)

private theorem toChart_algebraMap (hε : ε ^ 2 = 1) (h2 : IsUnit (2 : k)) (a : CircleRing k) :
    toChart hε h2 (algebraMap _ _ a) = toChartAux hε a := by
  simp [toChart]

private theorem fromChart_algebraMap (hε : ε ^ 2 = 1) (h2 : IsUnit (2 : k)) (p : k[X]) :
    fromChart hε h2 (algebraMap _ _ p) = fromChartAux ε p := by
  simp [fromChart]

private theorem toChart_comp_fromChart (hε : ε ^ 2 = 1) (h2 : IsUnit (2 : k)) :
    (toChart hε h2).comp (fromChart hε h2) = AlgHom.id k _ := by
  refine IsLocalization.algHom_ext (Submonoid.powers (1 + X ^ 2 : k[X]))
    (Polynomial.algHom_ext ?_)
  -- `(1 + εx)⁻¹` goes to `(1 + t²) / 2`
  have hv : toChart hε h2 (invSelf (1 + ε • x : CircleRing k)) *
      (2 * invSelf (1 + X ^ 2 : k[X])) = 1 := by
    rw [← toChartAux_one_add_smul_x hε, ← toChart_algebraMap hε h2]
    exact map_invSelf_mul_map (r := (1 + ε • x : CircleRing k)) (toChart hε h2)
  -- `t ↦ y / (1 + εx) ↦ (2t / (1 + t²)) · (1 + t²) / 2 = t`
  simp only [AlgHom.comp_apply, Algebra.algHom, IsScalarTower.toAlgHom_apply,
    fromChart_algebraMap, fromChartAux, aeval_X, map_mul, toChart_algebraMap, toChartAux_y,
    AlgHom.id_apply, map_ofNat]
  linear_combination algebraMap k[X] (Localization.Away (1 + X ^ 2 : k[X])) X * hv

private theorem fromChart_comp_toChart (hε : ε ^ 2 = 1) (h2 : IsUnit (2 : k)) :
    (fromChart hε h2).comp (toChart hε h2) = AlgHom.id k _ := by
  refine IsLocalization.algHom_ext (Submonoid.powers (1 + ε • x : CircleRing k))
    (algHom_ext ?_ ?_)
  all_goals
    -- `(1 + t²)⁻¹` goes to `(1 + εx) / 2`
    have hw : fromChart hε h2 (invSelf (1 + X ^ 2 : k[X])) *
        (2 * invSelf (1 + ε • x : CircleRing k)) = 1 := by
      rw [← fromChartAux_one_add_X_sq hε, ← fromChart_algebraMap hε h2]
      exact map_invSelf_mul_map (r := (1 + X ^ 2 : k[X])) (fromChart hε h2)
    simp only [AlgHom.comp_apply, Algebra.algHom, IsScalarTower.toAlgHom_apply,
      toChart_algebraMap, toChartAux_x, toChartAux_y, map_mul, AlgHom.commutes,
      fromChart_algebraMap, fromChartAux, map_sub, map_one, map_pow, aeval_X, map_ofNat,
      AlgHom.id_apply]
  · -- `x ↦ ε (1 - t²) / (1 + t²) ↦ ε (1 - y² / (1 + εx)²) (1 + εx) / 2 = x`
    linear_combination chart_x_eq (algebraMap_sq_eq_one hε) (map_x_sq_add_map_y_sq _)
      (one_add_mul_mul_invSelf ε) hw
  · -- `y ↦ 2t / (1 + t²) ↦ 2 (y / (1 + εx)) (1 + εx) / 2 = y`
    linear_combination
      algebraMap (CircleRing k) (Localization.Away (1 + ε • x : CircleRing k)) y * hw

/-- **The stereographic chart of the circle.** When `2` is invertible and `ε² = 1`, stereographic
projection from the point `(-ε, 0)` identifies the chart `1 + εx ≠ 0` of the circle with
`k[t, (1 + t²)⁻¹]`. The coordinate `t` is `y / (1 + εx)`; conversely `x = ε (1 - t²) / (1 + t²)`
and `y = 2t / (1 + t²)`. -/
noncomputable def stereographicEquiv (hε : ε ^ 2 = 1) (h2 : IsUnit (2 : k)) :
    Localization.Away (1 + ε • x : CircleRing k) ≃ₐ[k] Localization.Away (1 + X ^ 2 : k[X]) :=
  .ofAlgHom (toChart hε h2) (fromChart hε h2) (toChart_comp_fromChart hε h2)
    (fromChart_comp_toChart hε h2)

/-- In the stereographic chart, `x = ε (1 - t²) / (1 + t²)`. -/
@[simp]
theorem stereographicEquiv_algebraMap_x (hε : ε ^ 2 = 1) (h2 : IsUnit (2 : k)) :
    stereographicEquiv hε h2 (algebraMap (CircleRing k) _ x) =
      algebraMap k _ ε * algebraMap k[X] _ (1 - X ^ 2) * invSelf (1 + X ^ 2 : k[X]) := by
  rw [stereographicEquiv, AlgEquiv.ofAlgHom_apply, toChart_algebraMap, toChartAux_x]

/-- In the stereographic chart, `y = 2t / (1 + t²)`. -/
@[simp]
theorem stereographicEquiv_algebraMap_y (hε : ε ^ 2 = 1) (h2 : IsUnit (2 : k)) :
    stereographicEquiv hε h2 (algebraMap (CircleRing k) _ y) =
      algebraMap k[X] _ (2 * X) * invSelf (1 + X ^ 2 : k[X]) := by
  rw [stereographicEquiv, AlgEquiv.ofAlgHom_apply, toChart_algebraMap, toChartAux_y]

/-- The stereographic coordinate is `t = y / (1 + εx)`. -/
@[simp]
theorem stereographicEquiv_symm_algebraMap_X (hε : ε ^ 2 = 1) (h2 : IsUnit (2 : k)) :
    (stereographicEquiv hε h2).symm (algebraMap k[X] _ X) =
      algebraMap (CircleRing k) _ y * invSelf (1 + ε • x : CircleRing k) := by
  rw [stereographicEquiv, AlgEquiv.ofAlgHom_symm_apply, fromChart_algebraMap, fromChartAux,
    aeval_X]

private theorem one_add_smul_x_mul_one_sub_smul_x (hε : ε ^ 2 = 1) :
    (1 + ε • x : CircleRing k) * (1 - ε • x) = y ^ 2 := by
  have hεA : algebraMap k (CircleRing k) ε ^ 2 = 1 := algebraMap_sq_eq_one hε
  rw [show ε • (x : CircleRing k) = algebraMap k (CircleRing k) ε * x from Algebra.smul_def ε x]
  linear_combination -x_sq_add_y_sq (k := k) - x ^ 2 * hεA

/-- In the overlap `k[x, y, y⁻¹]`, `1 + εx` is a unit whenever `ε² = 1`. -/
theorem isUnit_one_add_smul_x_away_y (hε : ε ^ 2 = 1) :
    IsUnit (algebraMap (CircleRing k) (Localization.Away (y : CircleRing k)) (1 + ε • x)) := by
  have hyUnit : IsUnit
      (algebraMap (CircleRing k) (Localization.Away (y : CircleRing k)) (y ^ 2)) := by
    rw [map_pow]
    exact (algebraMap_isUnit y).pow 2
  exact isUnit_of_dvd_unit
    (map_dvd _ ⟨1 - ε • x, (one_add_smul_x_mul_one_sub_smul_x hε).symm⟩) hyUnit

/-- The canonical `k`-algebra map from the stereographic chart `k[x, y, (1 + εx)⁻¹]` to the
overlap `k[x, y, y⁻¹]`, for `ε² = 1`. -/
noncomputable def chartToOverlap (hε : ε ^ 2 = 1) :
    Localization.Away (1 + ε • x : CircleRing k) →ₐ[k] Localization.Away (y : CircleRing k) :=
  liftAlgHom (1 + ε • x : CircleRing k)
    (f := IsScalarTower.toAlgHom k (CircleRing k) (Localization.Away (y : CircleRing k))) <| by
    rw [IsScalarTower.toAlgHom_apply]
    exact isUnit_one_add_smul_x_away_y hε

/-- `chartToOverlap` commutes with the localization map from `CircleRing k`. -/
@[simp]
theorem chartToOverlap_algebraMap (hε : ε ^ 2 = 1) (a : CircleRing k) :
    chartToOverlap hε (algebraMap (CircleRing k) _ a) = algebraMap (CircleRing k) _ a := by
  simp [chartToOverlap]

/-- **Overlap compatibility of the stereographic charts.** On `k[x, y, y⁻¹]`, the two
stereographic coordinates `t₊ = y / (1 + x)` and `t₋ = y / (1 - x)` are mutually inverse:
`t₊ · t₋ = 1`. -/
theorem stereographic_overlap (h2 : IsUnit (2 : k)) :
    chartToOverlap (one_pow 2 : (1 : k) ^ 2 = 1)
        ((stereographicEquiv (one_pow 2 : (1 : k) ^ 2 = 1) h2).symm (algebraMap k[X] _ X)) *
      chartToOverlap (neg_one_sq : (-1 : k) ^ 2 = 1)
        ((stereographicEquiv (neg_one_sq : (-1 : k) ^ 2 = 1) h2).symm
          (algebraMap k[X] _ X)) = 1 := by
  rw [stereographicEquiv_symm_algebraMap_X, stereographicEquiv_symm_algebraMap_X]
  set s₁ : CircleRing k := 1 + (1 : k) • x
  set s₂ : CircleRing k := 1 + (-1 : k) • x
  have h₁ : chartToOverlap (one_pow 2 : (1 : k) ^ 2 = 1) (invSelf s₁) *
      algebraMap (CircleRing k) _ s₁ = 1 := by
    rw [← chartToOverlap_algebraMap (one_pow 2 : (1 : k) ^ 2 = 1) s₁]
    exact map_invSelf_mul_map (r := s₁) (chartToOverlap (one_pow 2 : (1 : k) ^ 2 = 1))
  have h₂ : chartToOverlap (neg_one_sq : (-1 : k) ^ 2 = 1) (invSelf s₂) *
      algebraMap (CircleRing k) _ s₂ = 1 := by
    rw [← chartToOverlap_algebraMap (neg_one_sq : (-1 : k) ^ 2 = 1) s₂]
    exact map_invSelf_mul_map (r := s₂) (chartToOverlap (neg_one_sq : (-1 : k) ^ 2 = 1))
  have hs₁₂ : algebraMap (CircleRing k) (Localization.Away (y : CircleRing k)) (y ^ 2) =
      algebraMap (CircleRing k) _ s₁ * algebraMap (CircleRing k) _ s₂ := by
    rw [← map_mul, y_sq]
    simp [s₁, s₂, sub_eq_add_neg, mul_comm]
  simp only [map_mul, chartToOverlap_algebraMap]
  calc
    (algebraMap (CircleRing k) (Localization.Away (y : CircleRing k)) y *
        chartToOverlap (one_pow 2 : (1 : k) ^ 2 = 1) (invSelf s₁)) *
      (algebraMap (CircleRing k) (Localization.Away (y : CircleRing k)) y *
        chartToOverlap (neg_one_sq : (-1 : k) ^ 2 = 1) (invSelf s₂))
        = (algebraMap (CircleRing k) (Localization.Away (y : CircleRing k)) y) ^ 2 *
            (chartToOverlap (one_pow 2 : (1 : k) ^ 2 = 1) (invSelf s₁) *
              chartToOverlap (neg_one_sq : (-1 : k) ^ 2 = 1) (invSelf s₂)) := by ring
    _ = (chartToOverlap (one_pow 2 : (1 : k) ^ 2 = 1) (invSelf s₁) *
          algebraMap (CircleRing k) _ s₁) *
        (chartToOverlap (neg_one_sq : (-1 : k) ^ 2 = 1) (invSelf s₂) *
          algebraMap (CircleRing k) _ s₂) := by
          rw [← map_pow, hs₁₂]
          ring
    _ = 1 := by rw [h₁, h₂, mul_one]

end CircleRing

end TauCeti
