/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.Algebra.Polynomial.SpecificDegree
import TauCeti.RingTheory.RegularLocalRing.Hypersurface

/-!
# The coordinate ring of the algebraic circle

Let `CircleQuotient k = k[x, y] / (x² + y² - 1)` be the coordinate ring of the algebraic circle
over `k`, and `CircleRing = CircleQuotient ℝ` its real specialization. Over any field `k` with
`2 ≠ 0`, the defining polynomial `X₀² + X₁² - 1` is irreducible and the Jacobian ideal
`(X₀² + X₁² - 1, 2 X₀, 2 X₁)` is the unit ideal, so `CircleQuotient k` is a Dedekind domain by
the smooth affine plane-curve criterion `MvPolynomial.isDedekindDomain_quotient_span_singleton`.
In particular, `CircleRing` is a Dedekind domain.

Geometrically, whenever `2` is invertible in `k`, the two principal open charts `D(1 + x)` and
`D(1 - x)` cover `Spec(CircleQuotient k)` since `(1 + x) + (1 - x) = 2` is a unit. On each chart
`s = 1 + ε x` (`ε ∈ {±1}`), stereographic projection `t = y / s` with inverse
`x = ε (1 - t²) / (1 + t²)`, `y = 2 t / (1 + t²)` identifies the localization
`CircleQuotient k[s⁻¹]` with `k[t, (1 + t²)⁻¹]`, with overlap transition `t₊ · t₋ = 1` on `D(y)`.

## Main definitions

* `TauCeti.CircleQuotient`: the coordinate ring `k[x, y] / (x² + y² - 1)` of the algebraic circle
  over `k`.
* `TauCeti.CircleQuotient.x`, `TauCeti.CircleQuotient.y`: the coordinate generators of
  `CircleQuotient k`.
* `TauCeti.CircleQuotient.liftAlgHom`: the universal property of `CircleQuotient k` as a
  `k`-algebra.
* `TauCeti.CircleQuotient.stereographicChartEquiv`: the `k`-algebra isomorphism
  `Localization.Away (1 + ε x) ≃ₐ[k] Localization.Away (X² + 1)` for `ε² = 1` and
  `Invertible (2 : k)`.
* `TauCeti.CircleQuotient.chartToOverlap`: the canonical map from a stereographic chart to
  `Localization.Away y`.
* `TauCeti.CircleRing`: the real coordinate ring `CircleQuotient ℝ`.

## Main results

* `TauCeti.irreducible_circlePoly`, `TauCeti.isDedekindDomain_circleQuotient`: over any field
  of characteristic different from two, `X₀² + X₁² - 1` is irreducible and its quotient is a
  Dedekind domain.
* `TauCeti.CircleQuotient.instIsDedekindDomain`: `CircleQuotient k` is a Dedekind domain when
  `2 ≠ 0` in `k`.
* `TauCeti.CircleQuotient.span_one_add_x_one_sub_x`: `1 + x` and `1 - x` generate the unit ideal.
* `TauCeti.CircleQuotient.stereographic_overlap`: on `Localization.Away y`, the two stereographic
  parameters satisfy `t₊ · t₋ = 1`.
-/

public section

open Polynomial

namespace TauCeti

noncomputable section

/-- The coordinate ring `k[x, y] / (x² + y² - 1)` of the algebraic circle over `k`. -/
abbrev CircleQuotient (k : Type*) [CommRing k] :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span
    {MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - (1 : MvPolynomial (Fin 2) k)}

/-! ## Irreducibility and Dedekind-domain structure -/

section Field

variable {k : Type*} [Field k]

/-- Over a field of characteristic different from two, `X₀² + X₁² - 1` is irreducible in
`k[X₀, X₁]`. -/
theorem irreducible_circlePoly (h2 : (2 : k) ≠ 0) :
    Irreducible (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k) := by
  let P : k[X][X] := Polynomial.X ^ 2 + Polynomial.C (Polynomial.X ^ 2 - 1)
  have hPeq : Polynomial.Bivariate.equivMvPolynomial k P =
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1 : MvPolynomial (Fin 2) k) := by
    simp only [P, map_add, map_sub, map_pow, map_one,
      Polynomial.Bivariate.equivMvPolynomial_X, Polynomial.Bivariate.equivMvPolynomial_C_X]
    ring
  rw [← hPeq, MulEquiv.irreducible_iff]
  have hdegC : (Polynomial.C (Polynomial.X ^ 2 - 1 : k[X])).natDegree <
      (Polynomial.X ^ 2 : k[X][X]).natDegree := by
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    decide
  have hmonic : P.Monic := (Polynomial.monic_X_pow 2).add_of_left <|
    Polynomial.degree_C_le.trans_lt (by
      rw [Polynomial.degree_X_pow]
      exact WithBot.coe_lt_coe.mpr (by decide))
  have hdegP : P.natDegree = 2 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hdegC, Polynomial.natDegree_X_pow]
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Polynomial.roots_eq_zero_iff_not_isRoot hmonic.ne_zero]
  intro g hg
  have hPeval : g ^ 2 + (Polynomial.X ^ 2 - 1) = 0 := by
    simpa [P, Polynomial.IsRoot] using hg
  have hg1 : g.eval 1 = 0 := by
    have h := congrArg (Polynomial.eval (1 : k)) hPeval
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero] at h
    exact sq_eq_zero_iff.mp (by linear_combination h)
  obtain ⟨h, hh⟩ : Polynomial.X - 1 ∣ g := by
    simpa only [map_one] using Polynomial.dvd_iff_isRoot.mpr hg1
  have hfact : (Polynomial.X - 1 : k[X]) * ((Polynomial.X - 1) * h ^ 2 + (Polynomial.X + 1)) =
      0 := by
    linear_combination hPeval - (g + (Polynomial.X - 1) * h) * hh
  have hrem : (Polynomial.X - 1) * h ^ 2 + (Polynomial.X + 1) = 0 :=
    (mul_eq_zero.mp hfact).resolve_left (Polynomial.X_sub_C_ne_zero 1)
  have h2zero : (2 : k) = 0 := by
    have h := congrArg (Polynomial.eval (1 : k)) hrem
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero,
      sub_self, zero_mul, zero_add] at h
    linear_combination h
  exact h2 h2zero

/-- Over a field of characteristic different from two, the coordinate ring
`k[X₀, X₁] / (X₀² + X₁² - 1)` of the circle is a Dedekind domain. -/
theorem isDedekindDomain_circleQuotient (h2 : (2 : k) ≠ 0) :
    IsDedekindDomain (CircleQuotient k) := by
  let f : MvPolynomial (Fin 2) k := MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1
  refine MvPolynomial.isDedekindDomain_quotient_span_singleton (irreducible_circlePoly h2) ?_
  rw [Ideal.eq_top_iff_one]
  have hp0 : MvPolynomial.pderiv 0 f = 2 * MvPolynomial.X 0 := by
    simp [f, MvPolynomial.pderiv_X]
  have hp1 : MvPolynomial.pderiv 1 f = 2 * MvPolynomial.X 1 := by
    simp [f, MvPolynomial.pderiv_X]
  have hmem2 : (2 : MvPolynomial (Fin 2) k) ∈
      Ideal.span {f, MvPolynomial.pderiv 0 f, MvPolynomial.pderiv 1 f} := by
    have hcomb : (2 : MvPolynomial (Fin 2) k) =
        MvPolynomial.X 0 * MvPolynomial.pderiv 0 f +
          MvPolynomial.X 1 * MvPolynomial.pderiv 1 f - 2 * f := by
      rw [hp0, hp1]
      dsimp only [f]
      ring
    rw [hcomb]
    refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  have h1 : MvPolynomial.C (2 : k)⁻¹ * (2 : MvPolynomial (Fin 2) k) = 1 := by
    rw [← map_ofNat (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k) 2, ← map_mul,
      inv_mul_cancel₀ h2, map_one]
  have hmem1 := Ideal.mul_mem_left _ (MvPolynomial.C (2 : k)⁻¹) hmem2
  rwa [h1] at hmem1

end Field

/-! ## Coordinate generators and universal property -/

namespace CircleQuotient

section CommRing

variable {k : Type*} [CommRing k]

/-- The defining ideal `(X₀² + X₁² - 1)` of `CircleQuotient k`. -/
private abbrev definingIdeal (k : Type*) [CommRing k] : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - (1 : MvPolynomial (Fin 2) k)}

/-- The first coordinate generator `x` of `CircleQuotient k`. -/
def x : CircleQuotient k :=
  Ideal.Quotient.mk (definingIdeal k) (MvPolynomial.X 0)

/-- The second coordinate generator `y` of `CircleQuotient k`. -/
def y : CircleQuotient k :=
  Ideal.Quotient.mk (definingIdeal k) (MvPolynomial.X 1)

/-- The circle relation `x² + y² = 1` in `CircleQuotient k`. -/
@[simp]
theorem x_sq_add_y_sq : (x : CircleQuotient k) ^ 2 + y ^ 2 = 1 := by
  have h : Ideal.Quotient.mk (definingIdeal k)
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  apply sub_eq_zero.mp
  simpa only [x, y, map_sub, map_add, map_pow, map_one] using h

/-- The universal property of `CircleQuotient k`: a `k`-algebra homomorphism
`CircleQuotient k →ₐ[k] B` is determined by two elements `a, b : B` satisfying `a² + b² = 1`. -/
def liftAlgHom {B : Type*} [CommRing B] [Algebra k B] (a b : B) (hab : a ^ 2 + b ^ 2 = 1) :
    CircleQuotient k →ₐ[k] B :=
  Ideal.Quotient.liftₐ (definingIdeal k) (MvPolynomial.aeval ![a, b]) fun p hp ↦ by
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp only [map_mul, map_sub, map_add, map_pow, map_one, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hab, sub_self, zero_mul]

/-- `liftAlgHom a b hab` sends `x` to `a`. -/
@[simp]
theorem liftAlgHom_x {B : Type*} [CommRing B] [Algebra k B] (a b : B) (hab : a ^ 2 + b ^ 2 = 1) :
    liftAlgHom a b hab (x : CircleQuotient k) = a :=
  MvPolynomial.aeval_X ![a, b] 0

/-- `liftAlgHom a b hab` sends `y` to `b`. -/
@[simp]
theorem liftAlgHom_y {B : Type*} [CommRing B] [Algebra k B] (a b : B) (hab : a ^ 2 + b ^ 2 = 1) :
    liftAlgHom a b hab (y : CircleQuotient k) = b :=
  MvPolynomial.aeval_X ![a, b] 1

/-- Two `k`-algebra homomorphisms out of `CircleQuotient k` coincide when they agree on `x` and
`y`. -/
@[ext]
theorem algHom_ext {B : Type*} [CommRing B] [Algebra k B] {f g : CircleQuotient k →ₐ[k] B}
    (hx : f x = g x) (hy : f y = g y) : f = g := by
  have hcomp : f.comp (Ideal.Quotient.mkₐ k (definingIdeal k)) =
      g.comp (Ideal.Quotient.mkₐ k (definingIdeal k)) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i
    · exact hx
    · exact hy
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact AlgHom.congr_fun hcomp p

end CommRing

/-- `CircleQuotient k` is a Dedekind domain whenever `k` is a field with `2 ≠ 0`. -/
instance instIsDedekindDomain {k : Type*} [Field k] [NeZero (2 : k)] :
    IsDedekindDomain (CircleQuotient k) :=
  isDedekindDomain_circleQuotient (NeZero.ne (2 : k))

/-! ### Stereographic charts covering `Spec(CircleQuotient k)` -/

section ChartHelpers

private theorem two_mul_algebraMap_invOf_two {k B : Type*} [CommRing k] [Invertible (2 : k)]
    [CommRing B] [Algebra k B] :
    (2 : B) * algebraMap k B (⅟(2 : k)) = 1 := by
  rw [← map_ofNat (algebraMap k B) 2, ← map_mul, mul_invOf_self, map_one]

private theorem two_mul_invSelf_mul_inv {k R : Type*} [CommRing k] [Invertible (2 : k)]
    [CommRing R] [Algebra k R] (r : R) :
    (2 : Localization.Away r) * IsLocalization.Away.invSelf r *
        (algebraMap k (Localization.Away r) (⅟(2 : k)) * algebraMap R (Localization.Away r) r) =
      1 := by
  calc
    (2 : Localization.Away r) * IsLocalization.Away.invSelf r *
        (algebraMap k (Localization.Away r) (⅟(2 : k)) * algebraMap R (Localization.Away r) r)
        = ((2 : Localization.Away r) * algebraMap k (Localization.Away r) (⅟(2 : k))) *
            (algebraMap R (Localization.Away r) r * IsLocalization.Away.invSelf r) := by ring
    _ = 1 := by
          rw [two_mul_algebraMap_invOf_two (k := k), IsLocalization.Away.mul_invSelf r, mul_one]

private theorem eq_of_two_mul_invSelf_mul_eq_one {k R : Type*} [CommRing k] [Invertible (2 : k)]
    [CommRing R] [Algebra k R] (r : R) {z : Localization.Away r}
    (hz : (2 : Localization.Away r) * IsLocalization.Away.invSelf r * z = 1) :
    z = algebraMap k (Localization.Away r) (⅟(2 : k)) * algebraMap R (Localization.Away r) r := by
  calc
    z = ((2 : Localization.Away r) * IsLocalization.Away.invSelf r *
          (algebraMap k (Localization.Away r) (⅟(2 : k)) *
            algebraMap R (Localization.Away r) r)) * z := by
            rw [two_mul_invSelf_mul_inv (k := k) r, one_mul]
    _ = algebraMap k (Localization.Away r) (⅟(2 : k)) * algebraMap R (Localization.Away r) r *
          ((2 : Localization.Away r) * IsLocalization.Away.invSelf r * z) := by ring
    _ = algebraMap k (Localization.Away r) (⅟(2 : k)) * algebraMap R (Localization.Away r) r := by
          rw [hz, mul_one]

private theorem liftAlgHom_algebraMap {A R S P : Type*} [CommSemiring A] [CommRing R]
    [CommRing S] [CommRing P] [Algebra A R] [Algebra A S] [Algebra A P] [Algebra R S]
    [IsScalarTower A R S] (x : R) [IsLocalization.Away x S] {f : R →ₐ[A] P} (hf : IsUnit (f x))
    (a : R) :
    IsLocalization.Away.liftAlgHom (S := S) x hf (algebraMap R S a) = f a := by
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

private theorem X_sq_add_one_mul_invSelf (k : Type*) [CommRing k] :
    (algebraMap k[X] (Localization.Away (Polynomial.X ^ 2 + 1 : k[X])) Polynomial.X ^ 2 + 1) *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : k[X]) =
      1 := by
  have hq : algebraMap k[X] (Localization.Away (Polynomial.X ^ 2 + 1 : k[X]))
      (Polynomial.X ^ 2 + 1) =
      algebraMap k[X] (Localization.Away (Polynomial.X ^ 2 + 1 : k[X])) Polynomial.X ^ 2 + 1 := by
    simp
  rw [← hq]
  exact IsLocalization.Away.mul_invSelf (Polynomial.X ^ 2 + 1 : k[X])

private theorem one_add_y_mul_invSelf_sq {k : Type*} [CommRing k] (ε : k) (hε : ε ^ 2 = 1) :
    (algebraMap (CircleQuotient k)
        (Localization.Away (1 + algebraMap k (CircleQuotient k) ε * x)) y *
      IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x)) ^ 2 + 1 =
      2 * IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x) := by
  set s : CircleQuotient k := 1 + algebraMap k (CircleQuotient k) ε * x
  let A_s := Localization.Away s
  let invS : A_s := IsLocalization.Away.invSelf s
  have hs_inv : algebraMap (CircleQuotient k) A_s s * invS = 1 := IsLocalization.Away.mul_invSelf s
  have hεA : (algebraMap k (CircleQuotient k) ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  have hs_sq_rel : (y : CircleQuotient k) ^ 2 + s ^ 2 = 2 * s := by
    dsimp only [s]
    linear_combination x_sq_add_y_sq (k := k) + x ^ 2 * hεA
  have hmap := congrArg (algebraMap (CircleQuotient k) A_s) hs_sq_rel
  simp only [map_add, map_pow, map_mul, map_ofNat] at hmap
  calc
    (algebraMap (CircleQuotient k) A_s y * invS) ^ 2 + 1
        = (algebraMap (CircleQuotient k) A_s y * invS) ^ 2 +
            (algebraMap (CircleQuotient k) A_s s * invS) ^ 2 := by rw [hs_inv, one_pow]
    _ = (algebraMap (CircleQuotient k) A_s y ^ 2 + algebraMap (CircleQuotient k) A_s s ^ 2) *
          invS ^ 2 := by ring
    _ = (2 * algebraMap (CircleQuotient k) A_s s) * invS ^ 2 := by rw [hmap]
    _ = 2 * (algebraMap (CircleQuotient k) A_s s * invS) * invS := by ring
    _ = 2 * invS := by rw [hs_inv, mul_one]

private theorem one_sub_y_mul_invSelf_sq {k : Type*} [CommRing k] (ε : k) (hε : ε ^ 2 = 1) :
    1 - (algebraMap (CircleQuotient k)
          (Localization.Away (1 + algebraMap k (CircleQuotient k) ε * x)) y *
        IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x)) ^ 2 =
      2 * algebraMap k _ ε * algebraMap (CircleQuotient k) _ x *
        IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x) := by
  set s : CircleQuotient k := 1 + algebraMap k (CircleQuotient k) ε * x
  let A_s := Localization.Away s
  let invS : A_s := IsLocalization.Away.invSelf s
  have hs_inv : algebraMap (CircleQuotient k) A_s s * invS = 1 := IsLocalization.Away.mul_invSelf s
  have hεA : (algebraMap k (CircleQuotient k) ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  have hεA' :
      algebraMap k A_s ε = algebraMap (CircleQuotient k) A_s (algebraMap k (CircleQuotient k) ε) :=
    IsScalarTower.algebraMap_apply k (CircleQuotient k) A_s ε
  have hnum : s ^ 2 - y ^ 2 = 2 * algebraMap k (CircleQuotient k) ε * x * s := by
    dsimp only [s]
    linear_combination -x_sq_add_y_sq (k := k) - x ^ 2 * hεA
  have hnumA := congrArg (algebraMap (CircleQuotient k) A_s) hnum
  simp only [map_sub, map_pow, map_mul, map_ofNat] at hnumA
  calc
    1 - (algebraMap (CircleQuotient k) A_s y * invS) ^ 2
        = (algebraMap (CircleQuotient k) A_s s * invS) ^ 2 -
            (algebraMap (CircleQuotient k) A_s y * invS) ^ 2 := by rw [hs_inv, one_pow]
    _ = (algebraMap (CircleQuotient k) A_s s ^ 2 - algebraMap (CircleQuotient k) A_s y ^ 2) *
          invS ^ 2 := by ring
    _ = (2 * algebraMap (CircleQuotient k) A_s (algebraMap k (CircleQuotient k) ε) *
          algebraMap (CircleQuotient k) A_s x * algebraMap (CircleQuotient k) A_s s) *
          invS ^ 2 := by rw [hnumA]
    _ = 2 * algebraMap k A_s ε * algebraMap (CircleQuotient k) A_s x *
          (algebraMap (CircleQuotient k) A_s s * invS) * invS := by rw [← hεA']; ring
    _ = 2 * algebraMap k A_s ε * algebraMap (CircleQuotient k) A_s x * invS := by
          rw [hs_inv, mul_one]

end ChartHelpers

section Charts

/-- The principal open subsets `D(1 + x)` and `D(1 - x)` cover `Spec(CircleQuotient k)` when
`2` is invertible in `k`. -/
theorem span_one_add_x_one_sub_x {k : Type*} [CommRing k] [Invertible (2 : k)] :
    Ideal.span ({1 + x, 1 - x} : Set (CircleQuotient k)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h2mem : (2 : CircleQuotient k) ∈ Ideal.span ({1 + x, 1 - x} : Set (CircleQuotient k)) := by
    have hadd : (1 + (x : CircleQuotient k)) + (1 - x) = 2 := by ring
    rw [← hadd]
    exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  have hmem1 := Ideal.mul_mem_right (algebraMap k (CircleQuotient k) (⅟(2 : k))) _ h2mem
  rwa [two_mul_algebraMap_invOf_two (k := k)] at hmem1

/-- Base `k`-algebra map `CircleQuotient k →ₐ[k] k[t, (t² + 1)⁻¹]` underlying the stereographic
chart. -/
private def stereographicChartBaseHom {k : Type*} [CommRing k] (ε : k) (hε : ε ^ 2 = 1) :
    CircleQuotient k →ₐ[k] Localization.Away (Polynomial.X ^ 2 + 1 : k[X]) := by
  set q : k[X] := Polynomial.X ^ 2 + 1
  let B_q := Localization.Away q
  let t : B_q := algebraMap k[X] B_q Polynomial.X
  let invQ : B_q := IsLocalization.Away.invSelf q
  have hq_inv : (t ^ 2 + 1) * invQ = 1 := X_sq_add_one_mul_invSelf k
  have hεB : (algebraMap k B_q ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  let xImg : B_q := algebraMap k B_q ε * (1 - t ^ 2) * invQ
  let yImg : B_q := 2 * t * invQ
  have hrel : xImg ^ 2 + yImg ^ 2 = 1 := by
    calc
      xImg ^ 2 + yImg ^ 2
          = (algebraMap k B_q ε) ^ 2 * (1 - t ^ 2) ^ 2 * invQ ^ 2 + 4 * t ^ 2 * invQ ^ 2 := by
              simp only [xImg, yImg]; ring
      _ = ((t ^ 2 + 1) * invQ) ^ 2 := by rw [hεB]; ring
      _ = 1 := by rw [hq_inv, one_pow]
  exact liftAlgHom xImg yImg hrel

private theorem stereographicChartBaseHom_x {k : Type*} [CommRing k] (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartBaseHom ε hε x =
      algebraMap k _ ε * (1 - algebraMap k[X] _ Polynomial.X ^ 2) *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : k[X]) := by
  simp [stereographicChartBaseHom]

private theorem stereographicChartBaseHom_y {k : Type*} [CommRing k] (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartBaseHom ε hε y =
      2 * algebraMap k[X] _ Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : k[X]) := by
  simp [stereographicChartBaseHom]

private theorem stereographicChartBaseHom_denom {k : Type*} [CommRing k]
    (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartBaseHom ε hε (1 + algebraMap k (CircleQuotient k) ε * x) =
      2 * IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : k[X]) := by
  set q : k[X] := Polynomial.X ^ 2 + 1
  let B_q := Localization.Away q
  let t : B_q := algebraMap k[X] B_q Polynomial.X
  let invQ : B_q := IsLocalization.Away.invSelf q
  have hq_inv : (t ^ 2 + 1) * invQ = 1 := X_sq_add_one_mul_invSelf k
  have hεB : (algebraMap k B_q ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  simp only [map_add, map_one, map_mul, AlgHom.commutes, stereographicChartBaseHom_x]
  calc
    1 + algebraMap k B_q ε * (algebraMap k B_q ε * (1 - t ^ 2) * invQ)
        = 1 + (algebraMap k B_q ε) ^ 2 * (1 - t ^ 2) * invQ := by ring
    _ = 1 + (1 - t ^ 2) * invQ := by rw [hεB, one_mul]
    _ = (t ^ 2 + 1) * invQ + (1 - t ^ 2) * invQ := by rw [hq_inv]
    _ = 2 * invQ := by ring

/-- Forward map of the stereographic chart
`CircleQuotient k[(1 + ε x)⁻¹] →ₐ[k] k[t, (t² + 1)⁻¹]`. -/
private def stereographicChartHom {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    Localization.Away (1 + algebraMap k (CircleQuotient k) ε * x) →ₐ[k]
      Localization.Away (Polynomial.X ^ 2 + 1 : k[X]) :=
  IsLocalization.Away.liftAlgHom (f := stereographicChartBaseHom ε hε)
    (1 + algebraMap k (CircleQuotient k) ε * x) (by
      rw [stereographicChartBaseHom_denom ε hε]
      exact isUnit_iff_exists_inv.mpr
        ⟨_, two_mul_invSelf_mul_inv (k := k) (Polynomial.X ^ 2 + 1 : k[X])⟩)

/-- Base `k`-algebra map `k[t] →ₐ[k] CircleQuotient k[(1 + ε x)⁻¹]` underlying the inverse
chart. -/
private def stereographicChartInvBaseHom {k : Type*} [CommRing k] (ε : k) :
    k[X] →ₐ[k] Localization.Away (1 + algebraMap k (CircleQuotient k) ε * x) :=
  Polynomial.aeval
    (algebraMap (CircleQuotient k) _ y *
      IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x))

private theorem stereographicChartInvBaseHom_X {k : Type*} [CommRing k] (ε : k) :
    stereographicChartInvBaseHom ε Polynomial.X =
      algebraMap (CircleQuotient k) _ y *
        IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x) := by
  simp [stereographicChartInvBaseHom]

private theorem stereographicChartInvBaseHom_denom {k : Type*} [CommRing k]
    (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartInvBaseHom ε (Polynomial.X ^ 2 + 1) =
      2 * IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x) := by
  simp only [map_add, map_pow, map_one, stereographicChartInvBaseHom_X]
  exact one_add_y_mul_invSelf_sq ε hε

/-- Inverse map of the stereographic chart
`k[t, (t² + 1)⁻¹] →ₐ[k] CircleQuotient k[(1 + ε x)⁻¹]`. -/
private def stereographicChartInv {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    Localization.Away (Polynomial.X ^ 2 + 1 : k[X]) →ₐ[k]
      Localization.Away (1 + algebraMap k (CircleQuotient k) ε * x) :=
  IsLocalization.Away.liftAlgHom (f := stereographicChartInvBaseHom ε)
    (Polynomial.X ^ 2 + 1 : k[X]) (by
      rw [stereographicChartInvBaseHom_denom ε hε]
      exact isUnit_iff_exists_inv.mpr
        ⟨_, two_mul_invSelf_mul_inv (k := k) (1 + algebraMap k (CircleQuotient k) ε * x)⟩)

private theorem stereographicChartHom_algebraMap {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) (a : CircleQuotient k) :
    stereographicChartHom ε hε (algebraMap (CircleQuotient k) _ a) =
      stereographicChartBaseHom ε hε a :=
  liftAlgHom_algebraMap _ _ a

private theorem stereographicChartInv_algebraMap {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) (p : k[X]) :
    stereographicChartInv ε hε (algebraMap k[X] _ p) =
      stereographicChartInvBaseHom ε p :=
  liftAlgHom_algebraMap _ _ p

private theorem stereographicChartHom_x {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartHom ε hε (algebraMap (CircleQuotient k) _ x) =
      algebraMap k _ ε * (1 - algebraMap k[X] _ Polynomial.X ^ 2) *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : k[X]) := by
  rw [stereographicChartHom_algebraMap, stereographicChartBaseHom_x]

private theorem stereographicChartHom_y {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartHom ε hε (algebraMap (CircleQuotient k) _ y) =
      2 * algebraMap k[X] _ Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : k[X]) := by
  rw [stereographicChartHom_algebraMap, stereographicChartBaseHom_y]

private theorem stereographicChartHom_denom {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartHom ε hε
        (algebraMap (CircleQuotient k) _ (1 + algebraMap k (CircleQuotient k) ε * x)) =
      2 * IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : k[X]) := by
  rw [stereographicChartHom_algebraMap, stereographicChartBaseHom_denom]

private theorem stereographicChartInv_X {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartInv ε hε (algebraMap k[X] _ Polynomial.X) =
      algebraMap (CircleQuotient k) _ y *
        IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x) := by
  rw [stereographicChartInv_algebraMap, stereographicChartInvBaseHom_X]

private theorem stereographicChartInv_denom {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartInv ε hε (algebraMap k[X] _ (Polynomial.X ^ 2 + 1 : k[X])) =
      2 * IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x) := by
  rw [stereographicChartInv_algebraMap, stereographicChartInvBaseHom_denom ε hε]

private theorem stereographicChartHom_comp_inv {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    (stereographicChartHom ε hε).comp (stereographicChartInv ε hε) = AlgHom.id k _ := by
  set s : CircleQuotient k := 1 + algebraMap k (CircleQuotient k) ε * x
  set q : k[X] := Polynomial.X ^ 2 + 1
  let B_q := Localization.Away q
  let t : B_q := algebraMap k[X] B_q Polynomial.X
  let invQ : B_q := IsLocalization.Away.invSelf q
  have hq_inv : (t ^ 2 + 1) * invQ = 1 := X_sq_add_one_mul_invSelf k
  have h2B : (2 : B_q) * algebraMap k B_q (⅟(2 : k)) = 1 := two_mul_algebraMap_invOf_two (k := k)
  have hΦ_invS :
      stereographicChartHom ε hε (IsLocalization.Away.invSelf s) =
        algebraMap k B_q (⅟(2 : k)) * (t ^ 2 + 1) := by
    have hmul : 2 * invQ * stereographicChartHom ε hε (IsLocalization.Away.invSelf s) = 1 := by
      rw [← stereographicChartHom_denom ε hε, ← map_mul,
        IsLocalization.Away.mul_invSelf, map_one]
    simpa [q, B_q, t] using eq_of_two_mul_invSelf_mul_eq_one q hmul
  apply Localization.algHom_ext (Submonoid.powers q)
  apply Polynomial.algHom_ext
  dsimp only [q]
  simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.algHom, IsScalarTower.toAlgHom_apply,
    stereographicChartInv_X, map_mul, stereographicChartHom_y]
  rw [hΦ_invS]
  calc
    2 * t * invQ * (algebraMap k B_q (⅟(2 : k)) * (t ^ 2 + 1))
        = (2 * algebraMap k B_q (⅟(2 : k))) * ((t ^ 2 + 1) * invQ) * t := by ring
    _ = t := by rw [h2B, hq_inv, mul_one, one_mul]

private theorem stereographicChartInv_comp_hom {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    (stereographicChartInv ε hε).comp (stereographicChartHom ε hε) = AlgHom.id k _ := by
  set s : CircleQuotient k := 1 + algebraMap k (CircleQuotient k) ε * x
  set q : k[X] := Polynomial.X ^ 2 + 1
  let A_s := Localization.Away s
  let invS : A_s := IsLocalization.Away.invSelf s
  have hs_inv : algebraMap (CircleQuotient k) A_s s * invS = 1 := IsLocalization.Away.mul_invSelf s
  have h2A : (2 : A_s) * algebraMap k A_s (⅟(2 : k)) = 1 := two_mul_algebraMap_invOf_two (k := k)
  have hε_sq : (algebraMap k A_s ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  have hΨ_invQ :
      stereographicChartInv ε hε (IsLocalization.Away.invSelf q) =
        algebraMap k A_s (⅟(2 : k)) * algebraMap (CircleQuotient k) A_s s := by
    have hmul : 2 * invS * stereographicChartInv ε hε (IsLocalization.Away.invSelf q) = 1 := by
      rw [← stereographicChartInv_denom ε hε, ← map_mul,
        IsLocalization.Away.mul_invSelf, map_one]
    exact eq_of_two_mul_invSelf_mul_eq_one s hmul
  apply Localization.algHom_ext (Submonoid.powers s)
  refine CircleQuotient.algHom_ext ?_ ?_
  · dsimp only [s]
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.algHom, IsScalarTower.toAlgHom_apply,
      stereographicChartHom_x, map_mul, map_sub, map_one, map_pow, AlgHom.commutes,
      stereographicChartInv_X, one_sub_y_mul_invSelf_sq ε hε]
    rw [hΨ_invQ]
    calc
      algebraMap k A_s ε *
          (2 * algebraMap k A_s ε * algebraMap (CircleQuotient k) A_s x * invS) *
          (algebraMap k A_s (⅟(2 : k)) * algebraMap (CircleQuotient k) A_s s)
          = (algebraMap k A_s ε) ^ 2 * (2 * algebraMap k A_s (⅟(2 : k))) *
              (algebraMap (CircleQuotient k) A_s s * invS) *
              algebraMap (CircleQuotient k) A_s x := by ring
      _ = algebraMap (CircleQuotient k) A_s x := by rw [hε_sq, h2A, hs_inv]; ring
  · dsimp only [s]
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.algHom, IsScalarTower.toAlgHom_apply,
      stereographicChartHom_y, map_mul, map_ofNat, stereographicChartInv_X]
    rw [hΨ_invQ]
    calc
      2 * (algebraMap (CircleQuotient k) A_s y * invS) *
          (algebraMap k A_s (⅟(2 : k)) * algebraMap (CircleQuotient k) A_s s)
          = (2 * algebraMap k A_s (⅟(2 : k))) * (algebraMap (CircleQuotient k) A_s s * invS) *
              algebraMap (CircleQuotient k) A_s y := by ring
      _ = algebraMap (CircleQuotient k) A_s y := by rw [h2A, hs_inv]; ring

/-- The stereographic chart isomorphism
`CircleQuotient k[(1 + ε x)⁻¹] ≃ₐ[k] k[t, (t² + 1)⁻¹]` for `ε ∈ {±1}` (`ε² = 1`) and
`Invertible (2 : k)`. It sends `x` to `ε (1 - t²) / (t² + 1)` and `y` to `2 t / (t² + 1)`, with
inverse sending `t` to `y / (1 + ε x)`. -/
def stereographicChartEquiv {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    Localization.Away (1 + algebraMap k (CircleQuotient k) ε * x) ≃ₐ[k]
      Localization.Away (Polynomial.X ^ 2 + 1 : k[X]) :=
  AlgEquiv.ofAlgHom (stereographicChartHom ε hε) (stereographicChartInv ε hε)
    (stereographicChartHom_comp_inv ε hε) (stereographicChartInv_comp_hom ε hε)

/-- The stereographic chart sends `x` to `ε (1 - t²) / (t² + 1)`. -/
@[simp]
theorem stereographicChartEquiv_x {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartEquiv ε hε (algebraMap (CircleQuotient k) _ x) =
      algebraMap k _ ε * (1 - algebraMap k[X] _ Polynomial.X ^ 2) *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : k[X]) :=
  stereographicChartHom_x ε hε

/-- The stereographic chart sends `y` to `2 t / (t² + 1)`. -/
@[simp]
theorem stereographicChartEquiv_y {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    stereographicChartEquiv ε hε (algebraMap (CircleQuotient k) _ y) =
      2 * algebraMap k[X] _ Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : k[X]) :=
  stereographicChartHom_y ε hε

/-- The inverse stereographic chart sends `t` to `y / (1 + ε x)`. -/
@[simp]
theorem stereographicChartEquiv_symm_X {k : Type*} [CommRing k] [Invertible (2 : k)]
    (ε : k) (hε : ε ^ 2 = 1) :
    (stereographicChartEquiv ε hε).symm (algebraMap k[X] _ Polynomial.X) =
      algebraMap (CircleQuotient k) _ y *
        IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x) :=
  stereographicChartInv_X ε hε

private theorem one_add_mul_x_mul_one_sub_mul_x {k : Type*} [CommRing k]
    (ε : k) (hε : ε ^ 2 = 1) :
    (1 + algebraMap k (CircleQuotient k) ε * x) *
        (1 - algebraMap k (CircleQuotient k) ε * x) =
      y ^ 2 := by
  have hεA : (algebraMap k (CircleQuotient k) ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  linear_combination -x_sq_add_y_sq (k := k) - x ^ 2 * hεA

/-- In `CircleQuotient k[y⁻¹]`, `1 + ε x` is a unit whenever `ε² = 1`. -/
theorem isUnit_one_add_mul_x_away_y {k : Type*} [CommRing k] (ε : k) (hε : ε ^ 2 = 1) :
    IsUnit
      (algebraMap (CircleQuotient k) (Localization.Away (y : CircleQuotient k))
        (1 + algebraMap k (CircleQuotient k) ε * x)) := by
  have hyUnit : IsUnit
      (algebraMap (CircleQuotient k) (Localization.Away (y : CircleQuotient k)) (y ^ 2)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit y).pow 2
  exact isUnit_of_dvd_unit
    (map_dvd _ ⟨1 - algebraMap k (CircleQuotient k) ε * x,
      (one_add_mul_x_mul_one_sub_mul_x ε hε).symm⟩)
    hyUnit

/-- The canonical `k`-algebra homomorphism from the stereographic chart
`CircleQuotient k[(1 + ε x)⁻¹]` into the overlap `CircleQuotient k[y⁻¹]`, for `ε² = 1`. -/
def chartToOverlap {k : Type*} [CommRing k] (ε : k) (hε : ε ^ 2 = 1) :
    Localization.Away (1 + algebraMap k (CircleQuotient k) ε * x) →ₐ[k]
      Localization.Away (y : CircleQuotient k) :=
  IsLocalization.Away.liftAlgHom
    (f := IsScalarTower.toAlgHom k (CircleQuotient k) (Localization.Away (y : CircleQuotient k)))
    (1 + algebraMap k (CircleQuotient k) ε * x) (by
      rw [IsScalarTower.toAlgHom_apply]
      exact isUnit_one_add_mul_x_away_y ε hε)

/-- `chartToOverlap` commutes with the localization map from `CircleQuotient k`. -/
@[simp]
theorem chartToOverlap_algebraMap {k : Type*} [CommRing k] (ε : k) (hε : ε ^ 2 = 1)
    (a : CircleQuotient k) :
    chartToOverlap ε hε (algebraMap (CircleQuotient k) _ a) =
      algebraMap (CircleQuotient k) _ a := by
  rw [chartToOverlap, liftAlgHom_algebraMap, IsScalarTower.toAlgHom_apply]

private theorem algebraMap_mul_chartToOverlap_invSelf {k : Type*} [CommRing k]
    (ε : k) (hε : ε ^ 2 = 1) :
    algebraMap (CircleQuotient k) (Localization.Away (y : CircleQuotient k))
        (1 + algebraMap k (CircleQuotient k) ε * x) *
      chartToOverlap ε hε
        (IsLocalization.Away.invSelf (1 + algebraMap k (CircleQuotient k) ε * x)) = 1 := by
  rw [← chartToOverlap_algebraMap ε hε, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- **Overlap compatibility of the two stereographic charts.** On `CircleQuotient k[y⁻¹]`, the
two stereographic parameters `t₊` (from `D(1 + x)`) and `t₋` (from `D(1 - x)`) are mutually
inverse: `t₊ · t₋ = 1`. -/
theorem stereographic_overlap {k : Type*} [CommRing k] [Invertible (2 : k)] :
    chartToOverlap (1 : k) (one_pow 2)
        ((stereographicChartEquiv (1 : k) (one_pow 2)).symm (algebraMap k[X] _ Polynomial.X)) *
      chartToOverlap (-1 : k) neg_one_sq
        ((stereographicChartEquiv (-1 : k) neg_one_sq).symm
          (algebraMap k[X] _ Polynomial.X)) = 1 := by
  rw [stereographicChartEquiv_symm_X, stereographicChartEquiv_symm_X]
  set s₁ : CircleQuotient k := 1 + algebraMap k (CircleQuotient k) 1 * x
  set s₂ : CircleQuotient k := 1 + algebraMap k (CircleQuotient k) (-1) * x
  set ι₁ := chartToOverlap (1 : k) (one_pow 2)
  set ι₂ := chartToOverlap (-1 : k) neg_one_sq
  have hs₁₂ :
      algebraMap (CircleQuotient k) (Localization.Away (y : CircleQuotient k)) (y ^ 2) =
        algebraMap (CircleQuotient k) _ s₁ * algebraMap (CircleQuotient k) _ s₂ := by
    rw [← map_mul, ← one_add_mul_x_mul_one_sub_mul_x (1 : k) (one_pow 2)]
    simp [s₁, s₂, sub_eq_add_neg]
  calc
    ι₁ (algebraMap (CircleQuotient k) _ y * IsLocalization.Away.invSelf s₁) *
        ι₂ (algebraMap (CircleQuotient k) _ y * IsLocalization.Away.invSelf s₂)
        = (algebraMap (CircleQuotient k) (Localization.Away (y : CircleQuotient k)) y *
            ι₁ (IsLocalization.Away.invSelf s₁)) *
          (algebraMap (CircleQuotient k) (Localization.Away (y : CircleQuotient k)) y *
            ι₂ (IsLocalization.Away.invSelf s₂)) := by
              simp only [ι₁, ι₂, map_mul, chartToOverlap_algebraMap]
    _ = algebraMap (CircleQuotient k) (Localization.Away (y : CircleQuotient k)) (y ^ 2) *
          (ι₁ (IsLocalization.Away.invSelf s₁) * ι₂ (IsLocalization.Away.invSelf s₂)) := by
            rw [map_pow]; ring
    _ = (algebraMap (CircleQuotient k) (Localization.Away (y : CircleQuotient k)) s₁ *
            ι₁ (IsLocalization.Away.invSelf s₁)) *
          (algebraMap (CircleQuotient k) (Localization.Away (y : CircleQuotient k)) s₂ *
            ι₂ (IsLocalization.Away.invSelf s₂)) := by
            rw [hs₁₂]; ring
    _ = 1 := by
          rw [algebraMap_mul_chartToOverlap_invSelf, algebraMap_mul_chartToOverlap_invSelf,
            mul_one]

end Charts

end CircleQuotient

/-! ## The coordinate ring of the real algebraic circle -/

/-- The coordinate ring of the real algebraic circle: `ℝ[x, y] / (x² + y² - 1)`. -/
abbrev CircleRing := CircleQuotient ℝ

end

end TauCeti
