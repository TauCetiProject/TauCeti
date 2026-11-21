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
# The coordinate ring of the real algebraic circle

Let `CircleRing = ℝ[x, y] / (x² + y² - 1)` be the coordinate ring of the real algebraic circle.
Over any field `k` with `2 ≠ 0`, the defining polynomial `X₀² + X₁² - 1` is irreducible and the
Jacobian ideal `(X₀² + X₁² - 1, 2 X₀, 2 X₁)` is the unit ideal, so `k[x, y] / (x² + y² - 1)` is
a Dedekind domain by the smooth affine plane-curve criterion
`MvPolynomial.isDedekindDomain_quotient_span_singleton`. In particular, `CircleRing` is a
Dedekind domain.

Geometrically, the two principal open charts `D(1 + x)` and `D(1 - x)` cover `Spec(CircleRing)`
since `(1 + x) + (1 - x) = 2` is a unit. On each chart `s = 1 + ε x` (`ε ∈ {±1}`), stereographic
projection `t = y / s` with inverse `x = ε (1 - t²) / (1 + t²)`, `y = 2 t / (1 + t²)` identifies
the localization `CircleRing[s⁻¹]` with `ℝ[t, (1 + t²)⁻¹]`, with overlap transition
`t₊ · t₋ = 1` on `D(y)`.

## Main definitions

* `TauCeti.CircleRing`: the coordinate ring `ℝ[x, y] / (x² + y² - 1)` of the real algebraic
  circle.
* `TauCeti.CircleRing.x`, `TauCeti.CircleRing.y`: the coordinate generators of `CircleRing`.
* `TauCeti.CircleRing.liftAlgHom`: the universal property of `CircleRing` as an `ℝ`-algebra.
* `TauCeti.CircleRing.stereographicChartEquiv`: the `ℝ`-algebra isomorphism
  `Localization.Away (1 + ε x) ≃ₐ[ℝ] Localization.Away (X² + 1)` for `ε² = 1`.
* `TauCeti.CircleRing.chartToOverlap`: the canonical map from a stereographic chart to
  `Localization.Away y`.

## Main results

* `TauCeti.irreducible_circlePoly`, `TauCeti.isDedekindDomain_circleQuotient`: over any field
  of characteristic different from two, `X₀² + X₁² - 1` is irreducible and its quotient is a
  Dedekind domain.
* `TauCeti.CircleRing.instIsDedekindDomain`: `CircleRing` is a Dedekind domain.
* `TauCeti.CircleRing.span_one_add_x_one_sub_x`: `1 + x` and `1 - x` generate the unit ideal.
* `TauCeti.CircleRing.stereographic_overlap`: on `Localization.Away y`, the two stereographic
  parameters satisfy `t₊ · t₋ = 1`.
-/

public section

open Polynomial

namespace TauCeti

noncomputable section

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
    IsDedekindDomain (MvPolynomial (Fin 2) k ⧸
      Ideal.span {MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - (1 : MvPolynomial (Fin 2) k)}) := by
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

/-! ## The coordinate ring of the real algebraic circle -/

/-- The coordinate ring of the real algebraic circle: `ℝ[x, y] / (x² + y² - 1)`. -/
abbrev CircleRing :=
  MvPolynomial (Fin 2) ℝ ⧸ Ideal.span
    {MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - (1 : MvPolynomial (Fin 2) ℝ)}

namespace CircleRing

/-- The defining ideal `(X₀² + X₁² - 1)` of `CircleRing`. -/
private abbrev definingIdeal : Ideal (MvPolynomial (Fin 2) ℝ) :=
  Ideal.span {MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - (1 : MvPolynomial (Fin 2) ℝ)}

/-- The first coordinate generator `x` of `CircleRing`. -/
def x : CircleRing :=
  Ideal.Quotient.mk definingIdeal (MvPolynomial.X 0)

/-- The second coordinate generator `y` of `CircleRing`. -/
def y : CircleRing :=
  Ideal.Quotient.mk definingIdeal (MvPolynomial.X 1)

/-- The circle relation `x² + y² = 1` in `CircleRing`. -/
@[simp]
theorem x_sq_add_y_sq : x ^ 2 + y ^ 2 = 1 := by
  have h : Ideal.Quotient.mk definingIdeal
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  apply sub_eq_zero.mp
  simpa only [x, y, map_sub, map_add, map_pow, map_one] using h

/-- `CircleRing` is a Dedekind domain. -/
instance instIsDedekindDomain : IsDedekindDomain CircleRing :=
  isDedekindDomain_circleQuotient two_ne_zero

/-- The universal property of `CircleRing`: an `ℝ`-algebra homomorphism `CircleRing →ₐ[ℝ] B`
is determined by two elements `a, b : B` satisfying `a² + b² = 1`. -/
def liftAlgHom {B : Type*} [CommRing B] [Algebra ℝ B] (a b : B) (hab : a ^ 2 + b ^ 2 = 1) :
    CircleRing →ₐ[ℝ] B :=
  Ideal.Quotient.liftₐ definingIdeal (MvPolynomial.aeval ![a, b]) fun p hp ↦ by
    rw [Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp only [map_mul, map_sub, map_add, map_pow, map_one, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hab, sub_self, zero_mul]

/-- `liftAlgHom a b hab` sends `x` to `a`. -/
@[simp]
theorem liftAlgHom_x {B : Type*} [CommRing B] [Algebra ℝ B] (a b : B) (hab : a ^ 2 + b ^ 2 = 1) :
    liftAlgHom a b hab x = a :=
  MvPolynomial.aeval_X ![a, b] 0

/-- `liftAlgHom a b hab` sends `y` to `b`. -/
@[simp]
theorem liftAlgHom_y {B : Type*} [CommRing B] [Algebra ℝ B] (a b : B) (hab : a ^ 2 + b ^ 2 = 1) :
    liftAlgHom a b hab y = b :=
  MvPolynomial.aeval_X ![a, b] 1

/-- Two `ℝ`-algebra homomorphisms out of `CircleRing` coincide when they agree on `x` and `y`. -/
@[ext]
theorem algHom_ext {B : Type*} [CommRing B] [Algebra ℝ B] {f g : CircleRing →ₐ[ℝ] B}
    (hx : f x = g x) (hy : f y = g y) : f = g := by
  have hcomp : f.comp (Ideal.Quotient.mkₐ ℝ definingIdeal) =
      g.comp (Ideal.Quotient.mkₐ ℝ definingIdeal) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    fin_cases i
    · exact hx
    · exact hy
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact AlgHom.congr_fun hcomp p

/-! ### Stereographic charts covering `Spec(CircleRing)` -/

/-- The principal open subsets `D(1 + x)` and `D(1 - x)` cover `Spec(CircleRing)`. -/
theorem span_one_add_x_one_sub_x : Ideal.span ({1 + x, 1 - x} : Set CircleRing) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h2 : (2 : CircleRing) ∈ Ideal.span ({1 + x, 1 - x} : Set CircleRing) := by
    have hadd : (1 + x) + (1 - x) = (2 : CircleRing) := by ring
    rw [← hadd]
    exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  have h1 : algebraMap ℝ CircleRing (2⁻¹) * (2 : CircleRing) = 1 := by
    rw [← map_ofNat (algebraMap ℝ CircleRing) 2, ← map_mul,
      inv_mul_cancel₀ two_ne_zero, map_one]
  have hmem1 := Ideal.mul_mem_left _ (algebraMap ℝ CircleRing (2⁻¹)) h2
  rwa [h1] at hmem1

private theorem two_mul_invSelf_mul_inv {R : Type*} [CommRing R] [Algebra ℝ R] (r : R) :
    (2 : Localization.Away r) * IsLocalization.Away.invSelf r *
        (algebraMap ℝ (Localization.Away r) (2⁻¹) * algebraMap R (Localization.Away r) r) =
      1 := by
  have h2 : (2 : Localization.Away r) * algebraMap ℝ (Localization.Away r) (2⁻¹) = 1 := by
    rw [← map_ofNat (algebraMap ℝ _) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  calc
    (2 : Localization.Away r) * IsLocalization.Away.invSelf r *
        (algebraMap ℝ (Localization.Away r) (2⁻¹) * algebraMap R (Localization.Away r) r)
        = ((2 : Localization.Away r) * algebraMap ℝ (Localization.Away r) (2⁻¹)) *
            (algebraMap R (Localization.Away r) r * IsLocalization.Away.invSelf r) := by ring
    _ = 1 := by rw [h2, IsLocalization.Away.mul_invSelf r, mul_one]

private theorem eq_of_two_mul_invSelf_mul_eq_one {R : Type*} [CommRing R] [Algebra ℝ R]
    (r : R) {z : Localization.Away r}
    (hz : (2 : Localization.Away r) * IsLocalization.Away.invSelf r * z = 1) :
    z = algebraMap ℝ (Localization.Away r) (2⁻¹) * algebraMap R (Localization.Away r) r := by
  calc
    z = (2 * IsLocalization.Away.invSelf r *
          (algebraMap ℝ (Localization.Away r) (2⁻¹) *
            algebraMap R (Localization.Away r) r)) * z := by
            rw [two_mul_invSelf_mul_inv r, one_mul]
    _ = algebraMap ℝ (Localization.Away r) (2⁻¹) * algebraMap R (Localization.Away r) r *
          (2 * IsLocalization.Away.invSelf r * z) := by ring
    _ = algebraMap ℝ (Localization.Away r) (2⁻¹) * algebraMap R (Localization.Away r) r := by
          rw [hz, mul_one]

/-- Base `ℝ`-algebra map `CircleRing →ₐ[ℝ] ℝ[t, (t² + 1)⁻¹]` underlying the stereographic chart. -/
private def stereographicChartBaseHom (ε : ℝ) (hε : ε ^ 2 = 1) :
    CircleRing →ₐ[ℝ] Localization.Away (Polynomial.X ^ 2 + 1 : ℝ[X]) := by
  set q : ℝ[X] := Polynomial.X ^ 2 + 1
  let B_q := Localization.Away q
  let t : B_q := algebraMap ℝ[X] B_q Polynomial.X
  let invQ : B_q := IsLocalization.Away.invSelf q
  have hq_inv : (t ^ 2 + 1) * invQ = 1 := by
    have hq_eq : algebraMap ℝ[X] B_q q = t ^ 2 + 1 := by simp [q, t]
    rw [← hq_eq]
    exact IsLocalization.Away.mul_invSelf q
  have hεB : (algebraMap ℝ B_q ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  let xImg : B_q := algebraMap ℝ B_q ε * (1 - t ^ 2) * invQ
  let yImg : B_q := 2 * t * invQ
  have hrel : xImg ^ 2 + yImg ^ 2 = 1 := by
    calc
      xImg ^ 2 + yImg ^ 2
          = (algebraMap ℝ B_q ε) ^ 2 * (1 - t ^ 2) ^ 2 * invQ ^ 2 + 4 * t ^ 2 * invQ ^ 2 := by
              simp only [xImg, yImg]; ring
      _ = ((t ^ 2 + 1) * invQ) ^ 2 := by rw [hεB]; ring
      _ = 1 := by rw [hq_inv, one_pow]
  exact liftAlgHom xImg yImg hrel

private theorem stereographicChartBaseHom_x (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartBaseHom ε hε x =
      algebraMap ℝ _ ε * (1 - algebraMap ℝ[X] _ Polynomial.X ^ 2) *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : ℝ[X]) := by
  simp [stereographicChartBaseHom]

private theorem stereographicChartBaseHom_y (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartBaseHom ε hε y =
      2 * algebraMap ℝ[X] _ Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : ℝ[X]) := by
  simp [stereographicChartBaseHom]

private theorem stereographicChartBaseHom_denom (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartBaseHom ε hε (1 + algebraMap ℝ CircleRing ε * x) =
      2 * IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : ℝ[X]) := by
  set q : ℝ[X] := Polynomial.X ^ 2 + 1
  let B_q := Localization.Away q
  let t : B_q := algebraMap ℝ[X] B_q Polynomial.X
  let invQ : B_q := IsLocalization.Away.invSelf q
  have hq_inv : (t ^ 2 + 1) * invQ = 1 := by
    have hq_eq : algebraMap ℝ[X] B_q q = t ^ 2 + 1 := by simp [q, t]
    rw [← hq_eq]
    exact IsLocalization.Away.mul_invSelf q
  have hεB : (algebraMap ℝ B_q ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  simp only [map_add, map_one, map_mul, AlgHom.commutes, stereographicChartBaseHom_x]
  calc
    1 + algebraMap ℝ B_q ε * (algebraMap ℝ B_q ε * (1 - t ^ 2) * invQ)
        = 1 + (algebraMap ℝ B_q ε) ^ 2 * (1 - t ^ 2) * invQ := by ring
    _ = 1 + (1 - t ^ 2) * invQ := by rw [hεB, one_mul]
    _ = (t ^ 2 + 1) * invQ + (1 - t ^ 2) * invQ := by rw [hq_inv]
    _ = 2 * invQ := by ring

/-- Forward map of the stereographic chart `CircleRing[(1 + ε x)⁻¹] →ₐ[ℝ] ℝ[t, (t² + 1)⁻¹]`. -/
private def stereographicChartHom (ε : ℝ) (hε : ε ^ 2 = 1) :
    Localization.Away (1 + algebraMap ℝ CircleRing ε * x) →ₐ[ℝ]
      Localization.Away (Polynomial.X ^ 2 + 1 : ℝ[X]) :=
  IsLocalization.Away.liftAlgHom (f := stereographicChartBaseHom ε hε)
    (1 + algebraMap ℝ CircleRing ε * x) (by
      rw [stereographicChartBaseHom_denom ε hε]
      exact isUnit_iff_exists_inv.mpr
        ⟨_, two_mul_invSelf_mul_inv (Polynomial.X ^ 2 + 1 : ℝ[X])⟩)

/-- Base `ℝ`-algebra map `ℝ[t] →ₐ[ℝ] CircleRing[(1 + ε x)⁻¹]` underlying the inverse chart. -/
private def stereographicChartInvBaseHom (ε : ℝ) :
    ℝ[X] →ₐ[ℝ] Localization.Away (1 + algebraMap ℝ CircleRing ε * x) :=
  Polynomial.aeval
    (algebraMap CircleRing _ y * IsLocalization.Away.invSelf (1 + algebraMap ℝ CircleRing ε * x))

private theorem stereographicChartInvBaseHom_X (ε : ℝ) :
    stereographicChartInvBaseHom ε Polynomial.X =
      algebraMap CircleRing _ y *
        IsLocalization.Away.invSelf (1 + algebraMap ℝ CircleRing ε * x) := by
  simp [stereographicChartInvBaseHom]

private theorem stereographicChartInvBaseHom_denom (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartInvBaseHom ε (Polynomial.X ^ 2 + 1) =
      2 * IsLocalization.Away.invSelf (1 + algebraMap ℝ CircleRing ε * x) := by
  set s : CircleRing := 1 + algebraMap ℝ CircleRing ε * x
  let A_s := Localization.Away s
  let invS : A_s := IsLocalization.Away.invSelf s
  have hs_inv : algebraMap CircleRing A_s s * invS = 1 := IsLocalization.Away.mul_invSelf s
  have hεA : (algebraMap ℝ CircleRing ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  have hs_sq_rel : y ^ 2 + s ^ 2 = 2 * s := by
    dsimp only [s]
    linear_combination x_sq_add_y_sq + x ^ 2 * hεA
  have hmap := congrArg (algebraMap CircleRing A_s) hs_sq_rel
  simp only [map_add, map_pow, map_mul, map_ofNat] at hmap
  simp only [map_add, map_pow, map_one, stereographicChartInvBaseHom_X]
  calc
    (algebraMap CircleRing A_s y * invS) ^ 2 + 1
        = (algebraMap CircleRing A_s y ^ 2 + algebraMap CircleRing A_s s ^ 2) * invS ^ 2 := by
            linear_combination -(1 + algebraMap CircleRing A_s s * invS) * hs_inv
    _ = (2 * algebraMap CircleRing A_s s) * invS ^ 2 := by rw [hmap]
    _ = 2 * (algebraMap CircleRing A_s s * invS) * invS := by ring
    _ = 2 * invS := by rw [hs_inv, mul_one]

/-- Inverse map of the stereographic chart `ℝ[t, (t² + 1)⁻¹] →ₐ[ℝ] CircleRing[(1 + ε x)⁻¹]`. -/
private def stereographicChartInv (ε : ℝ) (hε : ε ^ 2 = 1) :
    Localization.Away (Polynomial.X ^ 2 + 1 : ℝ[X]) →ₐ[ℝ]
      Localization.Away (1 + algebraMap ℝ CircleRing ε * x) :=
  IsLocalization.Away.liftAlgHom (f := stereographicChartInvBaseHom ε)
    (Polynomial.X ^ 2 + 1 : ℝ[X]) (by
      rw [stereographicChartInvBaseHom_denom ε hε]
      exact isUnit_iff_exists_inv.mpr
        ⟨_, two_mul_invSelf_mul_inv (1 + algebraMap ℝ CircleRing ε * x)⟩)

private theorem stereographicChartHom_x (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartHom ε hε (algebraMap CircleRing _ x) =
      algebraMap ℝ _ ε * (1 - algebraMap ℝ[X] _ Polynomial.X ^ 2) *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : ℝ[X]) := by
  simpa [stereographicChartHom] using stereographicChartBaseHom_x ε hε

private theorem stereographicChartHom_y (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartHom ε hε (algebraMap CircleRing _ y) =
      2 * algebraMap ℝ[X] _ Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : ℝ[X]) := by
  simpa [stereographicChartHom] using stereographicChartBaseHom_y ε hε

private theorem stereographicChartHom_denom (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartHom ε hε (algebraMap CircleRing _ (1 + algebraMap ℝ CircleRing ε * x)) =
      2 * IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : ℝ[X]) := by
  simpa [stereographicChartHom] using stereographicChartBaseHom_denom ε hε

private theorem stereographicChartInv_X (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartInv ε hε (algebraMap ℝ[X] _ Polynomial.X) =
      algebraMap CircleRing _ y *
        IsLocalization.Away.invSelf (1 + algebraMap ℝ CircleRing ε * x) := by
  simpa [stereographicChartInv] using stereographicChartInvBaseHom_X ε

private theorem stereographicChartInv_denom (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartInv ε hε (algebraMap ℝ[X] _ (Polynomial.X ^ 2 + 1 : ℝ[X])) =
      2 * IsLocalization.Away.invSelf (1 + algebraMap ℝ CircleRing ε * x) := by
  simpa [stereographicChartInv] using stereographicChartInvBaseHom_denom ε hε

private theorem stereographicChartHom_comp_inv (ε : ℝ) (hε : ε ^ 2 = 1) :
    (stereographicChartHom ε hε).comp (stereographicChartInv ε hε) = AlgHom.id ℝ _ := by
  set s : CircleRing := 1 + algebraMap ℝ CircleRing ε * x
  set q : ℝ[X] := Polynomial.X ^ 2 + 1
  let B_q := Localization.Away q
  let t : B_q := algebraMap ℝ[X] B_q Polynomial.X
  let invQ : B_q := IsLocalization.Away.invSelf q
  have hq_inv : (t ^ 2 + 1) * invQ = 1 := by
    have hq_eq : algebraMap ℝ[X] B_q q = t ^ 2 + 1 := by simp [q, t]
    rw [← hq_eq]
    exact IsLocalization.Away.mul_invSelf q
  have h2B : (2 : B_q) * algebraMap ℝ B_q (2⁻¹) = 1 := by
    rw [← map_ofNat (algebraMap ℝ B_q) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hΦ_invS :
      stereographicChartHom ε hε (IsLocalization.Away.invSelf s) =
        algebraMap ℝ B_q (2⁻¹) * (t ^ 2 + 1) := by
    have hmul : 2 * invQ * stereographicChartHom ε hε (IsLocalization.Away.invSelf s) = 1 := by
      rw [← stereographicChartHom_denom ε hε, ← map_mul,
        IsLocalization.Away.mul_invSelf, map_one]
    simpa [q, B_q, t] using eq_of_two_mul_invSelf_mul_eq_one q hmul
  apply Localization.algHom_ext (Submonoid.powers q)
  apply Polynomial.algHom_ext
  have hX : Algebra.algHom ℝ ℝ[X] (Localization (Submonoid.powers q)) Polynomial.X =
      algebraMap ℝ[X] (Localization.Away (Polynomial.X ^ 2 + 1 : ℝ[X])) Polynomial.X := rfl
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply, hX,
    stereographicChartInv_X, map_mul, stereographicChartHom_y, hΦ_invS]
  calc
    2 * t * invQ * (algebraMap ℝ B_q (2⁻¹) * (t ^ 2 + 1))
        = (2 * algebraMap ℝ B_q (2⁻¹)) * ((t ^ 2 + 1) * invQ) * t := by ring
    _ = t := by rw [h2B, hq_inv, mul_one, one_mul]

private theorem stereographicChartInv_comp_hom (ε : ℝ) (hε : ε ^ 2 = 1) :
    (stereographicChartInv ε hε).comp (stereographicChartHom ε hε) = AlgHom.id ℝ _ := by
  set s : CircleRing := 1 + algebraMap ℝ CircleRing ε * x
  set q : ℝ[X] := Polynomial.X ^ 2 + 1
  let A_s := Localization.Away s
  let invS : A_s := IsLocalization.Away.invSelf s
  have hs_inv : algebraMap CircleRing A_s s * invS = 1 := IsLocalization.Away.mul_invSelf s
  have h2A : (2 : A_s) * algebraMap ℝ A_s (2⁻¹) = 1 := by
    rw [← map_ofNat (algebraMap ℝ A_s) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hεA : (algebraMap ℝ CircleRing ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
  have hΨ_invQ :
      stereographicChartInv ε hε (IsLocalization.Away.invSelf q) =
        algebraMap ℝ A_s (2⁻¹) * algebraMap CircleRing A_s s := by
    have hmul : 2 * invS * stereographicChartInv ε hε (IsLocalization.Away.invSelf q) = 1 := by
      rw [← stereographicChartInv_denom ε hε, ← map_mul,
        IsLocalization.Away.mul_invSelf, map_one]
    exact eq_of_two_mul_invSelf_mul_eq_one s hmul
  apply Localization.algHom_ext (Submonoid.powers s)
  refine CircleRing.algHom_ext ?_ ?_
  · have hx : Algebra.algHom ℝ CircleRing (Localization (Submonoid.powers s)) x =
        algebraMap CircleRing (Localization.Away (1 + algebraMap ℝ CircleRing ε * x)) x := rfl
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply, hx,
      stereographicChartHom_x, map_mul, map_mul, map_sub, map_one, map_pow, AlgHom.commutes,
      stereographicChartInv_X, hΨ_invQ]
    have hεA' :
        algebraMap ℝ A_s ε = algebraMap CircleRing A_s (algebraMap ℝ CircleRing ε) :=
      IsScalarTower.algebraMap_apply ℝ CircleRing A_s ε
    have hnum : s ^ 2 - y ^ 2 = 2 * algebraMap ℝ CircleRing ε * x * s := by
      dsimp only [s]
      linear_combination -x_sq_add_y_sq - x ^ 2 * hεA
    have hnumA := congrArg (algebraMap CircleRing A_s) hnum
    simp only [map_sub, map_pow, map_mul, map_ofNat] at hnumA
    have hstep : 1 - (algebraMap CircleRing A_s y * invS) ^ 2 =
        2 * algebraMap ℝ A_s ε * algebraMap CircleRing A_s x * invS := by
      calc
        1 - (algebraMap CircleRing A_s y * invS) ^ 2
            = (algebraMap CircleRing A_s s ^ 2 - algebraMap CircleRing A_s y ^ 2) * invS ^ 2 := by
                linear_combination -(1 + algebraMap CircleRing A_s s * invS) * hs_inv
        _ = (2 * algebraMap CircleRing A_s (algebraMap ℝ CircleRing ε) *
              algebraMap CircleRing A_s x * algebraMap CircleRing A_s s) * invS ^ 2 := by
                rw [hnumA]
        _ = 2 * algebraMap ℝ A_s ε * algebraMap CircleRing A_s x *
              (algebraMap CircleRing A_s s * invS) * invS := by rw [← hεA']; ring
        _ = 2 * algebraMap ℝ A_s ε * algebraMap CircleRing A_s x * invS := by
              rw [hs_inv, mul_one]
    have hε_sq : (algebraMap ℝ A_s ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
    rw [hstep]
    calc
      algebraMap ℝ A_s ε * (2 * algebraMap ℝ A_s ε * algebraMap CircleRing A_s x * invS) *
          (algebraMap ℝ A_s (2⁻¹) * algebraMap CircleRing A_s s)
          = (algebraMap ℝ A_s ε) ^ 2 * (2 * algebraMap ℝ A_s (2⁻¹)) *
              (algebraMap CircleRing A_s s * invS) * algebraMap CircleRing A_s x := by ring
      _ = algebraMap CircleRing A_s x := by rw [hε_sq, h2A, hs_inv]; ring
  · have hy : Algebra.algHom ℝ CircleRing (Localization (Submonoid.powers s)) y =
        algebraMap CircleRing (Localization.Away (1 + algebraMap ℝ CircleRing ε * x)) y := rfl
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply, hy,
      stereographicChartHom_y, map_mul, map_mul, map_ofNat, stereographicChartInv_X, hΨ_invQ]
    calc
      2 * (algebraMap CircleRing A_s y * invS) *
          (algebraMap ℝ A_s (2⁻¹) * algebraMap CircleRing A_s s)
          = (2 * algebraMap ℝ A_s (2⁻¹)) * (algebraMap CircleRing A_s s * invS) *
              algebraMap CircleRing A_s y := by ring
      _ = algebraMap CircleRing A_s y := by rw [h2A, hs_inv]; ring

/-- The stereographic chart isomorphism
`CircleRing[(1 + ε x)⁻¹] ≃ₐ[ℝ] ℝ[t, (t² + 1)⁻¹]` for `ε ∈ {±1}` (`ε² = 1`).
It sends `x` to `ε (1 - t²) / (t² + 1)` and `y` to `2 t / (t² + 1)`, with inverse sending `t` to
`y / (1 + ε x)`. -/
def stereographicChartEquiv (ε : ℝ) (hε : ε ^ 2 = 1) :
    Localization.Away (1 + algebraMap ℝ CircleRing ε * x) ≃ₐ[ℝ]
      Localization.Away (Polynomial.X ^ 2 + 1 : ℝ[X]) :=
  AlgEquiv.ofAlgHom (stereographicChartHom ε hε) (stereographicChartInv ε hε)
    (stereographicChartHom_comp_inv ε hε) (stereographicChartInv_comp_hom ε hε)

/-- The stereographic chart sends `x` to `ε (1 - t²) / (t² + 1)`. -/
@[simp]
theorem stereographicChartEquiv_x (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartEquiv ε hε (algebraMap CircleRing _ x) =
      algebraMap ℝ _ ε * (1 - algebraMap ℝ[X] _ Polynomial.X ^ 2) *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : ℝ[X]) :=
  stereographicChartHom_x ε hε

/-- The stereographic chart sends `y` to `2 t / (t² + 1)`. -/
@[simp]
theorem stereographicChartEquiv_y (ε : ℝ) (hε : ε ^ 2 = 1) :
    stereographicChartEquiv ε hε (algebraMap CircleRing _ y) =
      2 * algebraMap ℝ[X] _ Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X ^ 2 + 1 : ℝ[X]) :=
  stereographicChartHom_y ε hε

/-- The inverse stereographic chart sends `t` to `y / (1 + ε x)`. -/
@[simp]
theorem stereographicChartEquiv_symm_X (ε : ℝ) (hε : ε ^ 2 = 1) :
    (stereographicChartEquiv ε hε).symm (algebraMap ℝ[X] _ Polynomial.X) =
      algebraMap CircleRing _ y *
        IsLocalization.Away.invSelf (1 + algebraMap ℝ CircleRing ε * x) :=
  stereographicChartInv_X ε hε

/-- In `CircleRing[y⁻¹]`, `1 + ε x` is a unit whenever `ε² = 1`. -/
theorem isUnit_one_add_mul_x_away_y (ε : ℝ) (hε : ε ^ 2 = 1) :
    IsUnit
      (algebraMap CircleRing (Localization.Away y) (1 + algebraMap ℝ CircleRing ε * x)) := by
  have hdvd : 1 + algebraMap ℝ CircleRing ε * x ∣ y ^ 2 := by
    refine ⟨1 - algebraMap ℝ CircleRing ε * x, ?_⟩
    have hεA : (algebraMap ℝ CircleRing ε) ^ 2 = 1 := by rw [← map_pow, hε, map_one]
    linear_combination x_sq_add_y_sq + x ^ 2 * hεA
  have hyUnit : IsUnit (algebraMap CircleRing (Localization.Away y) (y ^ 2)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit y).pow 2
  exact isUnit_of_dvd_unit (map_dvd _ hdvd) hyUnit

/-- The canonical `ℝ`-algebra homomorphism from the stereographic chart
`CircleRing[(1 + ε x)⁻¹]` into the overlap `CircleRing[y⁻¹]`, for `ε² = 1`. -/
def chartToOverlap (ε : ℝ) (hε : ε ^ 2 = 1) :
    Localization.Away (1 + algebraMap ℝ CircleRing ε * x) →ₐ[ℝ] Localization.Away y :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom ℝ CircleRing (Localization.Away y))
    (1 + algebraMap ℝ CircleRing ε * x) (by
      rw [IsScalarTower.toAlgHom_apply]
      exact isUnit_one_add_mul_x_away_y ε hε)

/-- `chartToOverlap` commutes with the localization map from `CircleRing`. -/
@[simp]
theorem chartToOverlap_algebraMap (ε : ℝ) (hε : ε ^ 2 = 1) (a : CircleRing) :
    chartToOverlap ε hε (algebraMap CircleRing _ a) = algebraMap CircleRing _ a := by
  simp only [chartToOverlap, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
  rfl

/-- **Overlap compatibility of the two stereographic charts.** On `CircleRing[y⁻¹]`, the two
stereographic parameters `t₊` (from `D(1 + x)`) and `t₋` (from `D(1 - x)`) are mutually inverse:
`t₊ · t₋ = 1`. -/
theorem stereographic_overlap :
    chartToOverlap 1 (one_pow 2)
        ((stereographicChartEquiv 1 (one_pow 2)).symm (algebraMap ℝ[X] _ Polynomial.X)) *
      chartToOverlap (-1) neg_one_sq
        ((stereographicChartEquiv (-1) neg_one_sq).symm
          (algebraMap ℝ[X] _ Polynomial.X)) = 1 := by
  rw [stereographicChartEquiv_symm_X, stereographicChartEquiv_symm_X]
  set s₁ : CircleRing := 1 + algebraMap ℝ CircleRing 1 * x
  set s₂ : CircleRing := 1 + algebraMap ℝ CircleRing (-1) * x
  set ι₁ := chartToOverlap 1 (one_pow 2)
  set ι₂ := chartToOverlap (-1) neg_one_sq
  have hs₁ : algebraMap CircleRing (Localization.Away y) s₁ *
      ι₁ (IsLocalization.Away.invSelf s₁) = 1 := by
    rw [← chartToOverlap_algebraMap 1 (one_pow 2) s₁, ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  have hs₂ : algebraMap CircleRing (Localization.Away y) s₂ *
      ι₂ (IsLocalization.Away.invSelf s₂) = 1 := by
    rw [← chartToOverlap_algebraMap (-1) neg_one_sq s₂, ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  have hs₁₂ : s₁ * s₂ = y ^ 2 := by
    simp only [s₁, s₂, map_one, map_neg, one_mul]
    linear_combination -x_sq_add_y_sq
  have hmul : algebraMap CircleRing (Localization.Away y) (y ^ 2) *
      (ι₁ (algebraMap CircleRing _ y * IsLocalization.Away.invSelf s₁) *
        ι₂ (algebraMap CircleRing _ y * IsLocalization.Away.invSelf s₂)) =
      algebraMap CircleRing (Localization.Away y) (y ^ 2) := by
    calc
      algebraMap CircleRing (Localization.Away y) (y ^ 2) *
          (ι₁ (algebraMap CircleRing _ y * IsLocalization.Away.invSelf s₁) *
            ι₂ (algebraMap CircleRing _ y * IsLocalization.Away.invSelf s₂))
          = (algebraMap CircleRing (Localization.Away y) s₁ *
              algebraMap CircleRing (Localization.Away y) s₂) *
            (algebraMap CircleRing (Localization.Away y) y *
              ι₁ (IsLocalization.Away.invSelf s₁) *
              (algebraMap CircleRing (Localization.Away y) y *
                ι₂ (IsLocalization.Away.invSelf s₂))) := by
                  rw [← hs₁₂, map_mul, map_mul, map_mul, chartToOverlap_algebraMap,
                    chartToOverlap_algebraMap]
      _ = (algebraMap CircleRing (Localization.Away y) s₁ *
              ι₁ (IsLocalization.Away.invSelf s₁)) *
            (algebraMap CircleRing (Localization.Away y) s₂ *
              ι₂ (IsLocalization.Away.invSelf s₂)) *
            algebraMap CircleRing (Localization.Away y) y ^ 2 := by ring
      _ = algebraMap CircleRing (Localization.Away y) (y ^ 2) := by
            rw [hs₁, hs₂, one_mul, one_mul, map_pow]
  have hyUnit : IsUnit (algebraMap CircleRing (Localization.Away y) (y ^ 2)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit y).pow 2
  exact hyUnit.mul_left_cancel (by simpa only [mul_one] using hmul)

end CircleRing

end

end TauCeti
