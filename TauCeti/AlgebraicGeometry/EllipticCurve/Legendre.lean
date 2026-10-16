/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# The Legendre form of an elliptic curve

The **Legendre form** of an elliptic curve is `y² = x (x - 1) (x - λ)`: the cubic on the right has
its three roots at `0`, `1` and `λ`. In Tau Ceti it is the curve `TauCeti.freyCurve 1 B` with
`B = -λ`, whose invariants `TauCeti.freyCurve_c₄`, `TauCeti.freyCurve_Δ` and `TauCeti.freyCurve_j`
specialise to

  `c₄ = 16 (B² + B + 1)`, `Δ = 16 B² (B + 1)²`, `j = 256 (B² + B + 1)³ / (B² (B + 1)²)`.

Away from characteristic `2` every elliptic curve takes this form after a finite separable
extension of the base field (Silverman, *AEC*, III.1.7). Over a field `F` with `2 ≠ 0`, suppose
that the `2`-division polynomial `4x³ + b₂x² + 2b₄x + b₆` of `W` factors as
`4 (x - e₁) (x - e₂) (x - e₃)` with `e₁ ≠ e₂`, and that `e₂ - e₁ = u²`. Completing the square in
`y`, moving `e₁` to the origin and scaling by `u` is a change of variables taking `W` to the
Legendre form with `λ = (e₃ - e₁) / (e₂ - e₁)`. A splitting field of the `2`-division polynomial,
followed by a splitting field of `X² - (e₂ - e₁)`, supplies the roots and the square root, and it
is separable because the `2`-division polynomial has nonzero discriminant `16 Δ`.

Since `j` is an explicit rational function of `λ`, the Legendre form ties the reduction of an
elliptic curve to its `j`-invariant: this is how the criterion
`WeierstrassCurve.hasPotentialGoodReduction_of_isInteger_j` for potential good reduction is
proved away from residue characteristic `2`. In residue characteristic `2` the Deuring normal form
of `TauCeti/AlgebraicGeometry/EllipticCurve/DeuringNormalForm.lean` takes its place.

## Main results

* `WeierstrassCurve.exists_variableChange_smul_eq_freyCurve_one`: a curve whose `2`-division
  polynomial splits, with `e₂ - e₁` a square, is a change of variables away from Legendre form.
* `WeierstrassCurve.exists_variableChange_smul_baseChange_eq_freyCurve_one`: away from
  characteristic `2`, an elliptic curve takes Legendre form over a finite separable extension.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.7 and VII.5.5.
-/

public section

universe u

open Polynomial TauCeti

namespace WeierstrassCurve

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

/-- **Legendre form.** If `2 ≠ 0`, the `2`-division polynomial of `W` factors as
`4 (X - e₁) (X - e₂) (X - e₃)` with `e₁ ≠ e₂`, and `e₂ - e₁ = u²`, then a change of variables takes
`W` to the Legendre form `y² = x (x - 1) (x - λ)` with `λ = (e₃ - e₁) / (e₂ - e₁)`, that is to
`freyCurve 1 (-λ)`. It completes the square in `y`, moves `e₁` to the origin and scales `x` by
`u²`. -/
theorem exists_variableChange_smul_eq_freyCurve_one (h2 : (2 : F) ≠ 0) {e₁ e₂ e₃ u : F}
    (h : W.twoTorsionPolynomial.toPoly = C 4 * (X - C e₁) * (X - C e₂) * (X - C e₃))
    (he : e₂ ≠ e₁) (hu : u ^ 2 = e₂ - e₁) :
    ∃ C : VariableChange F, C • W = freyCurve 1 ((e₁ - e₃) / (e₂ - e₁)) := by
  -- the coefficients of the `2`-division polynomial are the elementary symmetric functions
  rw [Cubic.C_mul_prod_X_sub_C_eq, Cubic.toPoly_injective, twoTorsionPolynomial] at h
  simp only [Cubic.mk.injEq, true_and] at h
  obtain ⟨hb₂, hb₄, hb₆⟩ := h
  simp only [b₂, b₄, b₆] at hb₂ hb₄ hb₆
  have hb₄' : 2 * W.a₄ + W.a₁ * W.a₃ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) :=
    mul_left_cancel₀ h2 (by linear_combination hb₄)
  have hα : e₂ - e₁ ≠ 0 := sub_ne_zero.mpr he
  have hu0 : u ≠ 0 := by rintro rfl; exact hα (by rw [← hu]; ring)
  refine ⟨⟨Units.mk0 u hu0, e₁, -W.a₁ / 2, -(W.a₁ * e₁ + W.a₃) / 2⟩, ?_⟩
  have hu4 : u ^ 4 = (e₂ - e₁) ^ 2 := by rw [← hu]; ring
  have hu6 : u ^ 6 = (e₂ - e₁) ^ 3 := by rw [← hu]; ring
  ext
  · rw [variableChange_a₁, freyCurve_a₁]
    field_simp
    ring
  · rw [variableChange_a₂, freyCurve_a₂, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hu]
    field_simp
    linear_combination hb₂
  · rw [variableChange_a₃, freyCurve_a₃]
    field_simp
    ring
  · rw [variableChange_a₄, freyCurve_a₄, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hu4]
    field_simp
    linear_combination hb₄' + e₁ * hb₂
  · rw [variableChange_a₆, freyCurve_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hu6]
    field_simp
    linear_combination hb₆ + e₁ * hb₄ + e₁ ^ 2 * hb₂

/-- **Legendre form over a finite separable extension.** Away from characteristic `2`, an
elliptic curve over `K` becomes isomorphic to a curve `y² = x (x - 1) (x + B)` over a finite
separable extension `L` of `K`: one obtained by adjoining the roots `e₁, e₂, e₃` of its
`2`-division polynomial and a square root of `e₂ - e₁`. -/
theorem exists_variableChange_smul_baseChange_eq_freyCurve_one {K : Type u} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic] (h2 : (2 : K) ≠ 0) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (C : VariableChange L) (B : L),
      C • W.baseChange L = freyCurve 1 B := by
  set P := W.twoTorsionPolynomial
  have hPa : P.a = 4 := by simp only [P, twoTorsionPolynomial]
  have ha : P.a ≠ 0 := by
    rw [hPa, show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  -- the roots of the `2`-division polynomial, in its splitting field `L₁`
  let L₁ := SplittingField P.toPoly
  have hsplit : (P.toPoly.map (algebraMap K L₁)).Splits := SplittingField.splits P.toPoly
  obtain ⟨e₁, e₂, e₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplit
  have hdisc : P.discr ≠ 0 := by
    rw [twoTorsionPolynomial_discr]
    exact mul_ne_zero (by rw [show (16 : K) = 2 ^ 4 by norm_num]; exact pow_ne_zero 4 h2)
      W.isUnit_Δ.ne_zero
  obtain ⟨h12, -, -⟩ := (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc
  have hsep₁ : P.toPoly.Separable := by
    have hnd := (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mp hdisc
    rw [Cubic.roots, Cubic.map_toPoly, nodup_roots_iff_of_splits
      ((Polynomial.map_ne_zero_iff (algebraMap K L₁).injective).mpr
        (Cubic.ne_zero_of_a_ne_zero ha)) hsplit] at hnd
    exact (separable_map _).mp hnd
  have : IsGalois K L₁ := IsGalois.of_separable_splitting_field hsep₁
  -- a square root of `e₂ - e₁`, in the splitting field `L` of `X² - (e₂ - e₁)` over `L₁`
  have h2₁ : ((2 : ℕ) : L₁) ≠ 0 := by
    rw [Nat.cast_ofNat, ← map_ofNat (algebraMap K L₁)]
    exact (_root_.map_ne_zero _).mpr h2
  let L := SplittingField (X ^ 2 - C (e₂ - e₁) : L₁[X])
  have : IsGalois L₁ L := IsGalois.of_separable_splitting_field
    (separable_X_pow_sub_C _ h2₁ (sub_ne_zero.mpr (Ne.symm h12)))
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.trans K L₁ L
  have : FiniteDimensional K L := Module.Finite.trans L₁ L
  obtain ⟨u, hu⟩ := (SplittingField.splits (X ^ 2 - C (e₂ - e₁) : L₁[X])).exists_eval_eq_zero
    (by rw [degree_map, degree_X_pow_sub_C two_pos]; norm_num)
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X,
    eval_C, sub_eq_zero] at hu
  -- the factorisation of the `2`-division polynomial of the base change to `L`
  set ψ := algebraMap L₁ L
  have hfac : (W.baseChange L).twoTorsionPolynomial.toPoly =
      C 4 * (X - C (ψ e₁)) * (X - C (ψ e₂)) * (X - C (ψ e₃)) := by
    have h := congrArg (Polynomial.map ψ) (Cubic.eq_prod_three_roots ha h3)
    rw [Cubic.map_toPoly, Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h
    simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C] at h
    rw [hPa, map_ofNat, map_ofNat] at h
    have hmap : (W.baseChange L).twoTorsionPolynomial = Cubic.map (algebraMap K L) P := by
      simp only [twoTorsionPolynomial, Cubic.map, baseChange, map_b₂, map_b₄, map_b₆, map_mul,
        map_ofNat, P]
    rw [hmap, Cubic.map_toPoly, h]
  have he : ψ e₂ ≠ ψ e₁ := fun h ↦ h12 (ψ.injective h).symm
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (_root_.map_ne_zero _).mpr h2
  obtain ⟨C, hC⟩ := exists_variableChange_smul_eq_freyCurve_one h2L hfac he (by rw [hu, map_sub])
  exact ⟨L, _, _, ‹_›, ‹_›, C, _, hC⟩

end WeierstrassCurve

end
