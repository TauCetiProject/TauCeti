/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.GenusZero
public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Genus
public import TauCeti.FieldTheory.FunctionField.Place.Map
-- Proof-only: a quadratic without roots is irreducible.
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# A genus-zero function field that is not rational

Genus zero together with a divisor of degree one forces a function field to be rational
(`TauCeti.nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one`, Stichtenoth,
Proposition 1.6.3). Genus zero alone does not. This file records the standard counterexample: the
function field of the conic `x² + y² + 1 = 0` over a field `k` in which `a² + b² + 1 = 0` has no
solution, such as `ℝ`, `ℚ`, or any ordered field (Stichtenoth, Remark 1.6.4).

The field is `F = k(x, y)` with `y² = −(x² + 1)`, an extension `y² = f(x)` with `f` squarefree of
degree two, so it has genus `⌊(2 − 1) / 2⌋ = 0` and exact constant field `k` by
`TauCeti.genus_eq_of_sq_eq`. It has no place of degree one: the residue field of a rational place
`P` is `k`, so if `x` is regular at `P` the residues of `x` and `y` solve `a² + b² + 1 = 0`, and
if `x` has a pole at `P` then so does `y`, and the residue of `y / x` is a square root of `−1`.
Hence `F` has no divisor of degree one either, and it is not isomorphic to `k(x)`.

## Main results

* `TauCeti.Place.degree_ne_one_of_sq_add_sq_add_one_eq_zero`: over such a `k`, a field containing
  `x` and `y` with `x² + y² + 1 = 0` has no place of degree one.
* `TauCeti.genus_eq_zero_of_sq_add_sq_add_one_eq_zero`: the conic has genus zero.
* `TauCeti.not_exists_divisor_degree_eq_one_of_sq_add_sq_add_one_eq_zero`: it has no divisor of
  degree one.
* `TauCeti.isEmpty_algEquiv_ratFunc_of_sq_add_sq_add_one_eq_zero`: **it is not rational**.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Remark 1.6.4.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F]

section Place

variable [Algebra k F]

/-- **The conic `x² + y² + 1 = 0` has no rational place.** If `a² + b² + 1 = 0` has no solution
in `k`, then a field `F / k` containing `x` and `y` with `x² + y² + 1 = 0` has no place of degree
one: at such a place the relation, or its rescaling `(y / x)² + (1 / x)² + 1 = 0` at a pole of
`x`, would reduce to a solution in the residue field `k`. -/
theorem Place.degree_ne_one_of_sq_add_sq_add_one_eq_zero (hk : ∀ a b : k, a ^ 2 + b ^ 2 + 1 ≠ 0)
    {x y : F} (hxy : x ^ 2 + y ^ 2 + 1 = 0) (P : Place k F) : P.degree ≠ 1 := by
  intro hP
  -- the residue map at a rational place, with values in `k`
  let φ : P.integers →+* k :=
    ((P.residueFieldEquivOfDegreeEqOne hP).symm : P.ResidueField →+* k).comp
      (IsLocalRing.residue P.integers)
  have hφ : ∀ z : P.integers, P.valuation (z : F) < 1 → φ z = 0 := fun z hz ↦ by
    simp [φ, P.residue_eq_zero_iff_valuation_lt_one.mpr hz]
  have hy2 : y ^ 2 = -(x ^ 2 + 1) := by linear_combination hxy
  rcases le_or_gt (P.valuation x) 1 with hx | hx
  · -- `x` and `y` are regular at `P`, and their residues solve `a² + b² + 1 = 0`
    have hy : P.valuation y ≤ 1 := by
      have h : P.valuation y ^ 2 ≤ 1 := by
        rw [← map_pow, hy2, Valuation.map_neg]
        exact (P.valuation.map_add _ _).trans
          (max_le (by rw [map_pow]; exact pow_le_one₀ zero_le hx) (by simp))
      exact (pow_le_one_iff_of_nonneg zero_le two_ne_zero).mp h
    have hx' : x ∈ P.integers := P.mem_integers_iff.mpr hx
    have hy' : y ∈ P.integers := P.mem_integers_iff.mpr hy
    have hrel : (⟨x, hx'⟩ : P.integers) ^ 2 + ⟨y, hy'⟩ ^ 2 + 1 = 0 :=
      Subtype.ext (by push_cast; exact hxy)
    have := congrArg φ hrel
    rw [map_add, map_add, map_pow, map_pow, map_one, map_zero] at this
    exact hk (φ ⟨x, hx'⟩) (φ ⟨y, hy'⟩) this
  · -- `x` has a pole at `P`, hence so does `y`, and `(y / x)² + (1 / x)² + 1 = 0` reduces to a
    -- square root of `-1` in `k`
    have hx0 : x ≠ 0 := fun h ↦ by simp [h] at hx
    have hvx : P.valuation x ≠ 0 := (zero_lt_one.trans hx).ne'
    have hvy : P.valuation y = P.valuation x := by
      refine (pow_left_inj₀ zero_le zero_le two_ne_zero).mp ?_
      rw [← map_pow, hy2, Valuation.map_neg, Valuation.map_add_eq_of_lt_left, map_pow]
      rw [map_one, map_pow]
      exact one_lt_pow₀ hx two_ne_zero
    have hu : y / x ∈ P.integers := by
      rw [P.mem_integers_iff, Valuation.map_div, hvy, div_self hvx]
    have hinv : P.valuation x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hx
    have hinv' : x⁻¹ ∈ P.integers := P.mem_integers_iff.mpr hinv.le
    have hrel : (⟨y / x, hu⟩ : P.integers) ^ 2 + ⟨x⁻¹, hinv'⟩ ^ 2 + 1 = 0 := by
      refine Subtype.ext ?_
      push_cast
      field_simp
      linear_combination hxy
    have := congrArg φ hrel
    rw [map_add, map_add, map_pow, map_pow, map_one, map_zero, hφ ⟨x⁻¹, hinv'⟩ hinv] at this
    exact hk (φ ⟨y / x, hu⟩) 0 this

end Place

section Conic

variable [Algebra (RatFunc k) F]

private theorem natDegree_neg_X_sq_add_one : (-(X ^ 2 + 1) : k[X]).natDegree = 2 := by
  rw [natDegree_neg]
  compute_degree!

/-- The polynomial `-(X ^ 2 + 1)` is squarefree when `a ^ 2 + 1 = 0` has no solution in `k`. -/
private theorem squarefree_neg_X_sq_add_one (hk : ∀ a b : k, a ^ 2 + b ^ 2 + 1 ≠ 0) :
    Squarefree (-(X ^ 2 + 1) : k[X]) := by
  refine (irreducible_of_degree_le_three_of_not_isRoot ?_ fun a ha ↦ ?_).squarefree
  · rw [natDegree_neg_X_sq_add_one, Finset.mem_Icc]
    omega
  · rw [IsRoot.def, eval_neg, eval_add, eval_pow, eval_X, eval_one] at ha
    exact hk a 0 (by linear_combination -ha)

/-- The conic relation in the form `y ^ 2 = f(x)` with `f = -(X ^ 2 + 1)`. -/
private theorem sq_eq_of_sq_add_sq_add_one_eq_zero {y : F}
    (hy : algebraMap (RatFunc k) F RatFunc.X ^ 2 + y ^ 2 + 1 = 0) :
    y ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) (-(X ^ 2 + 1))) := by
  simp only [map_neg, map_add, map_pow, map_one, RatFunc.algebraMap_X]
  linear_combination hy

private theorem two_ne_zero_of_forall_sq_add_sq_add_one_ne_zero
    (hk : ∀ a b : k, a ^ 2 + b ^ 2 + 1 ≠ 0) : (2 : k) ≠ 0 :=
  fun h ↦ hk 1 0 (by linear_combination h)

variable [Algebra k F] [IsScalarTower k (RatFunc k) F]

/-- **The conic has exact constant field `k`.** -/
theorem isIntegrallyClosedIn_of_sq_add_sq_add_one_eq_zero (hk : ∀ a b : k, a ^ 2 + b ^ 2 + 1 ≠ 0)
    {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : algebraMap (RatFunc k) F RatFunc.X ^ 2 + y ^ 2 + 1 = 0) :
    IsIntegrallyClosedIn k F :=
  isIntegrallyClosedIn_of_sq_eq (two_ne_zero_of_forall_sq_add_sq_add_one_ne_zero hk)
    (squarefree_neg_X_sq_add_one hk) (by rw [natDegree_neg_X_sq_add_one]; omega) hgen
    (sq_eq_of_sq_add_sq_add_one_eq_zero hy)

/-- **The conic is a function field over `k`.** -/
theorem isFunctionField_of_sq_add_sq_add_one_eq_zero (hk : ∀ a b : k, a ^ 2 + b ^ 2 + 1 ≠ 0)
    {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : algebraMap (RatFunc k) F RatFunc.X ^ 2 + y ^ 2 + 1 = 0) :
    IsFunctionField k F := by
  have : FiniteDimensional (RatFunc k) F := Module.finite_of_finrank_pos (by
    rw [finrank_ratFunc_eq_two_of_sq_eq (squarefree_neg_X_sq_add_one hk)
      (by rw [natDegree_neg_X_sq_add_one]; omega) hgen (sq_eq_of_sq_add_sq_add_one_eq_zero hy)]
    omega)
  exact isFunctionField_iff_functionField.mpr inferInstance

/-- **The conic has genus zero**: `y ^ 2 = -(x ^ 2 + 1)` is an extension `y ^ 2 = f(x)` with `f`
squarefree of degree two, so its genus is `⌊(2 - 1) / 2⌋ = 0`. -/
theorem genus_eq_zero_of_sq_add_sq_add_one_eq_zero (hk : ∀ a b : k, a ^ 2 + b ^ 2 + 1 ≠ 0)
    {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : algebraMap (RatFunc k) F RatFunc.X ^ 2 + y ^ 2 + 1 = 0) :
    genus k F = 0 := by
  rw [genus_eq_of_sq_eq (two_ne_zero_of_forall_sq_add_sq_add_one_ne_zero hk)
    (squarefree_neg_X_sq_add_one hk) (by rw [natDegree_neg_X_sq_add_one]; omega) hgen
    (sq_eq_of_sq_add_sq_add_one_eq_zero hy), natDegree_neg_X_sq_add_one]

/-- **The conic has no divisor of degree one**: it has genus zero, and a genus-zero function field
with a divisor of degree one has a rational place, which the conic lacks. -/
theorem not_exists_divisor_degree_eq_one_of_sq_add_sq_add_one_eq_zero
    (hk : ∀ a b : k, a ^ 2 + b ^ 2 + 1 ≠ 0) {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : algebraMap (RatFunc k) F RatFunc.X ^ 2 + y ^ 2 + 1 = 0) :
    ¬ ∃ D : Divisor k F, Divisor.degree D = 1 := fun hD ↦ by
  obtain ⟨P, hP⟩ := exists_place_degree_eq_one_of_genus_eq_zero_of_divisor_degree_eq_one
    (isFunctionField_of_sq_add_sq_add_one_eq_zero hk hgen hy)
    (isIntegrallyClosedIn_of_sq_add_sq_add_one_eq_zero hk hgen hy)
    (genus_eq_zero_of_sq_add_sq_add_one_eq_zero hk hgen hy) hD
  exact Place.degree_ne_one_of_sq_add_sq_add_one_eq_zero hk hy P hP

omit [IsScalarTower k (RatFunc k) F] in
/-- **The conic is not rational** (Stichtenoth, Remark 1.6.4): a `k`-isomorphism with `k(x)`
would transport the rational place at infinity of `k(x)` to a rational place of the conic. With
`TauCeti.genus_eq_zero_of_sq_add_sq_add_one_eq_zero`, this records that genus zero alone does not
force rationality: the degree-one divisor in
`TauCeti.nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one` cannot be dropped. -/
theorem isEmpty_algEquiv_ratFunc_of_sq_add_sq_add_one_eq_zero
    (hk : ∀ a b : k, a ^ 2 + b ^ 2 + 1 ≠ 0) {y : F}
    (hy : algebraMap (RatFunc k) F RatFunc.X ^ 2 + y ^ 2 + 1 = 0) :
    IsEmpty (F ≃ₐ[k] RatFunc k) :=
  ⟨fun e ↦ Place.degree_ne_one_of_sq_add_sq_add_one_eq_zero hk hy
    ((Place.infty k).map e.symm) (by simp)⟩

end Conic

end TauCeti
