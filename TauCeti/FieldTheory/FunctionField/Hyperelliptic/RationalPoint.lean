/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Genus.Basic
-- Proof-only: the action of `Aut(F / k(x))` on places, and the fundamental inequality.
import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre
import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois
-- Proof-only: the involution `y ↦ -y` of `F / k(x)`.
import TauCeti.FieldTheory.Galois.SquareRoot

/-!
# The rational place of an affine point of `y² = f(x)`

Let `F = k(x, y)` with `y² = f(x)` for a squarefree polynomial `f ∈ k[x]` of positive degree,
away from characteristic two. An affine point `(a, b)` of the curve off the branch locus, that is
with `b ≠ 0`, gives a place of `F`: there is a place `P` lying over the place `x = a` of `k(x)` at
which `y - b` vanishes, and it is rational and unramified over `k(x)`. The point `(a, -b)` gives
the other place over `x = a`, the image of `P` under the involution `y ↦ -y`.

This turns concrete points of a hyperelliptic curve into places of its function field, for
instance to read off the Weierstrass gaps at its unramified rational places.

## Main results

* `TauCeti.Place.exists_ord_sub_pos_of_sq_eq`: an affine point `(a, b)` with `b ≠ 0` is the
  center of a rational place of `F` unramified over `k(x)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.3 and Section VI.2.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

namespace Place

variable {k F : Type*} [Field k] [Field F] [Algebra (RatFunc k) F] [Algebra k F]
  [IsScalarTower k (RatFunc k) F]

/-- **The rational place of an affine point of `y² = f(x)` off the branch locus**: away from
characteristic two, if `F = k(x, y)` with `y² = f(x)` for a squarefree `f` of positive degree, and
`(a, b)` is a point of the curve with `b ≠ 0`, then some place `P` of `F` over the place `x = a`
of `k(x)` is rational, unramified over `k(x)`, and has both `x - a` and `y - b` vanishing at it. -/
theorem exists_ord_sub_pos_of_sq_eq (h2 : (2 : k) ≠ 0) {f : k[X]} (hf : Squarefree f)
    (hdeg : 0 < f.natDegree) {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f)) {a b : k}
    (hb : b ≠ 0) (hab : b ^ 2 = f.eval a) :
    letI : FiniteDimensional (RatFunc k) F :=
      (finiteDimensional_and_isSeparable_of_sq_eq h2 hf hdeg hgen hy).1
    ∃ P : Place k F, P.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a) ∧
      P.degree = 1 ∧ ramificationIdx (RatFunc k) P = 1 ∧
      0 < P.ord (algebraMap (RatFunc k) F RatFunc.X - algebraMap k F a) ∧
      0 < P.ord (y - algebraMap k F b) := by
  classical
  obtain ⟨_, _⟩ := finiteDimensional_and_isSeparable_of_sq_eq h2 hf hdeg hgen hy
  have hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
  set Q₀ := adicOfIrreducible (irreducible_X_sub_C a)
  set D := y - algebraMap k F b
  set S := y + algebraMap k F b
  set g : k[X] := f - C (b ^ 2)
  -- At a place over `x = a`, a polynomial in `x` has order `e` times its multiplicity at `a`.
  have hord : ∀ P : Place k F, P.restrict k (RatFunc k) = Q₀ → ∀ p : k[X], p ≠ 0 →
      P.ord (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p)) =
        ramificationIdx (RatFunc k) P * multiplicity (X - C a) p := fun P hP p hp ↦ by
    rw [ord_algebraMap_restrict k (RatFunc k) P, hP, ord_adicOfIrreducible_algebraMap _ hp]
  have hpos : ∀ P : Place k F, P.restrict k (RatFunc k) = Q₀ → ∀ p : k[X], p ≠ 0 →
      X - C a ∣ p → 0 < P.ord (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p)) :=
    fun P hP p hp hdvd ↦ by
      rw [hord P hP p hp]
      exact mul_pos (by exact_mod_cast ramificationIdx_pos (RatFunc k) P)
        (by exact_mod_cast (multiplicity_pos_of_dvd hdvd
          (.of_not_isUnit (irreducible_X_sub_C a).not_isUnit hp)))
  have hfa : ¬X - C a ∣ f := by
    rw [dvd_iff_isRoot, IsRoot, ← hab]
    exact pow_ne_zero 2 hb
  have hg : X - C a ∣ g := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_C, hab, sub_self]
  have hg0 : g ≠ 0 := fun h ↦ by
    rw [sub_eq_zero.mp h, natDegree_C] at hdeg
    exact lt_irrefl 0 hdeg
  -- `(y - b) (y + b) = f(x) - f(a)`.
  have hb2 : algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) (C (b ^ 2))) =
      algebraMap k F b ^ 2 := by
    rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply,
      map_pow]
  have hfac : D * S = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) g) := by
    simp only [D, S, g, map_sub, hb2, ← hy]
    ring
  have hG0 : algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) g) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (RatFunc.algebraMap_ne_zero hg0)
  obtain ⟨hD0, hS0⟩ := mul_ne_zero_iff.mp (hfac ▸ hG0)
  -- At a place over `x = a`, exactly one of `y - b` and `y + b` vanishes.
  have hexact : ∀ P : Place k F, P.restrict k (RatFunc k) = Q₀ →
      (0 < P.ord D ↔ ¬0 < P.ord S) := fun P hP ↦ by
    have hy0 : P.ord y = 0 := by
      have h := congrArg P.ord hy
      rw [ord_pow, hord P hP f hf.ne_zero, multiplicity_eq_zero_of_not_dvd hfa] at h
      push_cast at h
      omega
    have hb0 : P.ord (algebraMap k F b) = 0 := P.ord_algebraMap b
    have hD : 0 ≤ P.ord D := by
      have h := P.min_ord_le_ord_add (f := y) (g := -algebraMap k F b)
        (by rwa [← sub_eq_add_neg])
      rw [ord_neg, hy0, hb0, ← sub_eq_add_neg] at h
      simpa using h
    have hS : 0 ≤ P.ord S := by
      have h := P.min_ord_le_ord_add (f := y) (g := algebraMap k F b) hS0
      rw [hy0, hb0] at h
      simpa using h
    have hsum : 0 < P.ord D + P.ord S := by
      rw [← P.ord_mul hD0 hS0, hfac]
      exact hpos P hP g hg0 hg
    have hdiff : S + -D = algebraMap k F (2 * b) := by
      simp only [S, D, map_mul, map_ofNat]
      ring
    have h2b : algebraMap k F (2 * b) ≠ 0 := (_root_.map_ne_zero _).mpr (mul_ne_zero h2 hb)
    have hmin := P.min_ord_le_ord_add (f := S) (g := -D) (hdiff ▸ h2b)
    rw [ord_neg, hdiff, ord_algebraMap] at hmin
    constructor
    · intro hDpos hSpos
      exact absurd hmin (by simp [hDpos, hSpos])
    · intro hSpos
      omega
  -- The involution `y ↦ -y` of `F / k(x)` exchanges `y - b` and `-(y + b)`.
  obtain ⟨σ, hσ⟩ := TauCeti.exists_algEquiv_apply_eq_neg_of_sq_eq
    (finrank_ratFunc_eq_two_of_sq_eq hf hdeg hgen hy) hgen hy
  have hσsymm : σ.symm y = -y := by rw [AlgEquiv.symm_apply_eq, map_neg, hσ, neg_neg]
  have hsmul : ∀ P : Place k F, (σ • P).ord D = P.ord S := fun P ↦ by
    rw [ord_smul, map_sub, hσsymm, IsScalarTower.algebraMap_apply k (RatFunc k),
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply, ← neg_add', ord_neg]
  -- A place over `x = a` at which `y - b` vanishes, and its conjugate.
  obtain ⟨P₀, hP₀⟩ := restrict_surjective_of_finiteDimensional (IsFunctionField.ratFunc k) hF Q₀
  replace hP₀ : P₀.restrict k (RatFunc k) = Q₀ := hP₀
  obtain ⟨P, hPQ, hPD⟩ : ∃ P : Place k F, P.restrict k (RatFunc k) = Q₀ ∧ 0 < P.ord D := by
    by_cases h : 0 < P₀.ord D
    · exact ⟨P₀, hP₀, h⟩
    · refine ⟨σ • P₀, by rw [restrict_smul, hP₀], ?_⟩
      rw [hsmul]
      by_contra hS
      exact h ((hexact P₀ hP₀).mpr hS)
  have hne : σ • P ≠ P := fun h ↦ (hexact P hPQ).mp hPD (by rw [← hsmul, h]; exact hPD)
  -- `P` is unramified over `k(x)`: it lies neither over infinity nor over a zero of `f`.
  have he : ramificationIdx (RatFunc k) P = 1 := by
    have hle : ¬1 < ramificationIdx (RatFunc k) P := by
      rw [one_lt_ramificationIdx_iff_of_sq_eq h2 hf hgen hy P, hPQ]
      rintro (⟨h, -⟩ | ⟨q, hq, hqf, hqQ⟩)
      · exact adicOfIrreducible_ne_infty _ h
      · exact hfa (((adicOfIrreducible_eq_adicOfIrreducible_iff _ hq).mp hqQ).dvd.trans hqf)
    have := ramificationIdx_pos (RatFunc k) P
    omega
  -- `P` and its conjugate are two places over the rational place `x = a` of a quadratic
  -- extension, so both are rational.
  have hdeg1 : P.degree = 1 := by
    have hsum := sum_ramificationIdx_mul_relativeDegree_le_finrank k (RatFunc k) Q₀
      {P, σ • P} (by simp [hPQ])
    rw [Finset.sum_pair hne.symm, ramificationIdx_smul, relativeDegree_smul, he,
      finrank_ratFunc_eq_two_of_sq_eq hf hdeg hgen hy] at hsum
    have := one_le_relativeDegree k (RatFunc k) P
    rw [degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) P, hPQ,
      degree_adicOfIrreducible_X_sub_C]
    omega
  refine ⟨P, hPQ, hdeg1, he, ?_, hPD⟩
  have hxa : algebraMap (RatFunc k) F RatFunc.X - algebraMap k F a =
      algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) (X - C a)) := by
    rw [map_sub, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C,
      ← IsScalarTower.algebraMap_apply]
  rw [hxa]
  exact hpos P hPQ _ (X_sub_C_ne_zero a) dvd_rfl

end Place

end TauCeti
