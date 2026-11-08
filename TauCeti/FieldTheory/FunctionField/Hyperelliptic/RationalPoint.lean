/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Hyperelliptic.Genus.Basic
-- Proof-only: the action of `Aut(F / k(x))` on places.
import TauCeti.FieldTheory.FunctionField.Place.Extension.Galois
import TauCeti.FieldTheory.FunctionField.Place.Extension.RatFunc
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

section Helpers

/-- On the curve `y² = f(x)`, `(y - b)(y + b) = f(x) - b²`. -/
private theorem sub_mul_add_eq_algebraMap {f : k[X]} {y : F}
    (hy : y ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f)) (b : k) :
    (y - algebraMap k F b) * (y + algebraMap k F b) =
      algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) (f - C (b ^ 2))) := by
  have hb2 : algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) (C (b ^ 2))) =
      algebraMap k F b ^ 2 := by
    rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply,
      map_pow]
  simp only [map_sub, hb2, ← hy]
  ring

variable [FiniteDimensional (RatFunc k) F]

/-- At a place over `x = a`, on a point `(a, b)` of `y² = f(x)` with `b ≠ 0` and `2 ≠ 0`, exactly
one of `y - b` and `y + b` vanishes. -/
private theorem ord_sub_pos_iff_not_ord_add_pos (h2 : (2 : k) ≠ 0) {f : k[X]}
    (hdeg : 0 < f.natDegree) {y : F}
    (hy : y ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f)) {a b : k}
    (hb : b ≠ 0) (hab : b ^ 2 = f.eval a) {P : Place k F}
    (hP : P.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a)) :
    0 < P.ord (y - algebraMap k F b) ↔ ¬0 < P.ord (y + algebraMap k F b) := by
  have hfa : ¬X - C a ∣ f := by
    rw [dvd_iff_isRoot, IsRoot, ← hab]
    exact pow_ne_zero 2 hb
  have hf0 : f ≠ 0 := fun h ↦ hfa (h ▸ dvd_zero _)
  have hg : X - C a ∣ f - C (b ^ 2) := by
    simpa only [← hab] using X_sub_C_dvd_sub_C_eval (p := f) (a := a)
  have hg0 : f - C (b ^ 2) ≠ 0 := fun h ↦ by
    rw [sub_eq_zero.mp h, natDegree_C] at hdeg
    exact lt_irrefl 0 hdeg
  have hfac := sub_mul_add_eq_algebraMap hy b
  have hG0 : algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) (f - C (b ^ 2))) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (RatFunc.algebraMap_ne_zero hg0)
  obtain ⟨hD0, hS0⟩ := mul_ne_zero_iff.mp (hfac ▸ hG0)
  have hy0 : P.ord y = 0 := by
    have h := congrArg P.ord hy
    rw [ord_pow, ord_algebraMap_eq_of_restrict_eq a hP hf0,
      multiplicity_eq_zero_of_not_dvd hfa] at h
    push_cast at h
    omega
  have hb0 : P.ord (algebraMap k F b) = 0 := P.ord_algebraMap b
  have hD : 0 ≤ P.ord (y - algebraMap k F b) := by
    have h := P.min_ord_le_ord_add (f := y) (g := -algebraMap k F b)
      (by rwa [← sub_eq_add_neg])
    rw [ord_neg, hy0, hb0, ← sub_eq_add_neg] at h
    simpa using h
  have hS : 0 ≤ P.ord (y + algebraMap k F b) := by
    have h := P.min_ord_le_ord_add (f := y) (g := algebraMap k F b) hS0
    rw [hy0, hb0] at h
    simpa using h
  have hsum : 0 < P.ord (y - algebraMap k F b) + P.ord (y + algebraMap k F b) := by
    rw [← P.ord_mul hD0 hS0, hfac]
    exact ord_algebraMap_pos_of_restrict_eq a hP hg0 hg
  have hdiff : (y + algebraMap k F b) + -(y - algebraMap k F b) = algebraMap k F (2 * b) := by
    simp only [map_mul, map_ofNat]
    ring
  have h2b : algebraMap k F (2 * b) ≠ 0 := (_root_.map_ne_zero _).mpr (mul_ne_zero h2 hb)
  have hmin := P.min_ord_le_ord_add (f := y + algebraMap k F b) (g := -(y - algebraMap k F b))
    (hdiff ▸ h2b)
  rw [ord_neg, hdiff, ord_algebraMap] at hmin
  constructor
  · intro hDpos hSpos
    exact absurd hmin (by simp [hDpos, hSpos])
  · intro hSpos
    omega

end Helpers

section Helpers

variable [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]

/-- Away from the branch locus, a place over `x = a` is unramified over `k(x)`: it lies neither
over infinity nor over a zero of `f`. -/
private theorem ramificationIdx_eq_one_of_restrict_eq (h2 : (2 : k) ≠ 0) {f : k[X]}
    (hf : Squarefree f) {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f)) {a : k}
    (hfa : ¬X - C a ∣ f) {P : Place k F}
    (hP : P.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a)) :
    ramificationIdx (RatFunc k) P = 1 := by
  have hle : ¬1 < ramificationIdx (RatFunc k) P := by
    rw [one_lt_ramificationIdx_iff_of_sq_eq h2 hf hgen hy P, hP]
    rintro (⟨h, -⟩ | ⟨q, hq, hqf, hqQ⟩)
    · exact adicOfIrreducible_ne_infty _ h
    · exact hfa (((adicOfIrreducible_eq_adicOfIrreducible_iff _ hq).mp hqQ).dvd.trans hqf)
  have := ramificationIdx_pos (RatFunc k) P
  omega

/-- Away from the branch locus, a point `(a, b)` of `y² = f(x)` has a place over `x = a` at which
`y - b` vanishes and which is not fixed by the involution `y ↦ -y`. -/
private theorem exists_smul_ne_ord_sub_pos (h2 : (2 : k) ≠ 0) {f : k[X]} (hf : Squarefree f)
    (hdeg : 0 < f.natDegree) {y : F} (hgen : (RatFunc k)⟮y⟯ = ⊤)
    (hy : y ^ 2 = algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) f)) {a b : k}
    (hb : b ≠ 0) (hab : b ^ 2 = f.eval a) :
    ∃ (σ : F ≃ₐ[RatFunc k] F) (P : Place k F),
      P.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a) ∧
        0 < P.ord (y - algebraMap k F b) ∧ σ • P ≠ P := by
  classical
  have hF : IsFunctionField k F := isFunctionField_iff_functionField.mpr inferInstance
  have hexact := fun P : Place k F ↦
    ord_sub_pos_iff_not_ord_add_pos h2 hdeg hy hb hab (P := P)
  obtain ⟨σ, hσ⟩ := TauCeti.exists_algEquiv_apply_eq_neg_of_sq_eq
    (finrank_ratFunc_eq_two_of_sq_eq hf hdeg hgen hy) hgen hy
  obtain ⟨P₀, hP₀⟩ := restrict_surjective_of_finiteDimensional (IsFunctionField.ratFunc k) hF
    (adicOfIrreducible (irreducible_X_sub_C a))
  replace hP₀ : P₀.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a) := hP₀
  obtain ⟨P, hPQ, hPD⟩ : ∃ P : Place k F,
      P.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a) ∧
        0 < P.ord (y - algebraMap k F b) := by
    by_cases h : 0 < P₀.ord (y - algebraMap k F b)
    · exact ⟨P₀, hP₀, h⟩
    · refine ⟨σ • P₀, by rw [restrict_smul, hP₀], ?_⟩
      rw [ord_smul_sub_eq_ord_add σ P₀ hσ]
      by_contra hS
      exact h ((hexact P₀ hP₀).mpr hS)
  refine ⟨σ, P, hPQ, hPD, fun h ↦ (hexact P hPQ).mp hPD ?_⟩
  rw [← ord_smul_sub_eq_ord_add σ P hσ, h]
  exact hPD

end Helpers

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
  obtain ⟨_, _⟩ := finiteDimensional_and_isSeparable_of_sq_eq h2 hf hdeg hgen hy
  obtain ⟨σ, P, hPQ, hPD, hne⟩ := exists_smul_ne_ord_sub_pos h2 hf hdeg hgen hy hb hab
  have hfa : ¬X - C a ∣ f := by
    rw [dvd_iff_isRoot, IsRoot, ← hab]
    exact pow_ne_zero 2 hb
  have he := ramificationIdx_eq_one_of_restrict_eq h2 hf hgen hy hfa hPQ
  refine ⟨P, hPQ, degree_eq_one_of_smul_ne (finrank_ratFunc_eq_two_of_sq_eq hf hdeg hgen hy)
    (degree_adicOfIrreducible_X_sub_C a) σ hPQ hne, he, ?_, hPD⟩
  have hxa : algebraMap (RatFunc k) F RatFunc.X - algebraMap k F a =
      algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) (X - C a)) := by
    rw [map_sub, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C,
      ← IsScalarTower.algebraMap_apply]
  rw [hxa]
  exact ord_algebraMap_pos_of_restrict_eq a hPQ (X_sub_C_ne_zero a) dvd_rfl

end Place

end TauCeti
