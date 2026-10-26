/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Algebra.Polynomial.Degree.Operations
public import TauCeti.RingTheory.MvPolynomial.Homogeneous

import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.Tactic.LinearCombination

/-!
# Binary homogenization of a product of linear factors

Mathlib's `Polynomial.homogenize p n` is the binary form `Y ^ n p(X / Y)` of degree `n`, with
`X` the variable `0` and `Y` the variable `1`. This file computes it on a product of linear
factors: the homogenization of `∏ (X - a)` is `∏ (X - a Y)`. Consequently, a polynomial with as
many roots as its degree, `p = c ∏ (X - a)`, has degree-`(natDegree p)` homogenization
`F(x, y) = c ∏ (x - a y)` at *every* point `(x, y)`, including the points with `y = 0`.

More generally, the homogenization of degree `n ≥ natDegree p` of such a `p` is
`c X₁ ^ (n - natDegree p) ∏ (X₀ - a X₁)`; since every binary form `F` of degree `n` is the
homogenization of its dehomogenization `F(X, 1)`, of degree at most `n`, this factors binary forms
over an algebraically closed field into linear forms. If `F` has no squared linear factor, then
`X₁` occurs at most once and the roots of `F(X, 1)` are simple, so the linear factors are pairwise
non-proportional. Conversely, the homogenization of degree `natDegree p` of a squarefree
polynomial `p` has no squared linear factor.

This factorisation is the starting point of Liouville- and Roth-type lower bounds for binary forms
at integer points.

## Main results

* `Polynomial.homogenize_multiset_prod_X_sub_C`: `homogenize (∏ (X - a)) (card s) = ∏ (X - a Y)`.
* `Polynomial.eval_homogenize_natDegree_of_card_roots`: if `p` has `natDegree p` roots, then
  `F(x) = leadingCoeff p * ∏_{a ∈ roots p} (x 0 - a x 1)`.
* `Polynomial.homogenize_eq_C_mul_X_pow_mul_prod`: if `p` has `natDegree p` roots and
  `natDegree p ≤ n`, then its homogenization of degree `n` is
  `leadingCoeff p * X₁ ^ (n - natDegree p) * ∏ (X₀ - a X₁)`.
* `Polynomial.sub_natDegree_le_one_of_not_sq_dvd_homogenize`,
  `Polynomial.nodup_roots_of_not_sq_dvd_homogenize`: if neither `X₁ ^ 2` nor any
  `(X₀ - a X₁) ^ 2` divides the homogenization of degree `n ≥ natDegree p`, then
  `n ≤ natDegree p + 1` and the roots of `p` are simple.
* `Squarefree.not_sq_dvd_homogenize_natDegree`: conversely, the homogenization of degree
  `natDegree p` of a squarefree polynomial `p` has no squared linear factor.
* `MvPolynomial.aeval_X_one_map`: the dehomogenization `F(X, 1)` commutes with mapping the
  coefficients along a ring homomorphism.
* `MvPolynomial.IsHomogeneous.exists_linear_factors`: a nonzero binary form of degree `d` with no
  squared linear factor, whose dehomogenization splits, is `a ∏_{ℓ ∈ T} (ℓ.1 X₀ + ℓ.2 X₁)` for `d`
  pairwise non-proportional linear forms.
* `MvPolynomial.IsHomogeneous.mem_span_X_one_pow_of_aeval_eq_smul`: over a domain, a binary form
  of degree `d` that is semi-invariant under the universal substitution `x ↦ x - t y` is a
  multiple of `X₁ ^ d`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The homogenization of `∏_{a ∈ s} (X - a)` in degree `card s` is the product of the linear
binary forms `X₀ - a X₁`. -/
theorem homogenize_multiset_prod_X_sub_C (s : Multiset R) :
    (s.map fun a ↦ X - C a).prod.homogenize (Multiset.card s) =
      (s.map fun a ↦ MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm,
      homogenize_mul _ _ (natDegree_X_sub_C_le a) (natDegree_multiset_prod_X_sub_C_le s), ih,
      Multiset.map_cons, Multiset.prod_cons]
    congr 1
    rw [homogenize_sub, homogenize_X one_ne_zero, homogenize_C]
    simp

/-- The homogenization of `p` of degree `n ≥ natDegree p` is `X₁ ^ (n - natDegree p)` times its
homogenization of degree `natDegree p`. -/
theorem homogenize_eq_X_pow_mul_homogenize_natDegree {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    p.homogenize n = MvPolynomial.X 1 ^ (n - p.natDegree) * p.homogenize p.natDegree := by
  have h := homogenize_mul p 1 le_rfl (natDegree_one.trans_le (Nat.zero_le (n - p.natDegree)))
  rw [mul_one, Nat.add_sub_cancel' hn, homogenize_one] at h
  rw [h, mul_comm]

/-- If `p` has as many roots as its degree, its homogenization of degree `n ≥ natDegree p` is
the binary form `leadingCoeff p * X₁ ^ (n - natDegree p) * ∏_{a ∈ roots p} (X₀ - a X₁)`. -/
theorem homogenize_eq_C_mul_X_pow_mul_prod [IsDomain R] {p : R[X]} {n : ℕ}
    (hn : p.natDegree ≤ n) (hroots : Multiset.card p.roots = p.natDegree) :
    p.homogenize n = MvPolynomial.C p.leadingCoeff * MvPolynomial.X 1 ^ (n - p.natDegree) *
      (p.roots.map fun a ↦ MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod := by
  have hp := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [homogenize_eq_X_pow_mul_homogenize_natDegree hn, mul_right_comm _ (MvPolynomial.X 1 ^ _),
    mul_comm (MvPolynomial.X 1 ^ _)]
  congr 1
  calc p.homogenize p.natDegree
      = (C p.leadingCoeff * (p.roots.map fun a ↦ X - C a).prod).homogenize
          (Multiset.card p.roots) := by rw [hp, hroots]
    _ = _ := by rw [homogenize_C_mul, homogenize_multiset_prod_X_sub_C, MvPolynomial.C_mul']

/-- If `p` has as many roots as its degree, its homogenization `F` of degree `natDegree p`
factors at every point as `F(x) = leadingCoeff p * ∏_{a ∈ roots p} (x 0 - a x 1)`. -/
theorem eval_homogenize_natDegree_of_card_roots [IsDomain R] {p : R[X]}
    (hroots : Multiset.card p.roots = p.natDegree) (x : Fin 2 → R) :
    MvPolynomial.eval x (p.homogenize p.natDegree) =
      p.leadingCoeff * (p.roots.map fun a ↦ x 0 - a * x 1).prod := by
  rw [homogenize_eq_C_mul_X_pow_mul_prod le_rfl hroots, Nat.sub_self, pow_zero, mul_one]
  simp [map_multiset_prod, Multiset.map_map]

/-- If `X₁ ^ 2` does not divide the homogenization of `p` of degree `n ≥ natDegree p`, then
`n ≤ natDegree p + 1`. -/
theorem sub_natDegree_le_one_of_not_sq_dvd_homogenize {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n)
    (h : ¬MvPolynomial.X 1 ^ 2 ∣ p.homogenize n) : n - p.natDegree ≤ 1 := by
  by_contra! hk
  rw [homogenize_eq_X_pow_mul_homogenize_natDegree hn] at h
  exact h ((pow_dvd_pow _ hk).mul_right _)

/-- If no square `(X₀ - a X₁) ^ 2` divides the homogenization of `p` of degree `n ≥ natDegree p`,
then the roots of `p` are simple. -/
theorem nodup_roots_of_not_sq_dvd_homogenize [IsDomain R] {p : R[X]} {n : ℕ}
    (hn : p.natDegree ≤ n)
    (h : ∀ a, ¬(MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1) ^ 2 ∣ p.homogenize n) :
    p.roots.Nodup := by
  rw [Multiset.nodup_iff_ne_cons_cons]
  rintro a t ht
  have hp : p ≠ 0 := fun hp ↦ by simp [hp] at ht
  set s : Multiset R := a ::ₘ a ::ₘ 0
  have hs : s ≤ p.roots :=
    ht ▸ Multiset.cons_le_cons _ (Multiset.cons_le_cons _ (Multiset.zero_le _))
  obtain ⟨q, hq⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hp s).2 hs
  have hq₀ : q ≠ 0 := by rintro rfl; exact hp (by rw [hq, mul_zero])
  have hdeg : Multiset.card s + q.natDegree = p.natDegree := by
    rw [hq, natDegree_mul (Monic.ne_zero (monic_multiset_prod_of_monic _ _ fun a _ ↦
      monic_X_sub_C a)) hq₀, natDegree_multiset_prod_X_sub_C_eq_card]
  refine h a ⟨q.homogenize (n - Multiset.card s), ?_⟩
  rw [hq, ← Nat.add_sub_cancel' (show Multiset.card s ≤ n by omega),
    homogenize_mul _ _ (natDegree_multiset_prod_X_sub_C_le s) (by omega),
    homogenize_multiset_prod_X_sub_C]
  simp [s, sq]

/-- The homogenization of degree `natDegree p` of a squarefree polynomial `p` over a domain has no
squared linear factor `(a X₀ + b X₁) ^ 2`. -/
theorem _root_.Squarefree.not_sq_dvd_homogenize_natDegree [IsDomain R] {p : R[X]}
    (hp : Squarefree p) {a b : R} :
    ¬(MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1) ^ 2 ∣
      p.homogenize p.natDegree := by
  intro h
  rcases eq_or_ne a 0 with rfl | ha
  · -- `X₁` would divide the homogenization, whose `X₀ ^ natDegree p` coefficient is the leading
    -- coefficient of `p`.
    obtain ⟨q, hq⟩ := (dvd_pow_self _ two_ne_zero).trans h
    have hc := congr_arg
      (fun P : MvPolynomial (Fin 2) R ↦ P.coeff (Finsupp.single 0 p.natDegree)) hq
    classical
    simp only [coeff_homogenize, map_zero, zero_mul, zero_add, mul_assoc,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_mul'] at hc
    simp [hp.ne_zero] at hc
  · -- Setting `X₁ = 1` gives `(a X + b) ^ 2 ∣ p`, so `a X + b` would be a unit.
    obtain ⟨q, hq⟩ := h
    have hd := congr_arg (MvPolynomial.aeval ![(X : R[X]), 1]) hq
    rw [aeval_homogenize_X_one _ le_rfl] at hd
    simp only [map_pow, map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, algebraMap_eq] at hd
    have hu := natDegree_eq_zero_of_isUnit (hp _ ⟨_, by rw [hd, sq]⟩)
    rw [natDegree_linear ha] at hu
    exact one_ne_zero hu

end Polynomial

namespace MvPolynomial

open Finset

/-- The dehomogenization `F(X, 1)` of a binary form commutes with mapping the coefficients along a
ring homomorphism `φ`. -/
theorem aeval_X_one_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (F : MvPolynomial (Fin 2) R) :
    aeval ![Polynomial.X, 1] (F.map φ) = (aeval ![Polynomial.X, 1] F : Polynomial R).map φ := by
  rw [← Polynomial.coe_mapRingHom, map_aeval, aeval_def, eval₂_map]
  congr 1
  · ext n
    simp
  · funext i
    fin_cases i <;> simp

/-- **Splitting of binary forms.** Let `F ≠ 0` be a binary form of degree `d` over a domain, with
no squared linear factor, whose dehomogenization `F(X, 1)` has as many roots as its degree (for
instance, over an algebraically closed field). Then `F = a ∏_{ℓ ∈ T} (ℓ.1 X₀ + ℓ.2 X₁)` with
`a ≠ 0` and `d` pairwise non-proportional linear forms, each either `X₁` or `X₀ - α X₁` with `α`
a root of `F(X, 1)`. -/
theorem IsHomogeneous.exists_linear_factors {R : Type*} [CommRing R] [IsDomain R]
    {F : MvPolynomial (Fin 2) R} {d : ℕ} (hF : F.IsHomogeneous d) (hF₀ : F ≠ 0)
    (hroots : Multiset.card (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).roots =
      (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).natDegree)
    (hsq : ∀ a b : R, (a, b) ≠ (0, 0) → ¬(C a * X 0 + C b * X 1) ^ 2 ∣ F) :
    ∃ a : R, a ≠ 0 ∧ ∃ T : Finset (R × R), #T = d ∧
      (T : Set (R × R)).Pairwise (fun ℓ ℓ' ↦ ℓ.1 * ℓ'.2 - ℓ.2 * ℓ'.1 ≠ 0) ∧
      (∀ ℓ ∈ T, ℓ = (0, 1) ∨
        ∃ α ∈ (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).roots, ℓ = (1, -α)) ∧
      F = C a * ∏ ℓ ∈ T, (C ℓ.1 * X 0 + C ℓ.2 * X 1) := by
  classical
  -- `F = g.homogenize d` for the dehomogenization `g = F(X, 1)`.
  set g : Polynomial R := MvPolynomial.aeval ![Polynomial.X, 1] F
  have hgd : g.natDegree ≤ d := hF.natDegree_aeval_le fun i ↦ by fin_cases i <;> simp
  have hG : g.homogenize d = F := Polynomial.homogenize_eq_of_isHomogeneous hF rfl
  have hg₀ : g ≠ 0 := fun hg ↦ hF₀ (by rw [← hG, hg, Polynomial.homogenize_zero])
  -- No squared linear factor: `X₁ ^ 2 ∤ F` gives `k ≤ 1`, and `(X₀ - α X₁) ^ 2 ∤ F` gives
  -- simple roots.
  have hk := g.sub_natDegree_le_one_of_not_sq_dvd_homogenize hgd <| by
    simpa [hG] using hsq 0 1 (by simp)
  have hnodup := g.nodup_roots_of_not_sq_dvd_homogenize hgd fun α ↦ by
    have e : C 1 * X 0 + C (-α) * X 1 = (X 0 - C α * X 1 : MvPolynomial (Fin 2) R) := by
      rw [map_one, map_neg]
      ring
    rw [hG, ← e]
    exact hsq 1 (-α) (by simp)
  have hfac := g.homogenize_eq_C_mul_X_pow_mul_prod hgd hroots
  rw [hG] at hfac
  have hdk : g.natDegree + (d - g.natDegree) = d := Nat.add_sub_cancel' hgd
  generalize d - g.natDegree = k at hfac hdk hk
  -- The linear forms `X₀ - α X₁` for the roots `α`, and `k` copies of `X₁`.
  set s : Multiset (R × R) := g.roots.map (fun α ↦ ((1 : R), -α)) + Multiset.replicate k (0, 1)
  have hmem : ∀ ℓ ∈ s, (∃ α ∈ g.roots, ℓ = (1, -α)) ∨ ℓ = (0, 1) := fun ℓ hℓ ↦ by
    rcases Multiset.mem_add.1 hℓ with h | h
    · obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 h
      exact Or.inl ⟨α, hα, rfl⟩
    · exact Or.inr (Multiset.eq_of_mem_replicate h)
  have hs : s.Nodup := by
    refine Multiset.nodup_add.2 ⟨hnodup.map fun α β h ↦ neg_injective (Prod.ext_iff.1 h).2,
      ?_, Multiset.disjoint_left.2 fun h1 h2 ↦ ?_⟩
    · obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      all_goals simp
    · obtain ⟨α, -, rfl⟩ := Multiset.mem_map.1 h1
      exact one_ne_zero (Prod.ext_iff.1 (Multiset.eq_of_mem_replicate h2)).1
  set T : Finset (R × R) := ⟨s, hs⟩
  refine ⟨g.leadingCoeff, Polynomial.leadingCoeff_ne_zero.2 hg₀, T, ?_, ?_, ?_, ?_⟩
  · simp [T, s, hroots, hdk]
  · intro ℓ hℓ ℓ' hℓ' hne
    rcases hmem ℓ hℓ with ⟨α, -, rfl⟩ | rfl <;> rcases hmem ℓ' hℓ' with ⟨β, -, rfl⟩ | rfl
    · intro h
      obtain rfl : α = β := by linear_combination h
      exact hne rfl
    all_goals simp_all
  · intro ℓ hℓ
    rcases hmem ℓ hℓ with ⟨α, hα, rfl⟩ | rfl
    · exact Or.inr ⟨α, hα, rfl⟩
    · exact Or.inl rfl
  · rw [hfac, Finset.prod_eq_multiset_prod]
    simp only [T, s, Multiset.map_add, Multiset.prod_add, Multiset.map_map,
      Multiset.map_replicate, Multiset.prod_replicate, Function.comp_def]
    simp only [map_one, one_mul, map_zero, zero_mul, zero_add, map_neg, neg_mul,
      ← sub_eq_add_neg]
    ring


open scoped Polynomial in
/-- **Binary forms semi-invariant under `x ↦ x - t y` are multiples of `yᵈ`.** Over a domain, if a
binary form `f` of degree `d` satisfies `f(x - t y, y) = c f(x, y)` in `R[t][x, y]` for some
`c ∈ R[t]`, then `f` is a multiple of `X₁ ^ d`. -/
theorem IsHomogeneous.mem_span_X_one_pow_of_aeval_eq_smul {R : Type*} [CommRing R] [IsDomain R]
    {f : MvPolynomial (Fin 2) R} {d : ℕ} (hf : f.IsHomogeneous d) (c : R[X])
    (h : MvPolynomial.aeval ![X 0 - C Polynomial.X * X 1, X 1] f = c • f.map (algebraMap R R[X])) :
    f ∈ R ∙ (X 1 ^ d : MvPolynomial (Fin 2) R) := by
  -- The dehomogenization `p = f(x, 1)` and the value `a = f(0, 1)`.
  set p : R[X] := MvPolynomial.aeval ![(Polynomial.X : R[X]), 1] f with hp
  set a : R := MvPolynomial.aeval ![(0 : R), 1] f with ha
  -- Evaluating the semi-invariance at a point `(x, y)` gives `f(x - t y, y) = c f(x, y)`.
  have ev (x y : R[X]) : MvPolynomial.aeval ![x - Polynomial.X * y, y] f =
      c * MvPolynomial.aeval ![x, y] f := by
    have e := congrArg (MvPolynomial.aeval ![x, y]) h
    rw [map_smul, smul_eq_mul, aeval_map_algebraMap, ← AlgHom.coe_restrictScalars' (R := R),
      comp_aeval_apply] at e
    convert e using 3
    ext i; fin_cases i <;> simp
  have hC : MvPolynomial.aeval ![(0 : R[X]), 1] f = Polynomial.C a := by
    rw [ha, ← Polynomial.algebraMap_eq, ← aeval_algebraMap_apply]
    congr 1; ext i; fin_cases i <;> simp
  -- Evaluate at `(x, y) = (t, 1)` and at `(x, y) = (0, 1)`.
  have h1 : Polynomial.C a = c * p := by simpa [hC] using ev Polynomial.X 1
  have h2 : Polynomial.aeval (-Polynomial.X) p = c * Polynomial.C a := by
    rw [hp, comp_aeval_apply, ← hC, ← ev]
    congr 1; ext i; fin_cases i <;> simp
  have hdeg : p.natDegree = 0 := by
    rcases eq_or_ne p 0 with hp0 | hp0
    · rw [hp0, Polynomial.natDegree_zero]
    rcases eq_or_ne c 0 with hc0 | hc0
    · rw [hc0, zero_mul, ← Polynomial.comp_eq_aeval, Polynomial.comp_eq_zero_iff] at h2
      rcases h2 with h2 | ⟨-, h2⟩
      · exact absurd h2 hp0
      · have := congrArg Polynomial.natDegree h2
        simp at this
    · have := congrArg Polynomial.natDegree h1
      rw [Polynomial.natDegree_C, Polynomial.natDegree_mul hc0 hp0] at this
      omega
  -- `f` is the homogenization of its dehomogenization `p`, which is constant.
  have hf' : f = C (p.coeff 0) * X 1 ^ d := by
    rw [← Polynomial.homogenize_C, ← Polynomial.eq_C_of_natDegree_eq_zero hdeg,
      Polynomial.homogenize_eq_of_isHomogeneous hf hp.symm]
  exact Submodule.mem_span_singleton.mpr ⟨p.coeff 0, by rw [hf', smul_eq_C_mul]⟩

end MvPolynomial
