/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import TauCeti.Algebra.Polynomial.Bivariate

/-!
# Bivariate Schwartz–Zippel zero-count bound on planar grids

Given two bivariate linear polynomials `L₁, L₂ : MvPolynomial (Fin 2) K` over a field `K` whose
bivariate substitution `aevalAeval L₂ L₁ : K[X][X] →ₐ[K] MvPolynomial (Fin 2) K` is injective, any
nonzero bivariate polynomial `H : K[X][X]` vanishes at most
`#S * (H.natDegree + (Bivariate.swap H).natDegree)` times on the grid `S × S`.

This specializes Mathlib's multivariate `MvPolynomial.schwartz_zippel_totalDegree` to bivariate
polynomials via `Polynomial.totalDegree_aevalAeval_le` and `Polynomial.eval_aevalAeval`.

## Main results

* `Polynomial.card_grid_eval_eq_zero_le`: zero-count bound on `S × S` for `H` composed with
  `(L₂, L₁)` when `L₁.totalDegree ≤ 1`, `L₂.totalDegree ≤ 1`, and `aevalAeval L₂ L₁` is
  injective.
-/

public section

open scoped Finset Polynomial.Bivariate

namespace Polynomial

/-- **Bivariate Schwartz–Zippel zero-count bound.** For any finite subset `S` of a field `K` and
degree-at-most-one coordinate polynomials `L₁, L₂ : MvPolynomial (Fin 2) K` with injective
substitution `aevalAeval L₂ L₁`, every nonzero `H : K[X][X]` vanishes at most
`#S * (H.natDegree + (Bivariate.swap H).natDegree)` points of `S × S` under
`(x, y) ↦ (L₂(x, y), L₁(x, y))`. -/
theorem card_grid_eval_eq_zero_le {K : Type*} [Field K] [DecidableEq K]
    {S : Finset K} {L₁ L₂ : MvPolynomial (Fin 2) K}
    (hL₁ : L₁.totalDegree ≤ 1) (hL₂ : L₂.totalDegree ≤ 1)
    (hinj_hom : Function.Injective (aevalAeval L₂ L₁ : K[X][X] →ₐ[K] MvPolynomial (Fin 2) K))
    {H : K[X][X]} (hH : H ≠ 0) :
    #{p : ↥S × ↥S |
        (H.map (evalRingHom (MvPolynomial.eval ![p.1.val, p.2.val] L₂))).eval
          (MvPolynomial.eval ![p.1.val, p.2.val] L₁) = 0} ≤
      S.card * (H.natDegree + (Bivariate.swap H).natDegree) := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp
  have hS0 : 0 < S.card := hSne.card_pos
  set P : MvPolynomial (Fin 2) K := aevalAeval L₂ L₁ H
  have hP0 : P ≠ 0 := fun h ↦ hH (hinj_hom (h.trans (map_zero _).symm))
  let emb : ↥S × ↥S → Fin 2 → K := fun p ↦ ![p.1.val, p.2.val]
  have hemb_inj : Function.Injective emb := fun p q h ↦
    Prod.ext (Subtype.ext (congrFun h 0)) (Subtype.ext (congrFun h 1))
  have hsub : (Finset.univ.filter fun p : ↥S × ↥S ↦
        (H.map (evalRingHom (MvPolynomial.eval (emb p) L₂))).eval
          (MvPolynomial.eval (emb p) L₁) = 0).image emb ⊆
      (Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun f ↦ MvPolynomial.eval f P = 0 := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨p, hp, rfl⟩
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨Fintype.mem_piFinset.mpr fun i ↦ by
      fin_cases i <;> simp [emb, p.1.property, p.2.property], ?_⟩
    rw [eval_aevalAeval, ← map_evalRingHom_eval]
    exact hp.2
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hP0 S
  have hcard_le : #{f ∈ Fintype.piFinset fun _ : Fin 2 ↦ S | MvPolynomial.eval f P = 0} ≤
      S.card * P.totalDegree := by
    have hS_pos : (0 : NNRat) < S.card := mod_cast hS0
    have hmul := mul_le_mul_of_nonneg_right hsz (pow_pos hS_pos 2).le
    have hrhs : (P.totalDegree : NNRat) / S.card * (S.card : NNRat) ^ 2 =
        S.card * P.totalDegree := by
      rw [sq, ← mul_assoc, div_mul_cancel₀ _ hS_pos.ne', mul_comm]
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hS_pos.ne'), hrhs] at hmul
    exact_mod_cast hmul
  calc #{p : ↥S × ↥S |
          (H.map (evalRingHom (MvPolynomial.eval (emb p) L₂))).eval
            (MvPolynomial.eval (emb p) L₁) = 0}
      = ((Finset.univ.filter fun p : ↥S × ↥S ↦
          (H.map (evalRingHom (MvPolynomial.eval (emb p) L₂))).eval
            (MvPolynomial.eval (emb p) L₁) = 0).image emb).card :=
        (Finset.card_image_of_injective _ hemb_inj).symm
    _ ≤ #{f ∈ Fintype.piFinset fun _ : Fin 2 ↦ S | MvPolynomial.eval f P = 0} :=
        Finset.card_le_card hsub
    _ ≤ S.card * P.totalDegree := hcard_le
    _ ≤ S.card * (H.natDegree + (Bivariate.swap H).natDegree) := by
        refine Nat.mul_le_mul_left _ ((totalDegree_aevalAeval_le L₂ L₁ H).trans ?_)
        have h1 := Nat.mul_le_mul_left (Bivariate.swap H).natDegree hL₂
        have h2 := Nat.mul_le_mul_left H.natDegree hL₁
        omega

end Polynomial
