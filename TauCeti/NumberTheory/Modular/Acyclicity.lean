/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.RepresentationTheory.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Acyclicity of permutation modules of free `PSL(2, ℤ)`-sets

In `Γ = PSL(2, ℤ)` the classes of `S = (0 -1; 1 0)` and `U = T * S = (1 -1; 1 0)` satisfy
`S² = 1`, `U³ = 1` and `U * S = T`. Let `X` be a set on which `Γ` acts freely and `k[X]` its
permutation module over a ring `k`. Popa and Zagier show that no nonzero `ξ ∈ k[X]` is killed by
both `1 + S` and `1 + U + U²`; Choie and Zagier call this *acyclicity*. Freeness of the action
is Mathlib's `IsCancelSMul PSL(2, ℤ) X`.

The proof is a descent. If `ξ` is killed by both operators then `ξ = (T⁻¹ + T′⁻¹) ξ`, where
`T′ = U² * S` is the class of `(1 0; 1 1)`, so the coefficients of `ξ` satisfy
`c(x) = c(T x) + c(T′ x)`. Every point of the support of `ξ` therefore has its `T`- or its
`T′`-translate in the support. Iterating, a point of the finite support returns to itself under
the class of a product `g` of copies of `(1 1; 0 1)` and `(1 0; 1 1)` in `SL(2, ℤ)`. Such a
product has non-negative entries and is not `±1`, so its class is not `1`, contradicting
freeness.

## Main results

* `TauCeti.ModularGroup.coe_S_sq`, `TauCeti.ModularGroup.coe_T_mul_S_pow_three` and
  `TauCeti.ModularGroup.coe_T_mul_S_mul_coe_S`: the relations `S² = 1`, `U³ = 1` and `U S = T`
  in `PSL(2, ℤ)`.
* `TauCeti.ModularGroup.ker_one_add_S_inf_ker_one_add_T_mul_S_add_sq_eq_bot`: for a free
  `PSL(2, ℤ)`-set `X`, the kernels of `1 + S` and `1 + U + U²` on `k[X]` meet in `0`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105--122, arXiv:1711.00327, Section 2, Lemma 2.
* Y. J. Choie and D. Zagier, *Rational period functions for PSL(2, Z)*, Contemp. Math. 143
  (1993), 89--108.
-/

public section

open Matrix MonoidAlgebra
open scoped MatrixGroups

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-! ### Relations in `PSL(2, ℤ)` -/

/-- The class of `S` has order dividing `2` in `PSL(2, ℤ)`: in `SL(2, ℤ)`, `S² = -1`. -/
theorem coe_S_sq : ((S : SL(2, ℤ)) : PSL(2, ℤ)) ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by decide)

/-- The class of `U = T * S` has order dividing `3` in `PSL(2, ℤ)`: in `SL(2, ℤ)`,
`(T * S)³ = -1`. -/
theorem coe_T_mul_S_pow_three : ((T * S : SL(2, ℤ)) : PSL(2, ℤ)) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by decide)

/-- In `PSL(2, ℤ)`, `U * S = T` for `U = T * S`; in `SL(2, ℤ)` the product is `-T`. -/
theorem coe_T_mul_S_mul_coe_S :
    ((T * S : SL(2, ℤ)) : PSL(2, ℤ)) * (S : PSL(2, ℤ)) = (T : PSL(2, ℤ)) := by
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by decide)

/-! ### The descent -/

/-- Popa--Zagier's `T′ = (1 0; 1 1)`. -/
private def tPrime : SL(2, ℤ) :=
  ⟨!![1, 0; 1, 1], by decide⟩

/-- In `PSL(2, ℤ)`, `U² * S = T′`; in `SL(2, ℤ)` the product is `-T′`. -/
private lemma coe_T_mul_S_sq_mul_coe_S :
    ((T * S : SL(2, ℤ)) : PSL(2, ℤ)) ^ 2 * (S : PSL(2, ℤ)) = (tPrime : PSL(2, ℤ)) := by
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact Or.inr (by decide)

/-- A product of integer matrices with non-negative entries has non-negative entries. -/
private lemma nonneg_mul {g h : SL(2, ℤ)} (hg : ∀ i j, 0 ≤ g i j) (hh : ∀ i j, 0 ≤ h i j)
    (i j : Fin 2) : 0 ≤ (g * h) i j := by
  rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  exact Finset.sum_nonneg fun l _ ↦ mul_nonneg (hg i l) (hh l j)

/-- If `g` has non-negative entries and `t` is `T` or `T′`, then `t * g` is not `±1`. -/
private lemma coe_mul_ne_one {t g : SL(2, ℤ)} (ht : t = T ∨ t = tPrime)
    (hg : ∀ i j, 0 ≤ g i j) : ((t * g : SL(2, ℤ)) : PSL(2, ℤ)) ≠ 1 := by
  have h₀₀ := hg 0 0
  have h₀₁ := hg 0 1
  have h₁₀ := hg 1 0
  rw [Ne, QuotientGroup.eq_one_iff, SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  rintro (h | h) <;> obtain rfl := eq_inv_mul_iff_mul_eq.mpr h <;>
    rcases ht with rfl | rfl <;> revert h₀₀ h₀₁ h₁₀ <;> decide

/-- Let `E` and `P` be subsets of a group `G` with `1 ∈ P`, such that `e * p ∈ P` and
`e * p ≠ 1` for all `e ∈ E` and `p ∈ P`. If `G` acts freely on `X`, then a finite subset of `X`
each of whose points is moved back into it by some element of `E` is empty. -/
private lemma eq_empty_of_forall_exists_smul_mem {G X : Type*} [Group G] [MulAction G X]
    [IsCancelSMul G X] {E P : Set G} (hP : 1 ∈ P) (hE : ∀ e ∈ E, ∀ p ∈ P, e * p ∈ P ∧ e * p ≠ 1)
    {s : Finset X} (hs : ∀ x ∈ s, ∃ e ∈ E, e • x ∈ s) : s = ∅ := by
  choose! e he hes using hs
  set f : X → X := fun x ↦ e x • x
  -- every iterate of `f` stays in `s` and is the action of an element of `P`
  have hiter : ∀ m, ∀ x ∈ s, f^[m] x ∈ s ∧ ∃ p ∈ P, f^[m] x = p • x := by
    intro m
    induction m with
    | zero => exact fun x hx ↦ ⟨hx, 1, hP, by simp⟩
    | succ m ih =>
      intro x hx
      obtain ⟨hmem, p, hp, hpx⟩ := ih x hx
      rw [Function.iterate_succ_apply']
      exact ⟨hes _ hmem, e (f^[m] x) * p, (hE _ (he _ hmem) p hp).1, by rw [mul_smul, ← hpx]⟩
  -- by pigeonhole some `y = f^[i] x` returns to itself, under an element `e * p ≠ 1`
  refine Finset.eq_empty_of_forall_notMem fun x hx ↦ ?_
  obtain ⟨i, j, hij, heq⟩ := s.finite_toSet.exists_lt_map_eq_of_forall_mem
    (f := fun m ↦ f^[m] x) fun m ↦ (hiter m x hx).1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
  obtain ⟨hmem, p, hp, hpx⟩ := hiter m _ (hiter i x hx).1
  rw [show i + m + 1 = m + 1 + i by omega, Function.iterate_add_apply,
    Function.iterate_succ_apply', hpx] at heq
  change _ = e (p • _) • p • _ at heq
  rw [smul_smul] at heq
  exact (hE _ (he _ (hpx ▸ hmem)) p hp).2 (IsCancelSMul.eq_one_of_smul heq.symm)

/-- On a free `PSL(2, ℤ)`-set `X`, an element of `k[X]` whose coefficients satisfy
`c(x) = c(T x) + c(T′ x)` is zero. -/
private lemma eq_zero_of_coeff_eq_add {k X : Type*} [Ring k] [MulAction PSL(2, ℤ) X]
    [IsCancelSMul PSL(2, ℤ) X] {ξ : k[X]}
    (h : ∀ x, ξ.coeff x =
      ξ.coeff ((T : PSL(2, ℤ)) • x) + ξ.coeff ((tPrime : PSL(2, ℤ)) • x)) : ξ = 0 := by
  have h1 : ∀ i j, 0 ≤ (1 : SL(2, ℤ)) i j := fun i j ↦ by fin_cases i <;> fin_cases j <;> decide
  have hT : ∀ i j, 0 ≤ (T : SL(2, ℤ)) i j := fun i j ↦ by fin_cases i <;> fin_cases j <;> decide
  have hT' : ∀ i j, 0 ≤ tPrime i j := fun i j ↦ by fin_cases i <;> fin_cases j <;> decide
  have hs := eq_empty_of_forall_exists_smul_mem (E := {(T : PSL(2, ℤ)), (tPrime : PSL(2, ℤ))})
    (P := (↑) '' {g : SL(2, ℤ) | ∀ i j, 0 ≤ g i j}) ⟨1, h1, rfl⟩ ?_ (s := ξ.coeff.support)
    fun x hx ↦ ?_
  · rwa [Finsupp.support_eq_empty, coeff_eq_zero] at hs
  · rintro _ (rfl | rfl) _ ⟨g, hg, rfl⟩ <;> rw [← QuotientGroup.mk_mul]
    · exact ⟨⟨_, nonneg_mul hT hg, rfl⟩, coe_mul_ne_one (Or.inl rfl) hg⟩
    · exact ⟨⟨_, nonneg_mul hT' hg, rfl⟩, coe_mul_ne_one (Or.inr rfl) hg⟩
  · rw [Finsupp.mem_support_iff, h] at hx
    by_cases hTx : ξ.coeff ((T : PSL(2, ℤ)) • x) = 0
    · exact ⟨_, Or.inr rfl, Finsupp.mem_support_iff.mpr fun h' ↦ hx (by rw [hTx, h', add_zero])⟩
    · exact ⟨_, Or.inl rfl, Finsupp.mem_support_iff.mpr hTx⟩

/-- **Acyclicity** (Popa--Zagier, Lemma 2): if `PSL(2, ℤ)` acts freely on `X`, then on the
permutation module `k[X]` the kernels of `1 + S` and `1 + U + U²`, with `U = T * S`, meet in `0`.

Freeness is needed: on `k[ℙ¹(ℚ)]`, where `T` fixes `∞`, the element `[0] - [∞]` lies in both
kernels, since `S` swaps `0` and `∞` while `U` permutes `0`, `∞`, `1` cyclically. -/
theorem ker_one_add_S_inf_ker_one_add_T_mul_S_add_sq_eq_bot {k X : Type*} [Ring k]
    [MulAction PSL(2, ℤ) X] [IsCancelSMul PSL(2, ℤ) X] :
    LinearMap.ker (1 + Representation.ofMulAction k PSL(2, ℤ) X (S : PSL(2, ℤ))) ⊓
      LinearMap.ker (1 + Representation.ofMulAction k PSL(2, ℤ) X ((T * S : SL(2, ℤ)) : PSL(2, ℤ)) +
        Representation.ofMulAction k PSL(2, ℤ) X ((T * S : SL(2, ℤ)) : PSL(2, ℤ)) ^ 2) = ⊥ := by
  set u : PSL(2, ℤ) := ((T * S : SL(2, ℤ)) : PSL(2, ℤ))
  have hs : (S : PSL(2, ℤ))⁻¹ = S := inv_eq_of_mul_eq_one_right (by rw [← sq, coe_S_sq])
  have hu : u⁻¹ = u ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', coe_T_mul_S_pow_three])
  have hu2 : (u ^ 2)⁻¹ = u := by rw [← hu, inv_inv]
  rw [eq_bot_iff]
  intro ξ hξ
  obtain ⟨h₁, h₂⟩ := Submodule.mem_inf.mp hξ
  rw [LinearMap.mem_ker] at h₁ h₂
  rw [← map_pow] at h₂
  refine (Submodule.mem_bot k).mpr (eq_zero_of_coeff_eq_add fun x ↦ ?_)
  have e₁ := congrArg (fun η ↦ η.coeff x) h₁
  have e₂ := congrArg (fun η ↦ η.coeff ((S : PSL(2, ℤ)) • x)) h₂
  simp only [LinearMap.add_apply, Module.End.one_apply, coeff_add, Finsupp.add_apply,
    Representation.coeff_ofMulAction, hs, hu, hu2, coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply] at e₁ e₂
  rw [smul_smul, smul_smul, coe_T_mul_S_mul_coe_S, coe_T_mul_S_sq_mul_coe_S] at e₂
  rw [eq_neg_of_add_eq_zero_left e₁,
    neg_eq_of_add_eq_zero_right ((add_assoc _ _ _).symm.trans e₂), add_comm]

end TauCeti.ModularGroup
