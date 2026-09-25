/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.RepresentationTheory.Basic
import TauCeti.GroupTheory.GroupAction.Free
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.Modular.Relations

/-!
# Acyclicity of permutation modules of free `PSL(2, ℤ)`-sets

In `Γ = PSL(2, ℤ)` the classes of `S = (0 -1; 1 0)` and `U = T * S = (1 -1; 1 0)` satisfy
`S² = 1`, `U³ = 1` and `U * S = T`; these relations are in
`TauCeti.NumberTheory.Modular.Relations`, where `U` is written `(T : PSL(2, ℤ)) * S`. Let `X` be
a set on which `Γ` acts freely and `k[X]` its permutation module over a ring `k`. Then no nonzero
`ξ ∈ k[X]` is killed by both `1 + S` and `1 + U + U²`; Choie and Zagier call this *acyclicity*.
Popa and Zagier prove it for `ℚ[ℳ]`, where `ℳ` is the set of integral matrices of positive
determinant modulo `±1`; their descent applies to any free `X` and any ring `k`. Freeness of the
action is Mathlib's `IsCancelSMul PSL(2, ℤ) X`.

The proof is a descent. If `ξ` is killed by both operators then `ξ = (T⁻¹ + T′⁻¹) ξ`, where
`T′ = U² * S` is the class of `(1 0; 1 1)`, so the coefficients of `ξ` satisfy
`c(x) = c(T x) + c(T′ x)`. Every point of the support of `ξ` therefore has its `T`- or its
`T′`-translate in the support. Iterating, a point of the finite support returns to itself under
the class of a product `g` of copies of `(1 1; 0 1)` and `(1 0; 1 1)` in `SL(2, ℤ)`. Such a
product has non-negative entries and is not `±1`, so its class is not `1`, contradicting
freeness.

## Main results

* `TauCeti.ModularGroup.disjoint_ker_one_add_S_ker_one_add_T_mul_S_add_sq`: for a free
  `PSL(2, ℤ)`-set `X`, the kernels of `1 + S` and `1 + U + U²` on `k[X]` are disjoint.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105--122, arXiv:1711.00327, Section 3, Lemma 2.
* Y. J. Choie and D. Zagier, *Rational period functions for PSL(2, Z)*, Contemp. Math. 143
  (1993), 89--108.
-/

public section

open Matrix MonoidAlgebra
open scoped MatrixGroups

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-! ### The descent

`TauCeti.ModularGroup.tPrime` is Popa--Zagier's `T′ = (1 0; 1 1)`, whose class in `PSL(2, ℤ)` is
`U² * S`. The descent is `TauCeti.MulAction.eq_empty_of_forall_exists_smul_mem` with
`E = {T, T′}` and `P` the set of classes of the matrices in `SL(2, ℤ)` with non-negative entries.
-/

private lemma coe_mul_ne_one {t g : SL(2, ℤ)} (ht : t ∈ ({T, tPrime} : Set SL(2, ℤ)))
    (hg : ∀ i j, 0 ≤ g i j) : ((t * g : SL(2, ℤ)) : PSL(2, ℤ)) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff, SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  rintro (h | h) <;> obtain rfl := eq_inv_mul_iff_mul_eq.mpr h <;> rcases ht with rfl | rfl <;>
    revert hg <;> decide +kernel

private lemma eq_zero_of_coeff_eq_add {k X : Type*} [Ring k] [MulAction PSL(2, ℤ) X]
    [IsCancelSMul PSL(2, ℤ) X] {ξ : k[X]} (h : ∀ x, ξ.coeff x = ξ.coeff ((T : PSL(2, ℤ)) • x) +
      ξ.coeff ((tPrime : PSL(2, ℤ)) • x)) : ξ = 0 := by
  have hE : ∀ t ∈ ({1, T, tPrime} : Set SL(2, ℤ)), ∀ i j, 0 ≤ t i j := by
    rintro _ (rfl | rfl | rfl) i j <;> fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T]
  rw [← coeff_eq_zero, ← Finsupp.support_eq_empty]
  refine MulAction.eq_empty_of_forall_exists_smul_mem (G := PSL(2, ℤ)) (E := (↑) '' {T, tPrime})
    (P := (↑) '' {g : SL(2, ℤ) | ∀ i j, 0 ≤ g i j}) ⟨1, hE 1 (.inl rfl), rfl⟩ ?_ fun x hx ↦ ?_
  · rintro _ ⟨t, ht, rfl⟩ _ ⟨g, hg, rfl⟩
    rw [← QuotientGroup.mk_mul]
    refine ⟨⟨_, fun i j ↦ ?_, rfl⟩, coe_mul_ne_one ht hg⟩
    rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ ↦ mul_nonneg (hE t (.inr ht) i l) (hg l j)
  · rw [Finsupp.mem_support_iff, h] at hx
    by_cases hTx : ξ.coeff ((T : PSL(2, ℤ)) • x) = 0
    · refine ⟨_, ⟨tPrime, .inr rfl, rfl⟩, Finsupp.mem_support_iff.mpr fun h' ↦ hx ?_⟩
      rw [hTx, h', add_zero]
    · exact ⟨_, ⟨T, .inl rfl, rfl⟩, Finsupp.mem_support_iff.mpr hTx⟩

/-- **Acyclicity** (Popa--Zagier, Lemma 2): if `PSL(2, ℤ)` acts freely on `X`, then on the
permutation module `k[X]` the kernels of `1 + S` and `1 + U + U²`, with `U = T * S`, are
disjoint: their intersection is `0`.

Freeness is needed: on `k[ℙ¹(ℚ)]`, where `T` fixes `∞`, the element `[0] - [∞]` lies in both
kernels, since `S` swaps `0` and `∞` while `U` permutes `0`, `∞`, `1` cyclically. -/
theorem disjoint_ker_one_add_S_ker_one_add_T_mul_S_add_sq {k X : Type*} [Ring k]
    [MulAction PSL(2, ℤ) X] [IsCancelSMul PSL(2, ℤ) X] :
    Disjoint (LinearMap.ker (1 + Representation.ofMulAction k PSL(2, ℤ) X (S : PSL(2, ℤ))))
      (LinearMap.ker
        (1 + Representation.ofMulAction k PSL(2, ℤ) X ((T : PSL(2, ℤ)) * S) +
          Representation.ofMulAction k PSL(2, ℤ) X ((T : PSL(2, ℤ)) * S) ^ 2)) := by
  refine Submodule.disjoint_def.mpr fun ξ h₁ h₂ ↦ eq_zero_of_coeff_eq_add fun x ↦ ?_
  -- the coefficients of `(1 + S) ξ = 0` at `x` and of `(1 + U + U²) ξ = 0` at `S x`
  have e₁ := congrArg (fun η ↦ η.coeff x) (LinearMap.mem_ker.mp h₁)
  have e₂ := congrArg (fun η ↦ η.coeff ((S : PSL(2, ℤ)) • x)) (LinearMap.mem_ker.mp h₂)
  simp only [LinearMap.add_apply, Module.End.one_apply, coeff_add, Finsupp.coe_add, Pi.add_apply,
    Representation.coeff_ofMulAction, coeff_zero, Finsupp.coe_zero, Pi.zero_apply, ← map_pow,
    coe_S_inv, coe_T_mul_coe_S_inv, coe_T_mul_coe_S_sq_inv] at e₁ e₂
  rw [smul_smul, smul_smul, mul_coe_S_mul_coe_S, coe_T_mul_coe_S_sq_mul_coe_S] at e₂
  rw [eq_neg_of_add_eq_zero_left e₁, add_comm (ξ.coeff _)]
  exact neg_eq_of_add_eq_zero_right ((add_assoc _ _ _).symm.trans e₂)

end TauCeti.ModularGroup
