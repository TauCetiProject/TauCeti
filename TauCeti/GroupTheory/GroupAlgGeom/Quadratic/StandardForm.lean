/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Automorphism
public import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# The rewriting rules of the standard form

A strictly quadratic word of `G[X]` is brought to a standard quadratic word, or to a coefficient,
by a product of elementary `G`-automorphisms of `G[X]` (`GX.elementaryAut`) followed by a
conjugation in `G[X]`. The elementary automorphisms are the substitutions `x ↦ a x b`, for words
`a` and `b` in which `x` does not occur, and the inversions `x ↦ x⁻¹`. This is the corrected form
of [IFT], §2.7, Lemma 1 (and [VAR-I], §1, Lemma 6), which asserts a `G`-automorphism alone and
has no coefficient case: a coefficient `g ≠ 1` is strictly quadratic and is not a standard
quadratic word.

This file proves the rewriting rules of the reduction, which follows the normal form of polygonal
words in the classification of compact surfaces ([GaXu], Lemma 6.1), with the coefficients in
the role of boundary edges. The source states its rules for cyclic words, with new edges; here
the handle rule and the three-squares rule are equalities of elements of `G[X]` in the same
variables, and the automorphisms they provide fix every word in which the variables they move do
not occur, so that they apply inside a longer product.

## Main results

* `GX.transvection_crossCap`: the cross-cap rule `x U x V ↦ x² U⁻¹ V` ([GaXu], Step 3).
* `GX.transvection_rotate`: the rotation rule `x U V x⁻¹ W ↦ x V U x⁻¹ W` ([GaXu], Step 4).
* `GX.exists_mem_elementaryAut_apply_handle`: the handle rule ([GaXu], Step 4), carrying
  `x U y V x⁻¹ W y⁻¹ Z` to `x⁻¹ y⁻¹ x y W V U Z`.
* `GX.exists_mem_elementaryAut_apply_commutator_mul_sq`: a handle and a cross-cap are three
  cross-caps ([GaXu], Step 5), `x⁻¹ y⁻¹ x y s² ↦ x² y² s²`.
* `GX.exists_mem_elementaryAut_apply_prod_commutator_mul_prod_sq`: `n` handles followed by
  `r ≥ 1` cross-caps are `2n + r` cross-caps.
* `GX.exists_mem_elementaryAut_apply_mul_prod_sq`: a word in which none of the variables `xᵢ`
  occurs moves from the front of `∏ᵢ xᵢ²` to its back.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Lemma 1.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1, Lemma 6.
* [GaXu] J. Gallier, D. Xu, *A guide to the classification theorem for compact surfaces*,
  Springer (2013), Chapter 6, Lemma 6.1.
-/

public section

open Monoid.Coprod Subgroup
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.GX

variable {G X : Type*} [Group G] [DecidableEq X] {x y : X} {U V W Z : GX G X}

/-- The cross-cap rule: `x ↦ x U⁻¹` turns `x U x V` into `x² U⁻¹ V`. -/
theorem transvection_crossCap (hU : U ∈ avoiding x) (hV : V ∈ avoiding x) :
    transvection x 1 U⁻¹ (one_mem _) (inv_mem hU)
        (inr (FreeGroup.of x) * U * inr (FreeGroup.of x) * V) =
      inr (FreeGroup.of x) ^ 2 * (U⁻¹ * V) := by
  simp [hU, hV, mul_assoc, pow_two]

/-- The rotation rule: `x ↦ x U⁻¹` turns `x U V x⁻¹ W` into `x V U x⁻¹ W`. -/
theorem transvection_rotate (hU : U ∈ avoiding x) (hV : V ∈ avoiding x) (hW : W ∈ avoiding x) :
    transvection x 1 U⁻¹ (one_mem _) (inv_mem hU)
        (inr (FreeGroup.of x) * U * V * (inr (FreeGroup.of x))⁻¹ * W) =
      inr (FreeGroup.of x) * V * U * (inr (FreeGroup.of x))⁻¹ * W := by
  simp [hU, hV, hW, mul_assoc]

/-- The handle rule without conjugation: an elementary automorphism which fixes every word in
which `x` and `y` do not occur turns `x U y V x⁻¹ W y⁻¹ Z` into `[x, y] W V U Z`, where
`[x, y] = x⁻¹ y⁻¹ x y`. -/
theorem exists_mem_elementaryAut_apply_handle (hxy : x ≠ y) (hU : U ∈ avoiding x ⊓ avoiding y)
    (hV : V ∈ avoiding x ⊓ avoiding y) (hW : W ∈ avoiding x ⊓ avoiding y)
    (hZ : Z ∈ avoiding x ⊓ avoiding y) : ∃ f ∈ elementaryAut G X,
      f (inr (FreeGroup.of x) * U * inr (FreeGroup.of y) * V * (inr (FreeGroup.of x))⁻¹ * W *
          (inr (FreeGroup.of y))⁻¹ * Z) =
        ⁅(inr (FreeGroup.of x) : GX G X)⁻¹, (inr (FreeGroup.of y))⁻¹⁆ * (W * V * U * Z) ∧
      ∀ a ∈ avoiding x ⊓ avoiding y, f a = a := by
  rw [mem_inf] at hU hV hW hZ
  -- `x ↦ x W V` and `y ↦ (W V U)⁻¹ y W`, then the inversions of `x` and `y`: the automorphism
  -- `x ↦ x⁻¹ W V`, `y ↦ (W V U)⁻¹ y⁻¹ W`
  refine ⟨invertVar G y * invertVar G x *
      transvection y (W * V * U)⁻¹ W (inv_mem (mul_mem (mul_mem hW.2 hV.2) hU.2)) hW.2 *
      transvection x 1 (W * V) (one_mem _) (mul_mem hW.1 hV.1), ?_, ?_, fun a ha => ?_⟩
  · refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;> simp
  · -- `simp only`: the full simp set is noticeably slower here
    simp only [mul_assoc, mul_inv_rev, MulAut.mul_apply, map_mul, map_inv, inv_inv, one_mul,
      mul_inv_cancel_left, ne_eq, not_false_eq_true, inr_of_mem_avoiding_iff,
      transvection_inr_of_self, transvection_apply_of_mem_avoiding, invertVar_inr_of_self,
      invertVar_apply_of_mem_avoiding, commutatorElement_def, hxy, hxy.symm, hU.1, hU.2, hV.1, hV.2,
      hW.1, hW.2, hZ.1, hZ.2]
  · rw [mem_inf] at ha
    simp [ha.1, ha.2]

/-- A handle and a cross-cap are three cross-caps: for distinct variables `x`, `y`, `s` an
elementary automorphism which fixes every word in which `x`, `y` and `s` do not occur turns
`[x, y] s²` into `x² y² s²`, where `[x, y] = x⁻¹ y⁻¹ x y`. -/
theorem exists_mem_elementaryAut_apply_commutator_mul_sq {s : X} (hxy : x ≠ y) (hxs : x ≠ s)
    (hys : y ≠ s) : ∃ f ∈ elementaryAut G X,
      f (⁅(inr (FreeGroup.of x) : GX G X)⁻¹, (inr (FreeGroup.of y))⁻¹⁆ * inr (FreeGroup.of s) ^ 2) =
        inr (FreeGroup.of x) ^ 2 * inr (FreeGroup.of y) ^ 2 * inr (FreeGroup.of s) ^ 2 ∧
      ∀ a ∈ avoiding x ⊓ avoiding y ⊓ avoiding s, f a = a := by
  -- `x ↦ s x`, `y ↦ s y`, `y ↦ y s⁻¹`, `s ↦ y⁻¹ s`, `y ↦ y x`, then the inversions of `x`, `y`: the
  -- automorphism `x ↦ x y s x⁻¹`, `y ↦ x y s y⁻¹ x⁻¹ s⁻¹ y⁻¹ x⁻¹`, `s ↦ x y s`
  refine ⟨invertVar G y * invertVar G x *
      transvection y 1 (inr (FreeGroup.of x)) (one_mem _) (inr_of_mem_avoiding hxy) *
      transvection s (inr (FreeGroup.of y))⁻¹ 1 (inv_mem (inr_of_mem_avoiding hys)) (one_mem _) *
      transvection y 1 (inr (FreeGroup.of s))⁻¹ (one_mem _)
        (inv_mem (inr_of_mem_avoiding hys.symm)) *
      transvection y (inr (FreeGroup.of s)) 1 (inr_of_mem_avoiding hys.symm) (one_mem _) *
      transvection x (inr (FreeGroup.of s)) 1 (inr_of_mem_avoiding hxs.symm) (one_mem _), ?_, ?_,
      fun a ha => ?_⟩
  · refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_ <;> simp
  · -- `simp only`: the full simp set is noticeably slower here
    simp only [mul_assoc, pow_two, mul_one, one_mul, mul_inv_rev, inv_inv, inv_mul_cancel_left,
      MulAut.mul_apply, map_mul, map_inv, ne_eq, not_false_eq_true, inr_of_mem_avoiding_iff,
      transvection_inr_of_self, transvection_apply_of_mem_avoiding, invertVar_inr_of_self,
      invertVar_apply_of_mem_avoiding, commutatorElement_def, hxy, hxy.symm, hxs, hxs.symm, hys,
      hys.symm]
  · simp only [mem_inf] at ha
    simp [ha.1.1, ha.1.2, ha.2]

-- The step of `exists_mem_elementaryAut_apply_prod_commutator_mul_prod_sq`: the last of `n + 1`
-- handles and the first of `r + 1` cross-caps are three cross-caps, leaving `n` handles followed
-- by `r + 3` cross-caps.
private theorem exists_mem_elementaryAut_apply_prod_commutator_mul_prod_sq_succ {N n r : ℕ}
    (hN : 2 * (n + 1) + (r + 1) = N) {x : Fin N → X} (hx : Function.Injective x) :
    ∃ f ∈ elementaryAut G X,
      f ((List.ofFn fun i : Fin (n + 1) =>
            ⁅(inr (FreeGroup.of (x ⟨2 * i, by have := i.isLt; lia⟩)) : GX G X)⁻¹,
              (inr (FreeGroup.of (x ⟨2 * i + 1, by have := i.isLt; lia⟩)))⁻¹⁆).prod *
          (List.ofFn fun k : Fin (r + 1) => (inr (FreeGroup.of
            (x ⟨2 * (n + 1) + k, by have := k.isLt; lia⟩)) : GX G X) ^ 2).prod) =
        (List.ofFn fun i : Fin n =>
            ⁅(inr (FreeGroup.of (x ⟨2 * i, by have := i.isLt; lia⟩)) : GX G X)⁻¹,
              (inr (FreeGroup.of (x ⟨2 * i + 1, by have := i.isLt; lia⟩)))⁻¹⁆).prod *
          (List.ofFn fun k : Fin (r + 3) =>
            (inr (FreeGroup.of (x ⟨2 * n + k, by have := k.isLt; lia⟩)) : GX G X) ^ 2).prod ∧
      ∀ a, (∀ i, a ∈ avoiding (x i)) → f a = a := by
  obtain ⟨f, hf, hfw, hfa⟩ := exists_mem_elementaryAut_apply_commutator_mul_sq (G := G)
    (x := x ⟨2 * n, by lia⟩) (y := x ⟨2 * n + 1, by lia⟩) (s := x ⟨2 * n + 2, by lia⟩)
    (hx.ne (by simp)) (hx.ne (by simp)) (hx.ne (by simp))
  -- `f` fixes the words in the variables other than `x₂ₙ`, `x₂ₙ₊₁`, `x₂ₙ₊₂`
  have hfix {j : ℕ} (hj : j < N) (h : j < 2 * n ∨ 2 * n + 2 < j) :
      (inr (FreeGroup.of (x ⟨j, hj⟩)) : GX G X) ∈ avoiding (x ⟨2 * n, by lia⟩) ⊓
        avoiding (x ⟨2 * n + 1, by lia⟩) ⊓ avoiding (x ⟨2 * n + 2, by lia⟩) := by
    simp only [Subgroup.mem_inf, inr_of_mem_avoiding_iff, ne_eq, hx.eq_iff, Fin.mk.injEq]
    lia
  refine ⟨f, hf, ?_, fun a ha => hfa a ⟨⟨ha _, ha _⟩, ha _⟩⟩
  rw [List.ofFn_succ_last (n := n)]
  -- bring the indices of both sides to the form `2 * n + ⋯`
  simp only [List.ofFn_succ, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
    Fin.val_castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ, add_zero, zero_add,
    Nat.reduceAdd, ← mul_assoc, (by lia : 2 * (n + 1) = 2 * n + 2),
    (fun i => by lia : ∀ i : ℕ, 2 * n + 2 + (i + 1) = 2 * n + (i + 1 + 1 + 1))]
  rw [mul_assoc _ _ (_ ^ 2), map_mul, map_mul, hfw, hfa _ (list_prod_mem ?_),
    hfa _ (list_prod_mem ?_)]
  · simp [mul_assoc]
  · simp only [List.forall_mem_ofFn_iff]
    exact fun k => pow_mem (hfix (j := 2 * n + (k + 1 + 1 + 1)) (by lia) (by lia)) 2
  · simp only [List.forall_mem_ofFn_iff]
    intro i
    have h₁ := hfix (j := 2 * i) (by lia) (by lia)
    have h₂ := hfix (j := 2 * i + 1) (by lia) (by lia)
    rw [commutatorElement_def, inv_inv, inv_inv]
    exact mul_mem (mul_mem (mul_mem (inv_mem h₁) (inv_mem h₂)) h₁) h₂

/-- **Handles and cross-caps.** For injective `x : Fin N → X` with `N = 2n + r` and `r ≥ 1`, an
elementary automorphism which fixes every word in which no `xᵢ` occurs turns
`∏_{i<n} [x₂ᵢ, x₂ᵢ₊₁] ∏_{k<r} x²₂ₙ₊ₖ` into `∏_{i<N} xᵢ²`, where `[x, y] = x⁻¹ y⁻¹ x y`. -/
theorem exists_mem_elementaryAut_apply_prod_commutator_mul_prod_sq {N n r : ℕ} (hN : 2 * n + r = N)
    (hr : 0 < r) {x : Fin N → X} (hx : Function.Injective x) : ∃ f ∈ elementaryAut G X,
      f ((List.ofFn fun i : Fin n =>
            ⁅(inr (FreeGroup.of (x ⟨2 * i, by have := i.isLt; lia⟩)) : GX G X)⁻¹,
              (inr (FreeGroup.of (x ⟨2 * i + 1, by have := i.isLt; lia⟩)))⁻¹⁆).prod *
          (List.ofFn fun k : Fin r =>
            (inr (FreeGroup.of (x ⟨2 * n + k, by have := k.isLt; lia⟩)) : GX G X) ^ 2).prod) =
        (List.ofFn fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2).prod ∧
      ∀ a, (∀ i, a ∈ avoiding (x i)) → f a = a := by
  induction n generalizing r with
  | zero =>
    obtain rfl : r = N := by lia
    exact ⟨1, one_mem _, by simp, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr.ne'
    obtain ⟨f₁, hf₁, hf₁w, hf₁a⟩ :=
      exists_mem_elementaryAut_apply_prod_commutator_mul_prod_sq_succ (G := G) hN hx
    obtain ⟨f₂, hf₂, hf₂w, hf₂a⟩ := ih (r := r + 3) (by lia) (by lia)
    exact ⟨f₂ * f₁, mul_mem hf₂ hf₁, by rw [MulAut.mul_apply, hf₁w, hf₂w],
      fun a ha => by rw [MulAut.mul_apply, hf₁a a ha, hf₂a a ha]⟩

/-- **A word moves behind squares.** For `x : Fin N → X` and a word `P` in which no `xᵢ` occurs,
an elementary automorphism which fixes every word in which no `xᵢ` occurs turns `P ∏_{i<N} xᵢ²`
into `∏_{i<N} xᵢ² P`. -/
theorem exists_mem_elementaryAut_apply_mul_prod_sq {N : ℕ} {x : Fin N → X} {P : GX G X}
    (hP : ∀ i, P ∈ avoiding (x i)) : ∃ f ∈ elementaryAut G X,
      f (P * (List.ofFn fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2).prod) =
        (List.ofFn fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2).prod * P ∧
      ∀ a, (∀ i, a ∈ avoiding (x i)) → f a = a := by
  -- the simultaneous substitution `xᵢ ↦ P⁻¹ xᵢ P`
  obtain ⟨f, hf, hfx, hfa⟩ := exists_mem_elementaryAut_forall_apply_inr_of
    (Finset.univ.image x) (fun _ => P⁻¹) (fun _ => P) (by simp [hP]) (by simp [hP])
  refine ⟨f, hf, ?_, fun a ha => hfa a (by simp [ha])⟩
  -- `f` fixes `P` and acts on the squares `xᵢ²` as the conjugation by `P⁻¹`
  have hl : (List.ofFn fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2).map f =
      (List.ofFn fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2).map (MulAut.conj P⁻¹) := by
    simp [List.map_ofFn, Function.comp_def, hfx, pow_two, mul_assoc]
  rw [map_mul, hfa P (by simp [hP]), map_list_prod, hl, ← map_list_prod]
  simp [mul_assoc]

end TauCeti.GroupAlgGeom.GX
