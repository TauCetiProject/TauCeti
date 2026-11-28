/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction

/-!
# Conjugacy averaging and class-function pairings

A function on a finite group has a canonical class function obtained by averaging its conjugates.
Pairing against a class function is unchanged by this average. For a direct factor of a finite
product, the squared norm of the pairing is therefore bounded by the squared coefficient norm
on that factor times the squared norm of the averaged function on the whole product. This gives
trace bounds for central group-algebra elements tested against non-class functions.

The use of this estimate for Bessel trace functions follows
`New.Filling.re_sum_coeff_mul_trace_besselTranslate_le` in
[`New/Spanning/Unfolding/Moments.lean`][moments] of `grh-lean`.

[moments]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Spanning/Unfolding/Moments.lean
-/

public section

open scoped BigOperators

namespace TauCeti.ClassFunction

/-- Average a function over the conjugates of each argument, obtaining a class function. -/
noncomputable def conjAverage {k G : Type*} [Semiring k] [Algebra ℚ≥0 k]
    [Group G] [Fintype G] : (G → k) →ₗ[k] ClassFunction k G where
  toFun f := ⟨fun x ↦ 𝔼 g : G, f (g * x * g⁻¹), mem_iff.mpr fun x h ↦
    Fintype.expect_equiv (Equiv.mulRight h) _ _ fun g ↦ by simp [mul_assoc]⟩
  map_add' f g := Subtype.ext (funext fun x ↦ Finset.expect_add_distrib _ _ _)
  map_smul' c f := Subtype.ext (funext fun x ↦ (Finset.mul_expect _ _ c).symm)

/-- Evaluation of the conjugacy average at a group element. -/
theorem conjAverage_apply {k G : Type*} [Semiring k] [Algebra ℚ≥0 k]
    [Group G] [Fintype G] (f : G → k) (x : G) :
    (conjAverage f).val x = 𝔼 g : G, f (g * x * g⁻¹) := (rfl)

/-- Conjugacy averaging fixes every class function. -/
@[simp] theorem conjAverage_val {k G : Type*} [Semiring k] [Algebra ℚ≥0 k]
    [Group G] [Fintype G] (f : ClassFunction k G) : conjAverage f.val = f := by
  apply Subtype.ext
  funext x
  rw [conjAverage_apply]
  exact (Finset.expect_congr rfl fun g _ ↦ apply_conj f g x).trans (Fintype.expect_const _)

/-- Averaging the second argument leaves its sum pairing against a class function unchanged. -/
theorem sum_mul_conjAverage_eq {k G : Type*} [Semiring k] [Algebra ℚ≥0 k]
    [Group G] [Fintype G] (a : ClassFunction k G) (f : G → k) :
    ∑ x, a.val x * (conjAverage f).val x = ∑ x, a.val x * f x := by
  simp_rw [conjAverage_apply, Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  refine (Finset.expect_congr rfl fun g _ ↦ ?_).trans (Fintype.expect_const _)
  exact Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun x ↦ by
    have hx : (MulAut.conj g).toEquiv x = g * x * g⁻¹ := MulAut.conj_apply g x
    rw [hx, apply_conj a]

/-- Conjugacy averaging on a product restricts to conjugacy averaging on its first factor. -/
@[simp] theorem conjAverage_prod_mk_one {k G H : Type*} [Semiring k] [Algebra ℚ≥0 k]
    [Group G] [Fintype G] [Group H] [Fintype H] (f : G × H → k) (x : G) :
    (conjAverage f).val (x, 1) = (conjAverage (fun g ↦ f (g, 1))).val x := by
  simp only [conjAverage_apply, ← Finset.univ_product_univ, Finset.expect_product]
  simp

/-- The squared norm of a sum pairing on the first factor is bounded by the coefficient energy
there times the conjugacy-averaged energy on the entire group. No group-order factor is needed. -/
theorem norm_sum_mul_prod_mk_one_sq_le {k G H : Type*} [NormedRing k] [Algebra ℚ≥0 k]
    [Group G] [Fintype G] [Group H] [Fintype H] (a : ClassFunction k G) (f : G × H → k) :
    ‖∑ x, a.val x * f (x, 1)‖ ^ 2 ≤
      (∑ x, ‖a.val x‖ ^ 2) * ∑ y, ‖(conjAverage f).val y‖ ^ 2 := by
  classical
  rw [← sum_mul_conjAverage_eq a (fun x ↦ f (x, 1))]
  simp_rw [← conjAverage_prod_mk_one f]
  calc
    _ ≤ (∑ x, ‖a.val x‖ * ‖(conjAverage f).val (x, 1)‖) ^ 2 := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_mul_le _ _)
    _ ≤ (∑ x, ‖a.val x‖ ^ 2) * ∑ x, ‖(conjAverage f).val (x, 1)‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ _ := by
      gcongr
      have h : Function.Injective (fun x : G ↦ (x, (1 : H))) := fun _ _ h ↦ congrArg Prod.fst h
      exact (Finset.sum_image (f := fun y ↦ ‖(conjAverage f).val y‖ ^ 2) h.injOn).symm.le.trans
        (Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _)

end TauCeti.ClassFunction
