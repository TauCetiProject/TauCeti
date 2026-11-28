/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic.Abel

/-!
# Affine group actions on zero-sum hyperplanes

For a finite group Δ and an abelian group M, the left translation action (g • a) d =
a (g⁻¹ * d) on Δ → M preserves the coordinate sum sumValuesHom Δ M a = ∑ d, a d.
Shifting by a basepoint e : Δ → M identifies the affine hyperplane {a | ∑ d, a d = ∑ d, e d}
with the kernel (sumValuesHom Δ M).ker, yielding an affine Δ-action hyperplaneAction e whose
linear part is hyperplaneAction 0.

## Main definitions and results

* TauCeti.perm_pow_eq_one_of_map_sub: a difference-preserving permutation of an abelian group
  killed by 
 has 
-th power equal to 1.
* TauCeti.sumValuesHom: the additive homomorphism  ↦ ∑ g : Δ, a g from Δ → M to M.
* TauCeti.hyperplaneAction: the affine Δ-action on (sumValuesHom Δ M).ker shifted by e.
* TauCeti.hyperplaneAction_toPerm_apply: explicit coordinate formula for hyperplaneAction e.
* TauCeti.hyperplaneAction_toPerm_sub: the linear part of hyperplaneAction e is
  hyperplaneAction 0.
* TauCeti.sum_hyperplaneAction_toPerm_apply_one: summing the shifted evaluation at 1 over all
  g ∈ Δ recovers ∑ g, e g.

## Provenance

Adapted from New.DiscreteModule.perm_pow_eq_one_of_map_sub, sumValuesHom, hyperplaneAction,
hyperplaneAction_toPerm_apply, hyperplaneAction_toPerm_sub, and
sum_hyperplaneAction_toPerm_apply_one in src/Lib/General/Algebra/CartanMap.lean in grh-lean
(https://github.com/lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

/-- A permutation of an abelian group killed by 
 that preserves differences is a translation,
so its 
-th power is 1. -/
theorem perm_pow_eq_one_of_map_sub {V : Type*} [AddCommGroup V] {n : ℕ}
    (h_killed : ∀ x : V, n • x = 0) {σ : Equiv.Perm V} (hσ : ∀ x y : V, σ x - σ y = x - y) :
    σ ^ n = 1 := by
  have h_transl : σ = Equiv.addLeft (σ 0) :=
    Equiv.ext fun x ↦ by simpa [sub_eq_iff_eq_add'] using hσ x 0
  rw [h_transl]
  ext x
  simp [h_killed]

/-- The sum  ↦ ∑ g, a g of the values of a function on a finite type. -/
@[expose] def sumValuesHom (Δ M : Type*) [Fintype Δ] [AddCommMonoid M] : (Δ → M) →+ M where
  toFun a := ∑ g : Δ, a g
  map_zero' := by simp
  map_add' _ _ := Finset.sum_add_distrib

/-- The left translation action of a finite group Δ on the affine hyperplane of functions
Δ → M having the same coordinate sum as e, transported to (sumValuesHom Δ M).ker via
x ↦ e + x. -/
@[expose, instance_reducible] def hyperplaneAction {Δ M : Type*} [Group Δ] [Fintype Δ]
    [AddCommGroup M] (e : Δ → M) : MulAction Δ (sumValuesHom Δ M).ker where
  smul g x := ⟨fun d : Δ ↦ -e d + (e (g⁻¹ * d) + x.val (g⁻¹ * d)), by
    have h_sum (a : Δ → M) : ∑ d : Δ, a (g⁻¹ * d) = ∑ d : Δ, a d :=
      Equiv.sum_comp (Equiv.mulLeft g⁻¹) a
    simp [sumValuesHom, Finset.sum_add_distrib, h_sum, show ∑ d : Δ, x.val d = 0 from x.property]⟩
  one_smul x := Subtype.ext <| funext fun d ↦
    show -e d + (e (1⁻¹ * d) + x.val (1⁻¹ * d)) = x.val d by simp
  mul_smul g h x := Subtype.ext <| funext fun d ↦ by
    change -e d + (e ((g * h)⁻¹ * d) + x.val ((g * h)⁻¹ * d)) = -e d + (e (g⁻¹ * d) +
      (-e (g⁻¹ * d) + (e (h⁻¹ * (g⁻¹ * d)) + x.val (h⁻¹ * (g⁻¹ * d)))))
    simp [mul_assoc]

/-- Coordinate formula for hyperplaneAction e as a permutation of (sumValuesHom Δ M).ker. -/
theorem hyperplaneAction_toPerm_apply {Δ M : Type*} [Group Δ] [Fintype Δ] [AddCommGroup M]
    (e : Δ → M) (g : Δ) (x : (sumValuesHom Δ M).ker) (d : Δ) :
    ((hyperplaneAction e).toPerm g x).val d = -e d + (e (g⁻¹ * d) + x.val (g⁻¹ * d)) :=
  rfl

/-- The action hyperplaneAction e is affine with linear part hyperplaneAction 0. -/
theorem hyperplaneAction_toPerm_sub {Δ M : Type*} [Group Δ] [Fintype Δ] [AddCommGroup M]
    (e : Δ → M) (g : Δ) (x y : (sumValuesHom Δ M).ker) :
    (hyperplaneAction e).toPerm g x - (hyperplaneAction e).toPerm g y =
      (hyperplaneAction 0).toPerm g (x - y) := by
  ext d
  simp only [AddSubgroupClass.coe_sub, Pi.sub_apply, hyperplaneAction_toPerm_apply, Pi.zero_apply]
  abel

/-- On the affine hyperplane through e, summing the shifted evaluation at 1 over all g ∈ Δ
recovers ∑ g, e g. -/
theorem sum_hyperplaneAction_toPerm_apply_one {Δ M : Type*} [Group Δ] [Fintype Δ] [AddCommGroup M]
    (e : Δ → M) (y : (sumValuesHom Δ M).ker) :
    ∑ g : Δ, (e 1 + ((hyperplaneAction e).toPerm g⁻¹ y).val 1) = ∑ g : Δ, e g := by
  simp only [hyperplaneAction_toPerm_apply]
  simp [Finset.sum_add_distrib, show ∑ g : Δ, y.val g = 0 from y.property]

end TauCeti
