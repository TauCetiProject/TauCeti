/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Powers under a multiplicative equivalence

A multiplicative equivalence commutes with taking `n`-th powers, so the `n`-th power map is
injective on one side exactly when it is injective on the other.

## Main results

* `MulEquiv.injective_pow_iff` and its additive form `AddEquiv.injective_nsmul_iff`: taking `n`-th
  powers is injective on one side of an equivalence exactly when it is injective on the other.
* `MulEquiv.isOfFinOrder_iff` and its additive form `AddEquiv.isOfFinAddOrder_iff`: a
  multiplicative equivalence preserves and reflects finite order.
* `MulEquiv.isMulTorsionFree_iff` and its additive form `AddEquiv.isAddTorsionFree_iff`: one side
  of an equivalence is torsion-free exactly when the other is.
-/

public section

namespace MulEquiv

/-- Taking `n`-th powers is injective on `M` exactly when it is injective on `N`, for a
multiplicative equivalence `M ≃* N`, since the equivalence commutes with it. -/
@[to_additive /-- Multiplication by `n` is injective on `M` exactly when it is injective on `N`,
for an additive equivalence `M ≃+ N`, since the equivalence commutes with it. -/]
theorem injective_pow_iff {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) (n : ℕ) :
    Function.Injective (fun x : M ↦ x ^ n) ↔ Function.Injective (fun y : N ↦ y ^ n) := by
  have h : (fun y : N ↦ y ^ n) = e ∘ (fun x : M ↦ x ^ n) ∘ e.symm := by
    ext y
    simp
  rw [h, EquivLike.comp_injective, EquivLike.injective_comp]

/-- An element has finite order after applying a multiplicative equivalence `e : M ≃* N` if and
only if it has finite order in `M`. -/
@[to_additive (attr := simp)
/-- An element has finite additive order after applying an additive equivalence `e : M ≃+ N` if
and only if it has finite additive order in `M`. -/]
theorem isOfFinOrder_iff {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) {x : M} :
    IsOfFinOrder (e x) ↔ IsOfFinOrder x :=
  Function.Injective.isOfFinOrder_iff (f := e.toMonoidHom) e.injective

/-- For a multiplicative equivalence `M ≃* N`, the monoid `M` is torsion-free exactly when `N`
is. -/
@[to_additive /-- For an additive equivalence `M ≃+ N`, the monoid `M` is torsion-free exactly
when `N` is. -/]
theorem isMulTorsionFree_iff {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) :
    IsMulTorsionFree M ↔ IsMulTorsionFree N :=
  ⟨fun _ ↦ e.symm.injective.isMulTorsionFree e.symm.toMonoidHom,
    fun _ ↦ e.injective.isMulTorsionFree e.toMonoidHom⟩

end MulEquiv

end
