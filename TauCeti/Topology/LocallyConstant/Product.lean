/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
import TauCeti.Topology.LocallyConstant.Compact

/-!
# Currying locally constant functions

When the second factor is compact, locally constant functions on a product are equivalent to
locally constant families of locally constant functions on the second factor.
-/

public section

namespace LocallyConstant

variable {T S M : Type*} [TopologicalSpace T] [TopologicalSpace S]

/-- Uncurrying a locally constant family by evaluation on the two product coordinates. -/
def uncurry (f : LocallyConstant T (LocallyConstant S M)) : LocallyConstant (T × S) M :=
  ⟨fun p ↦ f p.1 p.2, by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun p ↦ ?_
    filter_upwards [Filter.Eventually.prod_nhds
      (f.isLocallyConstant.eventually_eq p.1)
      ((f p.1).isLocallyConstant.eventually_eq p.2)] with q hq
    exact (congrArg (fun g : LocallyConstant S M ↦ g q.2) hq.1).trans hq.2⟩

/-- Uncurrying evaluates the family at the first coordinate and then at the second coordinate. -/
@[simp]
theorem uncurry_apply (f : LocallyConstant T (LocallyConstant S M)) (p : T × S) :
    uncurry f p = f p.1 p.2 := by
  rfl

variable [CompactSpace S]

/-- Currying a locally constant function on a product with a compact second factor. -/
def curryEquiv :
    LocallyConstant (T × S) M ≃ LocallyConstant T (LocallyConstant S M) where
  toFun f := ⟨fun t ↦ ⟨fun s ↦ f (t, s),
      f.isLocallyConstant.comp_continuous (continuous_const.prodMk continuous_id)⟩,
    IsLocallyConstant.of_uncurry_coe f.isLocallyConstant⟩
  invFun := uncurry
  left_inv _ := rfl
  right_inv _ := rfl

/-- Evaluating the curried function recovers evaluation on the product. -/
@[simp]
theorem curryEquiv_apply_apply (f : LocallyConstant (T × S) M) (t : T) (s : S) :
    curryEquiv f t s = f (t, s) := by
  rfl

/-- Evaluating the inverse equivalence applies the family at the two coordinates. -/
@[simp]
theorem curryEquiv_symm_apply_apply (f : LocallyConstant T (LocallyConstant S M))
    (t : T) (s : S) : (curryEquiv.symm f) (t, s) = f t s := by
  rfl

/-- The linear refinement of currying with a compact second factor. -/
def curryLinearEquiv (R : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    LocallyConstant (T × S) M ≃ₗ[R] LocallyConstant T (LocallyConstant S M) where
  toEquiv := curryEquiv
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluating the linear currying equivalence recovers evaluation on the product. -/
@[simp]
theorem curryLinearEquiv_apply_apply (R : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    (f : LocallyConstant (T × S) M) (t : T) (s : S) :
    curryLinearEquiv R f t s = f (t, s) := by
  rfl

/-- The inverse linear equivalence evaluates a family at the product coordinates. -/
@[simp]
theorem curryLinearEquiv_symm_apply_apply (R : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] (f : LocallyConstant T (LocallyConstant S M)) (t : T) (s : S) :
    (curryLinearEquiv R).symm f (t, s) = f t s := by
  rfl

end LocallyConstant
