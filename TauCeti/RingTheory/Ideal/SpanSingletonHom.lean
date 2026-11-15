/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# Linear maps out of a principal ideal

For a nonzerodivisor `π` of a commutative ring `R`, the principal ideal `(π)` is free of rank one
on `π`, so evaluation at `π` identifies `Hom_R((π), M)` with `M` for every `R`-module `M`.

## Main definitions

* `Ideal.spanSingletonHomEquiv`: the linear equivalence `Hom_R((π), M) ≃ M`, `f ↦ f π`.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R] {M : Type*} [AddCommMonoid M] [Module R M] {π : R}

/-- For a nonzerodivisor `π`, evaluation at `π` identifies `Hom_R((π), M)` with `M`. -/
noncomputable def spanSingletonHomEquiv (hπ : π ∈ nonZeroDivisors R) :
    (span {π} →ₗ[R] M) ≃ₗ[R] M :=
  let e : R ≃ₗ[R] span {π} :=
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R R π)
      (LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton_eq_bot_iff.2
        (nonZeroDivisorsRight_eq_nonZeroDivisors (M₀ := R) ▸ hπ)))).trans
      (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range R R π).symm)
  (e.arrowCongr (LinearEquiv.refl R M)).symm.trans (LinearMap.ringLmapEquivSelf R R M)

@[simp]
theorem spanSingletonHomEquiv_apply (hπ : π ∈ nonZeroDivisors R) (f : span {π} →ₗ[R] M) :
    spanSingletonHomEquiv hπ f = f ⟨π, mem_span_singleton_self π⟩ := by
  simp only [spanSingletonHomEquiv]
  exact congrArg f (Subtype.ext (by simp))

/-- The inverse of `Ideal.spanSingletonHomEquiv` sends `x` to the map `c • π ↦ c • x`. -/
theorem spanSingletonHomEquiv_symm_apply_smul (hπ : π ∈ nonZeroDivisors R) (x : M) (c : R) :
    (spanSingletonHomEquiv hπ).symm x (c • ⟨π, mem_span_singleton_self π⟩) = c • x := by
  rw [map_smul, ← spanSingletonHomEquiv_apply hπ, LinearEquiv.apply_symm_apply]

end Ideal
