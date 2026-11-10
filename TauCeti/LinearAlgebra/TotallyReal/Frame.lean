/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Basic

/-!
# Doubled frames for totally real subspaces

For a linear parametrization `A : F →ₗ[R] E` of a subspace and an endomorphism `J`, the
map `(x, y) ↦ A x + J (A y)` is the doubled frame. Its bijectivity expresses maximal total
reality of the image of `A`, provided both `A` and `J ∘ A` are injective. This is the linear
invertibility criterion for coordinates adapted to a totally real submanifold.

No square identity for `J` is needed: injectivity on the parametrized subspace suffices.
-/

public section

namespace TauCeti

open LinearMap

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F] {J : E →ₗ[R] E} {A : F →ₗ[R] E}

/-- A bijective doubled frame has maximal totally real image. Neither injectivity assumption
on the individual factors is needed in this direction. -/
theorem isMaximalTotallyReal_range_of_bijective_coprod
    (h : Function.Bijective (A.coprod (J.comp A))) :
    IsMaximalTotallyReal J (LinearMap.range A) := by
  let e := LinearEquiv.ofBijective (A.coprod (J.comp A)) h
  have hc := _root_.Submodule.isCompl_map e
    (LinearMap.isCompl_range_inl_inr (R := R) (M := F) (M₂ := F))
  have he : e.toLinearMap = A.coprod (J.comp A) :=
    LinearMap.ext fun x => LinearEquiv.ofBijective_apply _ x
  rw [isMaximalTotallyReal_iff, ← LinearMap.range_comp]
  simpa only [← LinearMap.range_comp, he, LinearMap.coprod_inl,
    LinearMap.coprod_inr] using hc

/-- Complementarity of the image and its `J`-image makes the doubled frame bijective when
each half is injective. -/
theorem IsMaximalTotallyReal.bijective_coprod
    (h : IsMaximalTotallyReal J (LinearMap.range A))
    (hA : Function.Injective A) (hJA : Function.Injective (J.comp A)) :
    Function.Bijective (A.coprod (J.comp A)) := by
  have hr : LinearMap.range (J.comp A) = (LinearMap.range A).map J :=
    LinearMap.range_comp A J
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range]
    · simp [LinearMap.ker_eq_bot.mpr hA, LinearMap.ker_eq_bot.mpr hJA]
    · simpa only [hr] using h.disjoint
  · rw [← LinearMap.range_eq_top, LinearMap.range_coprod, hr]
    exact h.sup_eq_top

/-- The doubled-frame characterization of maximal total reality. -/
@[simp]
theorem bijective_coprod_iff_isMaximalTotallyReal_range
    (hA : Function.Injective A) (hJA : Function.Injective (J ∘ A)) :
    Function.Bijective (A.coprod (J.comp A)) ↔
      IsMaximalTotallyReal J (LinearMap.range A) :=
  ⟨isMaximalTotallyReal_range_of_bijective_coprod, fun h => h.bijective_coprod hA hJA⟩

end TauCeti
