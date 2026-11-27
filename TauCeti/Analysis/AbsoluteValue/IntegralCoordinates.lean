/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.ValuationSubring

/-!
# Integral coordinate tests for nonarchimedean absolute values

A family of linear tests on a vector space cuts out a submodule over the valuation ring:
all test values must have absolute value at most one. The tests need not be independent, so
one can use all coordinates of several maps at once.
-/

public section

namespace AbsoluteValue

variable {K R V : Type*} [Field K] [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommMonoid V] [Module K V] (w : AbsoluteValue K R) {I : Sort*}

/-- Vectors whose coordinates in the family `a` lie in the valuation ring of `w`. -/
def integralCoordinates (hw : IsNonarchimedean w) (a : I → V →ₗ[K] K) :
    Submodule (w.valuationSubring hw) V :=
  ⨅ i, (LinearMap.range (Algebra.linearMap (w.valuationSubring hw) K)).comap
    ((a i).restrictScalars (w.valuationSubring hw))

/-- Integrality in a family of coordinates means that every coordinate has absolute value at
most one. -/
@[simp] theorem mem_integralCoordinates_iff (hw : IsNonarchimedean w)
    (a : I → V →ₗ[K] K) {v : V} :
    v ∈ w.integralCoordinates hw a ↔ ∀ i, w (a i v) ≤ 1 := by
  have coe_iff (x : K) : (∃ y : w.valuationSubring hw, (y : K) = x) ↔ w x ≤ 1 := by
    refine ⟨?_, fun hx ↦ ⟨⟨x, (mem_valuationSubring_iff hw).2 hx⟩, rfl⟩⟩
    rintro ⟨y, rfl⟩
    exact (mem_valuationSubring_iff hw).1 y.property
  simp [integralCoordinates, ValuationSubring.algebraMap_apply, coe_iff]

/-- Pulling back the integral submodule amounts to composing each coordinate with the map. -/
@[simp] theorem comap_integralCoordinates {U : Type*} [AddCommMonoid U] [Module K U]
    (hw : IsNonarchimedean w) (a : I → U →ₗ[K] K) (f : V →ₗ[K] U) :
    (w.integralCoordinates hw a).comap (f.restrictScalars (w.valuationSubring hw)) =
      w.integralCoordinates hw (fun i ↦ (a i).comp f) := by
  ext v
  simp

/-- Testing all coordinates of all blocks at once cuts out the intersection of the integral
submodules for the individual blocks. -/
theorem integralCoordinates_sigma {J : Type*} {ι : J → Type*} (hw : IsNonarchimedean w)
    (a : (j : J) → ι j → V →ₗ[K] K) :
    w.integralCoordinates hw (fun i : Σ j, ι j ↦ a i.1 i.2) =
      ⨅ j, w.integralCoordinates hw (a j) := by
  ext v
  simp [Sigma.forall]

end AbsoluteValue
