/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized

/-!
# The augmentation of cubical chains

The **augmentation** `ε : C^□_0(X; R) → R` sends every singular `0`-cube, a point of `X`, to `1`.
It vanishes on boundaries: the boundary of a `1`-cube, a path, is its end point minus its starting
point.  No `0`-cube is degenerate, so the augmentation of the unnormalized chains descends to the
normalized ones without any condition.

## Main definitions

* `TauCeti.CubicalChain.augment X R`, `TauCeti.NormalizedCubicalChain.augment X R`: the
  augmentations.

## Main results

* `TauCeti.NormalizedCubicalChain.augment_boundary`: `ε ∘ ∂ = 0`.
* `TauCeti.NormalizedCubicalChain.augment_map`: the augmentation is natural.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace CubicalChain

section Semiring

variable (R : Type*) [Semiring R]

variable (X) in
/-- The augmentation of the unnormalized `0`-chains: the sum of the coefficients. -/
def augment : CubicalChain X R 0 →ₗ[R] R :=
  linearCombination R fun _ ↦ 1

@[simp]
theorem augment_single (c : SingularCube X 0) (a : R) : augment X R (single c a) = a := by
  rw [augment, linearCombination_single, smul_eq_mul, mul_one]

theorem degenerate_le_ker_augment : degenerate X R 0 ≤ LinearMap.ker (augment X R) := by
  rw [degenerate_zero]
  exact bot_le

theorem augment_map (f : C(X, Y)) : augment Y R ∘ₗ map R f 0 = augment X R := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp

end Semiring

variable (R : Type*) [Ring R]

/-- The augmentation vanishes on boundaries: a path contributes its end point minus its starting
point. -/
theorem augment_boundary : augment X R ∘ₗ boundary X R 0 = 0 := by
  refine lhom_ext' fun c ↦ LinearMap.ext_ring ?_
  simp [boundary_single]

end CubicalChain

namespace NormalizedCubicalChain

open CubicalChain

variable (R : Type*) [Ring R]

variable (X) in
/-- The augmentation of the normalized `0`-chains. -/
def augment : NormalizedCubicalChain X R 0 →ₗ[R] R :=
  Submodule.liftQ _ (CubicalChain.augment X R) (degenerate_le_ker_augment R)

@[simp]
theorem augment_mk (f : CubicalChain X R 0) :
    augment X R (Submodule.Quotient.mk f) = CubicalChain.augment X R f :=
  Submodule.liftQ_apply _ _ f

@[simp]
theorem augment_ofCube (c : SingularCube X 0) : augment X R (ofCube X R c) = 1 := by
  rw [ofCube_def, augment_mk, augment_single]

/-- The augmentation vanishes on boundaries. -/
theorem augment_boundary : augment X R ∘ₗ boundary X R 0 = 0 := by
  refine LinearMap.ext ((Submodule.Quotient.mk_surjective _).forall.2 fun f ↦ ?_)
  rw [LinearMap.comp_apply, boundary_mk, augment_mk, ← LinearMap.comp_apply,
    CubicalChain.augment_boundary, LinearMap.zero_apply, LinearMap.zero_apply]

/-- The augmentation is natural. -/
theorem augment_map (f : C(X, Y)) : augment Y R ∘ₗ map R f 0 = augment X R := by
  refine LinearMap.ext ((Submodule.Quotient.mk_surjective _).forall.2 fun g ↦ ?_)
  rw [LinearMap.comp_apply, map_mk, augment_mk, augment_mk, ← LinearMap.comp_apply,
    CubicalChain.augment_map]

end NormalizedCubicalChain

end TauCeti

end
