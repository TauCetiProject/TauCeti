/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.SimpleWeylPoint
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# Pinned rank-one words in the characteristic-three short-root G₂ carrier

The representative `simpleWeylPoint i A` is `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the numbered simple pinning.
Its underlying general-linear point agrees with the integral rank-one word, so the integral
signed-permutation matrix formulas also describe this independently generated carrier.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

universe v

/-- The pinned rank-one word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the carrier generated over `𝔽₃`. -/
noncomputable def simpleWeylPoint (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

/-- The rank-one word is the product prescribed by the numbered simple pinning. -/
theorem simpleWeylPoint_def (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    simpleWeylPoint i A =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) := (rfl)

/-- The pinned rank-one words agree as general-linear points with the integral words. -/
@[simp]
theorem coe_simpleWeylPoint (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    (simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 7) A) =
      (IntegralToralClosure.simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 7) A) := by
  simp only [simpleWeylPoint_def, IntegralToralClosure.simpleWeylPoint_def,
    Subgroup.coe_mul, coe_rootSubgroupPoints]

end TauCeti.G2ShortRoot.PrimeField
