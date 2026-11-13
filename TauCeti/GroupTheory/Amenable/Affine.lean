/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.GroupTheory.Amenable.Basic

import TauCeti.GroupTheory.Amenable.Abelian
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Amenability of the affine group of a line

The affine self-equivalences of a commutative ring are amenable for every group topology.
Their linear parts commute, and the kernel of `AffineEquiv.linearHom` consists of
translations, supplied by `AffineEquiv.constVAddHom`. The extension theorem therefore
applies to these two native homomorphisms with the discrete topology, and amenability
passes to every group topology. In particular, this gives the amenability
of the point stabilizers in the projective linear group of a field.

The closure of amenability under extensions is Proposition G.2.2 of Bekka,
de la Harpe and Valette, *Kazhdan's Property (T)*.
-/

public section

namespace TauCeti

/-- The affine group of a commutative ring is amenable for every group topology. -/
instance Amenable.affineEquiv {R : Type*} [CommRing R]
    [TopologicalSpace (R ≃ᵃ[R] R)] [IsTopologicalGroup (R ≃ᵃ[R] R)] :
    Amenable (R ≃ᵃ[R] R) := by
  apply Amenable.of_discrete
  let : TopologicalSpace (R ≃ᵃ[R] R) := ⊥
  let : DiscreteTopology (R ≃ᵃ[R] R) := ⟨rfl⟩
  let : TopologicalSpace (Multiplicative R) := ⊥
  let : DiscreteTopology (Multiplicative R) := ⟨rfl⟩
  let : TopologicalSpace (R ≃ₗ[R] R) := ⊥
  let : DiscreteTopology (R ≃ₗ[R] R) := ⟨rfl⟩
  let : TopologicalSpace (Rᵐᵒᵖ)ˣ := ⊥
  let : DiscreteTopology (Rᵐᵒᵖ)ˣ := ⟨rfl⟩
  let e : (R ≃ₗ[R] R) ≃* (Rᵐᵒᵖ)ˣ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R R).symm.trans
      (Units.mapEquiv (RingEquiv.moduleEndSelf R).symm.toMulEquiv)
  have : Amenable (R ≃ₗ[R] R) := .of_injective e.toMonoidHom e.injective
  refine .of_ker_le_range (AffineEquiv.constVAddHom R R) AffineEquiv.linearHom ?_
  intro f hf
  have hlinear : f.linear = 1 := MonoidHom.mem_ker.mp hf
  refine ⟨Multiplicative.ofAdd (f 0), AffineEquiv.ext fun x => ?_⟩
  simp [AffineEquiv.apply_eq_linear_add f x, hlinear, add_comm]

end TauCeti
