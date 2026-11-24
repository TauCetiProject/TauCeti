/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Graded algebra maps as homogeneous linear maps

A graded algebra map `φ : 𝒜 →ₐᵍ[R] ℬ` sends each piece `𝒜 i` into `ℬ i`, so its underlying
linear map is homogeneous of degree zero. For `ℤ`-graded algebras it therefore commutes with
every Koszul twist `a ↦ (-1) ^ (q * |a|) a`, the sign bookkeeping of differential graded
algebras.

## Main results

* `GradedAlgHom.isHomogeneous_toLinearMap`: the linear map underlying a graded algebra map is
  homogeneous of degree zero.
* `GradedAlgHom.map_koszulTwist`: a graded algebra map commutes with the Koszul twists.
-/

public section

namespace GradedAlgHom

variable {R A B : Type*}

section AddMonoid

variable {ι : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [DecidableEq ι] [AddMonoid ι] {𝒜 : ι → Submodule R A} {ℬ : ι → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The linear map underlying a graded algebra map is homogeneous of degree zero. -/
theorem isHomogeneous_toLinearMap (φ : 𝒜 →ₐᵍ[R] ℬ) :
    LinearMap.IsHomogeneous φ.toAlgHom.toLinearMap 𝒜 ℬ 0 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
    simpa only [add_zero, AlgHom.toLinearMap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      using φ.map_mem hx

end AddMonoid

variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- A graded algebra map between `ℤ`-graded algebras commutes with the Koszul twist
`a ↦ (-1) ^ (q * |a|) a` of every parameter `q`, since it has degree zero. -/
theorem map_koszulTwist (φ : 𝒜 →ₐᵍ[R] ℬ) (q : ℤ) (a : A) :
    φ ((TauCeti.InternalGrading.ofDecomposition 𝒜).koszulTwist q a) =
      (TauCeti.InternalGrading.ofDecomposition ℬ).koszulTwist q (φ a) := by
  have hφ : LinearMap.IsHomogeneous φ.toAlgHom.toLinearMap
      (TauCeti.InternalGrading.ofDecomposition 𝒜).piece
      (TauCeti.InternalGrading.ofDecomposition ℬ).piece 0 := by
    rw [TauCeti.InternalGrading.ofDecomposition_piece,
      TauCeti.InternalGrading.ofDecomposition_piece]
    exact φ.isHomogeneous_toLinearMap
  have h := hφ.koszulTwist_apply q a
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
    AlgHom.toLinearMap_apply, coe_toAlgHom] at h
  exact h.symm

end GradedAlgHom
