/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Module.Completion
public import TauCeti.Analysis.Normed.Ring.Completion
public import TauCeti.Topology.Algebra.LinearMapCompletion
public import TauCeti.Topology.Algebra.Star.Completion

/-!
# Isometric star operations and the C⋆-identity on completions

The norm of the completion of a seminormed additive group extends the norm of the group by
continuity, and the star operation extends through `UniformSpace.Completion.map`. An isometric
star operation therefore stays isometric on the completion. Together with
`UniformSpace.Completion.instNonUnitalNormedRing` and `UniformSpace.Completion.instStarRing`, this
makes the completion of a nonunital seminormed ⋆-ring with isometric star, such as an `L¹`
convolution algebra on compactly supported functions, a nonunital Banach ⋆-algebra.

The C⋆-identity `‖x⋆ * x‖ = ‖x‖ * ‖x‖` also extends by continuity. Completing a ⋆-algebra in a
C⋆-seminorm, such as the full crossed-product seminorm on a twisted convolution algebra, therefore
gives a C⋆-ring.

A continuous unital ⋆-homomorphism into a complete normed ⋆-algebra extends by continuity to a
⋆-homomorphism out of the completion of its domain (`StarAlgHom.fromCompletion`), building on
`NonUnitalStarAlgHom.fromCompletion` from `TauCeti.Topology.Algebra.LinearMapCompletion`. This is
how ⋆-homomorphisms bounded by a universal C⋆-seminorm pass to the universal C⋆-algebra.

## Main results

* `UniformSpace.Completion.instNormedStarGroup`: an isometric star operation stays isometric on
  the completion.
* `UniformSpace.Completion.cstarRing`: the completion of a seminormed ⋆-ring whose seminorm
  satisfies the C⋆-identity is a C⋆-ring.
* `StarAlgHom.fromCompletion`: the extension of a continuous unital ⋆-homomorphism to the
  completion of its domain.
-/

public section

open UniformSpace

/-- **An isometric star operation on a seminormed group stays isometric on its completion.** -/
instance UniformSpace.Completion.instNormedStarGroup {E : Type*} [SeminormedAddCommGroup E]
    [StarAddMonoid E] [NormedStarGroup E] : NormedStarGroup (Completion E) where
  norm_star_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a => rw [← Completion.coe_star, Completion.norm_coe, Completion.norm_coe, norm_star]

/-- **The completion of a seminormed ⋆-ring satisfying the C⋆-identity is a C⋆-ring.** The
inequality `‖x‖ * ‖x‖ ≤ ‖x⋆ * x‖` on `E` passes to the completion by continuity. This is not an
instance because `CStarRing` is only defined for normed rings, so the hypothesis cannot be stated
as a class on the seminormed ring `E`. -/
theorem UniformSpace.Completion.cstarRing {E : Type*} [NonUnitalSeminormedRing E] [StarRing E]
    [NormedStarGroup E] (h : ∀ x : E, ‖x‖ * ‖x‖ ≤ ‖star x * x‖) : CStarRing (Completion E) where
  norm_mul_self_le x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a =>
      simpa only [← Completion.coe_star, ← Completion.coe_mul', Completion.norm_coe] using h a

noncomputable section


namespace StarAlgHom

variable {𝕜 E D : Type*} [NormedField 𝕜] [SeminormedRing E] [NormedAlgebra 𝕜 E] [StarRing E]
  [ContinuousStar E] [NormedRing D] [NormedAlgebra 𝕜 D] [StarRing D] [ContinuousStar D]
  [CompleteSpace D]

/-- The extension by continuity of a continuous unital ⋆-homomorphism `φ : E → D` into a complete
normed ⋆-algebra to the completion of `E`. -/
def fromCompletion (φ : E →⋆ₐ[𝕜] D) (hφ : Continuous φ) : Completion E →⋆ₐ[𝕜] D where
  toFun := φ.toNonUnitalStarAlgHom.fromCompletion hφ
  map_one' := by
    rw [← Completion.coe_one]
    exact (φ.toNonUnitalStarAlgHom.fromCompletion_apply_coe hφ 1).trans (map_one φ)
  map_mul' := map_mul (φ.toNonUnitalStarAlgHom.fromCompletion hφ)
  map_zero' := map_zero (φ.toNonUnitalStarAlgHom.fromCompletion hφ)
  map_add' := map_add (φ.toNonUnitalStarAlgHom.fromCompletion hφ)
  commutes' r := by
    rw [Completion.algebraMap_def]
    exact (φ.toNonUnitalStarAlgHom.fromCompletion_apply_coe hφ _).trans (AlgHomClass.commutes φ r)
  map_star' := map_star (φ.toNonUnitalStarAlgHom.fromCompletion hφ)

/-- The extension agrees with the original ⋆-homomorphism on `E`. -/
@[simp]
theorem fromCompletion_apply_coe (φ : E →⋆ₐ[𝕜] D) (hφ : Continuous φ) (x : E) :
    φ.fromCompletion hφ x = φ x :=
  φ.toNonUnitalStarAlgHom.fromCompletion_apply_coe hφ x

/-- The extension is continuous. -/
@[fun_prop]
theorem continuous_fromCompletion (φ : E →⋆ₐ[𝕜] D) (hφ : Continuous φ) :
    Continuous (φ.fromCompletion hφ) :=
  φ.toNonUnitalStarAlgHom.continuous_fromCompletion hφ

end StarAlgHom
