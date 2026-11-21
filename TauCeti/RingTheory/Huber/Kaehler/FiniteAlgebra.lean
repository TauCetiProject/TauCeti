/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Basic
public import TauCeti.RingTheory.Huber.NoetherianType.Basic

import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.RingTheory.Huber.NoetherianType.ModuleTopology
import TauCeti.RingTheory.Huber.OpenMapping
import TauCeti.RingTheory.Huber.TensorProduct.FiniteAlgebra

/-!
# Continuous differentials of finite Huber algebras

For a module-finite `A`-algebra `B` carrying `IsModuleTopology A B` and a complete Hausdorff Huber
ring `B` of noetherian type, `CompletedTensor.toCompletion_bijective_of_isNoetherianType` yields
the comparison isomorphism `fromKaehler A B : Ω[B⁄A] ≃ₗ[B] Ωᶜ[B⁄A]` (`fromKaehlerEquiv`; over a
complete Tate ring `A`, `fromKaehler_bijective_of_finite_of_isTateRing`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, (1.6.2)(iii).
-/

public section

open UniformSpace
open scoped Uniformity

namespace TauCeti.Huber.ContinuousKaehlerDifferential

section FiniteAlgebraNoetherianType

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]

/-- **Finite-algebra comparison** (Huber 1996, §1.6, (1.6.2)(iii)): if `B` is a module-finite
`A`-algebra carrying the `A`-module topology and `B` is a complete Hausdorff Huber ring of
noetherian type, then the canonical comparison `fromKaehler A B : Ω[B⁄A] →ₗ[B] Ωᶜ[B⁄A]` is
bijective. -/
theorem fromKaehler_bijective_of_finite [IsModuleTopology A B] [Module.Finite A B] :
    Function.Bijective (fromKaehler A B) :=
  fromKaehler_bijective_of_bijective_toCompletion
    (CompletedTensor.toCompletion_bijective_of_isNoetherianType A B B)

variable (A B) in
/-- **Finite-algebra comparison as a linear equivalence** (Huber 1996, §1.6, (1.6.2)(iii)): for a
module-finite `A`-algebra `B` carrying the `A`-module topology with `B` a complete Hausdorff Huber
ring of noetherian type, `Ω[B⁄A] ≃ₗ[B] Ωᶜ[B⁄A]` via `fromKaehler A B`. -/
noncomputable def fromKaehlerEquiv [IsModuleTopology A B] [Module.Finite A B] :
    Ω[B⁄A] ≃ₗ[B] ContinuousKaehlerDifferential A B :=
  LinearEquiv.ofBijective (fromKaehler A B) (fromKaehler_bijective_of_finite (A := A) (B := B))

/-- Applying `fromKaehlerEquiv` is the canonical comparison map `fromKaehler`. -/
@[simp]
theorem fromKaehlerEquiv_apply [IsModuleTopology A B] [Module.Finite A B] (ω : Ω[B⁄A]) :
    fromKaehlerEquiv A B ω = fromKaehler A B ω := (rfl)

/-- The inverse of `fromKaehlerEquiv` cancels `fromKaehler`. -/
@[simp]
theorem fromKaehlerEquiv_symm_fromKaehler [IsModuleTopology A B] [Module.Finite A B]
    (ω : Ω[B⁄A]) :
    (fromKaehlerEquiv A B).symm (fromKaehler A B ω) = ω :=
  (fromKaehlerEquiv A B).symm_apply_apply ω

/-- `fromKaehler` cancels the inverse of `fromKaehlerEquiv`. -/
@[simp]
theorem fromKaehler_fromKaehlerEquiv_symm [IsModuleTopology A B] [Module.Finite A B]
    (ω : ContinuousKaehlerDifferential A B) :
    fromKaehler A B ((fromKaehlerEquiv A B).symm ω) = ω :=
  (fromKaehlerEquiv A B).apply_symm_apply ω

/-- The inverse of `fromKaehlerEquiv` sends the continuous universal derivation to the algebraic
Kähler derivation. -/
@[simp]
theorem fromKaehlerEquiv_symm_D [IsModuleTopology A B] [Module.Finite A B] (b : B) :
    (fromKaehlerEquiv A B).symm (D A B b) = KaehlerDifferential.D A B b :=
  (fromKaehlerEquiv A B).injective (by simp)

end FiniteAlgebraNoetherianType

/-- Over a complete Tate ring `A`, if `B` is a module-finite complete Hausdorff Huber `A`-algebra
of noetherian type, then the canonical comparison `fromKaehler A B : Ω[B⁄A] →ₗ[B] Ωᶜ[B⁄A]` is
bijective (Huber 1996, §1.6, (1.6.2)(iii)). -/
theorem fromKaehler_bijective_of_finite_of_isTateRing {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [IsTateRing A]
    [CompleteSpace A]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
    [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]
    [Module.Finite A B] :
    Function.Bijective (fromKaehler A B) := by
  have : (𝓤 B).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : ContinuousSMul A B :=
    continuousSMul_of_algebraMap A B (IsAdicHom.continuous inferInstance)
  have : IsModuleTopology A B := IsTateRing.isModuleTopology (A := A) (M := B)
  exact fromKaehler_bijective_of_finite (A := A) (B := B)

end TauCeti.Huber.ContinuousKaehlerDifferential
