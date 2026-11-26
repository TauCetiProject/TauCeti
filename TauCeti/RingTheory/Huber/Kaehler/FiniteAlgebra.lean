/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Basic
public import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete
public import TauCeti.RingTheory.Huber.NoetherianType.Basic

import TauCeti.RingTheory.Huber.NoetherianType.ModuleTopology
import TauCeti.RingTheory.Huber.TensorProduct.Finite.Algebra

/-!
# Continuous differentials of finite Huber algebras

For a module-finite `A`-algebra `B` carrying `IsModuleTopology A B` with `B` a complete Hausdorff
Huber ring such that `B ⊗[A] B` is naturally complete over `B`,
`CompletedTensor.toCompletion_bijective_of_isNaturallyComplete` yields the comparison isomorphism
`fromKaehler A B : Ω[B⁄A] ≃ₗ[B] Ωᶜ[B⁄A]` (`fromKaehlerEquiv`). In particular this holds when
`B` is of noetherian type (`fromKaehler_bijective_of_finite`), and over a complete Tate ring `A`
the module-topology assumption is automatic (`fromKaehler_bijective_of_finite_of_isTateRing`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, (1.6.2)(iii).
-/

public section

open TensorProduct UniformSpace
open scoped Uniformity

namespace TauCeti.Huber.ContinuousKaehlerDifferential

section NaturallyComplete

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]

/-- **Finite-algebra comparison** (Huber 1996, §1.6, (1.6.2)(iii)): if `B` is a module-finite
`A`-algebra carrying the `A`-module topology and `B ⊗[A] B` is naturally complete over the
complete Hausdorff Huber ring `B`, then the canonical comparison
`fromKaehler A B : Ω[B⁄A] →ₗ[B] Ωᶜ[B⁄A]` is bijective. -/
theorem fromKaehler_bijective_of_isNaturallyComplete [IsModuleTopology A B] [Module.Finite A B]
    (h : IsNaturallyComplete B (B ⊗[A] B)) : Function.Bijective (fromKaehler A B) :=
  fromKaehler_bijective_of_bijective_toCompletion
    (CompletedTensor.toCompletion_bijective_of_isNaturallyComplete A B B h)

variable (A B) in
/-- **Finite-algebra comparison as a linear equivalence** (Huber 1996, §1.6, (1.6.2)(iii)): for a
module-finite `A`-algebra `B` carrying the `A`-module topology with `B ⊗[A] B` naturally complete
over the complete Hausdorff Huber ring `B`, `Ω[B⁄A] ≃ₗ[B] Ωᶜ[B⁄A]` via
`fromKaehler A B`. -/
noncomputable def fromKaehlerEquiv [IsModuleTopology A B] [Module.Finite A B]
    (h : IsNaturallyComplete B (B ⊗[A] B)) :
    Ω[B⁄A] ≃ₗ[B] ContinuousKaehlerDifferential A B :=
  LinearEquiv.ofBijective (fromKaehler A B)
    (fromKaehler_bijective_of_isNaturallyComplete (A := A) (B := B) h)

/-- Applying `fromKaehlerEquiv` is the canonical comparison map `fromKaehler`. -/
@[simp] theorem fromKaehlerEquiv_apply [IsModuleTopology A B] [Module.Finite A B]
    (h : IsNaturallyComplete B (B ⊗[A] B)) (ω : Ω[B⁄A]) :
    fromKaehlerEquiv A B h ω = fromKaehler A B ω := (rfl)

/-- The inverse of `fromKaehlerEquiv` cancels `fromKaehler`. -/
@[simp] theorem fromKaehlerEquiv_symm_fromKaehler [IsModuleTopology A B] [Module.Finite A B]
    (h : IsNaturallyComplete B (B ⊗[A] B)) (ω : Ω[B⁄A]) :
    (fromKaehlerEquiv A B h).symm (fromKaehler A B ω) = ω :=
  (fromKaehlerEquiv A B h).symm_apply_apply ω

/-- `fromKaehler` cancels the inverse of `fromKaehlerEquiv`. -/
@[simp] theorem fromKaehler_fromKaehlerEquiv_symm [IsModuleTopology A B] [Module.Finite A B]
    (h : IsNaturallyComplete B (B ⊗[A] B)) (ω : ContinuousKaehlerDifferential A B) :
    fromKaehler A B ((fromKaehlerEquiv A B h).symm ω) = ω :=
  (fromKaehlerEquiv A B h).apply_symm_apply ω

/-- The inverse of `fromKaehlerEquiv` sends the continuous universal derivation to the algebraic
Kähler derivation. -/
@[simp] theorem fromKaehlerEquiv_symm_D [IsModuleTopology A B] [Module.Finite A B]
    (h : IsNaturallyComplete B (B ⊗[A] B)) (b : B) :
    (fromKaehlerEquiv A B h).symm (D A B b) = KaehlerDifferential.D A B b :=
  (fromKaehlerEquiv A B h).injective (by simp)

end NaturallyComplete

/-- **Finite-algebra comparison** (Huber 1996, §1.6, (1.6.2)(iii)): if `B` is a module-finite
`A`-algebra carrying the `A`-module topology and `B` is a complete Hausdorff Huber ring of
noetherian type, then the canonical comparison
`fromKaehler A B : Ω[B⁄A] →ₗ[B] Ωᶜ[B⁄A]` is bijective. -/
theorem fromKaehler_bijective_of_finite {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
    [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]
    [IsModuleTopology A B] [Module.Finite A B] : Function.Bijective (fromKaehler A B) :=
  fromKaehler_bijective_of_isNaturallyComplete
    (IsNoetherianType.isNaturallyComplete (A := B) (M := B ⊗[A] B))

/-- Over a complete Tate ring `A`, if `B` is a module-finite complete Hausdorff Huber `A`-algebra
of noetherian type, then the canonical comparison
`fromKaehler A B : Ω[B⁄A] →ₗ[B] Ωᶜ[B⁄A]` is bijective (Huber 1996, §1.6, (1.6.2)(iii)). -/
theorem fromKaehler_bijective_of_finite_of_isTateRing {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [IsTateRing A]
    [CompleteSpace A] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
    [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]
    [Module.Finite A B] : Function.Bijective (fromKaehler A B) := by
  have : (𝓤 B).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : ContinuousSMul A B := continuousSMul_of_algebraMap A B (IsAdicHom.continuous inferInstance)
  have : IsModuleTopology A B := IsTateRing.isModuleTopology (A := A) (M := B)
  exact fromKaehler_bijective_of_finite (A := A) (B := B)

end TauCeti.Huber.ContinuousKaehlerDifferential
