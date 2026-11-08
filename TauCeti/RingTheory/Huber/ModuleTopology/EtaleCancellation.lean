/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Pair
import TauCeti.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Algebra

/-!
# Cancellation for finite étale morphisms of Huber pairs

For morphisms `(A, A⁺) → (B, B⁺) → (C, C⁺)`, if the composite is finite étale and the
underlying ring map `A → B` is étale, then `(B, B⁺) → (C, C⁺)` is finite étale. In
particular, finite étale morphisms of Huber pairs satisfy cancellation. This is the affinoid
algebra statement underlying cancellation for finite étale morphisms of adic spaces.

The intermediate map need not be finite or give `B` its natural `A`-module topology, and its
plus ring need not be the integral closure of `A⁺`. The target already has its natural
`A`-module topology and hence its natural `B`-module topology. Its plus ring is the integral
closure of the image of `A⁺`, and therefore also of the larger image of `B⁺`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371
  (2015), §8.2, Definition 8.2.16, for the finite étale plus-ring condition.
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Lecture 7,
  Proposition 7.5.2(3), for cancellation of finite étale morphisms.
-/

public section

namespace TauCeti.Huber.Pair

variable {A B C : Type*}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  {S : Pair A} {T : Pair B} {U : Pair C}

/-- **Cancellation for finite étale morphisms of Huber pairs.** If the composite of two
morphisms is finite étale and the first underlying ring map is étale, then the second
morphism is finite étale. In particular, this applies when the first morphism is finite
étale. No finiteness or plus-ring equality is required of the first morphism. -/
theorem Hom.IsFiniteEtale.of_comp {φ : Hom S T} {ψ : Hom T U}
    (hφ : φ.toRingHom.Etale) (hcomp : (ψ.comp φ).IsFiniteEtale) : ψ.IsFiniteEtale := by
  let := φ.toRingHom.toAlgebra
  let := ψ.toRingHom.toAlgebra
  let := (ψ.comp φ).toRingHom.toAlgebra
  have : IsScalarTower A B C := .of_algebraMap_eq' (Hom.toRingHom_comp ψ φ)
  have : Algebra.Etale A B := hφ
  have : Algebra.Etale A C := hcomp.etale
  have : ContinuousSMul A B := continuousSMul_of_algebraMap A B φ.continuous_toRingHom
  have : ContinuousSMul B C := continuousSMul_of_algebraMap B C ψ.continuous_toRingHom
  have : IsModuleTopology A C := hcomp.isModuleTopology
  refine
    { finite := RingHom.Finite.of_comp_finite
        ((Hom.toRingHom_comp ψ φ) ▸ hcomp.finite)
      etale := Algebra.Etale.of_restrictScalars A B C
      isModuleTopology := IsModuleTopology.of_restrictScalars (R := A)
      plus_eq := ?_ }
  apply le_antisymm
  · rw [hcomp.plus_eq]
    apply Subring.integralClosure_subring_le_iff.mpr
    rintro _ ⟨a, ha, rfl⟩
    rw [Hom.toRingHom_comp, RingHom.comp_apply]
    exact (integralClosure (T.plus.map ψ.toRingHom) C).algebraMap_mem
      ⟨_, Subring.mem_map.mpr ⟨_, φ.map_mem_plus a ha, rfl⟩⟩
  · intro c hc
    exact ψ.mem_plus_of_isIntegral ((mem_integralClosure_iff _ _).mp hc)

end TauCeti.Huber.Pair

end
