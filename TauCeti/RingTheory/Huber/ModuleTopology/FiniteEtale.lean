/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.Pair
public import TauCeti.Topology.Algebra.Module.ModuleTopology
import TauCeti.RingTheory.RingHom.Etale

/-!
# Composition of finite étale morphisms of Huber pairs

Finite étale morphisms of Huber pairs compose. Besides finiteness and étaleness of the ring
maps, this requires restriction of scalars for the natural module topology and transitivity of
integrality on plus rings. The result does not require completeness, separatedness, a Tate
hypothesis, or sheafiness. It supplies the ring-level composition used on affinoid charts of
finite étale morphisms.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §8.2, Definition 8.2.16 and Lemma 8.2.17(c).
-/

public section

namespace TauCeti.Huber.Pair

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  {S : Pair A} {T : Pair B} {U : Pair C}

/-- The identity of any Huber pair is finite étale. -/
@[simp]
theorem Hom.isFiniteEtale_id (S : Pair A) : (Hom.id S).IsFiniteEtale where
  finite := by
    rw [Hom.toRingHom_id]
    exact RingHom.Finite.id A
  etale := by
    rw [Hom.toRingHom_id]
    exact RingHom.Etale.of_bijective Function.bijective_id
  isModuleTopology := by
    rw [Hom.toRingHom_id, ← Algebra.algebraMap_self (R := A), _root_.toAlgebra_algebraMap]
    infer_instance
  plus_eq := by
    rw [Hom.toRingHom_id, Subring.map_id]
    ext a
    exact ⟨fun ha ↦ algebraMap_mem (integralClosure S.plus A) ⟨a, ha⟩,
      fun ha ↦ Subring.isIntegrallyClosedIn_iff.mp
        S.isRingOfIntegralElements.isIntegrallyClosedIn ha⟩

/-- The composite of finite étale morphisms of Huber pairs is finite étale. Both its natural
topology and its integral-closure plus ring are taken over the original source pair. -/
theorem Hom.IsFiniteEtale.comp {f : Hom S T} {g : Hom T U} (hg : g.IsFiniteEtale)
    (hf : f.IsFiniteEtale) : (g.comp f).IsFiniteEtale where
  finite := by
    rw [Hom.toRingHom_comp]
    exact hg.finite.comp hf.finite
  etale := by
    rw [Hom.toRingHom_comp]
    exact hg.etale.comp hf.etale
  isModuleTopology := by
    rw [Hom.toRingHom_comp]
    algebraize [f.toRingHom, g.toRingHom, g.toRingHom.comp f.toRingHom]
    have : Module.Finite A B := hf.finite
    have : IsModuleTopology A B := hf.isModuleTopology
    have : IsModuleTopology B C := hg.isModuleTopology
    exact IsModuleTopology.restrictScalars A B C
  plus_eq := by
    ext c
    rw [Subalgebra.mem_toSubring, mem_integralClosure_iff]
    refine ⟨fun hc ↦ ?_, (g.comp f).mem_plus_of_isIntegral⟩
    have hplus (b : B) (hb : b ∈ T.plus) : IsIntegral (S.plus.map f.toRingHom) b := by
      rw [hf.plus_eq] at hb
      exact (mem_integralClosure_iff _ _).mp hb
    rw [hg.plus_eq] at hc
    exact Hom.isIntegral_plus_map_comp hplus ((mem_integralClosure_iff _ _).mp hc)

end TauCeti.Huber.Pair
