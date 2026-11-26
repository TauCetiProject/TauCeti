/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Generators
public import TauCeti.RingTheory.Huber.NoetherianType.ModuleTopology

/-!
# Finiteness and separatedness of continuous differentials

For topologically finite type `A → B` from Huber `A` into complete Hausdorff Huber `B` of
noetherian type, building on `TauCeti.RingTheory.Huber.Kaehler.Generators`, this file gives the
module-topology consequences of Huber (1996), §1.6, (1.6.2)(ii): completeness and Hausdorffness
(`isNaturallyComplete`, `t2Space`) and continuity (`continuous_fromIdeal`, `continuous_D`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, (1.6.2)(ii).
-/

public section

namespace TauCeti.Huber

namespace ContinuousKaehlerDifferential

open CompletedTensor

section FiniteType

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]

/-- **`Ωᶜ[B⁄A]` is naturally complete** as a `B`-module (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem isNaturallyComplete (h : IsTopologicallyFiniteType (algebraMap A B)) :
    IsNaturallyComplete B (ContinuousKaehlerDifferential A B) :=
  have := finite h; IsNoetherianType.isNaturallyComplete (A := B)

/-- **`Ωᶜ[B⁄A]` is Hausdorff** in its natural `B`-module topology
(Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem t2Space (h : IsTopologicallyFiniteType (algebraMap A B)) :
    T2Space (ContinuousKaehlerDifferential A B) :=
  have := finite h; IsNoetherianType.t2Space_of_isModuleTopology (A := B)

/-- **Continuity of the quotient presentation `I → Ωᶜ[B⁄A]`**: when `A, B` are Huber with `B`
complete Hausdorff of noetherian type and `A → B` topologically of finite type, `fromIdeal A B` is
continuous for the subspace topology on `ideal A B` and the `B`-module topology on `Ωᶜ[B⁄A]`. -/
theorem continuous_fromIdeal (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Continuous (fromIdeal A B) := by
  have := isNoetherianType_of_isTopologicallyFiniteType (B := B) h
  have : Module.Finite (CompletedTensor A B B) (ideal A B) := Module.Finite.iff_fg.mpr (ideal_fg h)
  have : IsModuleTopology (CompletedTensor A B B) (ideal A B) :=
    (ideal A B).isModuleTopology_of_isNoetherianType
  exact IsModuleTopology.continuous_of_linearMap (fromIdeal A B)

/-- **Continuity of the universal derivation** (Huber 1996, §1.6, Definition 1.6.1 and
(1.6.2)(ii)): when `A, B` are Huber with `B` complete Hausdorff of noetherian type and `A → B` is
topologically of finite type, `d : B → Ωᶜ[B⁄A]` is continuous. -/
theorem continuous_D (h : IsTopologicallyFiniteType (algebraMap A B)) : Continuous (D A B) :=
  ((continuous_fromIdeal h).comp (Continuous.subtype_mk
    ((continuous_inr A B B).sub (continuous_inl A B B)) _)).congr fun b ↦ (D_apply A B b).symm

end FiniteType

end ContinuousKaehlerDifferential

end TauCeti.Huber
