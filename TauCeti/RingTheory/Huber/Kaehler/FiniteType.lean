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
remaining Huber (1996), §1.6, (1.6.2)(ii) consequences: surjectivity of `fromKaehler`
(`fromKaehler_surjective`), finite generation of the completed diagonal ideal (`ideal_fg`),
completeness and Hausdorffness (`isNaturallyComplete`, `t2Space`), continuity
(`continuous_fromIdeal`, `continuous_D`), and uniqueness on base-changed tensors
(`linearMap_tensor_ext`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, (1.6.2)(ii).
-/

public section

open TensorProduct

namespace TauCeti.Huber

namespace ContinuousKaehlerDifferential

open CompletedTensor

section FiniteType

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [IsHuberRing B]
  [CompleteSpace B] [T0Space B] [IsNoetherianType B] [IsAdicHom (algebraMap A B)]

/-- The comparison `Ω[B⁄A] →ₗ[B] Ωᶜ[B⁄A]` is surjective (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem fromKaehler_surjective (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Function.Surjective (fromKaehler A B) := by
  have := isNoetherianType_of_isTopologicallyFiniteType (B := B) h
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_D_eq_top, Submodule.span_le]
  rintro _ ⟨b, rfl⟩; exact ⟨KaehlerDifferential.D A B b, fromKaehler_D A B b⟩

/-- **The completed diagonal ideal is finitely generated** (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem ideal_fg (h : IsTopologicallyFiniteType (algebraMap A B)) : (ideal A B).FG := by
  classical
  have := isNoetherianType_of_isTopologicallyFiniteType (B := B) h
  obtain ⟨s, hs, hdense⟩ := h.exists_finite_dense_adjoin
  exact ⟨hs.toFinset.image (fun b ↦ inr A B B b - inl A B B b), by
    simpa [Finset.coe_image, Set.Finite.coe_toFinset] using (ideal_eq_span hdense).symm⟩

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

/-- **Uniqueness for `R`-linear maps out of `R ⊗[B] Ωᶜ[B⁄A]`**: two `R`-linear maps agreeing on
`1 ⊗ₜ d b` for all `b : B` are equal. -/
theorem linearMap_tensor_ext (h : IsTopologicallyFiniteType (algebraMap A B))
    {R : Type*} [CommRing R] [Algebra B R] {Q : Type*} [AddCommGroup Q] [Module R Q]
    {f g : R ⊗[B] ContinuousKaehlerDifferential A B →ₗ[R] Q}
    (heq : ∀ b : B, f (1 ⊗ₜ[B] D A B b) = g (1 ⊗ₜ[B] D A B b)) : f = g := by
  have := isNoetherianType_of_isTopologicallyFiniteType (B := B) h
  let : Module B Q := Module.compHom Q (algebraMap B R)
  have : IsScalarTower B R Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact (LinearMap.liftBaseChangeEquiv R).symm.injective (linearMap_ext heq)

end FiniteType

end ContinuousKaehlerDifferential

end TauCeti.Huber
