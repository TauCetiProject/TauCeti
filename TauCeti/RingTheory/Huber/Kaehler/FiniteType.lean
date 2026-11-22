/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Basic
public import TauCeti.RingTheory.Huber.NoetherianType.ModuleTopology
public import TauCeti.RingTheory.Huber.TensorProduct.TopologicallyFiniteType

/-!
# Finiteness and separatedness of continuous differentials

For topologically finite type `A → B` from Huber `A` into complete Hausdorff Huber `B` of
noetherian type, `B ⊗̂_A B` is of noetherian type, so its ideals are closed. With
`closure_span_inr_sub_inl_eq_ideal`, this gives Huber (1996), §1.6, (1.6.2)(ii): algebraic
generation (`span_inr_sub_inl_eq_ideal`, `span_D_eq_top`, `span_range_derivation`), finiteness
(`ideal_fg`, `finite`), completeness/Hausdorffness (`isNaturallyComplete`, `t2Space`),
continuity (`continuous_fromIdeal`, `continuous_D`), and `linearMap_ext`.

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

/-- **Algebraic generation of the completed diagonal ideal** (Huber 1996, §1.6, (1.6.2)(ii)):
when `A → B` is topologically of finite type into complete Hausdorff Huber `B` of noetherian type
and `A[S]` is dense in `B`, `{1 ⊗ s − s ⊗ 1 | s ∈ S}` generates `ideal A B`. -/
theorem span_inr_sub_inl_eq_ideal (h : IsTopologicallyFiniteType (algebraMap A B)) {S : Set B}
    (hS : Dense (Algebra.adjoin A S : Set B)) :
    Ideal.span ((fun s ↦ inr A B B s - inl A B B s) '' S) = ideal A B :=
  have : IsNoetherianType (CompletedTensor A B B) :=
    .of_isTopologicallyFiniteType (isTopologicallyFiniteType_inl h)
  ((Ideal.span ((fun s ↦ inr A B B s - inl A B B s) '' S)).closure_eq_of_isClosed
    (IsNoetherianType.isClosed_ideal _)).symm.trans (closure_span_inr_sub_inl_eq_ideal hS)

/-- **Generation of `Ωᶜ[B⁄A]` by a topological generating set** (Huber 1996, §1.6, (1.6.2)(ii)):
when `A[S]` is dense in `B`, `d '' S` spans `Ωᶜ[B⁄A]` over `B`. -/
theorem span_D_eq_top (h : IsTopologicallyFiniteType (algebraMap A B)) {S : Set B}
    (hS : Dense (Algebra.adjoin A S : Set B)) : Submodule.span B (D A B '' S) = ⊤ :=
  span_D_eq_top_of_span_eq_ideal (span_inr_sub_inl_eq_ideal h hS)

/-- `Ωᶜ[B⁄A]` is generated over `B` by `Set.range (D A B)` (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem span_range_derivation (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Submodule.span B (Set.range (D A B)) = ⊤ := by
  simpa [Set.image_univ] using span_D_eq_top h (S := Set.univ) (by simp [Algebra.adjoin_univ])

/-- The comparison `Ω[B⁄A] →ₗ[B] Ωᶜ[B⁄A]` is surjective (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem fromKaehler_surjective (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Function.Surjective (fromKaehler A B) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_derivation h, Submodule.span_le]
  rintro _ ⟨b, rfl⟩; exact ⟨KaehlerDifferential.D A B b, fromKaehler_D A B b⟩

/-- **The completed diagonal ideal is finitely generated** (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem ideal_fg (h : IsTopologicallyFiniteType (algebraMap A B)) : (ideal A B).FG := by
  classical
  obtain ⟨N, hN⟩ := h.exists_finset_dense_adjoin
  exact ⟨N.image (fun s ↦ inr A B B s - inl A B B s),
    by simpa [Finset.coe_image] using span_inr_sub_inl_eq_ideal h hN⟩

/-- **`Ωᶜ[B⁄A]` is a finitely generated `B`-module** (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem finite (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Module.Finite B (ContinuousKaehlerDifferential A B) := by
  classical
  obtain ⟨N, hN⟩ := h.exists_finset_dense_adjoin
  exact ⟨⟨N.image (D A B), by simpa [Finset.coe_image] using span_D_eq_top h hN⟩⟩

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
  have : IsNoetherianType (CompletedTensor A B B) :=
    .of_isTopologicallyFiniteType (isTopologicallyFiniteType_inl h)
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

/-- Two `B`-linear maps out of `Ωᶜ[B⁄A]` agreeing on `d '' S` (for `A[S]` dense in `B`) are
equal when `A → B` is topologically of finite type into complete Hausdorff Huber `B` of noetherian
type. -/
theorem linearMap_ext_of_dense_adjoin (h : IsTopologicallyFiniteType (algebraMap A B))
    {S : Set B} (hS : Dense (Algebra.adjoin A S : Set B))
    {M : Type*} [AddCommGroup M] [Module B M] {f₁ f₂ : ContinuousKaehlerDifferential A B →ₗ[B] M}
    (heq : ∀ s ∈ S, f₁ (D A B s) = f₂ (D A B s)) : f₁ = f₂ :=
  LinearMap.ext_on (span_D_eq_top h hS) fun _ ⟨s, hs, hds⟩ ↦ hds ▸ heq s hs

/-- **Uniqueness for linear maps out of `Ωᶜ[B⁄A]`** (Huber 1996, §1.6, (1.6.2)(ii)): two `B`-linear
maps out of `Ωᶜ[B⁄A]` agreeing on `D A B` are equal. -/
theorem linearMap_ext (h : IsTopologicallyFiniteType (algebraMap A B))
    {M : Type*} [AddCommGroup M] [Module B M] {f₁ f₂ : ContinuousKaehlerDifferential A B →ₗ[B] M}
    (heq : ∀ b, f₁ (D A B b) = f₂ (D A B b)) : f₁ = f₂ :=
  linearMap_ext_of_dense_adjoin h (S := Set.univ) (by simp [Algebra.adjoin_univ]) fun b _ ↦ heq b

/-- **Uniqueness for `R`-linear maps out of `R ⊗[B] Ωᶜ[B⁄A]`**: two `R`-linear maps agreeing on
`1 ⊗ₜ d b` for all `b : B` are equal. -/
theorem linearMap_tensor_ext (h : IsTopologicallyFiniteType (algebraMap A B))
    {R : Type*} [CommRing R] [Algebra B R] {Q : Type*} [AddCommGroup Q] [Module R Q]
    {f g : R ⊗[B] ContinuousKaehlerDifferential A B →ₗ[R] Q}
    (heq : ∀ b : B, f (1 ⊗ₜ[B] D A B b) = g (1 ⊗ₜ[B] D A B b)) : f = g := by
  let : Module B Q := Module.compHom Q (algebraMap B R)
  have : IsScalarTower B R Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact (LinearMap.liftBaseChangeEquiv R).symm.injective (linearMap_ext h heq)

end FiniteType

end ContinuousKaehlerDifferential

end TauCeti.Huber
