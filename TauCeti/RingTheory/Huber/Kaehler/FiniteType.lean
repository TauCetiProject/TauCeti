/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Basic
public import TauCeti.RingTheory.Huber.NoetherianType.ModuleTopology
public import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType
public import TauCeti.RingTheory.Huber.TensorProduct.TopologicallyFiniteType

/-!
# Finiteness and separatedness of continuous differentials

For a topologically finite type homomorphism `A → B` from a Huber ring `A` into a complete
Hausdorff Huber ring `B` of noetherian type, `B ⊗̂_A B` is of noetherian type
(`isTopologicallyFiniteType_inl`, `IsNoetherianType.of_isTopologicallyFiniteType`), so its ideals
are closed. With `closure_span_inr_sub_inl_eq_ideal`, this yields Huber (1996), §1.6, (1.6.2)(ii):
algebraic generation of `I` (`span_inr_sub_inl_eq_ideal`), generation of `Ωᶜ[B⁄A]` by `d '' S`
and `Set.range (D A B)` (`span_D_eq_top`, `span_range_derivation`, continuous analogue of Mathlib's
`KaehlerDifferential.span_range_derivation`), finite generation (`ideal_fg`, `finite`), and
completeness/Hausdorffness (`isNaturallyComplete`, `t2Space`).

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

/-- **Algebraic generation of the completed diagonal ideal** (Huber 1996, §1.6, (1.6.2)(ii)):
when `A → B` is topologically of finite type into complete Hausdorff Huber `B` of noetherian type
and `A[S]` is dense in `B`, `{1 ⊗ s − s ⊗ 1 | s ∈ S}` generates `ideal A B`. -/
theorem span_inr_sub_inl_eq_ideal (h : IsTopologicallyFiniteType (algebraMap A B)) {S : Set B}
    (hS : Dense (Algebra.adjoin A S : Set B)) :
    Ideal.span ((fun s ↦ inr A B B s - inl A B B s) '' S) = ideal A B := by
  have : IsNoetherianType (CompletedTensor A B B) :=
    .of_isTopologicallyFiniteType (isTopologicallyFiniteType_inl h)
  let J := Ideal.span ((fun s ↦ inr A B B s - inl A B B s) '' S)
  have hJ : J.closure = J := J.closure_eq_of_isClosed (IsNoetherianType.isClosed_ideal J)
  exact hJ.symm.trans (closure_span_inr_sub_inl_eq_ideal hS)

/-- **Generation of `Ωᶜ[B⁄A]` by a topological generating set** (Huber 1996, §1.6, (1.6.2)(ii)):
when `A[S]` is dense in `B`, `d '' S` spans `Ωᶜ[B⁄A]` over `B`. -/
theorem span_D_eq_top (h : IsTopologicallyFiniteType (algebraMap A B)) {S : Set B}
    (hS : Dense (Algebra.adjoin A S : Set B)) :
    Submodule.span B (D A B '' S) = ⊤ :=
  span_D_eq_top_of_span_eq_ideal (span_inr_sub_inl_eq_ideal h hS)

/-- `Ωᶜ[B⁄A]` is generated over `B` by `Set.range (D A B)` (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem span_range_derivation (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Submodule.span B (Set.range (D A B)) = ⊤ := by
  simpa [Set.image_univ] using span_D_eq_top h (S := Set.univ) (by simp [Algebra.adjoin_univ])

/-- The comparison `Ω[B⁄A] →ₗ[B] Ωᶜ[B⁄A]` is surjective (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem fromKaehler_surjective (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Function.Surjective (fromKaehler A B) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← span_range_derivation h, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  exact ⟨KaehlerDifferential.D A B b, fromKaehler_D A B b⟩

/-- **The completed diagonal ideal is finitely generated** (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem ideal_fg (h : IsTopologicallyFiniteType (algebraMap A B)) :
    (ideal A B).FG := by
  classical
  obtain ⟨N, hN⟩ := h.exists_finset_dense_adjoin
  refine ⟨N.image (fun s ↦ inr A B B s - inl A B B s), ?_⟩
  simpa [Finset.coe_image] using span_inr_sub_inl_eq_ideal h hN

/-- **`Ωᶜ[B⁄A]` is a finitely generated `B`-module** (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem finite (h : IsTopologicallyFiniteType (algebraMap A B)) :
    Module.Finite B (ContinuousKaehlerDifferential A B) := by
  classical
  obtain ⟨N, hN⟩ := h.exists_finset_dense_adjoin
  refine ⟨⟨N.image (D A B), ?_⟩⟩
  simpa [Finset.coe_image] using span_D_eq_top h hN

/-- **`Ωᶜ[B⁄A]` is naturally complete** as a `B`-module (Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem isNaturallyComplete (h : IsTopologicallyFiniteType (algebraMap A B)) :
    IsNaturallyComplete B (ContinuousKaehlerDifferential A B) := by
  have := finite h
  exact IsNoetherianType.isNaturallyComplete (A := B)

/-- **`Ωᶜ[B⁄A]` is Hausdorff** in its natural `B`-module topology
(Huber 1996, §1.6, (1.6.2)(ii)). -/
theorem t2Space (h : IsTopologicallyFiniteType (algebraMap A B)) :
    T2Space (ContinuousKaehlerDifferential A B) := by
  have := finite h
  exact IsNoetherianType.t2Space_of_isModuleTopology (A := B)

end FiniteType

end ContinuousKaehlerDifferential

end TauCeti.Huber
