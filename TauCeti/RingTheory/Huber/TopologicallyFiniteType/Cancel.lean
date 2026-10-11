/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic

import TauCeti.RingTheory.Huber.WeightedEval.Completion
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# Cancellation of topological finite type

For continuous ring homomorphisms `φ : A → B` and `ψ : B → C`, with `A` Huber and `B`, `C`
nonarchimedean, a strict finite-type presentation of `ψ ∘ φ` also gives a strict finite-type
presentation of `ψ`. The target `C` must be complete and Hausdorff, so evaluation of restricted
series over `B` is available.
Neither completeness of `A` nor completeness of `B` is required.

This gives the cancellation assertion of Wedhorn's Proposition 6.33(2) when the original base
`A` is Tate: topological finite type over `A` is then strict topological finite type. It supplies
the underlying ring assertion for finite-type cancellation of Huber pairs over a Tate source;
the condition on the plus rings must be checked separately. It also applies when changing the
target affinoid neighborhood of a morphism locally of weakly finite type.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.33(2),
  Proposition 6.34, Proposition 8.46(2), and Proposition 8.50.
-/

public section

open Topology UniformSpace

namespace TauCeti.Huber

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C]
  [CompleteSpace C] [T0Space C] {φ : A →+* B} {ψ : B →+* C}

/-- **Strict topological finite type cancels on the right.** If the composite of continuous
homomorphisms `A → B → C` out of a Huber ring `A` is strictly topologically of finite type,
then `B → C` is strictly topologically of finite type. Only the final target is required to be
complete and Hausdorff. -/
theorem IsStrictlyTopologicallyFiniteType.of_comp [IsHuberRing A]
    (h : IsStrictlyTopologicallyFiniteType (ψ.comp φ)) (hφ : Continuous φ)
    (hψ : Continuous ψ) : IsStrictlyTopologicallyFiniteType ψ := by
  obtain ⟨k, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  let b : Fin k → C := fun i ↦ π (weightedX (fun _ ↦ ({1} : Set A))
    isWeightFamily_one_weight i)
  have hb : ∀ i, IsPowerBounded (b i) := fun i ↦
    (isPowerBounded_completion_coe_of_isPowerBounded
      (isPowerBounded_weightedX_one_weight i)).map_of_isOpenMap
        hπ.continuous.continuousAt hπ.isOpenMap
  let ρ := weightedEvalHomCompletion (φ := ψ) isWeightFamily_one_weight hψ.continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded ψ b).mpr hb)
  have hρ : Continuous ρ := continuous_weightedEvalHomCompletion ..
  have hweights : ∀ i : Fin k, φ '' ({1} : Set A) ⊆ ({1} : Set B) := by simp
  let α := weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight hweights
  have hα : Continuous α := continuous_weightedMapCompletion ..
  -- The original open quotient factors through evaluation over the larger coefficient ring.
  have hfactor : ρ.comp α = π := by
    apply completion_weightedRestrictedSubring_ringHom_ext_of_continuous
      isWeightFamily_one_weight (f := ρ.comp α) (g := π) (hρ.comp hα) hπ.continuous
    · intro a
      have ha := RingHom.congr_fun hcomm a
      simpa [ρ, α] using ha.symm
    · intro i
      simp [ρ, α, b]
  -- A continuous factor of a quotient map is quotient; for additive groups it is also open.
  have hopen : IsOpenQuotientMap ρ :=
    AddMonoidHom.isOpenQuotientMap_of_isQuotientMap <|
      IsQuotientMap.of_comp hα hρ (by
        simpa only [← hfactor, RingHom.coe_comp] using hπ.isQuotientMap)
  refine isStrictlyTopologicallyFiniteType_iff.mpr ⟨k, ρ, hopen, ?_⟩
  ext a
  simp [ρ]

/-- **Wedhorn Proposition 6.33(2), over a Tate base.** If `A → B → C` are continuous ring
homomorphisms, `A` is Tate and `C` is complete and Hausdorff, then topological
finite type of the composite implies topological finite type of `B → C`. -/
theorem IsTopologicallyFiniteType.of_comp [IsTateRing A]
    (h : IsTopologicallyFiniteType (ψ.comp φ)) (hφ : Continuous φ)
    (hψ : Continuous ψ) : IsTopologicallyFiniteType ψ := by
  exact (h.isStrictlyTopologicallyFiniteType.of_comp hφ hψ).isTopologicallyFiniteType

end TauCeti.Huber
