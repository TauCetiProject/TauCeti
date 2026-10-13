/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

import TauCeti.RingTheory.Huber.WeightedEval.Completion
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Cancellation of topological finite type

For continuous ring homomorphisms `φ : A → B` and `ψ : B → C`, with `A` Huber and `B`, `C`
nonarchimedean, a strict finite-type presentation of `ψ ∘ φ` also gives a strict finite-type
presentation of `ψ`. The target `C` must be complete and Hausdorff, so evaluation of restricted
series over `B` is available.
Neither completeness of `A` nor completeness of `B` is required.

This gives the cancellation assertion of Wedhorn's Proposition 6.33(2) when the original base
`A` is Tate: topological finite type over `A` is then strict topological finite type.

The same presentation cancels morphisms of Huber pairs topologically of finite type (Wedhorn,
Definition 8.42), where the plus rings must be controlled as well. A presentation
`π : (A⟨X₁, …, Xₖ⟩, A⟨X⟩⁺) ↠ (C, C⁺)` of `g ∘ f` factors through the coefficientwise map
`(A⟨X⟩, A⟨X⟩⁺) → (B⟨X⟩, B⟨X⟩⁺)` induced by `f`, by evaluation `ρ : B⟨X⟩ → C` at the images
`π(Xᵢ)`. The plus ring `C⁺` is integral over the image under `π` of the plus ring of `A⟨X⟩`, which
is contained in the image under `ρ` of the plus ring of `B⟨X⟩`, so `ρ` is a quotient mapping of
pairs. This is what is needed to shrink the target affinoid of a chart of a morphism locally of
finite type: if `A` is Tate, `B` is complete and Hausdorff, `(A, A⁺) → (B, B⁺)` is topologically
of finite type and it factors through a rational localisation `(A, A⁺) → (A', A'⁺)`, then
`(A', A'⁺) → (B, B⁺)` is again topologically of finite type.

## Main results

* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.of_comp`: strict topological finite type
  cancels on the right, over a Huber base.
* `TauCeti.Huber.IsTopologicallyFiniteType.of_comp`: Wedhorn Proposition 6.33(2) over a Tate base.
* `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.of_comp`: if the composite of morphisms of
  Huber pairs `(A, A⁺) → (B, B⁺) → (C, C⁺)` is topologically of finite type, with `A` Tate and
  `C` complete and Hausdorff, then so is `(B, B⁺) → (C, C⁺)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.33(2),
  Proposition 6.34, Definition 8.42, Proposition 8.46(2), and Proposition 8.50.
-/

public section

open Topology UniformSpace

namespace TauCeti.Huber

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C]
  [CompleteSpace C] [T0Space C] {φ : A →+* B} {ψ : B →+* C}

/-- The factorisation behind cancellation: a presentation `π : A⟨X₁, …, Xₖ⟩ ↠ C` of `ψ ∘ φ`
factors through the coefficientwise map `A⟨X⟩ → B⟨X⟩` by an open quotient map
`ρ : B⟨X₁, …, Xₖ⟩ ↠ C` presenting `ψ`, namely evaluation at the images `π(Xᵢ)`. -/
private theorem exists_isOpenQuotientMap_comp_weightedMapCompletion_eq [IsHuberRing A] {k : ℕ}
    {π : restrictedMvPowerSeriesCompletion k A →+* C} (hπ : IsOpenQuotientMap π)
    (hcomm : π.comp (algebraMap A (restrictedMvPowerSeriesCompletion k A)) = ψ.comp φ)
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    ∃ ρ : restrictedMvPowerSeriesCompletion k B →+* C, IsOpenQuotientMap ρ ∧
      ρ.comp (algebraMap B (restrictedMvPowerSeriesCompletion k B)) = ψ ∧
      ρ.comp (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight
        fun _ ↦ by simp) = π := by
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
  exact ⟨ρ, hopen, RingHom.ext fun a ↦ by simp [ρ], hfactor⟩

/-- **Strict topological finite type cancels on the right.** If the composite of continuous
homomorphisms `A → B → C` out of a Huber ring `A` is strictly topologically of finite type,
then `B → C` is strictly topologically of finite type. Only the final target is required to be
complete and Hausdorff. -/
theorem IsStrictlyTopologicallyFiniteType.of_comp [IsHuberRing A]
    (h : IsStrictlyTopologicallyFiniteType (ψ.comp φ)) (hφ : Continuous φ)
    (hψ : Continuous ψ) : IsStrictlyTopologicallyFiniteType ψ := by
  obtain ⟨k, π, hπ, hcomm⟩ := isStrictlyTopologicallyFiniteType_iff.mp h
  obtain ⟨ρ, hρ, hρψ, -⟩ :=
    exists_isOpenQuotientMap_comp_weightedMapCompletion_eq hπ hcomm hφ hψ
  exact isStrictlyTopologicallyFiniteType_iff.mpr ⟨k, ρ, hρ, hρψ⟩

/-- **Wedhorn Proposition 6.33(2), over a Tate base.** If `A → B → C` are continuous ring
homomorphisms, `A` is Tate and `C` is complete and Hausdorff, then topological
finite type of the composite implies topological finite type of `B → C`. -/
theorem IsTopologicallyFiniteType.of_comp [IsTateRing A]
    (h : IsTopologicallyFiniteType (ψ.comp φ)) (hφ : Continuous φ)
    (hψ : Continuous ψ) : IsTopologicallyFiniteType ψ := by
  exact (h.isStrictlyTopologicallyFiniteType.of_comp hφ hψ).isTopologicallyFiniteType

namespace Pair

/-! ### Morphisms of Huber pairs -/

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [CompleteSpace C]
  [T0Space C] [IsHuberRing C] {S : Pair A} {U : Pair B} {V : Pair C}

/-- **Topological finite type of morphisms of Huber pairs cancels on the right**, over a Tate
base: if `f : (A, A⁺) → (B, B⁺)` and `g : (B, B⁺) → (C, C⁺)` are morphisms of Huber pairs with
`A` Tate and `C` complete and Hausdorff, and `g ∘ f` is topologically of finite type, then so is
`g`. This is the cancellation statement of Wedhorn's Proposition 8.46, and the pair form of
`TauCeti.Huber.IsTopologicallyFiniteType.of_comp`: the presentation of `g` also controls the plus
ring `C⁺`. No completeness of `A` or `B` is assumed. -/
theorem Hom.IsTopologicallyFiniteType.of_comp {f : Hom S U} {g : Hom U V}
    (h : (g.comp f).IsTopologicallyFiniteType) : g.IsTopologicallyFiniteType := by
  obtain ⟨k, π, hπ, hcomm⟩ := h.exists_isQuotientMapping_one_weight
  have hcomm' : π.toRingHom.comp (algebraMap A (restrictedMvPowerSeriesCompletion k A)) =
      g.toRingHom.comp f.toRingHom := by
    rw [← Hom.toRingHom_weightedCompletionHom, ← Hom.toRingHom_comp, hcomm, Hom.toRingHom_comp]
  obtain ⟨ρ, hρ, hρg, hρπ⟩ := exists_isOpenQuotientMap_comp_weightedMapCompletion_eq
    hπ.isOpenQuotientMap hcomm' f.continuous_toRingHom g.continuous_toRingHom
  -- `ρ` sends the constants from `B⁺` into `C⁺` as `g` does, and the variables to `π(Xᵢ) ∈ C⁺`
  let ρ' : Hom (U.weighted (isWeightFamily_one_weight (k := k))).completion V :=
    { toRingHom := ρ
      continuous_toRingHom := hρ.continuous
      map_mem_plus := U.weighted_completion_plus_le_comap _ V hρ.continuous
        (fun b hb ↦ by
          rw [← algebraMap_completion_weightedRestrictedSubring_apply, ← RingHom.comp_apply, hρg]
          exact g.map_mem_plus b hb)
        (fun i t ht ↦ by
          obtain rfl := Set.mem_singleton_iff.mp ht
          have hx := π.map_mem_plus _ (S.weightedC_mul_weightedX_mem_weighted_completion_plus
            isWeightFamily_one_weight (i := i) (Set.mem_singleton 1))
          rwa [← hρπ, RingHom.comp_apply, weightedMapCompletion_coe, map_mul,
            weightedMap_weightedC, weightedMap_weightedX, map_one] at hx) }
  -- the image of the plus ring of `A⟨X⟩` under `π` lies in the image of that of `B⟨X⟩` under `ρ`
  have hle : (S.weighted isWeightFamily_one_weight).completion.plus.map π.toRingHom ≤
      (U.weighted isWeightFamily_one_weight).completion.plus.map ρ := fun y hy ↦ by
    obtain ⟨x, hx, rfl⟩ := Subring.mem_map.mp hy
    exact Subring.mem_map.mpr
      ⟨_, weighted_completion_plus_le_comap_weightedMapCompletion _ f _ _ hx,
        RingHom.congr_fun hρπ x⟩
  refine isTopologicallyFiniteType_iff.mpr ⟨k, fun _ ↦ {1}, fun _ ↦ Set.finite_singleton 1,
    isWeightFamily_one_weight, ρ',
      (Hom.isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral ρ').mpr ⟨hρ, fun c hc ↦ ?_⟩,
      Hom.ext ?_⟩
  · -- `c` is integral over the image of the plus ring of `A⟨X⟩`, hence over the larger image
    exact (hπ.mem_plus_iff.mp hc).map_of_comp_eq (Subring.inclusion hle) (RingHom.id C)
      (by ext; rfl)
  · rw [Hom.toRingHom_comp, Hom.toRingHom_weightedCompletionHom]
    exact hρg

end Pair

end TauCeti.Huber
