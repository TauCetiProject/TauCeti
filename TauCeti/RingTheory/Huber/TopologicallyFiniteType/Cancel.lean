/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

import TauCeti.RingTheory.Huber.WeightedEval.Completion
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.OfDefinition
import TauCeti.RingTheory.Huber.WeightedEval.Finite
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenIdeal

/-!
# Cancellation of topological finite type

For continuous ring homomorphisms `φ : A → B` and `ψ : B → C`, with `A` Huber and `B`, `C`
nonarchimedean, a strict finite-type presentation of `ψ ∘ φ` also gives a strict finite-type
presentation of `ψ`. The target `C` must be complete and Hausdorff, so evaluation of restricted
series over `B` is available.
Neither completeness of `A` nor completeness of `B` is required.

This gives the cancellation assertion of Wedhorn's Proposition 6.33(2) when the original base
`A` is Tate: topological finite type over `A` is then strict topological finite type.

For morphisms of Huber pairs, weighted presentations give cancellation without a Tate hypothesis
(Wedhorn, Proposition 8.46(2)). A presentation of `g ∘ f` factors through evaluation over `B`.
The new weights contain the images of the original weights and finitely many small generators of
open ideals of `B`; their evaluated weighted variables lie in `C⁺`. The plus ring `C⁺` is integral
over the image of the original completed plus ring, which is contained in the image of the new
one, so evaluation is a quotient mapping of pairs.

This permits shrinking the target affinoid of a finite-type chart: if
`(A, A⁺) → (C, C⁺)` is topologically of finite type and factors through a rational localisation
`(A, A⁺) → (B, B⁺)`, then `(B, B⁺) → (C, C⁺)` is again topologically of finite type, including
when `A` is not Tate.

## Main results

* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.of_comp`: strict topological finite type
  cancels on the right, over a Huber base.
* `TauCeti.Huber.IsTopologicallyFiniteType.of_comp`: Wedhorn Proposition 6.33(2) over a Tate base.
* `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.of_comp`: if the composite of morphisms of
  Huber pairs `(A, A⁺) → (B, B⁺) → (C, C⁺)` is topologically of finite type, with
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

omit [IsTopologicalRing A] in
/-- A weighted presentation of a composite factors through evaluation over the intermediate
coefficient ring, whenever the new weights contain the images of the old ones and their evaluated
weighted variables are bounded. -/
private theorem exists_isOpenQuotientMap_comp_weightedMapCompletion_eq
    [NonarchimedeanRing A] {k : ℕ}
    {T : Fin k → Set A} {T' : Fin k → Set B} (hT : IsWeightFamily T)
    (hT' : IsWeightFamily T') (hTT' : ∀ i, φ '' T i ⊆ T' i)
    {π : Completion (weightedRestrictedSubring T hT) →+* C} (hπ : IsOpenQuotientMap π)
    (hcomm : π.comp (algebraMap A (Completion (weightedRestrictedSubring T hT))) = ψ.comp φ)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hb : IsWeightBounded ψ T' (fun i ↦ π (weightedX T hT i))) :
    ∃ ρ : Completion (weightedRestrictedSubring T' hT') →+* C, IsOpenQuotientMap ρ ∧
      ρ.comp (algebraMap B (Completion (weightedRestrictedSubring T' hT'))) = ψ ∧
      ρ.comp (weightedMapCompletion hφ hT hT' hTT') = π := by
  let ρ := weightedEvalHomCompletion hT' hψ.continuousAt hb
  have hρ : Continuous ρ := continuous_weightedEvalHomCompletion ..
  let α := weightedMapCompletion hφ hT hT' hTT'
  have hα : Continuous α := continuous_weightedMapCompletion ..
  -- Constants and variables determine continuous maps from the completed weighted algebra.
  have hfactor : ρ.comp α = π := by
    apply completion_weightedRestrictedSubring_ringHom_ext_of_continuous
      hT (f := ρ.comp α) (g := π) (hρ.comp hα) hπ.continuous
    · intro a
      have ha := RingHom.congr_fun hcomm a
      simpa [ρ, α] using ha.symm
    · intro i
      simp [ρ, α]
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
  have hb : ∀ i : Fin k, IsPowerBounded (π (weightedX (fun _ ↦ ({1} : Set A))
      isWeightFamily_one_weight i)) := fun i ↦
    (isPowerBounded_completion_coe_of_isPowerBounded
      (isPowerBounded_weightedX_one_weight i)).map_of_isOpenMap
        hπ.continuous.continuousAt hπ.isOpenMap
  obtain ⟨ρ, hρ, hρψ, -⟩ :=
    exists_isOpenQuotientMap_comp_weightedMapCompletion_eq isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ by simp) hπ hcomm hφ hψ
      ((isWeightBounded_one_weight_iff_forall_isPowerBounded ψ _).mpr hb)
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

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [CompleteSpace C]
  [T0Space C] [IsHuberRing C] {S : Pair A} {U : Pair B} {V : Pair C}

/-- A weighted quotient presentation of `g ∘ f` gives a weighted quotient presentation of `g`.
Enlarge the coefficientwise images of the weights by small generators of open ideals so that they
are admissible over the intermediate Huber ring. -/
private theorem exists_isQuotientMapping_of_comp {k : ℕ} {T : Fin k → Set A}
    (hTfin : ∀ i, (T i).Finite) (hT : IsWeightFamily T) {f : Hom S U} {g : Hom U V}
    {π : Hom (S.weighted hT).completion V} (hπ : π.IsQuotientMapping)
    (hcomm : π.comp (S.weightedCompletionHom hT) = g.comp f) :
    ∃ (T' : Fin k → Set B) (_ : ∀ i, (T' i).Finite) (hT' : IsWeightFamily T')
      (ρ : Hom (U.weighted hT').completion V),
      ρ.IsQuotientMapping ∧ ρ.comp (U.weightedCompletionHom hT') = g := by
  classical
  let b : Fin k → C := fun i ↦ π.toRingHom (weightedX T hT i)
  have hcomm' : π.toRingHom.comp (algebraMap A (Completion (weightedRestrictedSubring T hT))) =
      g.toRingHom.comp f.toRingHom := by
    rw [← Hom.toRingHom_weightedCompletionHom, ← Hom.toRingHom_comp, hcomm, Hom.toRingHom_comp]
  have hgen (i : Fin k) (t : A) (ht : t ∈ T i) :
      g.toRingHom (f.toRingHom t) * b i ∈ V.plus := by
    have hx := π.map_mem_plus _
      (S.weightedC_mul_weightedX_mem_weighted_completion_plus hT ht)
    simp only [Completion.coe_mul, map_mul] at hx
    rw [← algebraMap_completion_weightedRestrictedSubring_apply, ← RingHom.comp_apply,
      hcomm'] at hx
    simpa only [RingHom.comp_apply, b] using hx
  -- The plus ring is open: each evaluated variable admits small coefficients lying in it.
  have hsmall (i : Fin k) :
      {t : B | g.toRingHom t * b i ∈ V.plus} ∈ nhds (0 : B) := by
    exact ((V.isRingOfIntegralElements.isOpen.preimage
      (g.continuous_toRingHom.mul_const (b i))).mem_nhds (by simp))
  choose G hG hGopen using fun i ↦ exists_finset_subset_isOpen_span (hsmall i)
  let T' : Fin k → Set B := fun i ↦ f.toRingHom '' T i ∪ (G i : Set B)
  have hT'fin : ∀ i, (T' i).Finite := fun i ↦
    ((hTfin i).image _).union (G i).finite_toSet
  have hTT' : ∀ i, f.toRingHom '' T i ⊆ T' i := fun _ ↦ Set.subset_union_left
  have hT' : IsWeightFamily T' := isWeightFamily_iff_isOpen_span.mpr fun i ↦
    Ideal.isOpen_of_isOpen_subideal (Ideal.span_mono Set.subset_union_right) (hGopen i)
  have hplus (i : Fin k) (t : B) (ht : t ∈ T' i) : g.toRingHom t * b i ∈ V.plus := by
    rcases ht with ⟨t, ht, rfl⟩ | ht
    · exact hgen i t ht
    · exact hG i ht
  have hb : IsWeightBounded g.toRingHom T' b :=
    isWeightBounded_of_isWeightedVarPowerBounded <|
      (isWeightedVarPowerBounded_iff_of_finite hT'fin).mpr fun i t ht ↦
        V.isRingOfIntegralElements.isPowerBounded_of_mem (hplus i t ht)
  obtain ⟨ρ, hρ, hρg, hρπ⟩ := exists_isOpenQuotientMap_comp_weightedMapCompletion_eq
    hT hT' hTT' hπ.isOpenQuotientMap hcomm' f.continuous_toRingHom g.continuous_toRingHom hb
  -- Evaluation respects the plus rings because it respects their constants and weighted variables.
  let ρ' : Hom (U.weighted hT').completion V :=
    { toRingHom := ρ
      continuous_toRingHom := hρ.continuous
      map_mem_plus := U.weighted_completion_plus_le_comap hT' V hρ.continuous
        (fun t ht ↦ by
          rw [← algebraMap_completion_weightedRestrictedSubring_apply, ← RingHom.comp_apply, hρg]
          exact g.map_mem_plus t ht)
        (fun i t ht ↦ by
          have hi := RingHom.congr_fun hρπ
            (weightedX T hT i : Completion (weightedRestrictedSubring T hT))
          simp only [RingHom.comp_apply, weightedMapCompletion_coe, weightedMap_weightedX] at hi
          rw [Completion.coe_mul, map_mul,
            ← algebraMap_completion_weightedRestrictedSubring_apply, ← RingHom.comp_apply, hρg,
            hi]
          exact hplus i t ht) }
  -- Integrality over the old image implies integrality over the larger image of the new plus ring.
  have hle : (S.weighted hT).completion.plus.map π.toRingHom ≤
      (U.weighted hT').completion.plus.map ρ := fun y hy ↦ by
    obtain ⟨x, hx, rfl⟩ := Subring.mem_map.mp hy
    exact Subring.mem_map.mpr
      ⟨_, weighted_completion_plus_le_comap_weightedMapCompletion _ f _ _ hx,
        RingHom.congr_fun hρπ x⟩
  refine ⟨T', hT'fin, hT', ρ',
    (Hom.isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral ρ').mpr ⟨hρ, ?_⟩,
    Hom.ext ?_⟩
  · exact fun c hc ↦ (hπ.mem_plus_iff.mp hc).map_of_comp_eq
      (Subring.inclusion hle) (RingHom.id C) (by ext; rfl)
  · rw [Hom.toRingHom_comp, Hom.toRingHom_weightedCompletionHom]
    exact hρg

/-- **Topological finite type of morphisms of Huber pairs cancels on the right**: if
`f : (A, A⁺) → (B, B⁺)` and `g : (B, B⁺) → (C, C⁺)` have composite topologically of finite type
and `C` is complete and Hausdorff, then `g` is topologically of finite type. This is Wedhorn's
Proposition 8.46(2). Neither a Tate hypothesis nor completeness of `A` or `B` is required. -/
theorem Hom.IsTopologicallyFiniteType.of_comp {f : Hom S U} {g : Hom U V}
    (h : (g.comp f).IsTopologicallyFiniteType) : g.IsTopologicallyFiniteType := by
  obtain ⟨k, T, hTfin, hT, π, hπ, hcomm⟩ := isTopologicallyFiniteType_iff.mp h
  obtain ⟨T', hT'fin, hT', ρ, hρ, hρg⟩ := exists_isQuotientMapping_of_comp hTfin hT hπ hcomm
  exact isTopologicallyFiniteType_iff.mpr ⟨k, T', hT'fin, hT', ρ, hρ, hρg⟩

end Pair

end TauCeti.Huber
