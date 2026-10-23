/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair
import TauCeti.RingTheory.Huber.WeightedEval.Finite
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenIdeal

/-!
# Partly unweighted presentations of Huber pairs

A completed weighted pair over a Huber ring admits a quotient presentation with two blocks of
variables: the original variables with new weights, and unweighted variables representing the
old weighted variables. The new weighted variables must belong to the original plus ring.
The resulting map is a quotient mapping of pairs, including the integral-closure condition on
the plus rings, rather than just an open quotient of rings.

For a morphism of Huber pairs topologically of finite type, the new weights can be chosen as
images of finite subsets of the source ring. This puts the weights of a second presentation
over the original coefficient ring, as required to flatten successive weighted presentations.
Neither coefficient ring needs to be Tate, complete, or Hausdorff.

The underlying open quotient is
`TauCeti.Huber.exists_isOpenQuotientMap_completion_weightedRestrictedSubring_append`.
The plus-ring argument follows the generator criterion and the unweighted presentation in
`TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark and Definition 8.41 and
  Proposition 8.46(1).
-/

public section

open UniformSpace Topology

namespace TauCeti.Huber.Pair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (S : Pair A) {k : ℕ} {T V : Fin k → Set A}

/-- A completed weighted Huber pair is a quotient of a partly unweighted pair, with any finite
new weights whose weighted variables lie in the original plus ring. The additional unweighted
variables lift all the old weighted variables, so the target plus ring is the integral closure
of the image of the source plus ring. -/
theorem exists_isQuotientMapping_weightedCompletionHom_append
    (hT : IsWeightFamily T) (hTfin : ∀ i, (T i).Finite)
    (hV : IsWeightFamily V) (hVfin : ∀ i, (V i).Finite)
    (hVX : ∀ i, ∀ a ∈ V i,
      ((weightedC T hT a * weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) ∈ (S.weighted hT).completion.plus) :
    ∃ (m : ℕ) (θ : Hom
      (S.weighted (hV.append (isWeightFamily_one_weight (k := m)))).completion
      (S.weighted hT).completion), θ.IsQuotientMapping ∧
        θ.comp (S.weightedCompletionHom (hV.append isWeightFamily_one_weight)) =
          S.weightedCompletionHom hT := by
  have hb : IsWeightedVarPowerBounded
      (algebraMap A (Completion (weightedRestrictedSubring T hT))) V
      (fun i ↦ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT))) := by
    apply (isWeightedVarPowerBounded_iff_of_finite hVfin).mpr
    intro i a ha
    simpa only [algebraMap_completion_weightedRestrictedSubring_apply, ← Completion.coe_mul]
      using (S.weighted hT).completion.isRingOfIntegralElements.isPowerBounded_of_mem (hVX i a ha)
  obtain ⟨m, idx, t, htT, ht, θ, hθ, hθA, hθX, hθY⟩ :=
    exists_isOpenQuotientMap_completion_weightedRestrictedSubring_append hT hTfin hV hb
  have hθC (a : A) : θ ((weightedC (Fin.append V fun _ : Fin m ↦ ({1} : Set A))
      (hV.append isWeightFamily_one_weight) a : weightedRestrictedSubring _ _) :
        Completion (weightedRestrictedSubring _ _)) =
        ((weightedC T hT a : weightedRestrictedSubring T hT) : Completion _) := by
    simpa only [RingHom.comp_apply, algebraMap_completion_weightedRestrictedSubring_apply]
      using RingHom.congr_fun hθA a
  -- The first block uses the new plus-ring hypothesis; the second lifts the old generators.
  let θ' : Hom (S.weighted (hV.append (isWeightFamily_one_weight (k := m)))).completion
      (S.weighted hT).completion :=
    { toRingHom := θ
      continuous_toRingHom := hθ.continuous
      map_mem_plus := S.weighted_completion_plus_le_comap _ _ hθ.continuous
        (fun a ha ↦ by
          rw [hθC]
          exact S.weightedC_mem_weighted_completion_plus hT ha)
        (by
          intro l
          refine Fin.addCases (fun i a ha ↦ ?_) (fun j a ha ↦ ?_) l
          · rw [Fin.append_left] at ha
            rw [Completion.coe_mul, map_mul, hθC, hθX, ← Completion.coe_mul]
            exact hVX i a ha
          · rw [Fin.append_right, Set.mem_singleton_iff] at ha
            subst a
            simpa only [map_one, one_mul, hθY] using
              S.weightedC_mul_weightedX_mem_weighted_completion_plus hT (htT j)) }
  -- Constants and old weighted variables lift from the source plus ring, hence are integral
  -- over its image. The closed integral closure then contains the entire target plus ring.
  have hint : ∀ x ∈ (S.weighted (hV.append (isWeightFamily_one_weight (k := m)))).completion.plus,
      IsIntegral ((S.weighted (hV.append isWeightFamily_one_weight)).completion.plus.map θ)
        (θ x) := fun x hx ↦
    isIntegral_algebraMap (R := (S.weighted _).completion.plus.map θ)
      (x := ⟨θ x, Subring.mem_map.mpr ⟨x, hx, rfl⟩⟩)
  refine ⟨m, θ', Hom.isQuotientMapping_of_isIntegral_weighted θ' hθ (fun a ha ↦ ?_)
    (fun i a ha ↦ ?_), Hom.ext ?_⟩
  · rw [← hθC]
    exact hint _ (S.weightedC_mem_weighted_completion_plus _ ha)
  · obtain ⟨j, rfl, rfl⟩ := ht i a ha
    rw [← hθY]
    exact hint _ (by
      simpa only [map_one, one_mul] using
        S.weightedC_mul_weightedX_mem_weighted_completion_plus
          (hV.append isWeightFamily_one_weight)
          (i := Fin.natAdd k j) (t := 1) (by simp))
  · rw [Hom.toRingHom_comp, Hom.toRingHom_weightedCompletionHom,
      Hom.toRingHom_weightedCompletionHom]
    exact hθA

variable {S} {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {U : Pair B}

/-- When a morphism of Huber pairs carries open ideals to ideals generating open ideals, the
weights in a partly unweighted presentation over its target can be chosen as images of finite
weight sets in its source. In particular, this applies to a morphism topologically of finite
type. The presentation is a quotient mapping of pairs over the target coefficient pair. -/
theorem exists_isQuotientMapping_weightedCompletionHom_image_append
    (f : Hom S U)
    (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map f.toRingHom : Set B))
    {T : Fin k → Set B} (hT : IsWeightFamily T) (hTfin : ∀ i, (T i).Finite) :
    ∃ (V : Fin k → Finset A) (_ : IsWeightFamily (fun i ↦ (V i : Set A)))
      (hW : IsWeightFamily (fun i ↦ f.toRingHom '' (V i : Set A)))
      (m : ℕ) (θ : Hom (U.weighted (hW.append (isWeightFamily_one_weight (k := m)))).completion
        (U.weighted hT).completion), θ.IsQuotientMapping ∧
          θ.comp (U.weightedCompletionHom (hW.append isWeightFamily_one_weight)) =
            U.weightedCompletionHom hT := by
  classical
  -- Openness of the plus ring supplies small coefficients for each original variable.
  have hsmall (i : Fin k) :
      {a : A | ((weightedC T hT (f.toRingHom a) * weightedX T hT i :
        weightedRestrictedSubring T hT) : Completion (weightedRestrictedSubring T hT)) ∈
          (U.weighted hT).completion.plus} ∈ nhds (0 : A) := by
    have hc : Continuous fun a : A ↦
        ((weightedC T hT (f.toRingHom a) * weightedX T hT i :
          weightedRestrictedSubring T hT) : Completion (weightedRestrictedSubring T hT)) :=
      (Completion.continuous_coe _).comp
        (((continuous_weightedC hT).comp f.continuous_toRingHom).mul_const _)
    exact (((U.weighted hT).completion.isRingOfIntegralElements.isOpen.preimage hc).mem_nhds
      (by simp))
  choose V hV hVopen using fun i ↦ exists_finset_subset_isOpen_span (hsmall i)
  have hVweight : IsWeightFamily (fun i ↦ (V i : Set A)) :=
    isWeightFamily_iff_isOpen_span.mpr hVopen
  have hW : IsWeightFamily (fun i ↦ f.toRingHom '' (V i : Set A)) := by
    apply isWeightFamily_iff_isOpen_span.mpr
    intro i
    rw [← Ideal.map_span]
    exact hopen (hVopen i)
  obtain ⟨m, θ, hθ, hθA⟩ := U.exists_isQuotientMapping_weightedCompletionHom_append hT hTfin hW
    (fun i ↦ (V i).finite_toSet.image _) (by
      rintro i _ ⟨a, ha, rfl⟩
      exact hV i ha)
  exact ⟨V, hVweight, hW, m, θ, hθ, hθA⟩

end TauCeti.Huber.Pair
