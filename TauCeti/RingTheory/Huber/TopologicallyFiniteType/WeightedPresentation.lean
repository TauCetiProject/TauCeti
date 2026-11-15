/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair
import TauCeti.RingTheory.Huber.WeightedEval.Finite
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate.Pair
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenIdeal
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenQuotient

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
`Pair.exists_openQuotientMap_of_weighted_presentation` refines a quotient presentation of the
target by a finite weight family on the target, adding the unweighted variables that enumerate it.

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

/-- If every product of a coefficient from `V i` with the `i`-th weighted variable lies in the plus
ring of the completed weighted pair, then the weighted variables are power bounded with respect to
the weights `V`. -/
private theorem isWeightedVarPowerBounded_weightedX_of_mem_plus
    (hT : IsWeightFamily T) (hVfin : ∀ i, (V i).Finite)
    (hVX : ∀ i, ∀ a ∈ V i,
      ((weightedC T hT a * weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) ∈ (S.weighted hT).completion.plus) :
    IsWeightedVarPowerBounded
      (algebraMap A (Completion (weightedRestrictedSubring T hT))) V
      (fun i ↦ ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT))) := by
  apply (isWeightedVarPowerBounded_iff_of_finite hVfin).mpr
  intro i a ha
  simpa only [algebraMap_completion_weightedRestrictedSubring_apply, ← Completion.coe_mul]
    using (S.weighted hT).completion.isRingOfIntegralElements.isPowerBounded_of_mem (hVX i a ha)

/-- A continuous ring homomorphism from the completed weighted power series with the extra
unweighted variables `Xⱼ ↦ tⱼ Xᵢ` to the completed power series for `T`, which is compatible with
the coefficients and sends the variables as prescribed, is a morphism of pairs, provided the new
weights `V` satisfy that `a Xᵢ` lies in the target plus ring for `a ∈ V i`. -/
theorem exists_hom_toRingHom_eq_of_weightedX {m : ℕ} {idx : Fin m → Fin k} {t : Fin m → A}
    (hT : IsWeightFamily T) (htT : ∀ j, t j ∈ T (idx j)) (hV : IsWeightFamily V)
    (hVX : ∀ i, ∀ a ∈ V i,
      ((weightedC T hT a * weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)) ∈ (S.weighted hT).completion.plus)
    (θ : Completion (weightedRestrictedSubring (Fin.append V fun _ : Fin m ↦ ({1} : Set A))
      (hV.append isWeightFamily_one_weight)) →+* Completion (weightedRestrictedSubring T hT))
    (hθc : Continuous θ)
    (hθA : θ.comp (algebraMap A _) = algebraMap A (Completion (weightedRestrictedSubring T hT)))
    (hθX : ∀ i, θ (weightedX _ (hV.append isWeightFamily_one_weight) (Fin.castAdd m i) :
        weightedRestrictedSubring _ _) =
      ((weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)))
    (hθY : ∀ j, θ (weightedX _ (hV.append isWeightFamily_one_weight) (Fin.natAdd k j) :
        weightedRestrictedSubring _ _) =
      ((weightedC T hT (t j) * weightedX T hT (idx j) : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT))) :
    ∃ θ' : Hom (S.weighted (hV.append (isWeightFamily_one_weight (k := m)))).completion
      (S.weighted hT).completion, θ'.toRingHom = θ := by
  have hθC (a : A) : θ ((weightedC (Fin.append V fun _ : Fin m ↦ ({1} : Set A))
      (hV.append isWeightFamily_one_weight) a : weightedRestrictedSubring _ _) :
        Completion (weightedRestrictedSubring _ _)) =
        ((weightedC T hT a : weightedRestrictedSubring T hT) : Completion _) := by
    simpa only [RingHom.comp_apply, algebraMap_completion_weightedRestrictedSubring_apply]
      using RingHom.congr_fun hθA a
  -- The first block uses the new plus-ring hypothesis; the second lifts the old generators.
  exact ⟨{ toRingHom := θ
           continuous_toRingHom := hθc
           map_mem_plus := S.weighted_completion_plus_le_comap _ _ hθc
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
                   S.weightedC_mul_weightedX_mem_weighted_completion_plus hT (htT j)) }, rfl⟩

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
  obtain ⟨m, idx, t, htT, ht, θ, hθ, hθA, hθX, hθY⟩ :=
    exists_isOpenQuotientMap_completion_weightedRestrictedSubring_append hT hTfin hV
      (S.isWeightedVarPowerBounded_weightedX_of_mem_plus hT hVfin hVX)
  obtain ⟨θ', rfl⟩ := exists_hom_toRingHom_eq_of_weightedX S hT htT hV hVX θ hθ.continuous hθA
    hθX hθY
  have hθC (a : A) : θ'.toRingHom ((weightedC (Fin.append V fun _ : Fin m ↦ ({1} : Set A))
      (hV.append isWeightFamily_one_weight) a : weightedRestrictedSubring _ _) :
        Completion (weightedRestrictedSubring _ _)) =
        ((weightedC T hT a : weightedRestrictedSubring T hT) : Completion _) := by
    simpa only [RingHom.comp_apply, algebraMap_completion_weightedRestrictedSubring_apply]
      using RingHom.congr_fun hθA a
  -- Constants and old weighted variables lift from the source plus ring, hence are integral
  -- over its image. The closed integral closure then contains the entire target plus ring.
  have hint : ∀ x ∈ (S.weighted (hV.append (isWeightFamily_one_weight (k := m)))).completion.plus,
      IsIntegral
        ((S.weighted (hV.append isWeightFamily_one_weight)).completion.plus.map θ'.toRingHom)
        (θ'.toRingHom x) := fun x hx ↦
    isIntegral_algebraMap (R := (S.weighted _).completion.plus.map θ'.toRingHom)
      (x := ⟨θ'.toRingHom x, Subring.mem_map.mpr ⟨x, hx, rfl⟩⟩)
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

/-- When a morphism of Huber pairs `f` carries open ideals to ideals generating open ideals,
every weight family `T` over the target admits finite weights `V` over the source, generating an
open ideal, such that `f(V)` generates an open ideal and `f a Xᵢ` lies in the plus ring of the
completed weighted power series for `T` whenever `a ∈ V i`. -/
theorem exists_finset_weights_image_mem_plus (f : Hom S U)
    (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map f.toRingHom : Set B))
    {T : Fin k → Set B} (hT : IsWeightFamily T) :
    ∃ (V : Fin k → Finset A) (_ : IsWeightFamily (fun i ↦ (V i : Set A)))
      (_ : IsWeightFamily (fun i ↦ f.toRingHom '' (V i : Set A))),
      ∀ i, ∀ a ∈ V i, ((weightedC T hT (f.toRingHom a) * weightedX T hT i :
        weightedRestrictedSubring T hT) : Completion (weightedRestrictedSubring T hT)) ∈
          (U.weighted hT).completion.plus := by
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
  exact ⟨V, hVweight, hW, fun i a ha ↦ hV i ha⟩

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
  obtain ⟨V, hVweight, hW, hV⟩ := exists_finset_weights_image_mem_plus f hopen hT
  obtain ⟨m, θ, hθ, hθA⟩ := U.exists_isQuotientMapping_weightedCompletionHom_append hT hTfin hW
    (fun i ↦ (V i).finite_toSet.image _) (by
      rintro i _ ⟨a, ha, rfl⟩
      exact hV i a ha)
  exact ⟨V, hVweight, hW, m, θ, hθ, hθA⟩

end TauCeti.Huber.Pair

namespace TauCeti.Huber.Pair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsHuberRing B] {U : Pair A} (V : Pair B)

/-- Refining a quotient presentation `π` of `V` by a finite weight family `Q` on `B`: there is a
presentation `σ`, with extra unweighted variables `Xⱼ`, of the completed power series for `Q` as an
open quotient of a completed weighted power-series pair over `U`. It extends `π` along the
coefficients and sends `Xⱼ` to `tⱼ X_{idx j}`, where every element of `Q i` is some `tⱼ` with
`idx j = i`. The construction adapts the presentation in the proof of
`TauCeti.Huber.IsTopologicallyFiniteType.comp`
(`TauCeti/RingTheory/Huber/TopologicallyFiniteType/Comp.lean`): the second weights are moved to the
original base and unweighted variables are added. The caller uses `Q = rationalWeight T s`. -/
theorem exists_openQuotientMap_of_weighted_presentation
    (f : Pair.Hom U V) (hf : f.IsTopologicallyFiniteType) {k n : ℕ} {R : Fin k → Set A}
    (hRfin : ∀ i, (R i).Finite)
    (hR : IsWeightFamily R) (π : Pair.Hom (U.weighted hR).completion V)
    (hπ : π.IsQuotientMapping)
    (hπf : π.comp (U.weightedCompletionHom hR) = f)
    {Q : Fin n → Set B} (hQ : IsWeightFamily Q) (hQfin : ∀ i, (Q i).Finite) :
    ∃ (m : ℕ) (idx : Fin m → Fin n) (t : Fin m → B),
      (∀ i, ∀ a ∈ Q i, ∃ j, idx j = i ∧ t j = a) ∧
      ∃ (Z : Fin (k + (n + m)) → Set A) (hZ : IsWeightFamily Z) (_ : ∀ i, (Z i).Finite)
        (σ : Pair.Hom (U.weighted hZ).completion (V.weighted hQ).completion)
        (ι : Pair.Hom (U.weighted hR).completion (U.weighted hZ).completion),
        IsOpenQuotientMap σ.toRingHom ∧ (∀ j, (1 : A) ∈ Z (Fin.natAdd k (Fin.natAdd n j))) ∧
        (∀ a, σ.toRingHom (algebraMap A (Completion (weightedRestrictedSubring Z hZ)) a) =
          algebraMap B (Completion (weightedRestrictedSubring Q hQ)) (f.toRingHom a)) ∧
        (∀ a, σ.toRingHom (ι.toRingHom a) =
          algebraMap B (Completion (weightedRestrictedSubring Q hQ)) (π.toRingHom a)) ∧
        ∀ j, σ.toRingHom (weightedX Z hZ (Fin.natAdd k (Fin.natAdd n j)) :
            weightedRestrictedSubring Z hZ) =
          algebraMap B (Completion (weightedRestrictedSubring Q hQ)) (t j) *
            (weightedX Q hQ (idx j) : weightedRestrictedSubring Q hQ) := by
  classical
  have hπA : π.toRingHom.comp (algebraMap A (Completion (weightedRestrictedSubring R hR))) =
      f.toRingHom := by
    rw [← Pair.Hom.toRingHom_weightedCompletionHom, ← Pair.Hom.toRingHom_comp, hπf]
  obtain ⟨G, hW, hW', hG⟩ := exists_finset_weights_image_mem_plus f
    (fun _ hJ ↦ hf.isTopologicallyFiniteType_toRingHom.isOpen_map hJ) hQ
  let W : Fin n → Set A := fun i ↦ (G i : Set A)
  have hWfin (i : Fin n) : (W i).Finite := (G i).finite_toSet
  have hb : IsWeightedVarPowerBounded (algebraMap B (Completion (weightedRestrictedSubring Q hQ)))
      (fun i ↦ f.toRingHom '' W i)
      fun i ↦ (weightedX Q hQ i : weightedRestrictedSubring Q hQ) :=
    V.isWeightedVarPowerBounded_weightedX_of_mem_plus hQ (fun i ↦ (hWfin i).image _)
      fun i _ ⟨a, ha, h⟩ ↦ h ▸ hG i a ha
  obtain ⟨m, idx, t, ht, hcover, θ, hθ, hθB, hθX, hθY⟩ :=
    exists_isOpenQuotientMap_completion_weightedRestrictedSubring_append hQ hQfin hW' hb
  have hWD := (hR.image_algebraMap_completion hW).append (isWeightFamily_one_weight (k := m))
  have hWB := hW'.append (isWeightFamily_one_weight (k := m))
  have hmap := image_append_algebraMap_weights (n := m) W π.toRingHom
    (RingHom.congr_fun hπA)
  let β := π.weightedMapCompletion hWD hWB fun i ↦ (hmap i).subset
  have hβ : IsOpenQuotientMap β.toRingHom := by
    rw [Pair.Hom.toRingHom_weightedMapCompletion]
    exact hπ.isOpenQuotientMap.weightedMapCompletion hWD hWB hmap
  have hβC (a) : β.toRingHom (algebraMap _ (Completion (weightedRestrictedSubring _ hWD)) a) =
      algebraMap B (Completion (weightedRestrictedSubring _ hWB)) (π.toRingHom a) := by
    rw [Pair.Hom.toRingHom_weightedMapCompletion,
      algebraMap_completion_weightedRestrictedSubring_apply, weightedMapCompletion_coe,
      weightedMap_weightedC, algebraMap_completion_weightedRestrictedSubring_apply]
  have hβX (j) : β.toRingHom (weightedX _ hWD j : weightedRestrictedSubring _ hWD) =
      (weightedX _ hWB j : weightedRestrictedSubring _ hWB) := by
    rw [Pair.Hom.toRingHom_weightedMapCompletion, weightedMapCompletion_coe,
      weightedMap_weightedX]
  have hZ := hR.append (hW.append (isWeightFamily_one_weight (k := m)))
  obtain ⟨e, ι, he, heX, heι, hιA⟩ := Pair.exists_iterate_pairHoms (U := U) hR hZ hWD
  have hZfin := finite_append_append_weights (n := m) hRfin hWfin
  have hZ1 : ∀ j : Fin m, (1 : A) ∈ Fin.append R (Fin.append W fun _ : Fin m ↦ ({1} : Set A))
      (Fin.natAdd k (Fin.natAdd n j)) := fun j ↦ by simp
  obtain ⟨θ', hθ'⟩ := V.exists_hom_toRingHom_eq_of_weightedX hQ ht hW'
    (fun i _ ⟨a, ha, h⟩ ↦ h ▸ hG i a ha) θ hθ.continuous hθB hθX hθY
  have hσι (a) : (θ'.comp (β.comp e)).toRingHom (ι.toRingHom a) =
      algebraMap B (Completion (weightedRestrictedSubring Q hQ)) (π.toRingHom a) := by
    simp only [Pair.Hom.toRingHom_comp, RingHom.comp_apply]
    rw [heι, hβC, hθ']
    exact RingHom.congr_fun hθB _
  refine ⟨m, idx, t, hcover, _, hZ, hZfin, θ'.comp (β.comp e), ι, ?_, hZ1,
    fun a ↦ ?_, hσι, fun j ↦ ?_⟩
  · simpa only [Pair.Hom.toRingHom_comp, RingHom.coe_comp, Function.comp_assoc, hθ'] using
      hθ.comp (hβ.comp he)
  · rw [← hιA, hσι]
    exact congrArg _ (RingHom.congr_fun hπA a)
  · simp only [Pair.Hom.toRingHom_comp, RingHom.comp_apply]
    rw [heX, hβX, hθ']
    simpa only [Completion.coe_mul, ← algebraMap_completion_weightedRestrictedSubring_apply]
      using hθY j

end TauCeti.Huber.Pair
