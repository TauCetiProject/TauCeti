/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.RingTheory.Huber.WeightedEval.Finite
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate.Pair
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenIdeal
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenQuotient
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Composition of topological finite type

For ring homomorphisms `φ : A → B` and `ψ : B → C` with `A` and `B` Huber rings, weighted
finite-type presentations combine into a weighted finite-type presentation of `ψ ∘ φ`. The key
point is to replace the weights of the second presentation by images of sufficiently small finite
weights in `A`. The corresponding weighted variables are power-bounded, so the second presentation
is an open quotient of one with those image weights and extra unweighted variables. Weighted
iteration then gives a presentation over `A`.

For strict finite-type presentations the construction has the simpler form

```text
A⟨X₁, …, Xₖ, Y₁, …, Yₘ⟩ ≅ A⟨X₁, …, Xₖ⟩⟨Y₁, …, Yₘ⟩ ↠ B⟨Y₁, …, Yₘ⟩ ↠ C.
```

The first map is the iteration isomorphism `TauCeti.Huber.iterateRingEquiv`, and the second is
the presentation of `φ` applied coefficientwise, which is again an open quotient map by
`IsOpenQuotientMap.weightedMapCompletion`. No completeness is required of `B` or `C`.

This gives Wedhorn's Proposition 6.33(1): the composite of homomorphisms topologically of finite
type, whose source rings are Huber, is topologically of finite type. No Tate hypothesis is needed.

The same presentation composes morphisms of Huber pairs topologically of finite type (Wedhorn,
Definition 8.42), where the plus rings must be controlled as well: each of the three maps is a
quotient mapping of the corresponding completed unweighted pairs. This is the composition
statement of Wedhorn's Proposition 8.46 over a Tate base. It is what lets a chart of a morphism
locally of finite type be refined by a rational subset of its source, since rational localisation
of a Tate pair is topologically of finite type
(`TauCeti.Huber.PairOfDefinition.isTopologicallyFiniteType_toCompletionLocHom`).

## Main results

* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.comp`: strict topological finite type is
  stable under composition, over a Huber base.
* `TauCeti.Huber.IsTopologicallyFiniteType.comp`: Wedhorn Proposition 6.33(1) for Huber rings.
* `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.comp`: the composite of morphisms of Huber
  pairs topologically of finite type is topologically of finite type, over a Tate base.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50,
  Definition 6.28, Proposition and Definition 6.29, Propositions 6.33 and 6.34, Remark and
  Definition 8.41, Definition 8.42, and Proposition 8.46.
-/

public section

namespace TauCeti.Huber

open Filter Topology UniformSpace

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
  [CommRing C] [TopologicalSpace C] {φ : A →+* B} {ψ : B →+* C}

/-- **Strict topological finite type is stable under composition.** If `φ : A → B` and
`ψ : B → C` are strictly topologically of finite type and `A` is Huber, then so is `ψ ∘ φ`,
presented by `A⟨X₁, …, Xₖ, Y₁, …, Yₘ⟩ ≅ A⟨X₁, …, Xₖ⟩⟨Y₁, …, Yₘ⟩ ↠ B⟨Y₁, …, Yₘ⟩ ↠ C`. -/
theorem IsStrictlyTopologicallyFiniteType.comp [IsHuberRing A]
    (hψ : IsStrictlyTopologicallyFiniteType ψ) (hφ : IsStrictlyTopologicallyFiniteType φ) :
    IsStrictlyTopologicallyFiniteType (ψ.comp φ) := by
  obtain ⟨k, π, hπ, rfl⟩ := isStrictlyTopologicallyFiniteType_iff.mp hφ
  obtain ⟨m, ρ, hρ, rfl⟩ := isStrictlyTopologicallyFiniteType_iff.mp hψ
  -- the presentation of `φ`, applied to the coefficients of series in `m` further variables
  let β := weightedMapCompletion (k := m) hπ.continuous isWeightFamily_one_weight
    isWeightFamily_one_weight fun _ ↦ by simp
  -- the iteration isomorphism at the trivial weights, whose image in `A⟨X₁, …, Xₖ⟩` is trivial
  have hUW : ∀ j : Fin m, algebraMap A (restrictedMvPowerSeriesCompletion k A) ''
      (fun _ : Fin (k + m) ↦ ({1} : Set A)) (Fin.natAdd k j) = {1} :=
    fun _ ↦ by simp [UniformSpace.Completion.coe_one]
  let e := iterateRingEquiv isWeightFamily_one_weight isWeightFamily_one_weight
    isWeightFamily_one_weight (fun _ ↦ rfl) hUW
  have he : IsOpenQuotientMap e :=
    (Homeomorph.mk e.toEquiv (continuous_iterateRingEquiv ..)
      (continuous_iterateRingEquiv_symm ..)).isOpenQuotientMap
  refine isStrictlyTopologicallyFiniteType_iff.mpr
    ⟨k + m, (ρ.comp β).comp (e : _ →+* _),
      hρ.comp ((hπ.weightedMapCompletion isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ by simp)).comp he), RingHom.ext fun a ↦ ?_⟩
  -- on a constant series each of the three maps acts as the corresponding structure map
  simp [β, e, algebraMap_completion_weightedRestrictedSubring_apply]

/-- **Wedhorn Proposition 6.33(1).** If `φ : A → B` and `ψ : B → C` are topologically of finite
type and `A` and `B` are Huber rings, then `ψ ∘ φ` is topologically of finite type.

Small finite weights in `A` are chosen so that their images times the variables of a presentation
of `ψ` are power-bounded. The partly-unweighted presentation theorem replaces that presentation by
one with these image weights. Applying the presentation of `φ` coefficientwise and flattening the
resulting weighted iteration gives the required presentation over `A`. -/
theorem IsTopologicallyFiniteType.comp [IsHuberRing A] [IsHuberRing B]
    (hψ : IsTopologicallyFiniteType ψ) (hφ : IsTopologicallyFiniteType φ) :
    IsTopologicallyFiniteType (ψ.comp φ) := by
  classical
  obtain ⟨k, T, hTfin, hT, π, hπ, hπφ⟩ := isTopologicallyFiniteType_iff.mp hφ
  obtain ⟨m, U, hUfin, hU, ρ, hρ, hρψ⟩ := isTopologicallyFiniteType_iff.mp hψ
  have hρψ_apply (b : B) :
      ρ (algebraMap B (Completion (weightedRestrictedSubring U hU)) b) = ψ b := by
    simpa only [RingHom.comp_apply] using RingHom.congr_fun hρψ b
  let y : Fin m → Completion (weightedRestrictedSubring U hU) := fun i ↦
    (weightedX U hU i : weightedRestrictedSubring U hU)
  -- Power-bounded elements form an open subring, so every variable admits a neighbourhood of
  -- scalar coefficients whose products with it are power-bounded.
  have hsmall (i : Fin m) :
      {a : A | IsPowerBounded
        (algebraMap B (Completion (weightedRestrictedSubring U hU)) (φ a) * y i)} ∈ 𝓝 0 := by
    have hc : Continuous fun a : A ↦
        algebraMap B (Completion (weightedRestrictedSubring U hU)) (φ a) * y i :=
      ((continuous_algebraMap_completion_weightedRestrictedSubring m B hU).comp hφ.continuous).mul
        continuous_const
    rw [show {a : A | IsPowerBounded
        (algebraMap B (Completion (weightedRestrictedSubring U hU)) (φ a) * y i)} =
      (fun a : A ↦ algebraMap B (Completion (weightedRestrictedSubring U hU)) (φ a) * y i) ⁻¹'
        (powerBoundedSubring (Completion (weightedRestrictedSubring U hU)) :
          Set (Completion (weightedRestrictedSubring U hU))) from
      Set.ext fun _ ↦ mem_powerBoundedSubring.symm]
    refine ((isOpen_powerBoundedSubring
      (Completion (weightedRestrictedSubring U hU))).preimage hc).mem_nhds ?_
    exact mem_powerBoundedSubring.mpr (by
      simpa only [map_zero, zero_mul] using
        (isPowerBounded_zero (M := Completion (weightedRestrictedSubring U hU))))
  choose G hG hGopen using fun i ↦ exists_finset_subset_isOpen_span (hsmall i)
  let V : Fin m → Set A := fun i ↦ (G i : Set A)
  have hVfin : ∀ i, (V i).Finite := fun i ↦ (G i).finite_toSet
  have hV : IsWeightFamily V := isWeightFamily_iff_isOpen_span.mpr hGopen
  have hφV : IsWeightFamily fun i ↦ φ '' V i := isWeightFamily_iff_isOpen_span.mpr fun i ↦ by
    rw [← Ideal.map_span]
    exact hφ.isOpen_map (hGopen i)
  have hVy : IsWeightedVarPowerBounded
      (algebraMap B (Completion (weightedRestrictedSubring U hU)))
      (fun i ↦ φ '' V i) y :=
    (isWeightedVarPowerBounded_iff_of_finite fun i ↦ (hVfin i).image φ).mpr fun i b hb ↦ by
      obtain ⟨a, ha, rfl⟩ := hb
      exact hG i ha
  obtain ⟨n, _, _, _, _, θ, hθ, hθB, _, _⟩ :=
    exists_isOpenQuotientMap_completion_weightedRestrictedSubring_append
      hU hUfin hφV hVy
  let D := Completion (weightedRestrictedSubring T hT)
  let W : Fin (m + n) → Set D := Fin.append
    (fun i ↦ algebraMap A D '' V i) (fun _ ↦ ({1} : Set D))
  let W' : Fin (m + n) → Set B := Fin.append
    (fun i ↦ φ '' V i) (fun _ ↦ ({1} : Set B))
  have hW : IsWeightFamily W :=
    (hT.image_algebraMap_completion hV).append isWeightFamily_one_weight
  have hW' : IsWeightFamily W' := hφV.append isWeightFamily_one_weight
  have hθB_apply (b : B) :
      θ (algebraMap B (Completion (weightedRestrictedSubring W' hW')) b) =
        algebraMap B (Completion (weightedRestrictedSubring U hU)) b := by
    simpa only [W', RingHom.comp_apply] using RingHom.congr_fun hθB b
  have hWW' : ∀ i, π '' W i = W' i := fun i ↦ Fin.addCases
    (fun j ↦ by
      simp only [W, W', Fin.append_left, Set.image_image]
      exact Set.image_congr fun a _ ↦ RingHom.congr_fun hπφ a)
    (fun j ↦ by simp [W, W']) i
  let β := weightedMapCompletion hπ.continuous hW hW' fun i ↦ (hWW' i).subset
  have hβ : IsOpenQuotientMap β := hπ.weightedMapCompletion hW hW' hWW'
  let Z : Fin (m + n) → Set A := Fin.append V fun _ ↦ ({1} : Set A)
  let Q : Fin (k + (m + n)) → Set A := Fin.append T Z
  have hZ : IsWeightFamily Z := hV.append isWeightFamily_one_weight
  have hQ : IsWeightFamily Q := hT.append hZ
  have hTQ : ∀ i, Q (Fin.castAdd (m + n) i) = T i := fun i ↦ by simp [Q]
  have hQW : ∀ j, algebraMap A D '' Q (Fin.natAdd k j) = W j := fun j ↦
    Fin.addCases (fun i ↦ by simp [Q, Z, W, D]) (fun i ↦ by
      simp only [Q, Z, W, Fin.append_right, Set.image_singleton]
      rw [map_one]) j
  have hπφ_apply (a : A) :
      π (algebraMap A (Completion (weightedRestrictedSubring T hT)) a) = φ a := by
    simpa only [RingHom.comp_apply] using RingHom.congr_fun hπφ a
  let e := iterateRingEquiv hT hW hQ hTQ hQW
  have he : IsOpenQuotientMap e :=
    (Homeomorph.mk e.toEquiv (continuous_iterateRingEquiv ..)
      (continuous_iterateRingEquiv_symm ..)).isOpenQuotientMap
  refine isTopologicallyFiniteType_iff.mpr
    ⟨k + (m + n), Q, fun i ↦ Fin.addCases (fun j ↦ by simpa [Q] using hTfin j)
      (fun j ↦ Fin.addCases (fun l ↦ by simpa [Q, Z] using hVfin l)
        (fun _ ↦ by simp [Q, Z]) j) i,
      hQ, (ρ.comp θ).comp (β.comp (e : _ →+* _)),
      hρ.comp (hθ.comp (hβ.comp he)), RingHom.ext fun a ↦ ?_⟩
  dsimp only [β, e]
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    algebraMap_completion_weightedRestrictedSubring_apply, iterateRingEquiv_apply,
    iterateSplitHom_coe_weightedC, iterateStructureHom_apply, weightedMapCompletion_coe,
    weightedMap_weightedC]
  rw [← algebraMap_completion_weightedRestrictedSubring_apply, hθB_apply, hρψ_apply,
    ← algebraMap_completion_weightedRestrictedSubring_apply, hπφ_apply]

namespace Pair

open UniformSpace

/-! ### Morphisms of Huber pairs

The presentation of the composite is the one above, now as quotient mappings of Huber pairs:
`(A⟨X, Y⟩, A⟨X, Y⟩⁺) ≅ (A⟨X⟩⟨Y⟩, A⟨X⟩⟨Y⟩⁺) ↠ (B⟨Y⟩, B⟨Y⟩⁺) ↠ (C, C⁺)`, each step controlling the
plus rings as well as the rings.
-/

variable {A A' B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsHuberRing A']
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]

/-- A quotient mapping `π : (A', A'⁺) → (B, B⁺)`, applied coefficientwise, induces a quotient
mapping `(A'⟨Y₁, …, Y_m⟩, A'⟨Y⟩⁺) → (B⟨Y₁, …, Y_m⟩, B⟨Y⟩⁺)` of the completed unweighted pairs. -/
private theorem exists_isQuotientMapping_weightedMapCompletion {S : Pair A'} {U : Pair B}
    {π : Hom S U} (hπ : π.IsQuotientMapping) (m : ℕ) :
    ∃ β : Hom (S.weighted (isWeightFamily_one_weight (k := m))).completion
      (U.weighted (isWeightFamily_one_weight (k := m))).completion,
      β.IsQuotientMapping ∧ β.toRingHom = weightedMapCompletion π.continuous_toRingHom
        isWeightFamily_one_weight isWeightFamily_one_weight fun _ ↦ by simp := by
  set F := weightedMapCompletion (k := m) π.continuous_toRingHom isWeightFamily_one_weight
    isWeightFamily_one_weight fun _ ↦ by simp
  have hFC (a : A') : F ((weightedC (fun _ : Fin m ↦ ({1} : Set A')) isWeightFamily_one_weight a :
      weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion m A') =
        (weightedC (fun _ : Fin m ↦ ({1} : Set B)) isWeightFamily_one_weight (π.toRingHom a) :
          weightedRestrictedSubring _ _) := by
    rw [weightedMapCompletion_coe, weightedMap_weightedC]
  have hFX (i : Fin m) (t : A') (ht : t ∈ ({1} : Set A')) :
      F ((weightedC (fun _ : Fin m ↦ ({1} : Set A')) isWeightFamily_one_weight t *
        weightedX _ isWeightFamily_one_weight i : weightedRestrictedSubring _ _) :
          restrictedMvPowerSeriesCompletion m A') =
        (weightedC (fun _ : Fin m ↦ ({1} : Set B)) isWeightFamily_one_weight 1 *
          weightedX _ isWeightFamily_one_weight i : weightedRestrictedSubring _ _) := by
    rw [weightedMapCompletion_coe, map_mul, weightedMap_weightedC, weightedMap_weightedX,
      Set.mem_singleton_iff.mp ht, map_one]
  let β : Hom (S.weighted (isWeightFamily_one_weight (k := m))).completion
      (U.weighted (isWeightFamily_one_weight (k := m))).completion :=
    { toRingHom := F
      continuous_toRingHom := continuous_weightedMapCompletion ..
      map_mem_plus := weighted_completion_plus_le_comap_weightedMapCompletion _ π _ _ }
  refine ⟨β, Hom.isQuotientMapping_of_isIntegral_weighted β
    (hπ.isOpenQuotientMap.weightedMapCompletion isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ by simp)) (fun b hb ↦ ?_) (fun i t ht ↦ ?_), rfl⟩
  · -- `b` is integral over `π(A'⁺)`, so its constant is integral over the constants of `π(A'⁺)`
    let φ : B →+* restrictedMvPowerSeriesCompletion m B :=
      Completion.coeRingHom.comp (weightedC _ isWeightFamily_one_weight)
    let ψ : S.plus.map π.toRingHom →+*
        (S.weighted (isWeightFamily_one_weight (k := m))).completion.plus.map β.toRingHom :=
      φ.restrict _ _ fun _ ⟨a, ha, hab⟩ ↦ Subring.mem_map.mpr
        ⟨_, S.weightedC_mem_weighted_completion_plus _ ha, by rw [← hab]; exact hFC a⟩
    exact (hπ.mem_plus_iff.mp hb).map_of_comp_eq ψ φ (by ext; rfl)
  · rw [Set.mem_singleton_iff.mp ht, ← hFX i 1 rfl]
    exact isIntegral_algebraMap (R := Subring.map _ _) (x := ⟨_, Subring.mem_map.mpr
      ⟨_, S.weightedC_mul_weightedX_mem_weighted_completion_plus _ rfl, rfl⟩⟩)

/-- **The composite of morphisms of Huber pairs topologically of finite type is topologically of
finite type**, over a Tate base: for `f : (A, A⁺) → (B, B⁺)` and `g : (B, B⁺) → (C, C⁺)`
topologically of finite type with `A` Tate, so is `g ∘ f`. This is the composition statement of
Wedhorn's Proposition 8.46, and the pair form of `TauCeti.Huber.IsTopologicallyFiniteType.comp`:
the presentation of `g ∘ f` also controls the plus ring `C⁺`. No completeness is assumed. -/
theorem Hom.IsTopologicallyFiniteType.comp [IsTateRing A] {S : Pair A} {U : Pair B} {V : Pair C}
    {f : Hom S U} {g : Hom U V} (hg : g.IsTopologicallyFiniteType)
    (hf : f.IsTopologicallyFiniteType) : (g.comp f).IsTopologicallyFiniteType := by
  have : IsTateRing B := IsTateRing.of_continuous f.continuous_toRingHom
  obtain ⟨k, π, hπ, rfl⟩ := hf.exists_isQuotientMapping_one_weight
  obtain ⟨m, ρ, hρ, rfl⟩ := hg.exists_isQuotientMapping_one_weight
  have hUW : ∀ j : Fin m, algebraMap A (restrictedMvPowerSeriesCompletion k A) ''
      (fun _ : Fin (k + m) ↦ ({1} : Set A)) (Fin.natAdd k j) = {1} :=
    fun _ ↦ by simp [Completion.coe_one]
  let e := S.iterateSplitHom isWeightFamily_one_weight isWeightFamily_one_weight
    isWeightFamily_one_weight (fun _ ↦ rfl) hUW
  have he := S.isQuotientMapping_iterateSplitHom isWeightFamily_one_weight
    isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ rfl) hUW
  obtain ⟨β, hβ, hβF⟩ := exists_isQuotientMapping_weightedMapCompletion hπ m
  refine isTopologicallyFiniteType_iff.mpr ⟨k + m, fun _ ↦ {1}, fun _ ↦ Set.finite_singleton 1,
    isWeightFamily_one_weight, ρ.comp (β.comp e), hρ.comp (hβ.comp he),
    Hom.ext (RingHom.ext fun a ↦ ?_)⟩
  -- on a constant each of the three maps acts as the corresponding structure map
  simp [e, hβF, algebraMap_completion_weightedRestrictedSubring_apply]

end Pair

end TauCeti.Huber
