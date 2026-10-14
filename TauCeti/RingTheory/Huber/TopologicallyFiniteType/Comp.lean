/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenQuotient
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Composition of topological finite type

For ring homomorphisms `φ : A → B` and `ψ : B → C` out of a Huber ring `A`, strict finite-type
presentations `A⟨X₁, …, Xₖ⟩ ↠ B` of `φ` and `B⟨Y₁, …, Yₘ⟩ ↠ C` of `ψ` combine into a strict
finite-type presentation of `ψ ∘ φ`:

```text
A⟨X₁, …, Xₖ, Y₁, …, Yₘ⟩ ≅ A⟨X₁, …, Xₖ⟩⟨Y₁, …, Yₘ⟩ ↠ B⟨Y₁, …, Yₘ⟩ ↠ C.
```

The first map is the iteration isomorphism `TauCeti.Huber.iterateRingEquiv`, and the second is
the presentation of `φ` applied coefficientwise, which is again an open quotient map by
`IsOpenQuotientMap.weightedMapCompletion`. No completeness is required of `B` or `C`.

Over a Tate ring `A`, topological finite type agrees with strict topological finite type, and a
Huber ring receiving a continuous homomorphism from `A` is again Tate. This gives Wedhorn's
Proposition 6.33(1) for a Tate base: the composite of homomorphisms topologically of finite type
is topologically of finite type.

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
* `TauCeti.Huber.IsTopologicallyFiniteType.comp`: Wedhorn Proposition 6.33(1) over a Tate base.
* `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.comp`: the composite of morphisms of Huber
  pairs topologically of finite type is topologically of finite type, over a Tate base.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50,
  Definition 6.28, Proposition and Definition 6.29, Propositions 6.33 and 6.34, Remark and
  Definition 8.41, Definition 8.42, and Proposition 8.46.
-/

public section

namespace TauCeti.Huber

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
      hρ.comp (hπ.weightedMapCompletion_one_weight.comp he), RingHom.ext fun a ↦ ?_⟩
  -- on a constant series each of the three maps acts as the corresponding structure map
  simp [β, e, algebraMap_completion_weightedRestrictedSubring_apply]

/-- **Wedhorn Proposition 6.33(1), over a Tate base.** If `φ : A → B` and `ψ : B → C` are
topologically of finite type, `A` is Tate and `B` is Huber, then `ψ ∘ φ` is topologically of
finite type. The base `B` of `ψ` is Tate because it receives the continuous homomorphism `φ`, so
both presentations can be taken strict. -/
theorem IsTopologicallyFiniteType.comp [IsTateRing A] [IsHuberRing B]
    (hψ : IsTopologicallyFiniteType ψ) (hφ : IsTopologicallyFiniteType φ) :
    IsTopologicallyFiniteType (ψ.comp φ) :=
  have : IsTateRing B := IsTateRing.of_continuous hφ.continuous
  (hψ.isStrictlyTopologicallyFiniteType.comp
    hφ.isStrictlyTopologicallyFiniteType).isTopologicallyFiniteType

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

/-- In an unweighted algebra the weighted variables `t Xᵢ`, `t ∈ {1}`, are the variables. -/
private theorem weightedC_mul_weightedX_one_weight {n : ℕ} {R : Type*} [CommRing R]
    [TopologicalSpace R] [NonarchimedeanRing R] (i : Fin n) {t : R} (ht : t ∈ ({1} : Set R)) :
    weightedC (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight t *
      weightedX _ isWeightFamily_one_weight i = weightedX _ isWeightFamily_one_weight i := by
  rw [Set.mem_singleton_iff.mp ht, map_one, one_mul]

/-- The completed plus ring of an unweighted pair contains the variables. -/
private theorem coe_weightedX_mem_weighted_completion_plus {n : ℕ} {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R] (Q : Pair R) (i : Fin n) :
    ((weightedX (fun _ : Fin n ↦ ({1} : Set R)) isWeightFamily_one_weight i :
      weightedRestrictedSubring _ _) : restrictedMvPowerSeriesCompletion n R) ∈
      (Q.weighted isWeightFamily_one_weight).completion.plus := by
  rw [← weightedC_mul_weightedX_one_weight i rfl]
  exact Q.weightedC_mul_weightedX_mem_weighted_completion_plus _ rfl

/-- The iteration isomorphism `A⟨X₁, …, X_{k+m}⟩ ≅ A⟨X₁, …, Xₖ⟩⟨Y₁, …, Y_m⟩` is a quotient
mapping of the unweighted completed pairs: it matches their plus rings. -/
private theorem exists_isQuotientMapping_iterateRingEquiv [IsHuberRing A] (S : Pair A)
    (k m : ℕ) :
    ∃ e : Hom (S.weighted (isWeightFamily_one_weight (k := k + m))).completion
      ((S.weighted (isWeightFamily_one_weight (k := k))).completion.weighted
        (isWeightFamily_one_weight (k := m))).completion,
      e.IsQuotientMapping ∧ ∀ x, e.toRingHom x = iterateSplitHom isWeightFamily_one_weight
        isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ rfl)
        (fun _ ↦ by simp [Completion.coe_one]) x := by
  -- the trivial weights of the last `m` variables have trivial image in `A⟨X₁, …, Xₖ⟩`
  have hUW : ∀ j : Fin m, algebraMap A (restrictedMvPowerSeriesCompletion k A) ''
      (fun _ : Fin (k + m) ↦ ({1} : Set A)) (Fin.natAdd k j) = {1} :=
    fun _ ↦ by simp [Completion.coe_one]
  let P := (S.weighted (isWeightFamily_one_weight (k := k))).completion
  -- the inclusion of the first block of variables preserves the plus rings
  have hfirst : P.plus ≤ (S.weighted (isWeightFamily_one_weight (k := k + m))).completion.plus.comap
      (iterateFirstBlockHom isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ rfl)) :=
    S.weighted_completion_plus_le_comap _ _ (continuous_iterateFirstBlockHom ..)
      (fun a ha ↦ by
        rw [iterateFirstBlockHom_coe_weightedC,
          algebraMap_completion_weightedRestrictedSubring_apply]
        exact S.weightedC_mem_weighted_completion_plus _ ha)
      (fun i t ht ↦ by
        rw [weightedC_mul_weightedX_one_weight i ht, iterateFirstBlockHom_coe_weightedX]
        exact coe_weightedX_mem_weighted_completion_plus S _)
  let e : Hom (S.weighted (isWeightFamily_one_weight (k := k + m))).completion
      (P.weighted (isWeightFamily_one_weight (k := m))).completion :=
    { toRingHom := iterateRingEquiv isWeightFamily_one_weight isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ rfl) hUW
      continuous_toRingHom := continuous_iterateRingEquiv ..
      map_mem_plus := fun x hx ↦ by
        simp only [RingHom.coe_coe, iterateRingEquiv_apply]
        refine S.weighted_completion_plus_le_comap _ _ (continuous_iterateSplitHom ..)
          (fun a ha ↦ ?_) (fun i t ht ↦ ?_) hx
        · rw [iterateSplitHom_coe_weightedC, iterateStructureHom_apply]
          exact P.weightedC_mem_weighted_completion_plus _
            (S.weightedC_mem_weighted_completion_plus _ ha)
        · rw [weightedC_mul_weightedX_one_weight i ht, iterateSplitHom_coe_weightedX]
          refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
          · rw [iterateVar_castAdd]
            exact P.weightedC_mem_weighted_completion_plus _
              (coe_weightedX_mem_weighted_completion_plus S i)
          · rw [iterateVar_natAdd]
            exact coe_weightedX_mem_weighted_completion_plus P j }
  have hes : ∀ x, e.toRingHom x = iterateSplitHom isWeightFamily_one_weight
      isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ rfl) hUW x :=
    fun _ ↦ iterateRingEquiv_apply ..
  refine ⟨e, Hom.isQuotientMapping_of_isIntegral_weighted e ?_ (fun c hc ↦ ?_)
    (fun j t ht ↦ ?_), hes⟩
  · exact (Homeomorph.mk (iterateRingEquiv isWeightFamily_one_weight isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ rfl) hUW).toEquiv (continuous_iterateRingEquiv ..)
      (continuous_iterateRingEquiv_symm ..)).isOpenQuotientMap
  · -- a constant `c ∈ A⟨X⟩⁺` is the image of `c` in the first block
    have h := congrArg (fun φ ↦ φ c) (iterateSplitHom_comp_iterateFirstBlockHom
      isWeightFamily_one_weight isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ rfl)
      hUW)
    simp only [RingHom.coe_comp, Function.comp_apply,
      algebraMap_completion_weightedRestrictedSubring_apply] at h
    rw [← h, ← hes]
    exact isIntegral_algebraMap (R := Subring.map e.toRingHom _)
      (x := ⟨_, Subring.mem_map.mpr ⟨_, hfirst hc, rfl⟩⟩)
  · -- the variable `Yⱼ` is the image of `X_{k+j}`
    rw [weightedC_mul_weightedX_one_weight j ht,
      ← iterateVar_natAdd (isWeightFamily_one_weight (k := k) (A := A)) isWeightFamily_one_weight,
      ← iterateSplitHom_coe_weightedX _ _ isWeightFamily_one_weight (fun _ ↦ rfl) hUW, ← hes]
    exact isIntegral_algebraMap (R := Subring.map _ _)
      (x := ⟨_, Subring.mem_map.mpr ⟨_, coe_weightedX_mem_weighted_completion_plus S _, rfl⟩⟩)

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
  obtain ⟨e, he, hes⟩ := exists_isQuotientMapping_iterateRingEquiv S k m
  obtain ⟨β, hβ, hβF⟩ := exists_isQuotientMapping_weightedMapCompletion hπ m
  refine isTopologicallyFiniteType_iff.mpr ⟨k + m, fun _ ↦ {1}, fun _ ↦ Set.finite_singleton 1,
    isWeightFamily_one_weight, ρ.comp (β.comp e), hρ.comp (hβ.comp he),
    Hom.ext (RingHom.ext fun a ↦ ?_)⟩
  -- on a constant each of the three maps acts as the corresponding structure map
  simp [hes, hβF, algebraMap_completion_weightedRestrictedSubring_apply]

end Pair

end TauCeti.Huber
