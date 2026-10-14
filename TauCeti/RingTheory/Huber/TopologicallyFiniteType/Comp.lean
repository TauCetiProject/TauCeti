/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate.Pair
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
      hρ.comp ((hπ.weightedMapCompletion isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ by simp)).comp he), RingHom.ext fun a ↦ ?_⟩
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
  let β := π.weightedMapCompletion (isWeightFamily_one_weight (k := m))
    isWeightFamily_one_weight (fun _ ↦ by simp)
  have hβ : β.IsQuotientMapping := hπ.weightedMapCompletion isWeightFamily_one_weight
    isWeightFamily_one_weight (fun _ ↦ by simp)
    hπ.isOpenQuotientMap.weightedMapCompletion_one_weight
  refine isTopologicallyFiniteType_iff.mpr ⟨k + m, fun _ ↦ {1}, fun _ ↦ Set.finite_singleton 1,
    isWeightFamily_one_weight, ρ.comp (β.comp e), hρ.comp (hβ.comp he),
    Hom.ext (RingHom.ext fun a ↦ ?_)⟩
  -- on a constant each of the three maps acts as the corresponding structure map
  simp [e, β, algebraMap_completion_weightedRestrictedSubring_apply]

end Pair

end TauCeti.Huber
