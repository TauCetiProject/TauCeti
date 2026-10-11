/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Basic

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
`IsOpenQuotientMap.weightedMapCompletion_one_weight`. No completeness is required of `B` or `C`.

Over a Tate ring `A`, topological finite type agrees with strict topological finite type, and a
Huber ring receiving a continuous homomorphism from `A` is again Tate. This gives Wedhorn's
Proposition 6.33(1) for a Tate base: the composite of homomorphisms topologically of finite type
is topologically of finite type. Together with the cancellation results in
`TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel`, this is the ring-level input to the
corresponding statements for morphisms of Huber pairs (Wedhorn, Proposition 8.46).

## Main results

* `TauCeti.Huber.IsStrictlyTopologicallyFiniteType.comp`: strict topological finite type is
  stable under composition, over a Huber base.
* `TauCeti.Huber.IsTopologicallyFiniteType.comp`: Wedhorn Proposition 6.33(1) over a Tate base.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50,
  Definition 6.28, Proposition and Definition 6.29, and Propositions 6.33 and 6.34.
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
  have he : IsOpenQuotientMap (iterateRingEquiv k m A) :=
    (Homeomorph.mk (iterateRingEquiv k m A).toEquiv (continuous_iterateRingEquiv k m A)
      (continuous_iterateRingEquiv_symm k m A)).isOpenQuotientMap
  refine isStrictlyTopologicallyFiniteType_iff.mpr
    ⟨k + m, (ρ.comp β).comp (iterateRingEquiv k m A : _ →+* _),
      hρ.comp (hπ.weightedMapCompletion_one_weight.comp he), RingHom.ext fun a ↦ ?_⟩
  -- on a constant series each of the three maps acts as the corresponding structure map
  simp [β, algebraMap_completion_weightedRestrictedSubring_apply]

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

end TauCeti.Huber
