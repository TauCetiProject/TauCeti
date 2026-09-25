/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Completion.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.DenseRange

/-!
# The adic spectrum is unchanged by completion

For a Huber ring `A` with a compatible uniform structure and any subring `A⁺ ⊆ A`, pullback along
the completion map `ι : A → Â` is a homeomorphism

```text
Spa (Â, Â⁺) ≃ₜ Spa (A, A⁺),
```

where `Â⁺` is the closure in `Â` of the image of `A⁺`.

This is Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), **Proposition 7.48**. The two halves are
already available and this file only assembles them: pullback along a dense map is inducing
(`isInducing_spaComap_of_denseRange`), and pullback along the completion map is surjective
(`spaComap_coeRingHom_surjective`). Since `spa A⁺` is T0, inducing upgrades to an embedding, and
an embedding onto everything is a homeomorphism.

The statement here is more general than Wedhorn's, which is for an affinoid ring: no Huber,
Hausdorff or completeness hypothesis is imposed on `A⁺`, and `A⁺` need not be a ring of integral
elements. Lemma 7.47 enters only as the justification for taking `Â⁺` to be the closure of the
image — when `A⁺` is a ring of integral elements, so is `Â⁺`, by
`TauCeti.Huber.IsRingOfIntegralElements.completion`.

Wedhorn's Proposition 7.48 also asserts that the homeomorphism matches rational subsets. That
clause is proved in `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Completion.RationalSubset`. One
direction is available for any dense map, as
`exists_mem_spaRationalFamily_spaComap_preimage_eq_of_denseRange`; the other rests on
`TauCeti.Huber.isOpen_map_coeRingHom`, that the image of an open ideal of `A` generates an open
ideal of `Â`.

## Main definitions

* `TauCeti.ValuationSpectrum.completionPlus`: the plus ring `Â⁺` of the completion, the closure of
  the image of `A⁺`. It is opaque; `completionPlus_def` is its characterisation.

## Main results

* `TauCeti.ValuationSpectrum.spaCompletionHomeomorph`: the adic spectrum is unchanged by
  completion.
* `TauCeti.ValuationSpectrum.spaCompletionHomeomorph_apply` and
  `TauCeti.ValuationSpectrum.coe_spaCompletionHomeomorph`: the homeomorphism is pullback along
  the completion map, pointwise and as an equality of functions.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.48 and Lemma 7.47.

-/

public section

namespace TauCeti.ValuationSpectrum

open Topology TauCeti.Huber UniformSpace

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-- The plus ring of the completion: the closure in `Â` of the image of `A⁺`. When `A⁺` is a ring
of integral elements so is this, by `TauCeti.Huber.IsRingOfIntegralElements.completion`, which is
Wedhorn's Lemma 7.47. -/
noncomputable def completionPlus (Aplus : Subring A) : Subring (Completion A) :=
  (Aplus.map (Completion.coeRingHom : A →+* Completion A)).topologicalClosure

/-- `completionPlus` is the closure of the image of `A⁺`. This is the bridge to the unbundled
statements, whose plus ring is spelled out — `completionPlus` is opaque, so unfolding goes through
this lemma. -/
theorem completionPlus_def (Aplus : Subring A) :
    completionPlus Aplus =
      (Aplus.map (Completion.coeRingHom : A →+* Completion A)).topologicalClosure :=
  (rfl)

/-- The completion map carries `A⁺` into `Â⁺`: this is the `hplus` argument `spaComap` takes
along `A → Â`. -/
theorem map_mem_completionPlus {Aplus : Subring A} {a : A} (ha : a ∈ Aplus) :
    Completion.coeRingHom a ∈ completionPlus Aplus :=
  Subring.le_topologicalClosure _ ⟨a, ha, rfl⟩

variable [IsHuberRing A]

/-- **Wedhorn Proposition 7.48.** Pullback along the completion map is a homeomorphism from
`Spa (Â, Â⁺)` onto `Spa (A, A⁺)`, where `Â⁺` is the closure of the image of `A⁺`. -/
noncomputable def spaCompletionHomeomorph (Aplus : Subring A) :
    spa (completionPlus Aplus) ≃ₜ spa Aplus :=
  (isInducing_spaComap_of_denseRange Completion.continuous_coeRingHom Completion.denseRange_coe
      Aplus (completionPlus Aplus) fun _ ha ↦ map_mem_completionPlus ha).isEmbedding
    |>.toHomeomorphOfSurjective (spaComap_coeRingHom_surjective Aplus)

/-- The completion homeomorphism is pullback along the completion map. -/
@[simp]
theorem spaCompletionHomeomorph_apply (Aplus : Subring A) (v : spa (completionPlus Aplus)) :
    spaCompletionHomeomorph Aplus v =
      spaComap Completion.coeRingHom Completion.continuous_coeRingHom Aplus (completionPlus Aplus)
        (fun _ ha ↦ map_mem_completionPlus ha) v :=
  Topology.IsEmbedding.toHomeomorphOfSurjective_apply _ _ v

/-- The completion homeomorphism, as a function, is pullback along the completion map. This is the
functional companion of the pointwise `spaCompletionHomeomorph_apply`, in the form that rewrites
under `Set.preimage` and `Set.image`. -/
@[simp]
theorem coe_spaCompletionHomeomorph (Aplus : Subring A) :
    ⇑(spaCompletionHomeomorph Aplus) =
      spaComap Completion.coeRingHom Completion.continuous_coeRingHom Aplus
        (completionPlus Aplus) fun _ ha ↦ map_mem_completionPlus ha :=
  funext (spaCompletionHomeomorph_apply Aplus)

end TauCeti.ValuationSpectrum

end
