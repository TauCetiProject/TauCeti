/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.AdicHom.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.OpenIdeal

/-!
# Weight families along adic homomorphisms

Over Huber rings a weight family is admissible exactly when each weight set generates an open
ideal (`TauCeti.Huber.isWeightFamily_iff_isOpen_span`). Adic homomorphisms carry open ideals to
ideals generating open ideals, so they carry weight families to weight families. For an adic
homomorphism `λ : A → B` and weights `T` on `A`, the weighted restricted power series
`B⟨X⟩_{λ(T)}` are therefore defined, which is what base change of `A⟨X⟩_T` along `λ` needs.
Without adicness this fails: for `ℤ_p → ℤ_p⟦T⟧` the ideal `p · ℤ_p⟦T⟧` is not open.

The coefficient map `A → A⟨X⟩_T` into the completed weighted series is itself adic, so
`A⟨X⟩_T` is an admissible factor of the completed tensor product of Huber rings.

## Main results

* `TauCeti.Huber.IsAdicHom.isWeightFamily_image`: an adic homomorphism carries weight families
  to weight families.
* `TauCeti.Huber.isAdicHom_algebraMap_completion_weightedRestrictedSubring`: the coefficient map
  into the completion of `A⟨X⟩_T` is adic.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, proof of Proposition 3.7.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Lemma 6.20 and Remark and Definition 5.48.
-/

public section

open UniformSpace

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {T : Fin k → Set A}

/-- **An adic homomorphism carries weight families to weight families.** If `f : A → B` is adic
and every `T i` generates an open ideal of `A`, then every `f(T i)` generates an open ideal of
`B`, so the weighted restricted power series `B⟨X⟩_{f(T)}` are defined. -/
theorem IsAdicHom.isWeightFamily_image {f : A →+* B} (hf : IsAdicHom f)
    (hT : IsWeightFamily T) : IsWeightFamily fun i ↦ f '' T i := by
  -- both rings are Huber, since `f` relates a pair of definition of each
  obtain ⟨P, Q, -⟩ := hf.exists_pairOfDefinition
  have : IsHuberRing A := ⟨⟨P⟩⟩
  have : IsHuberRing B := ⟨⟨Q⟩⟩
  refine isWeightFamily_iff_isOpen_span.mpr fun i ↦ ?_
  rw [← Ideal.map_span]
  exact hf.isOpen_map (isWeightFamily_iff_isOpen_span.mp hT i)

/-- **The coefficient map into the completed weighted series is adic.** It is continuous, and it
carries open ideals of `A` to ideals generating open ideals of the completion of `A⟨X⟩_T`. -/
instance isAdicHom_algebraMap_completion_weightedRestrictedSubring [IsHuberRing A]
    {hT : IsWeightFamily T} :
    IsAdicHom (algebraMap A (Completion (weightedRestrictedSubring T hT))) := by
  have he : algebraMap A (Completion (weightedRestrictedSubring T hT)) =
      Completion.coeRingHom.comp (algebraMap A (weightedRestrictedSubring T hT)) :=
    RingHom.ext (Completion.algebraMap_def _ _)
  refine IsAdicHom.of_continuous_isOpen_map
    (continuous_algebraMap_completion_weightedRestrictedSubring k A hT) fun J hJ ↦ ?_
  rw [he, ← Ideal.map_map]
  exact isOpen_map_coeRingHom (isOpen_map_algebraMap_weightedRestrictedSubring hJ)

end TauCeti.Huber
