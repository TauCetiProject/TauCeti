/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# A product law is determined by finite-dimensional marginals in its path coordinate

A finite measure on `γ × (∀ i, β i)` is determined by its images under `Prod.map id F.restrict`,
as `F` ranges over the finite sets of coordinates. On a rectangle `s ×ˢ t`, the section
`t ↦ μ (s ×ˢ t)` is a finite measure on the path space `∀ i, β i`, which is the projective limit of
its finite-dimensional marginals and hence determined by them; rectangles in turn determine a
finite measure on a product.

This is the shape in which a coding of an infinite family of random variables, jointly with a fixed
observation, is assembled from the codings of its finite subfamilies. The argument is the one that
closes `TauCeti.Probability.SeparatelyExchangeable.exists_common_visibleArray_coding` (in
`TauCeti.Probability.Exchangeability.Arrays.Strip.Cell.CommonCoding`), stated here for an arbitrary
observation space and path space.

## Main result

* `TauCeti.MeasureTheory.Measure.ext_prod_pi_of_forall_finset_map_restrict_eq` — two finite
  measures on `γ × (∀ i, β i)` with the same image under every `Prod.map id F.restrict` are equal.
-/

public section

open MeasureTheory

namespace TauCeti.MeasureTheory.Measure

variable {γ ι : Type*} {β : ι → Type*} [MeasurableSpace γ] [∀ i, MeasurableSpace (β i)]

/-- **Finite-dimensional marginals in the path coordinate determine a finite product law.** Two
finite measures on `γ × (∀ i, β i)` are equal as soon as, for every finite set `F` of coordinates,
their images under `Prod.map id F.restrict` agree. -/
theorem ext_prod_pi_of_forall_finset_map_restrict_eq {μ ν : Measure (γ × (∀ i, β i))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ F : Finset ι, μ.map (Prod.map id F.restrict) = ν.map (Prod.map id F.restrict)) :
    μ = ν := by
  -- Two finite laws on a product agree once they agree on rectangles `s ×ˢ t`; for a fixed
  -- measurable `s`, the section `t ↦ μ (s ×ˢ t)` is a finite measure on the path space, which is
  -- determined by its finite-dimensional marginals.
  refine Measure.ext_prod fun {s t} hs ht => ?_
  have hsec (μ : Measure (γ × (∀ i, β i))) :
      μ (s ×ˢ t) = ((μ.restrict (s ×ˢ Set.univ)).map Prod.snd) t := by
    rw [Measure.map_apply measurable_snd ht, Measure.restrict_apply (measurable_snd ht)]
    congr 1
    ext ⟨y, z⟩
    simp [and_comm]
  have hmarg (μ : Measure (γ × (∀ i, β i))) (F : Finset ι) :
      ((μ.restrict (s ×ˢ Set.univ)).map Prod.snd).map F.restrict =
        ((μ.map (Prod.map id F.restrict)).restrict (s ×ˢ Set.univ)).map Prod.snd := by
    have hFr : Measurable (Prod.map (id : γ → γ) (F.restrict (π := β))) :=
      measurable_id.prodMap (Finset.measurable_restrict F)
    have hpre : Prod.map id F.restrict ⁻¹' (s ×ˢ Set.univ) =
        (s ×ˢ Set.univ : Set (γ × (∀ i, β i))) := by
      ext
      simp
    rw [Measure.restrict_map hFr (hs.prod .univ), Measure.map_map measurable_snd hFr,
      Measure.map_map (Finset.measurable_restrict F) measurable_snd, hpre]
    rfl
  rw [hsec, hsec]
  refine congrFun (congrArg _ (IsProjectiveLimit.unique (P := fun F : Finset ι =>
    ((ν.restrict (s ×ˢ Set.univ)).map Prod.snd).map F.restrict) (fun F => ?_) fun F => rfl)) t
  dsimp only
  rw [hmarg, hmarg, h F]

end TauCeti.MeasureTheory.Measure
