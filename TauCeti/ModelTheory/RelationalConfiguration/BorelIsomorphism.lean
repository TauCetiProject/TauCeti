/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Separation
public import TauCeti.ModelTheory.Scott.Height

/-!
# Borel isomorphism on classes of relational configurations

Let `L` be a relational language with countably many relation symbols of each arity and `V` a
countable carrier, so that the configurations on `V` form a Polish space. For a set `K` of
configurations, isomorphism restricted to `K` is the set of pairs
`{p | isoSetoid L V p.1 p.2} ∩ K ×ˢ K`. It is always analytic, and this file says when it is
Borel.

* **Bounded Scott height.** If every configuration in `K` decodes to a structure of Scott height
  at most `β`, then isomorphism on `K` is back-and-forth equivalence at level `β`, because
  equivalence at the Scott height decides isomorphism. For `β < ω₁` and Borel `K` it is therefore
  Borel. The same holds when the internal stabilization ordinals on `K` are bounded below `ω₁`,
  since the Scott height lies within `ω` of the internal stabilization ordinal.
* **One countable level.** Conversely, for analytic `K`, if isomorphism on `K` is Borel then it is
  back-and-forth equivalence at a single countable level. The pairs of `K` that are not isomorphic
  then form an analytic set, which uniform back-and-forth separation splits at one level. For Borel
  `K` this characterises Borel isomorphism on `K`.
* **Borel strata.** For `β < ω₁`, the configurations whose decoded structure stabilizes internally
  at `β`, and hence those whose internal stabilization ordinal is at most `β`, form a Borel set:
  internal stabilization is a countable conjunction of conditions on back-and-forth equivalence
  of tuples. The Scott height quantifies over all countable structures, and Borelness of its
  strata is not claimed here.

The countability of the language matters for the first two results, as no countable set of
coordinates decides isomorphism once there are uncountably many relation symbols.

## Main results

* `TauCeti.RelationalConfiguration.measurableSet_iso_inter_of_scottHeight_le`: isomorphism on a
  Borel class of Scott height at most `β < ω₁` is Borel.
* `TauCeti.RelationalConfiguration.measurableSet_iso_inter_of_selfStabilizationOrdinal_le`: the
  same for internal stabilization ordinals at most `β < ω₁`.
* `TauCeti.RelationalConfiguration.measurableSet_iso_inter_iff_exists_bfLevel`: isomorphism on a
  Borel class is Borel exactly when it is back-and-forth equivalence at one countable level.
* `TauCeti.RelationalConfiguration.measurableSet_setOf_selfStabilizesCompletely` and
  `TauCeti.RelationalConfiguration.measurableSet_setOf_selfStabilizationOrdinal_le`: the strata
  of the internal stabilization ordinal below `ω₁` are Borel.

## References

* David Marker, *Lectures on Infinitary Model Theory*, lecture notes, University of Illinois at
  Chicago, 2013, Theorem 11.19: isomorphism on the models of a sentence of a countable vocabulary
  is Borel exactly when their Scott ranks are bounded below `ω₁`. Here the bound is on the Scott
  height rather than the internal rank, for which the backward direction fails.
* Cameron Freer's `cameronfreer/infinitary-logic`, checkpoint
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b` (Apache-2.0), covers related material in
  `InfinitaryLogic/Descriptive/IsomorphismBorel.lean`. The proofs here are built directly on
  Tau Ceti's Scott height, `bfEquivSetoid` and uniform back-and-forth separation.
-/

public section

universe u v w o

open FirstOrder FirstOrder.Language MeasureTheory Set
open scoped Ordinal

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-! ### Isomorphism on classes of bounded Scott height -/

/-- If the structure decoded from `c` has Scott height at most `β`, then a configuration is
isomorphic to `c` exactly when it is back-and-forth equivalent to `c` at level `β`. -/
theorem isoSetoid_iff_bfEquivSetoid_of_scottHeight_le [Countable V] {β : Ordinal.{w}}
    {c d : RelationalConfiguration L V} (h : @scottHeight L _ V c.toStructure ≤ β) :
    isoSetoid L V c d ↔ bfEquivSetoid L V β c d :=
  ⟨fun hcd => isoSetoid_le_bfEquivSetoid β hcd, fun hcd => isoSetoid_apply.2
    (@nonempty_equiv_of_bfEquiv_of_scottHeight_le L _ V c.toStructure _ V d.toStructure _ β h
      (bfEquivSetoid_apply.1 hcd))⟩

/-- On a set of configurations whose decoded structures have Scott height at most `β`,
isomorphism is back-and-forth equivalence at level `β`. -/
theorem setOf_isoSetoid_inter_eq_of_scottHeight_le [Countable V]
    {K : Set (RelationalConfiguration L V)} {β : Ordinal.{w}}
    (hK : ∀ c ∈ K, @scottHeight L _ V c.toStructure ≤ β) :
    {p : RelationalConfiguration L V × RelationalConfiguration L V | isoSetoid L V p.1 p.2} ∩
        K ×ˢ K =
      {p | bfEquivSetoid L V β p.1 p.2} ∩ K ×ˢ K := by
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod]
  exact and_congr_left fun hp => isoSetoid_iff_bfEquivSetoid_of_scottHeight_le (hK p.1 hp.1)

/-- **Borel isomorphism under bounded Scott height.** In a vocabulary with countably many relation
symbols of each arity, on a countable carrier, isomorphism restricted to a Borel set `K` of
configurations whose decoded structures have Scott height at most `β < ω₁` is Borel. -/
theorem measurableSet_iso_inter_of_scottHeight_le [Countable V] [∀ n, Countable (L.Relations n)]
    {K : Set (RelationalConfiguration L V)} (hK : MeasurableSet K) {β : Ordinal.{w}}
    (hβ : β < ω₁) (hKβ : ∀ c ∈ K, @scottHeight L _ V c.toStructure ≤ β) :
    MeasurableSet
      ({p : RelationalConfiguration L V × RelationalConfiguration L V | isoSetoid L V p.1 p.2} ∩
        K ×ˢ K) := by
  rw [setOf_isoSetoid_inter_eq_of_scottHeight_le hKβ]
  exact (measurableSet_setOf_bfEquivSetoid hβ).inter (hK.prod hK)

/-- **Borel isomorphism under bounded internal stabilization.** In a vocabulary with countably many
relation symbols of each arity, on a countable carrier, isomorphism restricted to a Borel set `K`
of configurations whose decoded structures have internal stabilization ordinal at most `β < ω₁`
is Borel. -/
theorem measurableSet_iso_inter_of_selfStabilizationOrdinal_le [Countable V]
    [∀ n, Countable (L.Relations n)] {K : Set (RelationalConfiguration L V)}
    (hK : MeasurableSet K) {β : Ordinal.{w}} (hβ : β < ω₁)
    (hKβ : ∀ c ∈ K, @selfStabilizationOrdinal L _ V c.toStructure ≤ β) :
    MeasurableSet
      ({p : RelationalConfiguration L V × RelationalConfiguration L V | isoSetoid L V p.1 p.2} ∩
        K ×ˢ K) :=
  measurableSet_iso_inter_of_scottHeight_le hK
    (Ordinal.isPrincipal_add_omega 1 hβ Ordinal.omega0_lt_omega_one) fun c hc =>
      (@scottHeight_le_selfStabilizationOrdinal_add_omega0 L _ V c.toStructure).trans
        (add_le_add_left (hKβ c hc) ω)

/-! ### Borel isomorphism is decided at one countable level -/

/-- If `K` is an analytic set of configurations on which isomorphism is Borel, then isomorphism on
`K` is back-and-forth equivalence at a single countable level. -/
theorem exists_bfLevel_of_measurableSet_iso_inter [Countable V] [∀ n, Countable (L.Relations n)]
    {K : Set (RelationalConfiguration L V)} (hK : AnalyticSet K)
    (h : MeasurableSet
      ({p : RelationalConfiguration L V × RelationalConfiguration L V | isoSetoid L V p.1 p.2} ∩
        K ×ˢ K)) :
    ∃ β : Ordinal.{o}, β < ω₁ ∧
      {p : RelationalConfiguration L V × RelationalConfiguration L V | isoSetoid L V p.1 p.2} ∩
          K ×ˢ K =
        {p | bfEquivSetoid L V β p.1 p.2} ∩ K ×ˢ K := by
  -- The non-isomorphic pairs of `K` form an analytic set, separated at one countable level.
  obtain ⟨β, hβ, hsep⟩ := exists_uniform_bfSeparation.{u, v, w, o}
    ((hK.prod hK).inter_measurableSet h.compl) fun p hp hiso => hp.2 ⟨hiso, hp.1⟩
  refine ⟨β, hβ, Subset.antisymm (fun p hp => ⟨isoSetoid_le_bfEquivSetoid β hp.1, hp.2⟩)
    fun p hp => ⟨?_, hp.2⟩⟩
  by_contra hiso
  exact hsep p ⟨hp.2, fun h' => hiso h'.1⟩ hp.1

/-- **Borel isomorphism is decided at one countable level.** In a vocabulary with countably many
relation symbols of each arity, on a countable carrier, isomorphism restricted to a Borel set `K`
of configurations is Borel exactly when it is back-and-forth equivalence on `K` at some level
`β < ω₁`. -/
theorem measurableSet_iso_inter_iff_exists_bfLevel [Countable V]
    [∀ n, Countable (L.Relations n)] {K : Set (RelationalConfiguration L V)}
    (hK : MeasurableSet K) :
    MeasurableSet
        ({p : RelationalConfiguration L V × RelationalConfiguration L V | isoSetoid L V p.1 p.2} ∩
          K ×ˢ K) ↔
      ∃ β : Ordinal.{o}, β < ω₁ ∧
        {p : RelationalConfiguration L V × RelationalConfiguration L V | isoSetoid L V p.1 p.2} ∩
            K ×ˢ K =
          {p | bfEquivSetoid L V β p.1 p.2} ∩ K ×ˢ K := by
  refine ⟨exists_bfLevel_of_measurableSet_iso_inter hK.analyticSet, fun ⟨β, hβ, heq⟩ => ?_⟩
  rw [heq]
  exact (measurableSet_setOf_bfEquivSetoid hβ).inter (hK.prod hK)

/-! ### Borel strata of the internal stabilization ordinal -/

/-- In a vocabulary with countably many relation symbols of each arity, on a countable carrier,
the configurations whose decoded structure stabilizes internally at a level `β < ω₁` form a Borel
set. -/
theorem measurableSet_setOf_selfStabilizesCompletely [Countable V]
    [∀ n, Countable (L.Relations n)] {β : Ordinal.{o}} (hβ : β < ω₁) :
    MeasurableSet
      {c : RelationalConfiguration L V | @SelfStabilizesCompletely L _ V c.toStructure β} := by
  -- Pull back the Borel back-and-forth conditions along the diagonal `c ↦ (c, c)`.
  have hbf (γ : Ordinal.{o}) (hγ : γ < ω₁) (n : ℕ) (a b : Fin n → V) :
      Measurable fun c : RelationalConfiguration L V =>
        @BFEquiv L _ V V c.toStructure c.toStructure γ n a b :=
    measurableSet_setOfPred.1
      ((measurable_id.prodMk measurable_id) (measurableSet_setOf_bfEquiv hγ a b))
  have hβ' : β + 1 < ω₁ := (Cardinal.isSuccLimit_omega 1).add_one_lt hβ
  simp only [selfStabilizesCompletely_def]
  exact measurableSet_setOfPred.2 (Measurable.forall fun n => Measurable.forall fun a =>
    Measurable.forall fun b => (hbf β hβ n a b).iff (hbf (β + 1) hβ' n a b))

/-- **Borel strata of the internal stabilization ordinal.** In a vocabulary with countably many
relation symbols of each arity, on a countable carrier, the configurations whose decoded structure
has internal stabilization ordinal at most `β < ω₁` form a Borel set. -/
theorem measurableSet_setOf_selfStabilizationOrdinal_le [Countable V]
    [∀ n, Countable (L.Relations n)] {β : Ordinal.{w}} (hβ : β < ω₁) :
    MeasurableSet
      {c : RelationalConfiguration L V | @selfStabilizationOrdinal L _ V c.toStructure ≤ β} := by
  simp only [selfStabilizationOrdinal_le_iff]
  exact measurableSet_setOf_selfStabilizesCompletely hβ

end TauCeti.RelationalConfiguration
