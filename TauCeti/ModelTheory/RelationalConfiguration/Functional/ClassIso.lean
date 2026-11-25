/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import TauCeti.ModelTheory.RelationalConfiguration.ClassIso
public import TauCeti.ModelTheory.RelationalConfiguration.Functional.Coding

/-!
# Invariant Borel classes of functional configurations and their graph codes

Isomorphism restricted to a class `K` of functional configurations is `classIso L V K`. On a
countable discrete carrier, for a language with countably many function and relation symbols of
each arity, the functional coding space `FunctionalConfiguration L V` is Polish, and the graph code
`FunctionalConfiguration L V → RelationalConfiguration L.graphLanguage V` is continuous and
injective, so by the Lusin–Souslin theorem it is a measurable embedding
(`TauCeti.FunctionalConfiguration.measurableEmbedding_graphCode`) and maps Borel sets to Borel sets
(`TauCeti.FunctionalConfiguration.measurableSet_image_graphCode`). It is equivariant, so it maps
isomorphism-invariant classes to isomorphism-invariant classes
(`TauCeti.FunctionalConfiguration.isomorphismInvariant_image_graphCode`). Two functional
configurations are isomorphic exactly when their graph codes are, so isomorphism on a class `K` and
isomorphism on its image are Borel bireducible, through the graph code and its measurable inverse
on the image (`TauCeti.FunctionalConfiguration.borelBireducible_classIso_image_graphCode`).

## Main definitions

* `TauCeti.FunctionalConfiguration.classIso L V K`: isomorphism restricted to a class `K` of
  functional configurations.

## Main results

* `TauCeti.FunctionalConfiguration.classIso_apply` and
  `TauCeti.FunctionalConfiguration.classIso_iff_exists_perm_smul_eq`: two members of `K` are
  related exactly when they are isomorphic, that is, when a permutation relabels one into the
  other.
* `TauCeti.FunctionalConfiguration.measurableEmbedding_graphCode`: the graph code is a measurable
  embedding.
* `TauCeti.FunctionalConfiguration.measurableSet_image_graphCode`: the image of a Borel class is
  Borel.
* `TauCeti.FunctionalConfiguration.isomorphismInvariant_image_graphCode`: the image of an
  invariant class is invariant.
* `TauCeti.FunctionalConfiguration.borelBireducible_classIso_image_graphCode`: isomorphism on a
  class and on its image are Borel bireducible.
-/

public section

open FirstOrder FirstOrder.Language Set

namespace TauCeti

open RelationalConfiguration

namespace FunctionalConfiguration

variable {L : Language} {V : Type*}

variable (L V) in
/-- **Isomorphism restricted to a class** of functional configurations: two members of `K` are
related when their decoded structures are isomorphic. -/
abbrev classIso (K : Set (FunctionalConfiguration L V)) : Setoid K :=
  (isoSetoid L V).comap Subtype.val

variable {K : Set (FunctionalConfiguration L V)}

/-- Isomorphism on a class is the pullback of isomorphism along the inclusion of the class. -/
theorem classIso_def (K : Set (FunctionalConfiguration L V)) :
    classIso L V K = (isoSetoid L V).comap Subtype.val :=
  (rfl)

/-- Two members of a class are related exactly when they are isomorphic. -/
@[simp]
theorem classIso_apply {F G : K} : classIso L V K F G ↔ isoSetoid L V F G :=
  Iff.rfl

/-- Two members of a class are related exactly when a permutation of the carrier relabels the
first into the second. -/
theorem classIso_iff_exists_perm_smul_eq {F G : K} :
    classIso L V K F G ↔ ∃ σ : Equiv.Perm V, σ • (F : FunctionalConfiguration L V) = G :=
  isoSetoid_iff_exists_perm_smul_eq

/-- **The graph code maps invariant classes to invariant classes**, being equivariant. -/
theorem isomorphismInvariant_image_graphCode (hK : IsomorphismInvariant K) :
    RelationalConfiguration.IsomorphismInvariant (graphCode '' K) := by
  refine RelationalConfiguration.isomorphismInvariant_iff.2 ?_
  rintro c d hcd ⟨F, hF, rfl⟩
  obtain ⟨σ, rfl⟩ := RelationalConfiguration.isoSetoid_iff_exists_perm_smul_eq.1 hcd
  exact ⟨σ • F, FunctionalConfiguration.isomorphismInvariant_iff.1 hK
    (isoSetoid_iff_exists_perm_smul_eq.2 ⟨σ, rfl⟩) hF, graphCode_perm_smul σ F⟩

variable [TopologicalSpace V] [DiscreteTopology V] [Countable V]
  [∀ n, Countable (L.Functions n)] [∀ n, Countable (L.Relations n)]

/-- **The graph code is a measurable embedding**, by the Lusin–Souslin theorem: it is continuous
and injective on the Polish functional coding space. -/
theorem measurableEmbedding_graphCode : MeasurableEmbedding (graphCode (L := L) (V := V)) :=
  continuous_graphCode.measurableEmbedding graphCode_injective

/-- **The graph code maps Borel classes to Borel classes.** -/
theorem measurableSet_image_graphCode (hK : MeasurableSet K) : MeasurableSet (graphCode '' K) :=
  measurableEmbedding_graphCode.measurableSet_image.2 hK

/-- **Isomorphism on a class and on its graph codes are Borel bireducible.** For every class `K` of
functional configurations on a countable discrete carrier, isomorphism on `K` is Borel bireducible
with isomorphism on the class `graphCode '' K` of graph codes. -/
theorem borelBireducible_classIso_image_graphCode (K : Set (FunctionalConfiguration L V)) :
    (classIso L V K).BorelBireducible (RelationalConfiguration.classIso (graphCode '' K)) := by
  let e := measurableEmbedding_graphCode.equivImage K
  refine Setoid.borelBireducible_iff.2 ⟨Setoid.borelReducible_iff.2
    ⟨e, e.measurable, fun F G => isoSetoid_graphCode_iff.symm⟩, Setoid.borelReducible_iff.2
    ⟨e.symm, e.symm.measurable, fun c d => ?_⟩⟩
  obtain ⟨F, rfl⟩ := e.surjective c
  obtain ⟨G, rfl⟩ := e.surjective d
  simp only [MeasurableEquiv.symm_apply_apply]
  exact isoSetoid_graphCode_iff

end FunctionalConfiguration

end TauCeti
