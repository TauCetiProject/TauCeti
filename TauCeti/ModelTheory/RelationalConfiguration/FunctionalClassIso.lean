/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import TauCeti.ModelTheory.RelationalConfiguration.ClassIso
public import TauCeti.ModelTheory.RelationalConfiguration.FunctionalCoding

/-!
# Invariant Borel classes of functional configurations and their graph codes

Give the functional coding space `FunctionalConfiguration L ℕ` its Borel σ-algebra. For a language
with countably many function and relation symbols of each arity it is Polish, and the graph code
`FunctionalConfiguration L ℕ → RelationalConfiguration L.graphLanguage ℕ` is continuous and
injective, so by the Lusin–Souslin theorem it maps Borel sets to Borel sets
(`TauCeti.FunctionalConfiguration.measurableSet_image_graphCode`). It is equivariant, so it maps
isomorphism-invariant classes to isomorphism-invariant classes
(`TauCeti.FunctionalConfiguration.isomorphismInvariant_image_graphCode`). Two functional
configurations are isomorphic exactly when their graph codes are, so isomorphism on a class `K` and
isomorphism on its image are Borel bireducible, through the graph code one way and the continuous
inverse `ofGraphCode` the other
(`TauCeti.FunctionalConfiguration.borelBireducible_classIso_image_graphCode`).

## Main definitions

* `TauCeti.FunctionalConfiguration.classIso K`: isomorphism restricted to a class `K` of
  functional configurations.

## Main results

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

variable {L : Language} {V : Type*} [TopologicalSpace V]

/-- The Borel σ-algebra of the functional coding space. -/
instance instMeasurableSpace : MeasurableSpace (FunctionalConfiguration L V) :=
  borel _

instance instBorelSpace : BorelSpace (FunctionalConfiguration L V) :=
  ⟨rfl⟩

variable (L V) in
/-- **Isomorphism restricted to a class** of functional configurations: two members of `K` are
related when their decoded structures are isomorphic. -/
abbrev classIso (K : Set (FunctionalConfiguration L V)) : Setoid K :=
  (isoSetoid L V).comap Subtype.val

omit [TopologicalSpace V] in
/-- **The graph code maps invariant classes to invariant classes**, being equivariant. -/
theorem isomorphismInvariant_image_graphCode {K : Set (FunctionalConfiguration L V)}
    (hK : ∀ ⦃F G⦄, isoSetoid L V F G → F ∈ K → G ∈ K) :
    IsomorphismInvariant (graphCode '' K) := by
  refine isomorphismInvariant_iff.2 ?_
  rintro c d hcd ⟨F, hF, rfl⟩
  obtain ⟨σ, rfl⟩ := RelationalConfiguration.isoSetoid_iff_exists_perm_smul_eq.1 hcd
  refine ⟨σ • F, hK (isoSetoid_iff_exists_perm_smul_eq.2 ⟨σ, rfl⟩) hF, graphCode_perm_smul σ F⟩

variable [∀ n, Countable (L.Functions n)] [∀ n, Countable (L.Relations n)]

/-- The graph language has countably many relation symbols of each arity. -/
private theorem countable_graphLanguage_relations (n : ℕ) :
    Countable (L.graphLanguage.Relations n) :=
  (sigma_mk_injective (i := n)).countable

attribute [local instance] countable_graphLanguage_relations

/-- **The graph code maps Borel classes to Borel classes**, by the Lusin–Souslin theorem: it is
continuous and injective on the Polish functional coding space. -/
theorem measurableSet_image_graphCode {K : Set (FunctionalConfiguration L ℕ)}
    (hK : MeasurableSet K) : MeasurableSet (graphCode '' K) :=
  (continuous_graphCode.measurableEmbedding graphCode_injective).measurableSet_image.2 hK

/-- **Isomorphism on a class and on its graph codes are Borel bireducible.** For every class `K` of
functional configurations on `ℕ`, isomorphism on `K` is Borel bireducible with isomorphism on the
class `graphCode '' K` of graph codes. -/
theorem borelBireducible_classIso_image_graphCode (K : Set (FunctionalConfiguration L ℕ)) :
    (classIso L ℕ K).BorelBireducible
      (RelationalConfiguration.classIso (graphCode '' K)) := by
  refine Setoid.borelBireducible_iff.2 ⟨Setoid.borelReducible_iff.2
    ⟨fun F => ⟨graphCode F.val, mem_image_of_mem _ F.property⟩,
      (continuous_graphCode.measurable.comp measurable_subtypeVal).subtype_mk,
      fun F G => isoSetoid_graphCode_iff.symm⟩, Setoid.borelReducible_iff.2
    ⟨fun c => ⟨ofGraphCode ⟨c.val, ?_⟩, ?_⟩, ?_, fun c d => ?_⟩⟩
  · obtain ⟨F, -, hF⟩ := c.property
    exact hF ▸ isGraphCode_graphCode F
  · obtain ⟨F, hF, h⟩ := c.property
    convert hF
    simp_rw [← h, ofGraphCode_graphCode]
  · exact (continuous_ofGraphCode.measurable.comp
      (measurable_subtypeVal.subtype_mk)).subtype_mk
  · obtain ⟨_, ⟨F, -, rfl⟩⟩ := c
    obtain ⟨_, ⟨G, -, rfl⟩⟩ := d
    simp only [ofGraphCode_graphCode]
    exact isoSetoid_graphCode_iff

end FunctionalConfiguration

end TauCeti
