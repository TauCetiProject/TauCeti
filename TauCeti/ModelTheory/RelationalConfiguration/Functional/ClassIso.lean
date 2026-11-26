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
* `TauCeti.FunctionalConfiguration.borelBireducible_classIso_preimage_rel`: for a relational
  language, isomorphism on a class `K` of configurations and on the class of functional
  configurations whose relational part lies in `K` are Borel bireducible.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer, 1995, §16.C (the space of countable
  structures, with function symbols coded by their graphs), and Theorem 15.1 (Lusin–Souslin).
* G. Paolini and S. Shelah, *Torsion-free abelian groups are Borel complete*, Ann. of Math. 199
  (2024), arXiv:2102.12371, Fact 1.1 and Definition 1.6 (the isomorphism relation on a class of
  structures with universe `ℕ`, and its subspace Borel structure).
* R. Camerlo and S. Gao, *The completeness of the isomorphism relation for countable Boolean
  algebras*, Trans. Amer. Math. Soc. 353 (2001), §1.
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

/-- Isomorphism on a class is the orbit relation of the logic action, pulled back to the class. -/
theorem classIso_eq_comap_orbitRel :
    classIso L V K = (MulAction.orbitRel (Equiv.Perm V) _).comap Subtype.val := by
  rw [classIso_def, isoSetoid_eq_orbitRel]

/-- Two members of a class are related exactly when a permutation of the carrier relabels the
first into the second. -/
theorem classIso_iff_exists_perm_smul_eq {F G : K} :
    classIso L V K F G ↔ ∃ σ : Equiv.Perm V, σ • (F : FunctionalConfiguration L V) = G :=
  isoSetoid_iff_exists_perm_smul_eq

/-- **The graph code maps invariant classes to invariant classes**, being equivariant. -/
theorem isomorphismInvariant_image_graphCode (hK : IsomorphismInvariant K) :
    RelationalConfiguration.IsomorphismInvariant (graphCode '' K) := by
  refine RelationalConfiguration.isomorphismInvariant_iff_isInvariantBlock.2 fun σ => ?_
  rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
  exact ⟨σ • F, FunctionalConfiguration.isomorphismInvariant_iff_isInvariantBlock.1 hK σ
    (smul_mem_smul_set hF), graphCode_perm_smul σ F⟩

section Relational

variable [L.IsRelational] [TopologicalSpace V]

/-- **Relational classes as functional classes.** For a relational language, isomorphism on a
class `K` of configurations and isomorphism on the class of functional configurations whose
relational part lies in `K` are Borel bireducible, through the relational part and the empty
function table. -/
theorem borelBireducible_classIso_preimage_rel [∀ n, Countable (L.Relations n)] [Countable V]
    (K : Set (RelationalConfiguration L V)) :
    (classIso L V (rel ⁻¹' K)).BorelBireducible (RelationalConfiguration.classIso K) := by
  have hrel : Continuous (rel : FunctionalConfiguration L V → _) := continuous_rel
  have hmk : Continuous fun c : RelationalConfiguration L V =>
      (mk isEmptyElim c : FunctionalConfiguration L V) :=
    continuous_mk continuous_const continuous_id
  have hmem (c : K) : (mk isEmptyElim c.val : FunctionalConfiguration L V) ∈ rel ⁻¹' K := by
    simp [rel_mk]
  refine Setoid.borelBireducible_iff.2 ⟨Setoid.borelReducible_iff.2
    ⟨fun F => ⟨F.val.rel, F.property⟩, (hrel.measurable.comp measurable_subtypeVal).subtype_mk,
      fun F G => ?_⟩, Setoid.borelReducible_iff.2
    ⟨fun c => ⟨mk isEmptyElim c.val, hmem c⟩,
      (hmk.measurable.comp measurable_subtypeVal).subtype_mk (h := hmem), fun c d => ?_⟩⟩
  · rw [classIso_apply, RelationalConfiguration.classIso_apply, isoSetoid_iff_isoSetoid_rel]
  · rw [classIso_apply, RelationalConfiguration.classIso_apply, isoSetoid_iff_isoSetoid_rel,
      rel_mk, rel_mk]

end Relational

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
  -- `e` is the graph code corestricted to `graphCode '' K`: this holds by unfolding
  -- `MeasurableEmbedding.equivImage` to `Equiv.Set.image`, and Mathlib states no lemma for it.
  have he (F : K) : (e F : RelationalConfiguration L.graphLanguage V) = graphCode F.val := rfl
  have hiff (F G : K) : classIso L V K F G ↔ RelationalConfiguration.classIso _ (e F) (e G) := by
    rw [classIso_apply, RelationalConfiguration.classIso_apply, he, he, isoSetoid_graphCode_iff]
  refine Setoid.borelBireducible_iff.2 ⟨Setoid.borelReducible_iff.2
    ⟨e, e.measurable, hiff⟩, Setoid.borelReducible_iff.2
    ⟨e.symm, e.symm.measurable, fun c d => ?_⟩⟩
  obtain ⟨F, rfl⟩ := e.surjective c
  obtain ⟨G, rfl⟩ := e.surjective d
  rw [e.symm_apply_apply, e.symm_apply_apply, hiff]

end FunctionalConfiguration

end TauCeti
