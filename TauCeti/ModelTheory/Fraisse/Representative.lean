/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Fraisse

/-!
# Fraïssé classes from representative families

For a family `F : I → Bundled L.Structure` of concrete structures, its **isomorphism closure**
`representativeClass F` is the class of structures isomorphic to some `F i`. It is the least
isomorphism-invariant class containing every representative. It does not change when the
representatives are replaced by isomorphic ones, or under surjective reindexing, so permuting or
duplicating representatives gives the same class.

The Fraïssé conditions can be read off the representatives. Every member is finitely generated, the
class is hereditary, and it has joint embedding or amalgamation exactly when the representatives
satisfy the corresponding condition. For heredity, the condition is that every finitely generated
substructure of a representative is isomorphic to a representative. A countable family has
countably many isomorphism classes in its closure. So the closure of a countable nonempty family
satisfying these conditions is a Fraïssé class (`isFraisse_representativeClass`).

The index type and the carrier universe are independent. Neither countability of the language nor a
decision procedure for isomorphism is needed, and no canonical representative is chosen.

## Main definitions

* `FirstOrder.Language.representativeClass`: the isomorphism closure of a family of structures.

## Main results

* `FirstOrder.Language.mem_representativeClass_congr`: membership is invariant under isomorphism.
* `FirstOrder.Language.representativeClass_subset_iff`: the closure is the least
  isomorphism-invariant class containing the representatives.
* `FirstOrder.Language.representativeClass_congr`: replacing the representatives by isomorphic
  ones, in both directions, does not change the closure.
* `FirstOrder.Language.representativeClass_comp_subset` and
  `FirstOrder.Language.representativeClass_comp`: reindexing shrinks the closure, and surjective
  reindexing preserves it.
* `FirstOrder.Language.forall_mem_representativeClass_fg_iff`,
  `FirstOrder.Language.hereditary_representativeClass_iff`,
  `FirstOrder.Language.jointEmbedding_representativeClass_iff` and
  `FirstOrder.Language.amalgamation_representativeClass_iff`: the Fraïssé conditions on the closure
  are equivalent to conditions on the representatives.
* `FirstOrder.Language.representativeClass_countable_quotient`: a countable family has countably
  many isomorphism classes in its closure.
* `FirstOrder.Language.isFraisse_representativeClass`: the closure of a countable nonempty family
  satisfying the representative conditions is a Fraïssé class.

## References

* The definition and the transfer of the Fraïssé conditions to the closure are ported from
  `cameronfreer/computable-model-theory` at commit `5d5f65cef1e47776f0e3e60b3bacfda507f00aed`,
  `ComputableModelTheory/ModelTheory/RepresentativeAge.lean`, through
  `isFraisse_representativeClass`.
-/

public section

universe u v w z z'

namespace FirstOrder.Language

open CategoryTheory FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {I : Type z} {J : Type z'}

/-- The **isomorphism closure** of a family of structures: the structures isomorphic to some
member of the family. -/
def representativeClass (F : I → Bundled.{w} L.Structure) : Set (Bundled.{w} L.Structure) :=
  {M | ∃ i, Nonempty (M ≃[L] F i)}

variable {F : I → Bundled.{w} L.Structure}

/-- Membership in the isomorphism closure: being isomorphic to some representative. -/
@[simp]
theorem mem_representativeClass_iff {M : Bundled.{w} L.Structure} :
    M ∈ representativeClass F ↔ ∃ i, Nonempty (M ≃[L] F i) :=
  Iff.rfl

/-- Each representative lies in its isomorphism closure. This simp rule takes priority over the
unfolding `mem_representativeClass_iff`, which would leave an isomorphism to find. -/
@[simp high]
theorem mem_representativeClass (i : I) : F i ∈ representativeClass F :=
  ⟨i, ⟨Language.Equiv.refl L (F i)⟩⟩

/-- **Isomorphism invariance.** Isomorphic structures are both in the isomorphism closure or both
outside it. -/
theorem mem_representativeClass_congr {M N : Bundled.{w} L.Structure}
    (h : Nonempty (M ≃[L] N)) : M ∈ representativeClass F ↔ N ∈ representativeClass F :=
  ⟨fun ⟨i, ⟨e⟩⟩ => ⟨i, ⟨e.comp h.some.symm⟩⟩, fun ⟨i, ⟨e⟩⟩ => ⟨i, ⟨e.comp h.some⟩⟩⟩

/-- **Leastness.** An isomorphism-invariant class contains the isomorphism closure exactly when it
contains every representative. -/
theorem representativeClass_subset_iff {K : Set (Bundled.{w} L.Structure)}
    (hK : ∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → M ∈ K → N ∈ K) :
    representativeClass F ⊆ K ↔ ∀ i, F i ∈ K :=
  ⟨fun h i => h (mem_representativeClass i),
    fun h _ ⟨i, ⟨e⟩⟩ => hK _ _ ⟨e.symm⟩ (h i)⟩

/-- The isomorphism closure of a family is empty exactly when the family is. -/
@[simp]
theorem representativeClass_eq_empty_iff : representativeClass F = ∅ ↔ IsEmpty I :=
  ⟨fun h => ⟨fun i => (h ▸ mem_representativeClass (F := F) i : F i ∈ (∅ : Set _))⟩,
    fun _ => Set.eq_empty_of_forall_notMem fun _ ⟨i, _⟩ => isEmptyElim i⟩

/-- The isomorphism closure of a family is nonempty exactly when the family is. -/
@[simp]
theorem representativeClass_nonempty_iff : (representativeClass F).Nonempty ↔ Nonempty I :=
  ⟨fun ⟨_, i, _⟩ => ⟨i⟩, fun ⟨i⟩ => ⟨F i, mem_representativeClass i⟩⟩

/-- If every representative of `F` is isomorphic to a representative of `G`, the isomorphism
closure of `F` is contained in that of `G`. -/
theorem representativeClass_subset_of_forall_exists_equiv {G : J → Bundled.{w} L.Structure}
    (h : ∀ i, ∃ j, Nonempty (F i ≃[L] G j)) : representativeClass F ⊆ representativeClass G :=
  fun _ ⟨i, ⟨e⟩⟩ =>
    let ⟨j, ⟨e'⟩⟩ := h i
    ⟨j, ⟨e'.comp e⟩⟩

/-- **Replacing representatives.** Two families have the same isomorphism closure when each
representative of either family is isomorphic to a representative of the other. -/
theorem representativeClass_congr {G : J → Bundled.{w} L.Structure}
    (hFG : ∀ i, ∃ j, Nonempty (F i ≃[L] G j)) (hGF : ∀ j, ∃ i, Nonempty (G j ≃[L] F i)) :
    representativeClass F = representativeClass G :=
  (representativeClass_subset_of_forall_exists_equiv hFG).antisymm
    (representativeClass_subset_of_forall_exists_equiv hGF)

/-- **Reindexing.** The isomorphism closure of a reindexed family is contained in the original
closure. -/
theorem representativeClass_comp_subset (g : J → I) :
    representativeClass (F ∘ g) ⊆ representativeClass F :=
  representativeClass_subset_of_forall_exists_equiv fun j => ⟨g j, ⟨Language.Equiv.refl L _⟩⟩

/-- **Surjective reindexing.** Reindexing along a surjection does not change the isomorphism
closure. In particular, permuting or duplicating representatives gives the same class. -/
theorem representativeClass_comp {g : J → I} (hg : Function.Surjective g) :
    representativeClass (F ∘ g) = representativeClass F :=
  representativeClass_congr (fun j => ⟨g j, ⟨Language.Equiv.refl L _⟩⟩) fun i =>
    let ⟨j, hj⟩ := hg i
    ⟨j, ⟨hj ▸ Language.Equiv.refl L _⟩⟩

/-- **Finite generation.** Every member of the isomorphism closure is finitely generated exactly
when every representative is. -/
theorem forall_mem_representativeClass_fg_iff :
    (∀ M ∈ representativeClass F, Structure.FG L M) ↔ ∀ i, Structure.FG L (F i) :=
  ⟨fun h i => h _ (mem_representativeClass i), fun h _ ⟨i, ⟨e⟩⟩ => e.fg_iff.mpr (h i)⟩

/-- **Countability up to isomorphism.** A countable family has an isomorphism closure with countably
many isomorphism classes. Only the index type is assumed countable. -/
theorem representativeClass_countable_quotient [Countable I] :
    (Quotient.mk' '' representativeClass F).Countable := by
  apply (Set.countable_range (fun i => Quotient.mk' (F i))).mono
  rintro _ ⟨M, ⟨i, ⟨e⟩⟩, rfl⟩
  exact ⟨i, Quotient.sound ⟨e.symm⟩⟩

/-- **Hereditary property.** The isomorphism closure is hereditary exactly when every finitely
generated substructure of a representative is isomorphic to a representative. -/
theorem hereditary_representativeClass_iff :
    Hereditary (representativeClass F) ↔
      ∀ i (S : L.Substructure (F i)), S.FG → ∃ j, Nonempty (S ≃[L] F j) := by
  refine ⟨fun h i S hS => h _ (mem_representativeClass i)
    (show (Bundled.of S : Bundled.{w} L.Structure) ∈ L.age (F i) from
      ⟨(Substructure.fg_iff_structure_fg S).1 hS, ⟨S.subtype⟩⟩), fun hsub => ?_⟩
  rintro M ⟨i, ⟨e⟩⟩ N ⟨hN, ⟨f⟩⟩
  let g := e.toEmbedding.comp f
  obtain ⟨j, ⟨h⟩⟩ := hsub i g.toHom.range (hN.range g.toHom)
  exact ⟨j, ⟨h.comp g.equivRange⟩⟩

/-- **Joint embedding.** The isomorphism closure has the joint embedding property exactly when any
two representatives embed into a common representative. -/
theorem jointEmbedding_representativeClass_iff :
    JointEmbedding (representativeClass F) ↔
      ∀ i j, ∃ k, Nonempty (F i ↪[L] F k) ∧ Nonempty (F j ↪[L] F k) := by
  refine ⟨fun h i j => ?_, fun hjep => ?_⟩
  · obtain ⟨P, ⟨k, ⟨e⟩⟩, ⟨f⟩, ⟨g⟩⟩ :=
      h _ (mem_representativeClass i) _ (mem_representativeClass j)
    exact ⟨k, ⟨e.toEmbedding.comp f⟩, ⟨e.toEmbedding.comp g⟩⟩
  rintro M ⟨i, ⟨e⟩⟩ N ⟨j, ⟨f⟩⟩
  obtain ⟨k, ⟨g⟩, ⟨h⟩⟩ := hjep i j
  exact ⟨F k, mem_representativeClass k, ⟨g.comp e.toEmbedding⟩, ⟨h.comp f.toEmbedding⟩⟩

/-- **Amalgamation.** The isomorphism closure has the amalgamation property exactly when any two
embeddings out of a representative into representatives are amalgamated in a representative. -/
theorem amalgamation_representativeClass_iff :
    Amalgamation (representativeClass F) ↔
      ∀ i j k (f : F i ↪[L] F j) (g : F i ↪[L] F k),
        ∃ (l : I) (a : F j ↪[L] F l) (b : F k ↪[L] F l), a.comp f = b.comp g := by
  refine ⟨fun h i j k f g => ?_, fun hap => ?_⟩
  · obtain ⟨Q, a, b, ⟨l, ⟨e⟩⟩, hab⟩ := h _ _ _ f g (mem_representativeClass i)
      (mem_representativeClass j) (mem_representativeClass k)
    refine ⟨l, e.toEmbedding.comp a, e.toEmbedding.comp b, ?_⟩
    rw [Embedding.comp_assoc, hab, ← Embedding.comp_assoc]
  rintro M N P f g ⟨i, ⟨eM⟩⟩ ⟨j, ⟨eN⟩⟩ ⟨k, ⟨eP⟩⟩
  obtain ⟨l, a, b, h⟩ := hap i j k
    (eN.toEmbedding.comp (f.comp eM.symm.toEmbedding))
    (eP.toEmbedding.comp (g.comp eM.symm.toEmbedding))
  refine ⟨F l, a.comp eN.toEmbedding, b.comp eP.toEmbedding, mem_representativeClass l, ?_⟩
  ext x
  have hx := congrArg (fun h : F i ↪[L] F l => h (eM x)) h
  simpa only [Embedding.comp_apply, Language.Equiv.coe_toEmbedding,
    Language.Equiv.symm_apply_apply] using hx

variable (F) in
/-- **Fraïssé classes from representatives.** A countable nonempty family of finitely generated
structures, closed under finitely generated substructures up to isomorphism and with joint
embedding and amalgamation among the representatives, has an isomorphism closure that is a
Fraïssé class. No infinite structure is constructed. -/
theorem isFraisse_representativeClass [Nonempty I] [Countable I]
    (hfg : ∀ i, Structure.FG L (F i))
    (hsub : ∀ i (S : L.Substructure (F i)), S.FG → ∃ j, Nonempty (S ≃[L] F j))
    (hjep : ∀ i j, ∃ k, Nonempty (F i ↪[L] F k) ∧ Nonempty (F j ↪[L] F k))
    (hap : ∀ i j k (f : F i ↪[L] F j) (g : F i ↪[L] F k),
      ∃ (l : I) (a : F j ↪[L] F l) (b : F k ↪[L] F l), a.comp f = b.comp g) :
    IsFraisse (representativeClass F) where
  is_nonempty := representativeClass_nonempty_iff.2 ‹_›
  FG := forall_mem_representativeClass_fg_iff.2 hfg
  is_essentially_countable := representativeClass_countable_quotient
  hereditary := hereditary_representativeClass_iff.2 hsub
  jointEmbedding := jointEmbedding_representativeClass_iff.2 hjep
  amalgamation := amalgamation_representativeClass_iff.2 hap

end FirstOrder.Language
