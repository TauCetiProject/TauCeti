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
`representativeClass F` is the class of structures isomorphic to some `F i`. The Fraïssé conditions
can be checked on the representatives: finite generation, countability up to isomorphism (from a
countable index type), the hereditary property (from finitely generated substructures of
representatives), joint embedding and amalgamation all transfer to the closure. So the closure of a
countable nonempty family satisfying them is a Fraïssé class (`isFraisse_representativeClass`).

The index type and the carrier universe are independent. Neither countability of the language nor a
decision procedure for isomorphism is needed, and no canonical representative is chosen.

## Main definitions

* `FirstOrder.Language.representativeClass`: the isomorphism closure of a family of structures.

## Main results

* `FirstOrder.Language.representativeClass_countable_quotient`: a countable family has countably
  many isomorphism classes in its closure.
* `FirstOrder.Language.representativeClass_hereditary`,
  `FirstOrder.Language.representativeClass_jointEmbedding` and
  `FirstOrder.Language.representativeClass_amalgamation`: the Fraïssé conditions transfer from the
  representatives.
* `FirstOrder.Language.isFraisse_representativeClass`: the closure of a countable nonempty family
  satisfying them is a Fraïssé class.

## References

* Ported from `cameronfreer/computable-model-theory` at commit
  `5d5f65cef1e47776f0e3e60b3bacfda507f00aed`,
  `ComputableModelTheory/ModelTheory/RepresentativeAge.lean`, through
  `isFraisse_representativeClass`, with the same statements; the unfolding lemma
  `mem_representativeClass_iff` is new.
-/

public section

universe u v w z

namespace FirstOrder.Language

open CategoryTheory FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {I : Type z} (F : I → Bundled.{w} L.Structure)

/-- The **isomorphism closure** of a family of structures: the structures isomorphic to some
member of the family. -/
def representativeClass : Set (Bundled.{w} L.Structure) :=
  {M | ∃ i, Nonempty (M ≃[L] F i)}

variable {F} in
/-- Unfolding lemma for `representativeClass`. -/
theorem mem_representativeClass_iff {M : Bundled.{w} L.Structure} :
    M ∈ representativeClass F ↔ ∃ i, Nonempty (M ≃[L] F i) :=
  Iff.rfl

/-- Each representative lies in its isomorphism closure. -/
theorem mem_representativeClass (i : I) : F i ∈ representativeClass F :=
  ⟨i, ⟨Language.Equiv.refl L (F i)⟩⟩

/-- The isomorphism closure of a nonempty family is nonempty. -/
theorem representativeClass_nonempty [Nonempty I] : (representativeClass F).Nonempty :=
  ⟨F (Classical.choice inferInstance), mem_representativeClass F _⟩

/-- If every representative is finitely generated, so is every member of the closure. -/
theorem representativeClass_fg (hfg : ∀ i, Structure.FG L (F i))
    {M : Bundled.{w} L.Structure} (hM : M ∈ representativeClass F) : Structure.FG L M := by
  obtain ⟨i, ⟨e⟩⟩ := hM
  exact e.fg_iff.mpr (hfg i)

/-- **Countability up to isomorphism.** A countable family has an isomorphism closure with countably
many isomorphism classes. Only the index type is assumed countable. -/
theorem representativeClass_countable_quotient [Countable I] :
    (Quotient.mk' '' representativeClass F).Countable := by
  apply (Set.countable_range (fun i => Quotient.mk' (F i))).mono
  rintro _ ⟨M, ⟨i, ⟨e⟩⟩, rfl⟩
  exact ⟨i, Quotient.sound ⟨e.symm⟩⟩

/-- **Hereditary property.** It suffices that every finitely generated substructure of a
representative is isomorphic to a representative. -/
theorem representativeClass_hereditary
    (hsub : ∀ i (S : L.Substructure (F i)), S.FG →
      ∃ j, Nonempty (S ≃[L] F j)) : Hereditary (representativeClass F) := by
  rintro M ⟨i, ⟨e⟩⟩ N ⟨hN, ⟨f⟩⟩
  let g := e.toEmbedding.comp f
  obtain ⟨j, ⟨h⟩⟩ := hsub i g.toHom.range (hN.range g.toHom)
  exact ⟨j, ⟨h.comp g.equivRange⟩⟩

/-- **Joint embedding** transfers from the representatives to their isomorphism closure. -/
theorem representativeClass_jointEmbedding
    (hjep : ∀ i j, ∃ k, Nonempty (F i ↪[L] F k) ∧ Nonempty (F j ↪[L] F k)) :
    JointEmbedding (representativeClass F) := by
  rintro M ⟨i, ⟨e⟩⟩ N ⟨j, ⟨f⟩⟩
  obtain ⟨k, ⟨g⟩, ⟨h⟩⟩ := hjep i j
  exact ⟨F k, mem_representativeClass F k, ⟨g.comp e.toEmbedding⟩,
    ⟨h.comp f.toEmbedding⟩⟩

/-- **Amalgamation** of representative embeddings transfers to their isomorphism closure. -/
theorem representativeClass_amalgamation
    (hap : ∀ i j k (f : F i ↪[L] F j) (g : F i ↪[L] F k),
      ∃ (l : I) (a : F j ↪[L] F l) (b : F k ↪[L] F l), a.comp f = b.comp g) :
    Amalgamation (representativeClass F) := by
  rintro M N P f g ⟨i, ⟨eM⟩⟩ ⟨j, ⟨eN⟩⟩ ⟨k, ⟨eP⟩⟩
  obtain ⟨l, a, b, h⟩ := hap i j k
    (eN.toEmbedding.comp (f.comp eM.symm.toEmbedding))
    (eP.toEmbedding.comp (g.comp eM.symm.toEmbedding))
  refine ⟨F l, a.comp eN.toEmbedding, b.comp eP.toEmbedding,
    mem_representativeClass F l, ?_⟩
  ext x
  have hx := congrArg (fun h : F i ↪[L] F l => h (eM x)) h
  simpa only [Embedding.comp_apply, Language.Equiv.coe_toEmbedding,
    Language.Equiv.symm_apply_apply] using hx

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
  is_nonempty := representativeClass_nonempty F
  FG := fun _ h => representativeClass_fg F hfg h
  is_essentially_countable := representativeClass_countable_quotient F
  hereditary := representativeClass_hereditary F hsub
  jointEmbedding := representativeClass_jointEmbedding F hjep
  amalgamation := representativeClass_amalgamation F hap

end FirstOrder.Language
