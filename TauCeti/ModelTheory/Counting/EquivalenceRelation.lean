/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.RelationalConfiguration
public import TauCeti.ModelTheory.BackAndForth.Graph
public import TauCeti.ModelTheory.Counting.Classes
public import TauCeti.ModelTheory.Scott.EquivalenceRelation

/-!
# A perfect set of countable equivalence relations

An equivalence relation `r` on `V` is presented in the language of graphs by the graph
`SimpleGraph.fromRel r`, in which two vertices are adjacent when they are distinct and
`r`-related. The first-order sentence `TauCeti.equivalenceRelationSentence` says that adjacency is
irreflexive, symmetric and transitive between distinct vertices; its models are exactly the graphs
of equivalence relations (`TauCeti.realize_equivalenceRelationSentence_iff`), and its model class
on a carrier `V` consists of the configurations of these graphs
(`TauCeti.mem_modelsOf_equivalenceRelationSentence_iff`). Two such configurations are isomorphic
exactly when the equivalence relations are.

This sentence has continuum many countable models, witnessed by an explicit perfect set of pairwise
non-isomorphic models on `ℕ`, with no use of Silver's theorem or of the continuum hypothesis. Split
`ℕ` into blocks `B k` with `k + 2` elements. For `z : ℕ → Bool`, the configuration
`TauCeti.equivalenceRelationCantorFamily z` is the graph of the equivalence relation in which `B k`
is a single class when `z k = true` and splits into singletons otherwise. Each atom depends on at
most one bit of `z`, so the family is continuous. The classes with at least two elements are the
blocks `B k` with `z k = true`, of size `k + 2`, so the class sizes recover `z`, and distinct `z`
give non-isomorphic models. The range of the family is therefore a perfect set of pairwise
non-isomorphic models: the second alternative of Morley's theorem holds for this sentence, at the
tier `ℕ`.

## Main results

* `TauCeti.realize_equivalenceRelationSentence_iff`: the models of the sentence are the graphs of
  equivalence relations.
* `TauCeti.isoSetoid_toRelationalConfiguration_fromRel_iff`: the configurations of the graphs of
  two equivalence relations are isomorphic exactly when the relations are.
* `TauCeti.isoSetoid_fromRel_iff_enatCard_eq`: on a countable carrier, the graphs of two
  equivalence relations with infinite classes are isomorphic exactly when the relations have
  equally many classes.
* `TauCeti.isoSetoid_equivalenceRelationCantorFamily_iff`: the explicit family is injective up to
  isomorphism.
* `TauCeti.hasCantorAntichainOn_modelsOf_equivalenceRelationSentence` and
  `TauCeti.hasPerfectlyManyCountableModels_equivalenceRelationSentence`: a Cantor family, hence a
  perfect set, of pairwise non-isomorphic models on `ℕ`.
* `TauCeti.countableModelCount_equivalenceRelationSentence`: exactly continuum many countable
  models.

## References

* M. Morley, *The number of countable models*, J. Symbolic Logic 35 (1970), 14–18.
* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, the chapter
  on the space of countable models.
-/

public section

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Cardinal Set SimpleGraph

namespace TauCeti

open RelationalConfiguration

/-! ### The sentence of equivalence relations -/

/-- In the language of graphs, the sentence saying that adjacency is the graph
`SimpleGraph.fromRel r` of an equivalence relation `r`: it is irreflexive, symmetric, and
transitive between distinct vertices. -/
def equivalenceRelationSentence : Language.graph.Sentenceω :=
  (adj.irreflexive ⊓ adj.symmetric ⊓
    ∀' ∀' ∀' (adj.boundedFormula₂ &0 &1 ⟹ adj.boundedFormula₂ &1 &2 ⟹
      ∼((&0).bdEqual &2) ⟹ adj.boundedFormula₂ &0 &2)).toInf

/-- A structure in the language of graphs satisfies `equivalenceRelationSentence` exactly when it
is the graph of an equivalence relation. -/
theorem realize_equivalenceRelationSentence_iff {M : Type*} [S : Language.graph.Structure M] :
    SentenceInf.Realize equivalenceRelationSentence M ↔
      ∃ r : Setoid M, S = (fromRel r).structure := by
  -- As in Mathlib's `Relations.realize_transitive`, the quantifiers unfold definitionally.
  have htrans : M ⊨ (∀' ∀' ∀' (adj.boundedFormula₂ &0 &1 ⟹ adj.boundedFormula₂ &1 &2 ⟹
      ∼((&0).bdEqual &2) ⟹ adj.boundedFormula₂ &0 &2) : Language.graph.Sentence) ↔
      ∀ x y z : M, RelMap adj ![x, y] → RelMap adj ![y, z] → x ≠ z → RelMap adj ![x, z] :=
    forall₃_congr fun _ _ _ => imp_congr BoundedFormula.realize_rel₂ <|
      imp_congr BoundedFormula.realize_rel₂ <|
        imp_congr (not_congr (BoundedFormula.realize_bdEqual _ _)) BoundedFormula.realize_rel₂
  simp only [equivalenceRelationSentence, Sentence.realize_toInf, Sentence.realize_inf,
    Relations.realize_irreflexive, Relations.realize_symmetric, htrans]
  refine ⟨fun ⟨⟨hirr, hsymm⟩, htrans⟩ => ?_, ?_⟩
  · -- `x` and `y` are related when they are equal or adjacent.
    let r : Setoid M :=
      { r x y := x = y ∨ RelMap adj ![x, y]
        iseqv :=
          { refl _ := .inl rfl
            symm h := h.imp Eq.symm (hsymm.symm _ _)
            trans {x y z} hxy hyz := by
              rcases hxy with rfl | hxy
              · exact hyz
              rcases hyz with rfl | hyz
              · exact .inr hxy
              by_cases hxz : x = z
              · exact .inl hxz
              · exact .inr (htrans x y z hxy hyz hxz) } }
    have : M ⊨ Theory.simpleGraph := Theory.simpleGraph_model_iff.2 ⟨hirr, hsymm⟩
    refine ⟨r, structure_simpleGraphOfStructure.symm.trans (congrArg SimpleGraph.structure ?_)⟩
    ext x y
    simp only [simpleGraphOfStructure_adj, fromRel_adj]
    refine ⟨fun h => ⟨fun hxy => hirr.irrefl y (hxy ▸ h), .inl (.inr h)⟩, ?_⟩
    rintro ⟨hne, (rfl | h) | (rfl | h)⟩
    · exact absurd rfl hne
    · exact h
    · exact absurd rfl hne
    · exact hsymm.symm _ _ h
  · rintro ⟨r, rfl⟩
    simp only [relMap_adj, fromRel_adj]
    refine ⟨⟨⟨fun _ h => h.1 rfl⟩, ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩⟩,
      fun x y z hxy hyz hxz => ⟨hxz, .inl (r.trans' (hxy.2.elim id r.symm') ?_)⟩⟩
    exact hyz.2.elim id r.symm'

/-- The graph of an equivalence relation satisfies `equivalenceRelationSentence`. -/
@[simp]
theorem realize_equivalenceRelationSentence_fromRel {V : Type*} (r : Setoid V) :
    letI := (fromRel r).structure
    SentenceInf.Realize equivalenceRelationSentence V :=
  letI := (fromRel r).structure
  realize_equivalenceRelationSentence_iff.2 ⟨r, rfl⟩

/-- The models of `equivalenceRelationSentence` on `V` are the configurations of the graphs of
the equivalence relations on `V`. -/
theorem mem_modelsOf_equivalenceRelationSentence_iff {V : Type*}
    {c : RelationalConfiguration Language.graph V} :
    c ∈ modelsOf equivalenceRelationSentence ↔
      ∃ r : Setoid V, c = (fromRel r).toRelationalConfiguration := by
  rw [mem_modelsOf, @realize_equivalenceRelationSentence_iff _ c.toStructure]
  -- A configuration is determined by its decoded structure.
  refine exists_congr fun r => ?_
  rw [← equivStructure.injective.eq_iff, equivStructure_apply, equivStructure_apply,
    toStructure_toRelationalConfiguration]

/-- The configurations of the graphs of two equivalence relations are isomorphic exactly when the
relations are isomorphic. -/
theorem isoSetoid_toRelationalConfiguration_fromRel_iff {V : Type*} {r s : Setoid V} :
    isoSetoid Language.graph V (fromRel r).toRelationalConfiguration
        (fromRel s).toRelationalConfiguration ↔ Nonempty (⇑r ≃r ⇑s) := by
  rw [isoSetoid_apply, ← Setoid.nonempty_equiv_fromRel_iff, toStructure_toRelationalConfiguration,
    toStructure_toRelationalConfiguration]

/-- On a countable carrier, the graphs of two equivalence relations with infinite classes are
isomorphic exactly when the relations have equally many classes, counted in `ℕ∞`. -/
theorem isoSetoid_fromRel_iff_enatCard_eq {V : Type*} [Countable V] {r s : Setoid V}
    (hr : ∀ x : V, {x' | r x x'}.Infinite) (hs : ∀ x : V, {x' | s x x'}.Infinite) :
    isoSetoid Language.graph V (fromRel r).toRelationalConfiguration
        (fromRel s).toRelationalConfiguration ↔
      ENat.card (Quotient r) = ENat.card (Quotient s) := by
  rw [isoSetoid_toRelationalConfiguration_fromRel_iff]
  exact ⟨fun ⟨e⟩ => ENat.card_congr (Quotient.congr e.toEquiv fun _ _ => e.map_rel_iff.symm),
    Setoid.nonempty_relIso_of_infinite hr hs⟩

/-! ### An explicit perfect set of models on `ℕ` -/

/-- A bijection of the disjoint union of the blocks `Fin (k + 2)` with `ℕ`. -/
private noncomputable def blockEquiv : (Σ k : ℕ, Fin (k + 2)) ≃ ℕ :=
  nonempty_equiv_of_countable.some

/-- The index of the block of `ℕ` containing `n`. -/
private noncomputable def block (n : ℕ) : ℕ :=
  (blockEquiv.symm n).1

/-- The block `k` has `k + 2` elements. -/
private theorem encard_block_preimage (k : ℕ) : (block ⁻¹' {k}).encard = k + 2 := by
  have h : block ⁻¹' {k} = blockEquiv '' range (Sigma.mk k) := by
    ext n
    simp [block, blockEquiv.image_eq_preimage_symm, range_sigmaMk]
  rw [h, blockEquiv.injective.encard_image, ← image_univ, sigma_mk_injective.encard_image]
  simp

/-- The equivalence relation on `ℕ` in which the block `k` is a single class when `z k = true`
and splits into singletons otherwise. -/
private noncomputable def blockSetoid (z : ℕ → Bool) : Setoid ℕ :=
  Setoid.ker fun n => if z (block n) then Sum.inl (block n) else Sum.inr n

private theorem blockSetoid_iff {z : ℕ → Bool} {m n : ℕ} :
    blockSetoid z m n ↔ m = n ∨ block m = block n ∧ z (block m) = true := by
  rw [blockSetoid, Setoid.ker_def]
  split_ifs with hm hn hn <;> grind

/-- Two distinct points are adjacent in the graph of `blockSetoid z` exactly when they lie in one
block whose bit is set. -/
private theorem fromRel_blockSetoid_adj {z : ℕ → Bool} {u v : ℕ} :
    (fromRel (blockSetoid z)).Adj u v ↔ u ≠ v ∧ block u = block v ∧ z (block u) = true := by
  simp only [fromRel_adj, blockSetoid_iff]
  grind

/-- The class of `n` is its block when the bit of the block is set, and `{n}` otherwise. -/
private theorem encard_setOf_blockSetoid (z : ℕ → Bool) (n : ℕ) :
    {m | blockSetoid z n m}.encard = if z (block n) then (block n : ℕ∞) + 2 else 1 := by
  split_ifs with hn
  · rw [← encard_block_preimage]
    congr 1
    ext m
    simp only [mem_ofPred_eq, blockSetoid_iff, mem_preimage, mem_singleton_iff]
    grind
  · rw [encard_eq_one]
    refine ⟨n, ?_⟩
    ext m
    simp only [mem_ofPred_eq, blockSetoid_iff, mem_singleton_iff]
    grind

/-- An isomorphism of the relations sends a set bit to a set bit: the block `k` is a class of
`k + 2` elements, and it is sent to a class of the same size. -/
private theorem eq_true_of_relIso {z z' : ℕ → Bool} (f : ⇑(blockSetoid z) ≃r ⇑(blockSetoid z'))
    {k : ℕ} (hk : z k = true) : z' k = true := by
  obtain ⟨n, hn⟩ : ∃ n, block n = k := ⟨blockEquiv ⟨k, 0⟩, by simp [block]⟩
  have hf : {m | blockSetoid z' (f n) m} = f '' {m | blockSetoid z n m} := by
    rw [← f.coe_fn_toEquiv, f.toEquiv.image_eq_preimage_symm]
    ext m
    simp only [mem_preimage, mem_ofPred_eq, ← f.map_rel_iff, RelIso.coe_fn_toEquiv]
    exact iff_of_eq (congrArg _ (f.apply_symm_apply m).symm)
  have h := congrArg encard hf
  rw [f.injective.encard_image] at h
  simp only [encard_setOf_blockSetoid, hn, hk, ↓reduceIte] at h
  split_ifs at h with h'
  · have : block (f n) = k := by
      norm_cast at h
      omega
    rwa [this] at h'
  · norm_cast at h
    omega

private theorem eq_of_relIso {z z' : ℕ → Bool} (f : ⇑(blockSetoid z) ≃r ⇑(blockSetoid z')) :
    z = z' :=
  funext fun _ => Bool.eq_iff_iff.2 ⟨eq_true_of_relIso f, eq_true_of_relIso f.symm⟩

/-- **An explicit Cantor family of equivalence relations.** Split `ℕ` into blocks, the block `k`
with `k + 2` elements. For `z : ℕ → Bool`, this is the configuration on `ℕ` of the graph of the
equivalence relation whose classes are the blocks `k` with `z k = true` and the singletons of the
other points. -/
noncomputable def equivalenceRelationCantorFamily (z : ℕ → Bool) :
    RelationalConfiguration Language.graph ℕ :=
  (fromRel (blockSetoid z)).toRelationalConfiguration

/-- Every member of the family is a model of `equivalenceRelationSentence`. -/
theorem equivalenceRelationCantorFamily_mem_modelsOf (z : ℕ → Bool) :
    equivalenceRelationCantorFamily z ∈ modelsOf equivalenceRelationSentence :=
  mem_modelsOf_equivalenceRelationSentence_iff.2 ⟨_, rfl⟩

/-- Each atom of the family depends on at most one bit, so the family is continuous. -/
theorem continuous_equivalenceRelationCantorFamily :
    Continuous equivalenceRelationCantorFamily := by
  refine continuous_iff.2 fun a => ?_
  induction a using Atom.induction_adjAtom with
  | h u v =>
    simp only [equivalenceRelationCantorFamily, eval_toRelationalConfiguration_adjAtom,
      fromRel_blockSetoid_adj, ← and_assoc]
    by_cases h : u ≠ v ∧ block u = block v
    · -- The atom reads the bit of the common block of `u` and `v`.
      simpa only [eq_true h, true_and, Bool.decide_eq_true] using
        continuous_apply (A := fun _ : ℕ => Bool) (block u)
    · simpa only [eq_false h, false_and, decide_false] using continuous_const (y := false)

/-- Two members of the family are isomorphic only when their parameters are equal. -/
@[simp]
theorem isoSetoid_equivalenceRelationCantorFamily_iff {z z' : ℕ → Bool} :
    isoSetoid Language.graph ℕ (equivalenceRelationCantorFamily z)
      (equivalenceRelationCantorFamily z') ↔ z = z' :=
  isoSetoid_toRelationalConfiguration_fromRel_iff.trans
    ⟨fun ⟨f⟩ => eq_of_relIso f, fun h => h ▸ ⟨RelIso.refl _⟩⟩

/-- The models on `ℕ` of `equivalenceRelationSentence` carry a Cantor antichain for isomorphism:
the family `equivalenceRelationCantorFamily`. -/
theorem hasCantorAntichainOn_modelsOf_equivalenceRelationSentence :
    (isoSetoid Language.graph ℕ).HasCantorAntichainOn (modelsOf equivalenceRelationSentence) :=
  Setoid.hasCantorAntichainOn_iff.2 ⟨_, continuous_equivalenceRelationCantorFamily,
    equivalenceRelationCantorFamily_mem_modelsOf,
    fun _ _ hne h => hne (isoSetoid_equivalenceRelationCantorFamily_iff.1 h)⟩

/-- `equivalenceRelationSentence` has a perfect set of pairwise non-isomorphic models on `ℕ`. -/
theorem hasPerfectlyManyCountableModels_equivalenceRelationSentence :
    HasPerfectlyManyCountableModels equivalenceRelationSentence :=
  .of_nat hasCantorAntichainOn_modelsOf_equivalenceRelationSentence.hasPerfectAntichainOn

/-- There are exactly continuum many countable equivalence relations up to isomorphism. -/
theorem countableModelCount_equivalenceRelationSentence :
    countableModelCount equivalenceRelationSentence = 𝔠 :=
  hasPerfectlyManyCountableModels_equivalenceRelationSentence.countableModelCount_eq

end TauCeti
