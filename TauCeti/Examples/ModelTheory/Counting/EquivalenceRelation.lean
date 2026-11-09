/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.BoundedRank
public import TauCeti.ModelTheory.Counting.EquivalenceRelation
public import TauCeti.ModelTheory.Scott.EquivalenceRelation
import TauCeti.Data.Set.Infinite
import TauCeti.Data.Setoid.Nat

/-!
# Countably many equivalence relations with infinite classes

In the language of graphs, an equivalence relation `r` is presented by the graph
`SimpleGraph.fromRel r`, in which two vertices are adjacent when they are distinct and
`r`-related. The sentence `TauCeti.EquivalenceRelationCounting.infiniteClassesSentence` of
`L_{ω₁ω}` says that adjacency is such a graph and that every vertex has at least `n` neighbours,
for every `n`: its models are the equivalence relations all of whose classes are infinite
(`TauCeti.EquivalenceRelationCounting.realize_infiniteClassesSentence_iff`).

Every model has internal Scott rank one, whatever its cardinality: a finite partial isomorphism
extends by back-and-forth, since a new element is matched by a fresh element of the matching
class, or of a class not yet met. So the internal Scott ranks of the models are bounded below
`ω₁`, and the bounded-rank dichotomy
(`TauCeti.countableModelCount_le_aleph0_or_hasPerfectlyMany_of_internalScottRank_le`) applies.
Its first alternative holds: up to isomorphism, the countable models are the empty structure and,
for each `k ∈ {1, 2, …, ℵ₀}`, the relation on `ℕ` with `k` infinite classes, since two countable
equivalence relations with infinite classes and equally many classes are isomorphic
(`TauCeti.isoSetoid_fromRel_iff_enatCard_eq`). So the sentence has exactly `ℵ₀` countable models
(`TauCeti.EquivalenceRelationCounting.countableModelCount_infiniteClassesSentence`).

## Main results

All in the namespace `TauCeti.EquivalenceRelationCounting`:

* `realize_infiniteClassesSentence_iff`: the models are the graphs of equivalence relations with
  infinite classes.
* `internalScottRank_eq_one_of_realize`: every model has internal Scott rank one.
* `mk_quotient_isoSetoidOn_nat_infiniteClassesSentence`: `ℵ₀` models on `ℕ` up to isomorphism.
* `countableModelCount_infiniteClassesSentence`: exactly `ℵ₀` countable models, so no perfect set
  of pairwise non-isomorphic countable models
  (`not_hasPerfectlyManyCountableModels_infiniteClassesSentence`).

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, the chapter
  on Scott rank.
-/

public section

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Cardinal Set SimpleGraph

namespace TauCeti.EquivalenceRelationCounting

open RelationalConfiguration

/-! ### The sentence -/

/-- The first-order sentence saying that every vertex has at least `n` neighbours: for every `x`
there are pairwise distinct `y₀, …, yₙ₋₁`, each adjacent to `x`. -/
private noncomputable def neighborCardGe (n : ℕ) : Language.graph.Sentence :=
  Formula.iAlls (Fin 1) <| Formula.iExs (Fin n) <|
    (Formula.iInf fun p : {p : Fin n × Fin n // p.1 ≠ p.2} =>
        ∼(Term.equal (Term.var (.inr p.1.1)) (Term.var (.inr p.1.2)))) ⊓
      Formula.iInf fun i : Fin n =>
        adj.formula₂ (Term.var (.inl (.inr 0))) (Term.var (.inr i))

private theorem realize_neighborCardGe_iff {M : Type*} [Language.graph.Structure M] (n : ℕ) :
    M ⊨ neighborCardGe n ↔
      ∀ x : M, ∃ y : Fin n → M, Function.Injective y ∧ ∀ i, RelMap adj ![x, y i] := by
  simp only [neighborCardGe, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_inf, Formula.realize_iInf, Formula.realize_not, Formula.realize_equal,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨y, hy, hadj⟩ := h fun _ => x
    exact ⟨y, fun i j hij => by_contra fun hne => hy ⟨(i, j), hne⟩ hij, hadj⟩
  · obtain ⟨y, hy, hadj⟩ := h (x 0)
    exact ⟨y, fun p hp => p.2 (hy hp), hadj⟩

/-- The sentence of `L_{ω₁ω}` in the language of graphs saying that adjacency is the graph of an
equivalence relation all of whose classes are infinite. -/
noncomputable def infiniteClassesSentence : Language.graph.Sentenceω :=
  equivalenceRelationSentence ⊓ .iInf fun n => (neighborCardGe n).toInf

/-- The graph of an equivalence relation satisfies `infiniteClassesSentence` exactly when all
classes of the relation are infinite. -/
@[simp]
theorem realize_infiniteClassesSentence_fromRel {V : Type*} (r : Setoid V) :
    letI := (fromRel r).structure
    SentenceInf.Realize infiniteClassesSentence V ↔ ∀ x : V, {x' | r x x'}.Infinite := by
  let := (fromRel r).structure
  simp only [infiniteClassesSentence, SentenceInf.realize_inf, SentenceInf.realize_iInf,
    Sentence.realize_toInf, realize_neighborCardGe_iff, realize_equivalenceRelationSentence_fromRel,
    true_and, relMap_adj, fromRel_adj]
  rw [forall_comm]
  refine forall_congr' fun x => ?_
  have hinf := forall_exists_injective_iff_infinite {y | x ≠ y ∧ (r x y ∨ r y x)}
  simp only [mem_ofPred_eq] at hinf
  rw [hinf]
  -- The neighbours of `x` are its class with `x` removed.
  have hcl : {y | x ≠ y ∧ (r x y ∨ r y x)} = {x' | r x x'} \ {x} := by
    ext y
    simp only [mem_ofPred_eq, mem_sdiff, mem_singleton_iff, or_iff_left_of_imp r.symm', ne_comm]
    exact and_comm
  rw [hcl]
  exact ⟨fun h => h.mono sdiff_subset, fun h => h.sdiff (finite_singleton x)⟩

/-- The models of `infiniteClassesSentence`, in any universe, are the graphs of equivalence
relations all of whose classes are infinite. -/
theorem realize_infiniteClassesSentence_iff {M : Type*} [S : Language.graph.Structure M] :
    SentenceInf.Realize infiniteClassesSentence M ↔
      ∃ r : Setoid M, S = (fromRel r).structure ∧ ∀ x : M, {x' | r x x'}.Infinite := by
  refine ⟨fun h => ?_, ?_⟩
  · have hequiv : SentenceInf.Realize equivalenceRelationSentence M :=
      (SentenceInf.realize_inf.1 h).1
    obtain ⟨r, rfl⟩ := realize_equivalenceRelationSentence_iff.1 hequiv
    exact ⟨r, rfl, (realize_infiniteClassesSentence_fromRel r).1 h⟩
  · rintro ⟨r, rfl, hr⟩
    exact (realize_infiniteClassesSentence_fromRel r).2 hr

/-- The models of `infiniteClassesSentence` on `V` are the configurations of the graphs of the
equivalence relations on `V` with infinite classes. -/
theorem mem_modelsOf_infiniteClassesSentence_iff {V : Type*}
    {c : RelationalConfiguration Language.graph V} :
    c ∈ modelsOf infiniteClassesSentence ↔ ∃ r : Setoid V,
      c = (fromRel r).toRelationalConfiguration ∧ ∀ x : V, {x' | r x x'}.Infinite := by
  rw [mem_modelsOf, @realize_infiniteClassesSentence_iff _ c.toStructure]
  -- A configuration is determined by its decoded structure.
  refine exists_congr fun r => and_congr_left' ?_
  rw [← equivStructure.injective.eq_iff, equivStructure_apply, equivStructure_apply,
    toStructure_toRelationalConfiguration]

/-! ### Scott rank -/

/-- Every model of `infiniteClassesSentence`, of any cardinality, has internal Scott rank one. -/
theorem internalScottRank_eq_one_of_realize {M : Type*} [Language.graph.Structure M]
    (hM : SentenceInf.Realize infiniteClassesSentence M) :
    internalScottRank (L := Language.graph) M = 1 := by
  obtain ⟨r, rfl, hr⟩ := realize_infiniteClassesSentence_iff.1 hM
  exact Setoid.internalScottRank_fromRel_eq_one hr

/-- The internal Scott ranks of the models of `infiniteClassesSentence` are bounded by `1 < ω₁`,
so the bounded-rank dichotomy applies to it. -/
example : countableModelCount infiniteClassesSentence ≤ ℵ₀ ∨
    HasPerfectlyManyCountableModels infiniteClassesSentence :=
  countableModelCount_le_aleph0_or_hasPerfectlyMany_of_internalScottRank_le
    (Ordinal.one_lt_omega0.trans Ordinal.omega0_lt_omega_one)
    fun _ _ _ _ hM => (internalScottRank_eq_one_of_realize hM).le

/-! ### Counting the models -/

/-- The models of `infiniteClassesSentence` on `ℕ` have countably many isomorphism classes: the
class of a model is determined by its number of classes in `ℕ∞`. -/
theorem countable_quotient_isoSetoidOn_nat_infiniteClassesSentence :
    Countable (Quotient (isoSetoidOn ℕ infiniteClassesSentence)) := by
  choose r hr hinf using fun c : modelsOf (V := ℕ) infiniteClassesSentence =>
    mem_modelsOf_infiniteClassesSentence_iff.1 c.2
  refine Function.Injective.countable
    (f := fun q : Quotient (isoSetoidOn ℕ infiniteClassesSentence) =>
      ENat.card (Quotient (r q.out)))
    fun q q' h => ?_
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  refine Quotient.sound (isoSetoidOn_apply.2 ?_)
  rw [hr q.out, hr q'.out]
  exact (isoSetoid_fromRel_iff_enatCard_eq (hinf _) (hinf _)).2 h

private theorem fromRel_ker_ofNat_mem_modelsOf (k : ℕ) :
    (fromRel (Setoid.ker (Fin.ofNat (k + 1)))).toRelationalConfiguration ∈
      modelsOf infiniteClassesSentence :=
  mem_modelsOf_infiniteClassesSentence_iff.2 ⟨_, rfl, Setoid.infinite_setOf_ker_finOfNat k⟩

/-- The models of `infiniteClassesSentence` on `ℕ` have infinitely many isomorphism classes: for
each `k`, the relation with `k + 1` infinite classes gives one. -/
theorem infinite_quotient_isoSetoidOn_nat_infiniteClassesSentence :
    Infinite (Quotient (isoSetoidOn ℕ infiniteClassesSentence)) := by
  refine Infinite.of_injective (fun k : ℕ => (⟦⟨_, fromRel_ker_ofNat_mem_modelsOf k⟩⟧ :
    Quotient (isoSetoidOn ℕ infiniteClassesSentence))) fun k k' h => ?_
  have hiso := (isoSetoid_fromRel_iff_enatCard_eq (Setoid.infinite_setOf_ker_finOfNat k)
    (Setoid.infinite_setOf_ker_finOfNat k')).1 (isoSetoidOn_apply.1 (Quotient.exact h))
  rw [Setoid.enatCard_quotient_ker_finOfNat, Setoid.enatCard_quotient_ker_finOfNat] at hiso
  have : k + 1 = k' + 1 := by exact_mod_cast hiso
  omega

/-- The sentence has exactly `ℵ₀` models on `ℕ` up to isomorphism. -/
theorem mk_quotient_isoSetoidOn_nat_infiniteClassesSentence :
    #(Quotient (isoSetoidOn ℕ infiniteClassesSentence)) = ℵ₀ :=
  have := countable_quotient_isoSetoidOn_nat_infiniteClassesSentence
  have := infinite_quotient_isoSetoidOn_nat_infiniteClassesSentence
  mk_eq_aleph0 _

/-- On a finite carrier, any two models of `infiniteClassesSentence` are isomorphic: the carrier
of a model must be empty. -/
theorem subsingleton_quotient_isoSetoidOn_infiniteClassesSentence {V : Type*} [Finite V] :
    Subsingleton (Quotient (isoSetoidOn V infiniteClassesSentence)) := by
  refine ⟨fun q q' => Quotient.inductionOn₂ q q' fun c d => Quotient.sound ?_⟩
  obtain ⟨r, hc, hr⟩ := mem_modelsOf_infiniteClassesSentence_iff.1 c.2
  obtain ⟨s, hd, -⟩ := mem_modelsOf_infiniteClassesSentence_iff.1 d.2
  have : IsEmpty V := ⟨fun x => hr x (Set.toFinite _)⟩
  refine isoSetoidOn_apply.2 ?_
  rw [hc, hd, isoSetoid_toRelationalConfiguration_fromRel_iff]
  exact ⟨⟨Equiv.refl V, fun {a} => isEmptyElim a⟩⟩

/-- **The countable models of `infiniteClassesSentence`.** Up to isomorphism there are exactly
`ℵ₀`: the empty structure and, for each `k ∈ {1, 2, …, ℵ₀}`, the relation on `ℕ` with `k` infinite
classes. -/
theorem countableModelCount_infiniteClassesSentence :
    countableModelCount infiniteClassesSentence = ℵ₀ := by
  refine le_antisymm (countableModelCount_le_aleph0_iff.2
    ⟨countable_quotient_isoSetoidOn_nat_infiniteClassesSentence, fun n =>
      have := subsingleton_quotient_isoSetoidOn_infiniteClassesSentence (V := Fin n)
      inferInstance⟩) ?_
  rw [← mk_quotient_isoSetoidOn_nat_infiniteClassesSentence]
  exact mk_quotient_isoSetoidOn_nat_le_countableModelCount _

/-- The sentence has no perfect set of pairwise non-isomorphic countable models: the first
alternative of the bounded-rank dichotomy holds. -/
theorem not_hasPerfectlyManyCountableModels_infiniteClassesSentence :
    ¬ HasPerfectlyManyCountableModels infiniteClassesSentence := fun h =>
  aleph0_lt_continuum.ne <|
    countableModelCount_infiniteClassesSentence.symm.trans h.countableModelCount_eq

end TauCeti.EquivalenceRelationCounting
