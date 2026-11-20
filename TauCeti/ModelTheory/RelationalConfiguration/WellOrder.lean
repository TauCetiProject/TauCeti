/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.Tree.Descending
public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# The coded well-order class

For a relational language `L` with a distinguished binary relation symbol `lt`, a code
`c : RelationalConfiguration L ℕ` assigns to `lt` a relation `codeRel lt c` on `ℕ`, and the
**coded well-orders** `wellOrderClass lt` are the codes for which it is a strict well-order. The
class is closed under isomorphism, and every countably infinite ordinal is the order type of one
of its codes.

For every relational language, an analytic class of coded well-orders has order types bounded
below `ω₁`: the descending tree of a code is well-founded exactly when the coded relation is, its
node sets are clopen in the code, and its rank bounds the order type, so the analytic boundedness
theorem for families of well-founded trees applies. Since every countable ordinal occurs, the
coded well-orders are not analytic.

With countably many relation symbols the coding space is Polish, and the coded well-orders are
coanalytic, not Borel, and the coded models of no `L_{ω₁ω}` sentence: model classes are Borel.

## Main definitions

* `TauCeti.RelationalConfiguration.codeRel`: the relation a code assigns to `lt`.
* `TauCeti.RelationalConfiguration.wellOrderClass`: the coded well-orders.

## Main results

* `TauCeti.RelationalConfiguration.isomorphismInvariant_wellOrderClass` and
  `TauCeti.RelationalConfiguration.exists_mem_wellOrderClass_type_eq`: invariance, and every
  countably infinite ordinal is a coded order type.
* `TauCeti.RelationalConfiguration.analytic_type_bounded`: analytic classes of coded well-orders
  have order types bounded below `ω₁`, for every relational language.
* `TauCeti.RelationalConfiguration.not_analyticSet_wellOrderClass`: the coded well-orders are not
  analytic, for every relational language.
* `TauCeti.RelationalConfiguration.analyticSet_compl_wellOrderClass`,
  `TauCeti.RelationalConfiguration.not_measurableSet_wellOrderClass` and
  `TauCeti.RelationalConfiguration.not_exists_modelsOf_eq_wellOrderClass`: with countably many
  relation symbols, the class is coanalytic, not Borel, and not a model class.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 9:
  Theorem 9.27(vi) (well-orders form a coanalytic set) and Corollary 9.42(ii) (boundedness), in
  their boldface forms.
-/

public section

open FirstOrder FirstOrder.Language Descriptive Tree MeasureTheory

namespace TauCeti.RelationalConfiguration


variable {L : Language} [L.IsRelational] (lt : L.Relations 2)

/-- The relation a code assigns to the binary relation symbol `lt`. -/
def codeRel (c : RelationalConfiguration L ℕ) (x y : ℕ) : Prop :=
  @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y]

/-- The coded relation holds at a pair exactly when the corresponding atom is true. -/
theorem codeRel_iff {c : RelationalConfiguration L ℕ} {x y : ℕ} :
    codeRel lt c x y ↔ c.eval (atom lt ![x, y]) = true :=
  toStructure_relMap c lt ![x, y]

/-- The **coded well-orders**: the codes on `ℕ` whose relation for `lt` is a strict
well-order. The definition is exposed so that membership can serve as the well-order instance
in statements about order types. -/
@[expose] def wellOrderClass : Set (RelationalConfiguration L ℕ) :=
  {c | IsWellOrder ℕ (codeRel lt c)}

/-- Membership in the coded well-orders. -/
theorem mem_wellOrderClass {c : RelationalConfiguration L ℕ} :
    c ∈ wellOrderClass lt ↔ IsWellOrder ℕ (codeRel lt c) := Iff.rfl

/-- The coded well-orders are closed under isomorphism of decoded structures. -/
theorem isomorphismInvariant_wellOrderClass : IsomorphismInvariant (wellOrderClass lt) := by
  refine isomorphismInvariant_iff.2 fun c d h hc => ?_
  obtain ⟨e⟩ := isoSetoid_apply.1 h
  let g : ℕ ≃ ℕ := @Language.Equiv.toEquiv L ℕ ℕ c.toStructure d.toStructure e
  -- the isomorphism of decoded structures is an isomorphism of the coded relations
  let f : codeRel lt c ≃r codeRel lt d := ⟨g, fun {x y} => by
    have := @Language.Equiv.map_rel L ℕ ℕ c.toStructure d.toStructure e 2 lt ![x, y]
    simp only [codeRel]
    convert this using 2
    funext i; fin_cases i <;> rfl⟩
  have : IsWellOrder ℕ (codeRel lt c) := hc
  exact f.symm.toRelEmbedding.isWellOrder

/-- Membership of a node in the descending tree is clopen in the code. -/
theorem isClopen_setOf_mem_descendingTree_codeRel (l : List ℕ) :
    IsClopen {c : RelationalConfiguration L ℕ | l ∈ descendingTree (codeRel lt c)} := by
  induction l with
  | nil => simpa using isClopen_univ
  | cons x l ih =>
    cases l with
    | nil => simpa using isClopen_univ
    | cons y l =>
      have h : {c : RelationalConfiguration L ℕ | (x :: y :: l) ∈ descendingTree (codeRel lt c)} =
          {c | c.eval (atom lt ![y, x]) = true} ∩
            {c | (y :: l) ∈ descendingTree (codeRel lt c)} := by
        ext c; simp [mem_descendingTree, List.isChain_cons_cons, codeRel_iff]
      rw [h]
      exact (isClopen_setOf_eval _ true).inter ih

/-- **Analytic classes of coded well-orders have bounded order types**, for every relational
language: the descending trees of their codes have clopen node sets, so their ranks, which bound
the order types, are bounded below `ω₁`. -/
theorem analytic_type_bounded {A : Set (RelationalConfiguration L ℕ)} (hA : AnalyticSet A)
    (hAW : A ⊆ wellOrderClass lt) :
    ∃ β < (Ordinal.omega 1 : Ordinal.{0}), ∀ c (hc : c ∈ A),
      @Ordinal.type ℕ (codeRel lt c) (hAW hc) < β := by
  obtain ⟨β, hβ, hb⟩ := hA.exists_treeRank_lt_omega_one_of_isClosed
    (fun c => descendingTree (codeRel lt c))
    (fun c hc => isWellFounded_descendingTree_iff.2 (hAW hc).wf)
    (fun u => (isClopen_setOf_mem_descendingTree_codeRel lt u).isClosed)
  exact ⟨β, hβ, fun c hc => (@type_le_rank_descendingTree _ _ (hAW hc)).trans_lt (hb c hc)⟩

/-- **Every countably infinite ordinal is the order type of a coded well-order.** -/
theorem exists_mem_wellOrderClass_type_eq {β : Ordinal.{0}} (hω : Ordinal.omega0 ≤ β)
    (hβ : β < Ordinal.omega 1) :
    ∃ c : RelationalConfiguration L ℕ, ∃ h : IsWellOrder ℕ (codeRel lt c),
      @Ordinal.type ℕ (codeRel lt c) h = β := by
  classical
  have : Countable β.ToType := Cardinal.countable_toType_of_lt_omega_one hβ
  have : Infinite β.ToType := by
    rw [Cardinal.infinite_iff, Cardinal.mk_toType]
    simpa using Ordinal.card_le_card hω
  have : Denumerable β.ToType := (nonempty_denumerable _).some
  let e : β.ToType ≃ ℕ := Denumerable.eqv _
  -- the structure in which `lt` is the order of `β` transported to `ℕ`, and nothing else holds
  -- `lt` holds of `xs` when the arity is `2` and its two entries are ordered as in `β`; no other
  -- relation symbol holds anywhere
  let S : L.Structure ℕ := ⟨fun f => isEmptyElim f, fun {n} R xs => ∃ h : n = 2,
    h ▸ R = lt ∧ e.symm (xs (Fin.cast h.symm 0)) < e.symm (xs (Fin.cast h.symm 1))⟩
  let c := @ofStructure L ℕ S
  have hc (x y : ℕ) : codeRel lt c x y ↔ e.symm x < e.symm y := by
    rw [codeRel_iff, @eval_ofStructure L ℕ S, decide_eq_true_eq]
    exact ⟨fun ⟨_, _, hlt⟩ => hlt, fun h => ⟨rfl, rfl, h⟩⟩
  let f : codeRel lt c ≃r (· < · : β.ToType → β.ToType → Prop) :=
    ⟨e.symm, fun {x y} => (hc x y).symm⟩
  have hwo : IsWellOrder ℕ (codeRel lt c) := f.toRelEmbedding.isWellOrder
  exact ⟨c, hwo, (Ordinal.type_eq.2 ⟨f⟩).trans (Ordinal.type_toType β)⟩

/-- **The coded well-orders are not analytic**, for every relational language. -/
theorem not_analyticSet_wellOrderClass : ¬ AnalyticSet (wellOrderClass lt) := by
  intro hA
  obtain ⟨β, hβ, hb⟩ := analytic_type_bounded lt hA subset_rfl
  have hγ : max β Ordinal.omega0 < Ordinal.omega 1 :=
    max_lt hβ Ordinal.omega0_lt_omega_one
  obtain ⟨c, hwo, htype⟩ := exists_mem_wellOrderClass_type_eq lt (le_max_right _ _) hγ
  have := hb c hwo
  rw [htype] at this
  exact (lt_irrefl _ (this.trans_le (le_max_left _ _)))

/-- **The coded well-orders are not Borel**, with countably many relation symbols. -/
theorem not_measurableSet_wellOrderClass [∀ n, Countable (L.Relations n)] :
    ¬ MeasurableSet (wellOrderClass lt) :=
  fun h => not_analyticSet_wellOrderClass lt h.analyticSet

/-- **No `L_{ω₁ω}` sentence defines the coded well-orders**, with countably many relation
symbols. -/
theorem not_exists_modelsOf_eq_wellOrderClass [∀ n, Countable (L.Relations n)] :
    ¬ ∃ φ : L.Sentenceω, modelsOf φ = wellOrderClass lt := fun ⟨φ, h⟩ =>
  not_measurableSet_wellOrderClass lt (h ▸ measurableSet_modelsOf φ)

omit [L.IsRelational] in
/-- The truth value of `lt` at a pair is continuous jointly in the code and the pair. -/
private theorem continuous_eval_atom_pair :
    Continuous fun q : RelationalConfiguration L ℕ × (ℕ × ℕ) =>
      q.1.eval (atom lt ![q.2.1, q.2.2]) :=
  continuous_prod_of_discrete_right.2 fun p => continuous_eval (atom lt ![p.1, p.2])

omit [L.IsRelational] in
/-- A relation is a strict well-order exactly when it is trichotomous and well-founded. -/
private theorem isWellOrder_iff {r : ℕ → ℕ → Prop} : IsWellOrder ℕ r ↔
    (∀ a b, ¬ r a b → ¬ r b a → a = b) ∧ WellFounded r :=
  ⟨fun h => ⟨h.trichotomous, h.wf⟩, fun ⟨ht, hw⟩ => { trichotomous := ht, wf := hw }⟩

/-- **The coded well-orders are coanalytic**, with countably many relation symbols. -/
theorem analyticSet_compl_wellOrderClass [∀ n, Countable (L.Relations n)] :
    AnalyticSet (wellOrderClass lt)ᶜ := by
  -- the codes of trichotomous relations, a closed set
  let C : Set (RelationalConfiguration L ℕ) :=
    {c | ∀ a b, ¬ codeRel lt c a b → ¬ codeRel lt c b a → a = b}
  -- the codes with an infinite descending sequence, paired with it, a closed set
  let D : Set (RelationalConfiguration L ℕ × (ℕ → ℕ)) :=
    {p | ∀ n, codeRel lt p.1 (p.2 (n + 1)) (p.2 n)}
  have hcl (a b : ℕ) : IsClopen {c : RelationalConfiguration L ℕ | codeRel lt c a b} := by
    simpa [codeRel_iff] using isClopen_setOf_eval (atom lt ![a, b]) true
  have hC : IsClosed C := by
    have h : C = ⋂ a, ⋂ b, ({c | codeRel lt c a b} ∪ ({c | codeRel lt c b a} ∪
        {_c | a = b})) := by
      ext c
      simp only [C, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union]
      exact forall₂_congr fun a b => by tauto
    rw [h]
    refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
    refine (hcl a b).isClosed.union ((hcl b a).isClosed.union ?_)
    by_cases hab : a = b <;> simp [hab]
  have hD : IsClosed D := by
    have : D = ⋂ n, (fun p : RelationalConfiguration L ℕ × (ℕ → ℕ) =>
        p.1.eval (atom lt ![p.2 (n + 1), p.2 n])) ⁻¹' {true} := by
      ext p; simp [D, codeRel_iff]
    rw [this]
    refine isClosed_iInter fun n => (isClosed_discrete {true}).preimage ?_
    exact (continuous_eval_atom_pair lt).comp (by fun_prop :
      Continuous fun p : RelationalConfiguration L ℕ × (ℕ → ℕ) => (p.1, (p.2 (n + 1), p.2 n)))
  have heq : (wellOrderClass lt)ᶜ = Cᶜ ∪ Prod.fst '' D := by
    ext c
    simp only [Set.mem_compl_iff, mem_wellOrderClass, isWellOrder_iff,
      wellFounded_iff_isEmpty_descending_chain, Set.mem_union, Set.mem_image, Prod.exists, D, C,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      rcases not_and_or.1 h with h1 | h2
      · exact Or.inl h1
      · obtain ⟨f, hf⟩ := not_isEmpty_iff.1 h2
        exact Or.inr ⟨c, f, hf, rfl⟩
    · rintro (h1 | ⟨_, f, hf, rfl⟩) h
      · exact h1 h.1
      · exact h.2.false ⟨f, hf⟩
  rw [heq, Set.union_eq_iUnion]
  refine AnalyticSet.iUnion fun b => ?_
  cases b
  · exact (hD.analyticSet).image_of_continuous continuous_fst
  · exact hC.isOpen_compl.measurableSet.analyticSet

end TauCeti.RelationalConfiguration
