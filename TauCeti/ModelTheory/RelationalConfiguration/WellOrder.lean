/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
public import TauCeti.SetTheory.Descriptive.Tree.Descending

/-!
# The coded well-orders

Fix a binary relation symbol `lt` of a language `L`. Every relational configuration `c` on a
carrier `V` assigns to `lt` a binary relation `codeRel lt c` on `V`, and `wellOrderClass lt` is the
set of configurations for which this relation is a strict well-order of `V`. The class only
constrains the atoms of `lt`.

On a countable carrier the class is coanalytic: a strict well-order is a trichotomous relation
without infinite descending sequences, the trichotomous relations form a closed set, and the
relations with a descending sequence are a projection of a closed subset of the product with `ℕ → V`
(`analyticSet_compl_wellOrderClass`, for countably many relation symbols). On a countably infinite
carrier it is not analytic. The tree of finite descending sequences of `codeRel lt c` has clopen
node sets in `c`, it is well-founded exactly when `codeRel lt c` is, and for a well-order its rank
bounds the order type (`Descriptive.Tree.type_le_rank_descendingTree`). By the boundedness theorem
for analytic families of well-founded trees, the order types of an analytic set of coded well-orders
are bounded below `ω₁` (`exists_type_lt_omega_one_of_analyticSet`), whereas on a countably infinite
carrier every countable infinite order type occurs (`exists_mem_wellOrderClass_type_eq`). Hence the
class is not analytic (`not_analyticSet_wellOrderClass`), not measurable for the product σ-algebra
(`not_measurableSet_wellOrderClass`), and not the model class of any `L_{ω₁ω}` sentence
(`not_exists_modelsOf_eq_wellOrderClass`). The first two hold for every language and the third for
every relational language; none of them assumes the relation symbols are countable, and none needs
model existence.

## Main definitions

* `TauCeti.RelationalConfiguration.codeRel`: the relation a configuration assigns to `lt`.
* `TauCeti.RelationalConfiguration.wellOrderClass`: the configurations for which that relation is
  a strict well-order.

## Main results

* `TauCeti.RelationalConfiguration.isomorphismInvariant_setOf_codeRel`: a class defined by an
  isomorphism-invariant property of `codeRel lt c` is isomorphism invariant.
* `TauCeti.RelationalConfiguration.isomorphismInvariant_wellOrderClass`: the class is isomorphism
  invariant.
* `TauCeti.RelationalConfiguration.analyticSet_compl_wellOrderClass`: the class is coanalytic.
* `TauCeti.RelationalConfiguration.exists_mem_wellOrderClass_type_eq`: every order type `β` with
  `ω ≤ β < ω₁` is coded on a countably infinite carrier.
* `TauCeti.RelationalConfiguration.exists_type_lt_omega_one_of_analyticSet`: an analytic set of
  coded well-orders has order types bounded below `ω₁`.
* `TauCeti.RelationalConfiguration.not_analyticSet_wellOrderClass`,
  `TauCeti.RelationalConfiguration.not_measurableSet_wellOrderClass` and
  `TauCeti.RelationalConfiguration.not_exists_modelsOf_eq_wellOrderClass`: the class is not
  analytic, not measurable for the product σ-algebra (so not Borel when there are countably many
  relation symbols) and not the model class of a sentence.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, lecture notes, University of Illinois at
  Chicago, 2013: Theorem 9.27(vi) (the well-orders form a `Π¹₁` set) and Corollary 9.42(ii) (ranks
  of a `Σ¹₁` set of well-founded trees are bounded), whose relativisations are used here.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, Section 31 (the boundedness theorem for analytic sets of well-founded trees).
* Cameron Freer's `cameronfreer/infinitary-logic` (Apache-2.0) at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, in `InfinitaryLogic/Descriptive/WellOrderClass.lean`,
  `WellOrderNonBorel.lean` and `AnalyticWellOrderBoundedness.lean`, formalizes the same well-order
  class, its coanalyticity and the boundedness of the order types of analytic sets of codes. This
  file diverges from it: the source obtains non-Borelness from López–Escobar, fragment
  Löwenheim–Skolem and the model-theoretic boundedness of well-ordered models, whereas here
  non-analyticity, non-measurability and non-definability come from the descriptive boundedness
  theorem for well-founded trees, on any countably infinite carrier and for languages with any
  number of relation symbols.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language MeasureTheory Set Descriptive Descriptive.Tree
open scoped Ordinal

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {V : Type w}

/-! ### The relation of a binary symbol -/

/-- The binary relation that the configuration `c` assigns to the binary relation symbol `lt`:
`codeRel lt c x y` holds when the atom `lt(x, y)` is true in `c`. -/
def codeRel (lt : L.Relations 2) (c : RelationalConfiguration L V) (x y : V) : Prop :=
  c.eval (atom lt ![x, y]) = true

/-- Unfolding lemma for `codeRel`. -/
theorem codeRel_iff {lt : L.Relations 2} {c : RelationalConfiguration L V} {x y : V} :
    codeRel lt c x y ↔ c.eval (atom lt ![x, y]) = true :=
  Iff.rfl

/-- The code of a structure assigns to `lt` the interpretation of `lt` in that structure. -/
@[simp]
theorem codeRel_ofStructure [L.Structure V] (lt : L.Relations 2) (x y : V) :
    codeRel lt (ofStructure L V) x y ↔ Structure.RelMap lt ![x, y] := by
  classical
  rw [codeRel_iff, eval_ofStructure, decide_eq_true_iff]

/-- The decoded structure of a configuration interprets `lt` by `codeRel lt c`. -/
theorem relMap_toStructure_iff_codeRel [L.IsRelational] (lt : L.Relations 2)
    (c : RelationalConfiguration L V) (x y : V) :
    @Structure.RelMap L V c.toStructure 2 lt ![x, y] ↔ codeRel lt c x y :=
  toStructure_relMap c lt ![x, y]

/-- Relabelling a configuration by `σ` transports the relation of `lt` along `σ`. -/
@[simp]
theorem codeRel_perm_smul (lt : L.Relations 2) (σ : Equiv.Perm V)
    (c : RelationalConfiguration L V) (x y : V) :
    codeRel lt (σ • c) x y ↔ codeRel lt c (σ.symm x) (σ.symm y) := by
  have h : (σ.symm ∘ ![x, y] : Fin 2 → V) = ![σ.symm x, σ.symm y] := by
    ext i
    fin_cases i <;> rfl
  rw [codeRel_iff, codeRel_iff, eval_perm_smul, Atom.map_atom, h]

/-- Each instance `codeRel lt c x y` of the relation of a binary symbol is a measurable condition
on the configuration `c`. -/
theorem measurableSet_setOf_codeRel (lt : L.Relations 2) (x y : V) :
    MeasurableSet {c : RelationalConfiguration L V | codeRel lt c x y} := by
  simpa only [codeRel_iff] using measurableSet_setOf_eval (atom lt ![x, y]) true

/-! ### The class of coded well-orders -/

/-- The **coded well-orders**: the configurations `c` for which `codeRel lt c` is a strict
well-order of the carrier. -/
def wellOrderClass (lt : L.Relations 2) : Set (RelationalConfiguration L V) :=
  {c | IsWellOrder V (codeRel lt c)}

/-- Unfolding lemma for `wellOrderClass`. -/
@[simp]
theorem mem_wellOrderClass {lt : L.Relations 2} {c : RelationalConfiguration L V} :
    c ∈ wellOrderClass lt ↔ IsWellOrder V (codeRel lt c) :=
  Iff.rfl

/-- The configurations whose relation `codeRel lt c` has a property `P` invariant under relation
isomorphisms form an isomorphism-invariant class. -/
theorem isomorphismInvariant_setOf_codeRel [L.IsRelational] (lt : L.Relations 2)
    {P : (V → V → Prop) → Prop} (hP : ∀ {r s : V → V → Prop}, r ≃r s → P r → P s) :
    IsomorphismInvariant {c : RelationalConfiguration L V | P (codeRel lt c)} := by
  refine isomorphismInvariant_iff.2 fun c d hcd hc => ?_
  obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 hcd
  exact hP ⟨σ, by simp⟩ hc

/-- The coded well-orders form an isomorphism-invariant class. -/
theorem isomorphismInvariant_wellOrderClass [L.IsRelational] (lt : L.Relations 2) :
    IsomorphismInvariant (wellOrderClass (V := V) lt) :=
  isomorphismInvariant_setOf_codeRel lt fun e _ => e.symm.toRelEmbedding.isWellOrder

/-! ### Coanalyticity -/

/-- Each node of the tree of descending sequences of `codeRel lt c` is present for a clopen set of
configurations `c`. -/
theorem isClopen_setOf_mem_descendingTree_codeRel (lt : L.Relations 2) (u : List V) :
    IsClopen {c : RelationalConfiguration L V | u ∈ descendingTree (codeRel lt c)} := by
  induction u with
  | nil => simp [isClopen_univ]
  | cons a u ih =>
    cases u with
    | nil => simp [isClopen_univ]
    | cons b u =>
      simp only [mem_descendingTree, List.isChain_cons_cons, codeRel_iff, ofPred_and] at ih ⊢
      exact (isClopen_setOf_eval (atom lt ![b, a]) true).inter ih

/-- On a countable carrier, in a language with countably many relation symbols, the coded
well-orders form a coanalytic set: their complement is analytic. -/
theorem analyticSet_compl_wellOrderClass [∀ n, Countable (L.Relations n)] [Countable V]
    (lt : L.Relations 2) : AnalyticSet (wellOrderClass (V := V) lt)ᶜ := by
  -- Give the countable carrier its discrete topology, making `ℕ → V` Polish.
  let _ : TopologicalSpace V := ⊥
  have : DiscreteTopology V := ⟨rfl⟩
  have : PolishSpace V := inferInstance
  -- The codes of trichotomous relations form a closed set.
  let T : Set (RelationalConfiguration L V) :=
    {c | ∀ x y, ¬ codeRel lt c x y → ¬ codeRel lt c y x → x = y}
  have hT : IsClosed T := by
    simp only [T, ofPred_forall]
    refine isClosed_iInter fun x => isClosed_iInter fun y => ?_
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, codeRel_iff, imp_false, not_not, ← or_iff_not_imp_left, ofPred_or]
      exact (isClopen_setOf_eval (atom lt ![x, y]) true).isClosed.union
        (isClopen_setOf_eval (atom lt ![y, x]) true).isClosed
  -- The pairs of a sequence and a code along which the sequence descends form a closed set.
  let K : Set ((ℕ → V) × RelationalConfiguration L V) :=
    {p | ∀ n, codeRel lt p.2 (p.1 (n + 1)) (p.1 n)}
  have hK : IsClosed K := by
    simp only [K, codeRel_iff, ofPred_forall]
    refine isClosed_iInter fun n => isClosed_eq ?_ continuous_const
    have hG : Continuous fun q : (V × V) × RelationalConfiguration L V =>
        q.2.eval (atom lt ![q.1.1, q.1.2]) :=
      continuous_prod_of_discrete_left.2 fun q => continuous_eval (atom lt ![q.1, q.2])
    have hp : Continuous fun p : (ℕ → V) × RelationalConfiguration L V =>
        ((p.1 (n + 1), p.1 n), p.2) := by
      fun_prop
    exact hG.comp hp
  have heq : (wellOrderClass (V := V) lt)ᶜ = Tᶜ ∪ Prod.snd '' K := by
    ext c
    have hwo : IsWellOrder V (codeRel lt c) ↔
        (∀ x y, ¬ codeRel lt c x y → ¬ codeRel lt c y x → x = y) ∧
          ¬ ∃ f : ℕ → V, ∀ n, codeRel lt c (f (n + 1)) (f n) := by
      rw [← nonempty_subtype, not_nonempty_iff, ← wellFounded_iff_isEmpty_descending_chain]
      exact ⟨fun h => ⟨h.toTrichotomous.trichotomous, h.wf⟩,
        fun ⟨h₁, h₂⟩ => { trichotomous := h₁, wf := h₂ }⟩
    simp only [mem_compl_iff, mem_wellOrderClass, hwo, not_and_or, not_not, mem_union,
      mem_image, Prod.exists, exists_eq_right, T, K, mem_ofPred_eq]
  rw [heq]
  exact hT.isOpen_compl.measurableSet.analyticSet.union
    (hK.analyticSet.image_of_continuous continuous_snd)

/-! ### Order types of coded well-orders -/

/-- On a countably infinite carrier every order type `β` with `ω ≤ β < ω₁` is the order type of a
coded well-order. -/
theorem exists_mem_wellOrderClass_type_eq [Countable V] [Infinite V] (lt : L.Relations 2)
    {β : Ordinal.{w}} (hωβ : ω ≤ β) (hβ : β < ω₁) :
    ∃ c : RelationalConfiguration L V, ∃ hc : c ∈ wellOrderClass lt,
      @Ordinal.type V (codeRel lt c) (mem_wellOrderClass.1 hc) = β := by
  have : Countable β.ToType := Cardinal.countable_toType_of_lt_omega_one hβ
  have : Infinite β.ToType := Cardinal.infinite_iff.2 <| by
    simpa [Cardinal.mk_toType] using Ordinal.card_le_card hωβ
  obtain ⟨e⟩ : Nonempty (β.ToType ≃ V) :=
    Cardinal.eq.1 (by rw [Cardinal.mk_eq_aleph0, Cardinal.mk_eq_aleph0])
  -- Code the order of `β.ToType` transported to `V` along `e`.
  let r : V → V → Prop := fun x y => e.symm x < e.symm y
  let S := relStructure lt r (Classical.arbitrary V)
  let c := @ofStructure L V S
  let f : codeRel lt c ≃r ((· < ·) : β.ToType → β.ToType → Prop) :=
    ⟨e.symm, fun {x y} =>
      ((@codeRel_ofStructure L V S lt x y).trans (relMap_relStructure_self lt r _ x y)).symm⟩
  have : IsWellOrder V (codeRel lt c) := f.toRelEmbedding.isWellOrder
  exact ⟨c, mem_wellOrderClass.2 this, f.ordinalType_congr.trans (Ordinal.type_toType β)⟩

/-- **Boundedness for coded well-orders.** On a countable carrier, the order types of an analytic
set of coded well-orders are bounded by a countable ordinal. -/
theorem exists_type_lt_omega_one_of_analyticSet [Countable V] {lt : L.Relations 2}
    {A : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hAW : A ⊆ wellOrderClass lt) :
    ∃ β < ω₁, ∀ c (hc : c ∈ A),
      @Ordinal.type V (codeRel lt c) (mem_wellOrderClass.1 (hAW hc)) < β := by
  obtain ⟨β, hβ, hb⟩ := hA.exists_treeRank_lt_omega_one_of_isClosed
    (fun c => descendingTree (codeRel lt c))
    (fun c hc => isWellFounded_descendingTree_iff.2 (@IsWellOrder.wf _ _ (hAW hc)))
    (fun u => (isClopen_setOf_mem_descendingTree_codeRel lt u).isClosed)
  exact ⟨β, hβ, fun c hc =>
    (@type_le_rank_descendingTree V (codeRel lt c) (hAW hc)).trans_lt (hb c hc)⟩

/-! ### The coded well-orders are not analytic, not measurable and not definable -/

/-- On a countably infinite carrier the coded well-orders do not form an analytic set. -/
theorem not_analyticSet_wellOrderClass [Countable V] [Infinite V] (lt : L.Relations 2) :
    ¬ AnalyticSet (wellOrderClass (V := V) lt) := by
  intro h
  obtain ⟨β, hβ, hb⟩ := exists_type_lt_omega_one_of_analyticSet h subset_rfl
  obtain ⟨c, hc, hcβ⟩ := exists_mem_wellOrderClass_type_eq (V := V) lt (le_max_right β ω)
    (max_lt hβ Ordinal.omega0_lt_omega_one)
  exact (hb c hc).not_ge (hcβ ▸ le_max_left β ω)

/-- The countable case of `not_measurableSet_wellOrderClass`, where measurable sets are
analytic. -/
private theorem not_measurableSet_wellOrderClass_of_countable [∀ n, Countable (L.Relations n)]
    [Countable V] [Infinite V] (lt : L.Relations 2) :
    ¬ MeasurableSet (wellOrderClass (V := V) lt) :=
  fun h => not_analyticSet_wellOrderClass lt h.analyticSet

/-- On a countably infinite carrier the coded well-orders are not measurable for the product
σ-algebra, in any language. -/
theorem not_measurableSet_wellOrderClass [Countable V] [Infinite V] (lt : L.Relations 2) :
    ¬ MeasurableSet (wellOrderClass (V := V) lt) := by
  -- A measurable set of configurations is pulled back from a countable sublanguage, which may be
  -- taken to contain `lt`; there the coded well-orders are not analytic.
  intro h
  obtain ⟨R₀, hR₀, D₀, hD₀, hD⟩ := exists_countable_sublanguage_of_measurableSet h
  -- Enlarge the countable set of symbols by `lt`.
  let R₁ : Set (Σ n, L.Relations n) := insert ⟨2, lt⟩ R₀
  have : Countable R₁ := (hR₀.insert _).to_subtype
  let ι₁ := symbSublangIncl (L := L) ∅ R₁
  let incl := symbSublangInclusion (L := L) (subset_refl ∅) (subset_insert ⟨2, lt⟩ R₀)
  let lt₁ : (symbSublang (L := L) ∅ R₁).Relations 2 := ⟨lt, mem_insert _ _⟩
  have hcode (c : RelationalConfiguration L V) :
      codeRel lt₁ (ι₁.reductConfiguration c) = codeRel lt c := by
    ext x y
    simp [codeRel_iff, lt₁, ι₁]
  -- In the countable sublanguage, `D₀` pulls back to the coded well-orders of `lt₁`.
  have hW : incl.reductConfiguration ⁻¹' D₀ = wellOrderClass (V := V) lt₁ := by
    ext d
    obtain ⟨c, rfl⟩ := reductConfiguration_symbSublang_surjective ∅ R₁ d
    rw [mem_preimage, ← LHom.comp_reductConfiguration, symbSublangIncl_comp_symbSublangInclusion,
      ← mem_preimage, ← hD,
      mem_wellOrderClass, mem_wellOrderClass, hcode]
  exact not_measurableSet_wellOrderClass_of_countable lt₁
    (hW ▸ incl.measurable_reductConfiguration hD₀)

/-- **The coded well-orders are not definable.** On a countably infinite carrier, no `L_{ω₁ω}`
sentence has the coded well-orders as its model class. Compare
`FirstOrder.Language.wellOrdering_undefinable`, the corresponding statement about all countable
nonempty structures. -/
theorem not_exists_modelsOf_eq_wellOrderClass [L.IsRelational] [Countable V] [Infinite V]
    (lt : L.Relations 2) : ¬ ∃ φ : L.Sentenceω, modelsOf φ = wellOrderClass (V := V) lt :=
  fun ⟨φ, hφ⟩ => not_measurableSet_wellOrderClass lt (hφ ▸ measurableSet_modelsOf φ)

end TauCeti.RelationalConfiguration
