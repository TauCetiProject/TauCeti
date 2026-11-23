/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.ModelTheory.Order
public import TauCeti.ModelTheory.RelationalConfiguration.Theory

/-!
# The configuration space of linear orders and the dense linear order orbit

The theory of linear orders in `Language.order` constrains finite sets of comparisons,
so its model class is closed. The additional dense linear order axioms each ask for a
witness to a finite pattern for every assignment of their universal variables. On a
countable carrier this cuts out a Gδ subspace. On `ℕ`, Mathlib's countable categoricity of
dense linear orders without endpoints identifies the subspace with a single orbit of the
permutation action.

## Main results

* `TauCeti.RelationalConfiguration.isClosed_modelsOfTheory_linearOrder`
* `TauCeti.RelationalConfiguration.isGδ_modelsOfTheory_dlo`
* `TauCeti.RelationalConfiguration.polishSpace_modelsOfTheory_dlo`
* `TauCeti.RelationalConfiguration.exists_modelsOfTheory_dlo_eq_orbit`
-/

public section

open FirstOrder FirstOrder.Language Set TopologicalSpace

namespace TauCeti.RelationalConfiguration

variable {V : Type*}

private def leEvent (x y : V) : Set (RelationalConfiguration Language.order V) :=
  {c | c.eval (atom (L := Language.order) leSymb ![x, y]) = true}

private theorem isClopen_leEvent (x y : V) : IsClopen (leEvent x y) :=
  isClopen_setOf_eval _ _

private theorem mem_modelsOfTheory_linearOrder_iff {c : RelationalConfiguration Language.order V} :
    c ∈ modelsOfTheory Language.order.linearOrderTheory ↔
      (∀ x, c ∈ leEvent x x) ∧
      (∀ x y z, c ∈ leEvent x y → c ∈ leEvent y z → c ∈ leEvent x z) ∧
      (∀ x y, c ∈ leEvent x y → c ∈ leEvent y x → x = y) ∧
      (∀ x y, c ∈ leEvent x y ∨ c ∈ leEvent y x) := by
  simp only [mem_modelsOfTheory, linearOrderTheory, partialOrderTheory, preorderTheory,
    Theory.model_insert_iff, Theory.model_singleton_iff, Relations.realize_total,
    Relations.realize_antisymmetric, Relations.realize_reflexive, Relations.realize_transitive,
    toStructure_relMap, leEvent, mem_ofPred_eq]
  exact ⟨fun ⟨htotal, hanti, hrefl, htrans⟩ ↦
    ⟨hrefl.refl, htrans.trans, hanti.antisymm, htotal.total⟩,
    fun ⟨hrefl, htrans, hanti, htotal⟩ ↦
      ⟨⟨htotal⟩, ⟨hanti⟩, ⟨hrefl⟩, ⟨htrans⟩⟩⟩

/-- The codes for non-strict linear orders form a closed class on any carrier. -/
theorem isClosed_modelsOfTheory_linearOrder :
    IsClosed (modelsOfTheory (V := V) Language.order.linearOrderTheory) := by
  have heq (x y : V) :
      IsClopen (Set.ofPred fun _ : RelationalConfiguration Language.order V ↦ x = y) := by
    by_cases h : x = y <;> simp [h, IsClopen]
  let S :=
    ((⋂ x : V, leEvent x x) ∩
      (⋂ x : V, ⋂ y : V, ⋂ z : V, ((leEvent x y ∩ leEvent y z) \ leEvent x z)ᶜ)) ∩
    ((⋂ x : V, ⋂ y : V, ((leEvent x y ∩ leEvent y x) \
      (Set.ofPred fun _ : RelationalConfiguration Language.order V ↦ x = y))ᶜ) ∩
      (⋂ x : V, ⋂ y : V, leEvent x y ∪ leEvent y x))
  have hS : modelsOfTheory (V := V) Language.order.linearOrderTheory = S := by
    ext c
    simp only [mem_modelsOfTheory_linearOrder_iff, S, mem_inter_iff, mem_iInter, mem_compl_iff,
      mem_sdiff, mem_ofPred_eq, mem_union, not_and, not_not, and_assoc]
  rw [hS]
  refine (isClosed_iInter fun x ↦ (isClopen_leEvent x x).isClosed).inter
    (isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun z ↦ ?_) |>.inter
    ((isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_).inter
      (isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
        ((isClopen_leEvent x y).union (isClopen_leEvent y x)).isClosed))
  · exact ((((isClopen_leEvent x y).inter (isClopen_leEvent y z)).diff
      (isClopen_leEvent x z)).compl).isClosed
  · exact ((((isClopen_leEvent x y).inter (isClopen_leEvent y x)).diff (heq x y)).compl).isClosed

private def ltEvent (x y : V) : Set (RelationalConfiguration Language.order V) :=
  leEvent x y \ leEvent y x

private theorem isClopen_ltEvent (x y : V) : IsClopen (ltEvent x y) :=
  (isClopen_leEvent x y).diff (isClopen_leEvent y x)

private theorem mem_modelsOfTheory_dlo_iff {c : RelationalConfiguration Language.order V} :
    c ∈ modelsOfTheory Language.order.dlo ↔
      c ∈ modelsOfTheory Language.order.linearOrderTheory ∧
      (∀ x, ∃ y, c ∉ leEvent y x) ∧ (∀ x, ∃ y, c ∉ leEvent x y) ∧
      (∀ x y, c ∈ ltEvent x y → ∃ z, c ∈ ltEvent x z ∧ c ∈ ltEvent z y) := by
  classical
  have hsub : Language.order.linearOrderTheory ⊆ Language.order.dlo := Set.subset_union_left
  by_cases hc : c ∈ modelsOfTheory Language.order.linearOrderTheory
  · let := c.toStructure
    have hmodel : V ⊨ Language.order.linearOrderTheory := mem_modelsOfTheory.mp hc
    let : LinearOrder V := Language.order.linearOrderOfModels V
    have hle (x y : V) : x ≤ y ↔ c ∈ leEvent x y :=
      c.toStructure_relMap leSymb ![x, y]
    have hlt (x y : V) : x < y ↔ c ∈ ltEvent x y := by
      rw [lt_iff_le_not_ge, hle, hle, ltEvent, mem_sdiff]
    simp only [dlo, mem_modelsOfTheory, Theory.model_union_iff, Theory.model_insert_iff,
      Theory.model_singleton_iff, realize_noTopOrder_iff, realize_noBotOrder_iff,
      realize_denselyOrdered_iff, hmodel, true_and, ← hle, ← hlt]
    exact ⟨fun ⟨⟨htop⟩, ⟨hbot⟩, ⟨hdense⟩⟩ ↦ ⟨htop, hbot, hdense⟩,
      fun ⟨htop, hbot, hdense⟩ ↦ ⟨⟨htop⟩, ⟨hbot⟩, ⟨hdense⟩⟩⟩
  · exact iff_of_false (fun hd ↦ hc (modelsOfTheory_anti hsub hd)) (fun hd ↦ hc hd.1)

/-- On a countable carrier, the codes for dense linear orders without endpoints form a Gδ set. -/
theorem isGδ_modelsOfTheory_dlo [Countable V] :
    IsGδ (modelsOfTheory (V := V) Language.order.dlo) := by
  let S := modelsOfTheory (V := V) Language.order.linearOrderTheory ∩
    (⋂ x : V, ⋃ y : V, (leEvent y x)ᶜ) ∩ (⋂ x : V, ⋃ y : V, (leEvent x y)ᶜ) ∩
    (⋂ x : V, ⋂ y : V, (ltEvent x y)ᶜ ∪ ⋃ z : V, ltEvent x z ∩ ltEvent z y)
  have hS : modelsOfTheory (V := V) Language.order.dlo = S := by
    ext c
    simp only [mem_modelsOfTheory_dlo_iff, S, mem_inter_iff, mem_iInter, mem_iUnion, mem_compl_iff,
      mem_union, and_assoc, or_iff_not_imp_left, not_not]
  rw [hS]
  refine (((isClosed_modelsOfTheory_linearOrder.isGδ.inter ?_).inter ?_).inter ?_)
  · exact IsGδ.iInter_of_isOpen fun x ↦
      isOpen_iUnion fun y ↦ (isClopen_leEvent y x).isClosed.isOpen_compl
  · exact IsGδ.iInter_of_isOpen fun x ↦
      isOpen_iUnion fun y ↦ (isClopen_leEvent x y).isClosed.isOpen_compl
  · refine IsGδ.iInter fun x ↦ IsGδ.iInter_of_isOpen fun y ↦ ?_
    exact (isClopen_ltEvent x y).isClosed.isOpen_compl.union
      (isOpen_iUnion fun z ↦ (isClopen_ltEvent x z).isOpen.inter (isClopen_ltEvent z y).isOpen)

/-- The configuration subspace of dense linear orders without endpoints is Polish on a
countable carrier. -/
theorem polishSpace_modelsOfTheory_dlo [Countable V] :
    PolishSpace (modelsOfTheory (V := V) Language.order.dlo) :=
  isGδ_modelsOfTheory_dlo.polishSpace

/-- The orbit of any dense linear order code on a countable carrier is its entire model class. -/
theorem modelsOfTheory_dlo_eq_orbit [Countable V]
    {c : RelationalConfiguration Language.order V} (hc : c ∈ modelsOfTheory Language.order.dlo) :
    modelsOfTheory Language.order.dlo = MulAction.orbit (Equiv.Perm V) c := by
  ext d
  rw [MulAction.mem_orbit_iff, ← isoSetoid_iff_exists_perm_smul_eq]
  refine ⟨fun hd ↦ ?_, fun hd ↦ ((isomorphismInvariant_modelsOfTheory _).mem_iff hd).1 hc⟩
  rcases isEmpty_or_nonempty V with hV | hV
  · have hcd : c = d := by
      ext a
      induction a using Atom.induction_atom with
      | h R x => cases R; exact isEmptyElim (x 0)
    subst d
    exact (isoSetoid _ _).refl c
  · refine isoSetoid_apply.mpr ?_
    exact @IsFraisseLimit.nonempty_equiv Language.order _ V c.toStructure V d.toStructure
      inferInstance ‹Countable V› ‹Countable V›
      (@isFraisseLimit_of_countable_nonempty_dlo V c.toStructure _ hV (mem_modelsOfTheory.mp hc))
      (@isFraisseLimit_of_countable_nonempty_dlo V d.toStructure _ hV (mem_modelsOfTheory.mp hd))

/-- The DLO model class on `ℕ` is a single permutation orbit, with a representative given by
transporting the order of `ℚ`. -/
theorem exists_modelsOfTheory_dlo_eq_orbit :
    ∃ c : RelationalConfiguration Language.order ℕ,
      modelsOfTheory Language.order.dlo = MulAction.orbit (Equiv.Perm ℕ) c := by
  let := orderStructure ℚ
  have : Language.order.OrderedStructure ℚ := ⟨fun _ ↦ Iff.rfl⟩
  obtain ⟨e⟩ : Nonempty (ℚ ≃ ℕ) := nonempty_equiv_of_countable
  exact ⟨e.encodeVia, modelsOfTheory_dlo_eq_orbit ((e.encodeVia_mem_modelsOfTheory_iff _).2
    inferInstance)⟩

end TauCeti.RelationalConfiguration
