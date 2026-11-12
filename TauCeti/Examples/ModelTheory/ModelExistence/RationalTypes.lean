/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.ModelExistence.Types
import TauCeti.ModelTheory.BackAndForth.DiscreteOrder
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

/-!
# Regression example: the realized types of `(ℚ, <)`

In the language of orders, whose only symbol is `≤`, the rationals realize one complete
`L_{ω₁ω}`-type of single elements and three complete types of pairs, those of `x₀ < x₁`,
`x₀ = x₁` and `x₀ > x₁`. Each type of pairs is isolated among the realized types by a
quantifier-free formula: `¬ x₁ ≤ x₀`, `x₀ = x₁` and `¬ x₀ ≤ x₁`. Of these only `x₀ = x₁` is
atomic; the strict comparisons are negations of atomic formulas, since `<` is not a symbol of the
language.

Tuples with the same order type have the same complete type, because `ℚ` forms an extension pair
with itself.
-/

open FirstOrder FirstOrder.Language TauCeti

attribute [local instance] orderStructure

-- `ℚ` realizes one complete type of single elements and three complete types of pairs, isolated
-- by `¬ x₁ ≤ x₀`, `x₀ = x₁` and `¬ x₀ ≤ x₁`; the second formula is atomic, the first is not.
example :
    let lt : Language.order.BoundedFormulaω Empty 2 := BoundedFormula.toOmega ((&1).le (&0)).not
    let eq : Language.order.BoundedFormulaω Empty 2 := BoundedFormula.toOmega (.equal (&0) (&1))
    let gt : Language.order.BoundedFormulaω Empty 2 := BoundedFormula.toOmega ((&0).le (&1)).not
    realizedTypes (L := Language.order) ℚ 1 = {infinitaryType ℚ ![0]} ∧
      realizedTypes (L := Language.order) ℚ 2 =
        {infinitaryType ℚ ![0, 1], infinitaryType ℚ ![0, 0], infinitaryType ℚ ![1, 0]} ∧
      (realizedTypes (L := Language.order) ℚ 2).ncard = 3 ∧
      (∀ b : Fin 2 → ℚ,
        (lt.Realize Empty.elim b ↔
          infinitaryType (L := Language.order) ℚ b = infinitaryType ℚ ![0, 1]) ∧
        (eq.Realize Empty.elim b ↔
          infinitaryType (L := Language.order) ℚ b = infinitaryType ℚ ![0, 0]) ∧
        (gt.Realize Empty.elim b ↔
          infinitaryType (L := Language.order) ℚ b = infinitaryType ℚ ![1, 0])) ∧
      eq.IsAtomic ∧ ¬ lt.IsAtomic := by
  intro lt eq gt
  -- tuples with the same atomic type have the same complete type
  have htype {n : ℕ} {a b : Fin n → ℚ} (h : SameAtomicType (L := Language.order) a b) :
      infinitaryType (L := Language.order) ℚ a = infinitaryType ℚ b :=
    h.infinitaryType_eq_of_isExtensionPair (dlo_isExtensionPair ℚ ℚ) (dlo_isExtensionPair ℚ ℚ)
  have hlt (b : Fin 2 → ℚ) : lt.Realize Empty.elim b ↔ b 0 < b 1 := by
    simp [lt]
  have heq (b : Fin 2 → ℚ) : eq.Realize Empty.elim b ↔ b 0 = b 1 := by
    simp [eq]
  have hgt (b : Fin 2 → ℚ) : gt.Realize Empty.elim b ↔ b 1 < b 0 := by
    simp [gt]
  -- the type of a pair is determined by the comparison of its entries
  have tlt {b : Fin 2 → ℚ} (hb : b 0 < b 1) :
      infinitaryType (L := Language.order) ℚ b = infinitaryType ℚ ![0, 1] :=
    htype ((sameAtomicType_order_iff _ _).2 ⟨fun i j => by
      fin_cases i <;> fin_cases j <;> simp [hb.ne, hb.ne'], fun i j => by
      fin_cases i <;> fin_cases j <;> simp [hb.le, hb.not_ge]⟩)
  have teq {b : Fin 2 → ℚ} (hb : b 0 = b 1) :
      infinitaryType (L := Language.order) ℚ b = infinitaryType ℚ ![0, 0] :=
    htype ((sameAtomicType_order_iff _ _).2 ⟨fun i j => by
      fin_cases i <;> fin_cases j <;> simp [hb], fun i j => by
      fin_cases i <;> fin_cases j <;> simp [hb]⟩)
  have tgt {b : Fin 2 → ℚ} (hb : b 1 < b 0) :
      infinitaryType (L := Language.order) ℚ b = infinitaryType ℚ ![1, 0] :=
    htype ((sameAtomicType_order_iff _ _).2 ⟨fun i j => by
      fin_cases i <;> fin_cases j <;> simp [hb.ne, hb.ne'], fun i j => by
      fin_cases i <;> fin_cases j <;> simp [hb.le, hb.not_ge]⟩)
  have h2 : realizedTypes (L := Language.order) ℚ 2 =
      {infinitaryType ℚ ![0, 1], infinitaryType ℚ ![0, 0], infinitaryType ℚ ![1, 0]} := by
    ext p
    simp only [mem_realizedTypes, Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨fun ⟨b, hb⟩ => ?_, ?_⟩
    · subst hb
      rcases lt_trichotomy (b 0) (b 1) with h | h | h
      · exact Or.inl (tlt h)
      · exact Or.inr (Or.inl (teq h))
      · exact Or.inr (Or.inr (tgt h))
    · rintro (h | h | h) <;> exact ⟨_, h.symm⟩
  refine ⟨?_, h2, ?_, fun b => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · ext p
    simp only [mem_realizedTypes, Set.mem_singleton_iff]
    refine ⟨fun ⟨a, ha⟩ => ha ▸ htype ((sameAtomicType_order_iff _ _).2
      ⟨fun i j => ?_, fun i j => ?_⟩), fun h => ⟨_, h.symm⟩⟩ <;>
    · rw [Subsingleton.elim i j]
      simp
  -- the isolating formulas separate the three types
  · rw [h2, Set.ncard_eq_three]
    refine ⟨_, _, _, fun h => ?_, fun h => ?_, fun h => ?_, rfl⟩
    · have := (Set.ext_iff.1 h lt).1 (mem_infinitaryType.2 ((hlt _).2 (by simp)))
      norm_num [mem_infinitaryType, hlt] at this
    · have := (Set.ext_iff.1 h lt).1 (mem_infinitaryType.2 ((hlt _).2 (by simp)))
      norm_num [mem_infinitaryType, hlt] at this
    · have := (Set.ext_iff.1 h eq).1 (mem_infinitaryType.2 ((heq _).2 (by simp)))
      norm_num [mem_infinitaryType, heq] at this
  · exact ⟨fun h => tlt ((hlt b).1 h), fun e => mem_infinitaryType.1 <| (Set.ext_iff.1 e lt).2 <|
      mem_infinitaryType.2 ((hlt _).2 (by simp))⟩
  · exact ⟨fun h => teq ((heq b).1 h), fun e => mem_infinitaryType.1 <| (Set.ext_iff.1 e eq).2 <|
      mem_infinitaryType.2 ((heq _).2 (by simp))⟩
  · exact ⟨fun h => tgt ((hgt b).1 h), fun e => mem_infinitaryType.1 <| (Set.ext_iff.1 e gt).2 <|
      mem_infinitaryType.2 ((hgt _).2 (by simp))⟩
  -- `x₀ = x₁` is atomic, while `¬ x₁ ≤ x₀` is an implication
  · simp only [eq, BoundedFormula.toInf_equal]
    exact .equal _ _
  · simp only [lt, BoundedFormula.toInf_not]
    rintro ⟨⟩
