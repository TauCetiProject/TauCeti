/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Scott.DenseLinearOrder
public import Mathlib.Analysis.Real.Cardinality

/-!
# Regression examples for the Scott analysis of dense linear orders

These downstream examples check the rational numbers: their internal Scott rank is one, they are
potentially isomorphic but not isomorphic to the real numbers, and their Scott sentence holds in
the uncountable model `ℝ` but fails in the discrete order `ℤ`.
-/

public section

namespace TauCeti

open FirstOrder FirstOrder.Language

attribute [local instance] orderStructure

-- Under `orderStructure`, the order symbol is interpreted as the order.
local instance {M : Type*} [LE M] : Language.order.OrderedStructure M := ⟨fun _ => Iff.rfl⟩

-- The rational numbers have internal Scott rank one.
example : internalScottRank (L := Language.order) ℚ = 1 := by simp

-- Potential isomorphism is strictly weaker than isomorphism for uncountable structures.
example : PotentialIso (L := Language.order) ℚ ℝ ∧ IsEmpty (ℚ ≃[Language.order] ℝ) :=
  ⟨potentialIso_of_dlo ℚ ℝ, ⟨fun e => not_countable (α := ℝ) e.symm.injective.countable⟩⟩

-- Tuples of `ℚ` and `ℝ` with the same order type agree at every back-and-forth level.
example (α : Ordinal) :
    BFEquiv (L := Language.order) α 2 ![(0 : ℚ), 1] ![(0 : ℝ), 2] := by
  refine (bfEquiv_iff_sameAtomicType_of_dlo ℚ ℝ).mpr ((sameAtomicType_iff _ _).mpr ⟨?_, ?_⟩)
  · intro i j
    fin_cases i <;> fin_cases j <;> simp
  · intro k r f
    obtain ⟨⟩ := r
    rw [order.relation_eq_leSymb .le, relMap_leSymb, relMap_leSymb]
    simp only [Function.comp_apply]
    generalize f 0 = i
    generalize f 1 = j
    fin_cases i <;> fin_cases j <;> norm_num

-- The Scott sentence of `ℚ` has the uncountable model `ℝ`.
example : SentenceInf.Realize (scottSentence (L := Language.order) ℚ) ℝ :=
  (realize_scottSentence_iff_of_dlo ℚ ℝ).mpr ⟨inferInstance, inferInstance⟩

-- The Scott sentence of `ℚ` fails in the discrete order `ℤ`.
example : ¬ SentenceInf.Realize (scottSentence (L := Language.order) ℚ) ℤ := by
  rw [realize_scottSentence_iff_of_dlo]
  rintro ⟨-, h⟩
  have := denselyOrdered_of_dlo (L := Language.order) ℤ
  obtain ⟨z, h₀, h₁⟩ := exists_between (show (0 : ℤ) < 1 by norm_num)
  omega

end TauCeti
