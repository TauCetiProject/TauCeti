/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Real.Cardinality
public import TauCeti.ModelTheory.RelationalConfiguration.AnalyticPC

/-!
# Examples: an invariant analytic class that is not a projective class

Take unary predicates `P_r`, one for each real number `r`. The code on `ℕ` in which every `P_r` is
empty is fixed by every permutation of `ℕ`, so its singleton is an isomorphism-invariant class of
codes, and the singleton is analytic. But a single `L_{ω₁ω}` sentence mentions only countably many
of the `P_r`, so the singleton is not the projective class of any sentence along
`LHom.sumInl : L →ᴸ L.sum W`. The forward direction of the analytic characterization (an invariant
analytic class is a projective class) therefore needs countably many relation symbols.
-/

public section

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration MeasureTheory

namespace TauCeti.AnalyticPCExample

/-- The relational language with one unary predicate `P_r` for each real number `r`. -/
def realPredicates : Language where
  Functions _ := Empty
  Relations
    | 1 => ℝ
    | _ => Empty

instance : realPredicates.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

/-- The predicates `P_r` are uncountably many. -/
theorem not_countable_relations : ¬ Countable (Σ n, realPredicates.Relations n) := fun _ =>
  Cardinal.not_countable_real (Set.countable_univ_iff.2
    ((show Function.Injective fun r : ℝ => (⟨1, r⟩ : Σ n, realPredicates.Relations n) from
      fun _ _ hrs => eq_of_heq (Sigma.mk.inj_iff.1 hrs).2).countable))

/-- The code on `ℕ` in which every predicate `P_r` is empty. -/
def emptyCode : RelationalConfiguration realPredicates ℕ :=
  RelationalConfiguration.mk fun _ => false

-- Every permutation of `ℕ` fixes the empty code, so its singleton is isomorphism invariant.
example (σ : Equiv.Perm ℕ) : σ • emptyCode = emptyCode :=
  RelationalConfiguration.ext fun a => by simp [emptyCode]

-- The singleton of the empty code is analytic: it is the range of a constant map.
example : AnalyticSet ({emptyCode} : Set (RelationalConfiguration realPredicates ℕ)) := by
  rw [← Set.range_const (c := emptyCode) (ι := ℕ → ℕ)]
  exact analyticSet_range_of_polishSpace continuous_const

-- It is not the projective class of any sentence, whatever the language `W` of added symbols.
example (W : Language) [W.IsRelational] (ψ : (realPredicates.sum W).Sentenceω) :
    {c : RelationalConfiguration realPredicates ℕ |
        @LHom.PCMem _ _ LHom.sumInl ψ ℕ c.toStructure} ≠ {emptyCode} :=
  LHom.setOf_pcMem_ne_singleton LHom.sumInl LHom.sumInl_injective not_countable_relations ψ
    emptyCode

end TauCeti.AnalyticPCExample
