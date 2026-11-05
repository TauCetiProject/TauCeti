/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Infinite

/-!
# Counting countable pure sets

In the empty language there is one structure up to isomorphism on each fixed carrier. Thus
there are countably infinitely many countable pure sets up to isomorphism: one for each finite
cardinality (including zero), and one countably infinite class. Conjoining the infinitude
sentence removes exactly the finite classes, leaving a count of one.

The fixed-carrier calculation uses Mathlib's `FirstOrder.Language.empty.nonempty_equiv_iff`:
isomorphism in the empty language is simply a bijection of carriers.
-/

public section

universe w

open FirstOrder FirstOrder.Language Cardinal

namespace TauCeti

open RelationalConfiguration

/-- There is exactly one isomorphism class of pure sets on any fixed carrier, even the empty
carrier. -/
@[simp]
theorem mk_quotient_isoSetoidOn_empty_top (V : Type w) :
    #(Quotient (isoSetoidOn V (⊤ : Language.empty.Sentenceω))) = 1 := by
  let := Language.emptyStructure (M := V)
  have : Nonempty (Quotient (isoSetoidOn V (⊤ : Language.empty.Sentenceω))) :=
    ⟨⟦⟨ofStructure Language.empty V, by simp⟩⟧⟩
  have : Subsingleton (Quotient (isoSetoidOn V (⊤ : Language.empty.Sentenceω))) := by
    refine ⟨fun p q => ?_⟩
    induction p, q using Quotient.inductionOn₂ with
    | h c d =>
      exact Quotient.sound (isoSetoidOn_apply.2 (isoSetoid_apply.2
        ((@Language.empty.nonempty_equiv_iff V V c.1.toStructure d.1.toStructure).2 rfl)))
  exact mk_eq_one _

/-- There are countably infinitely many countable pure sets up to isomorphism, counting all
finite cardinalities and the countably infinite cardinality. -/
@[simp]
theorem countableModelCount_empty_top :
    countableModelCount (⊤ : Language.empty.Sentenceω) = ℵ₀ := by
  rw [countableModelCount_eq_add_sum]
  simp only [mk_quotient_isoSetoidOn_empty_top, sum_const, lift_one, mul_one, mk_nat,
    lift_aleph0]
  exact_mod_cast nat_add_aleph0 1

/-- The countably infinite pure sets form one isomorphism class. -/
@[simp]
theorem countableModelCount_empty_infiniteSentence :
    countableModelCount Language.empty.infiniteSentence = 1 := by
  have hmodels {V : Type} :
      modelsOf (V := V) (⊤ ⊓ Language.empty.infiniteSentence) =
        modelsOf Language.empty.infiniteSentence := by simp
  have hcount : countableModelCount (⊤ ⊓ Language.empty.infiniteSentence) =
      countableModelCount Language.empty.infiniteSentence :=
    (countableModelCount_le_of_subset (by rw [hmodels]) (fun _ => by rw [hmodels])).antisymm
      (countableModelCount_le_of_subset (by rw [hmodels]) (fun _ => by rw [hmodels]))
  rw [← hcount, countableModelCount_inf_infiniteSentence, mk_quotient_isoSetoidOn_empty_top]

end TauCeti
