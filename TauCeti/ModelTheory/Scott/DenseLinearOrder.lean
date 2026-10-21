/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Karp
public import TauCeti.ModelTheory.Scott.ExtensionPair
public import TauCeti.ModelTheory.Scott.PotentialIso
public import Mathlib.ModelTheory.Order
public import Mathlib.SetTheory.Cardinal.Rat
public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Scott analysis of dense linear orders

Dense linear orders without endpoints, the models of Mathlib's first-order theory
`Language.order.dlo`, are the basic example of back-and-forth: by Cantor's argument
(Mathlib's `dlo_isExtensionPair`) every finite order-preserving partial map extends to any new
point. In the language of back-and-forth equivalence this gives, for structures of every
cardinality:

* between two nonempty dense linear orders without endpoints, tuples are back-and-forth
  equivalent at every level exactly when they have the same order type, and the two orders are
  potentially isomorphic;
* every dense linear order without endpoints, including the empty one, has internal Scott rank
  one;
* the Scott sentence of a countable nonempty dense linear order without endpoints, such as
  `ℚ`, is satisfied exactly by the nonempty models of `Language.order.dlo`, in every cardinality.

For countable structures potential isomorphism is isomorphism
(`TauCeti.countable_potentialIso_iff_iso`), so the first item refines Cantor's
`ℵ₀`-categoricity (Mathlib's `aleph0_categorical_dlo`). For uncountable orders it is strictly
weaker, even in a single cardinality: the lexicographic product `ω₁ ×ₗ ℚ` of `ω₁` copies of `ℚ`
and its order dual are nonempty dense linear orders without endpoints of cardinality `ℵ₁`, hence
potentially isomorphic and `L∞ω`-equivalent, but they are not isomorphic, because the first has
cofinality `ℵ₁` and the second has cofinality `ℵ₀`.

## Main results

* `TauCeti.dlo_isExtensionPair_self`: the self-extension property, with no nonemptiness
  assumption.
* `TauCeti.bfEquiv_iff_sameAtomicType_of_dlo` and `TauCeti.potentialIso_of_dlo`.
* `TauCeti.internalScottRank_eq_one_of_dlo`.
* `TauCeti.realize_scottSentence_iff_of_dlo`.
* `TauCeti.isEmpty_equiv_orderDual_toType_omega_one_lex_rat` and
  `TauCeti.exists_dlo_aleph_one_potentialIso_isEmpty_equiv`: two dense linear orders without
  endpoints of cardinality `ℵ₁` that are potentially isomorphic but not isomorphic.

## References

* Georg Cantor, *Beiträge zur Begründung der transfiniten Mengenlehre*, 1895.
* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, 1965.
* Carol Karp, *Finite-quantifier equivalence*, in *The Theory of Models*, 1965.
-/

public section

universe w w' o

namespace TauCeti

open FirstOrder FirstOrder.Language

section Self

variable (M : Type w) [Language.order.Structure M] [M ⊨ Language.order.dlo]

/-- A dense linear order without endpoints has the self-extension property. Unlike Mathlib's
`dlo_isExtensionPair`, no nonemptiness is assumed: for an empty order it holds vacuously. -/
theorem dlo_isExtensionPair_self : Language.order.IsExtensionPair M M := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact fun _ m => isEmptyElim m
  · exact dlo_isExtensionPair M M

/-- Every dense linear order without endpoints, of any cardinality and including the empty one,
has internal Scott rank one. -/
@[simp]
theorem internalScottRank_eq_one_of_dlo :
    internalScottRank (L := Language.order) M = 1 :=
  (dlo_isExtensionPair_self M).internalScottRank_eq_one

end Self

section Pair

variable (M : Type w) [Language.order.Structure M] [M ⊨ Language.order.dlo] [Nonempty M]
variable (N : Type w') [Language.order.Structure N] [N ⊨ Language.order.dlo] [Nonempty N]

/-- Between nonempty dense linear orders without endpoints, tuples are back-and-forth equivalent
at any level exactly when they have the same order type. -/
theorem bfEquiv_iff_sameAtomicType_of_dlo {α : Ordinal.{o}} {n : ℕ} {a : Fin n → M}
    {b : Fin n → N} :
    BFEquiv (L := Language.order) α n a b ↔ SameAtomicType (L := Language.order) a b :=
  ⟨BFEquiv.sameAtomicType, fun h =>
    h.bfEquiv_of_isExtensionPair (dlo_isExtensionPair M N) (dlo_isExtensionPair N M) α⟩

/-- Any two nonempty dense linear orders without endpoints are potentially isomorphic, whatever
their cardinalities. -/
theorem potentialIso_of_dlo : PotentialIso (L := Language.order) M N :=
  (isTupleBFSystem_sameAtomicType (dlo_isExtensionPair M N) (dlo_isExtensionPair N M)
    sameAtomicType_elim0).potentialIso

end Pair

/-- The Scott sentence of a countable nonempty dense linear order without endpoints holds in a
structure of any cardinality exactly when that structure is a nonempty dense linear order
without endpoints. -/
theorem realize_scottSentence_iff_of_dlo (M : Type w) [Language.order.Structure M]
    [M ⊨ Language.order.dlo] [Nonempty M] [Countable M] (N : Type w')
    [Language.order.Structure N] :
    SentenceInf.Realize (scottSentence (L := Language.order) M) N ↔
      Nonempty N ∧ N ⊨ Language.order.dlo := by
  constructor
  · intro h
    have hMN := ((potentialIso_of_realize_scottSentence M h).infEquivAt
      ℕ).elementarilyEquivalent
    exact ⟨hMN.nonempty, hMN.theory_model⟩
  · rintro ⟨hN, hdlo⟩
    exact (infEquivAt_iff.mp ((potentialIso_of_dlo M N).infEquivAt ℕ) _).mp
      (realize_scottSentence_self M)

section AlephOne

open Cardinal Order
open scoped Ordinal

attribute [local instance] orderStructure

-- Under `orderStructure`, the order symbol is interpreted as the order.
local instance {M : Type*} [LE M] : Language.order.OrderedStructure M := ⟨fun _ => Iff.rfl⟩

/-- The lexicographic product `ω₁ ×ₗ ℚ` is not isomorphic, as a structure in the language of
orders, to its order dual: it has cofinality `ℵ₁`, while its order dual has cofinality `ℵ₀`. -/
theorem isEmpty_equiv_orderDual_toType_omega_one_lex_rat :
    IsEmpty ((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ ≃[Language.order]
      ((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ)ᵒᵈ) := by
  have : Nonempty (ω₁ : Ordinal.{w}).ToType :=
    Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne'
  have : NoTopOrder (ω₁ : Ordinal.{w}).ToType :=
    one_lt_cof_iff.mp (by simp [one_lt_aleph0.trans_le (aleph0_le_aleph 1)])
  have := NoTopOrder.to_noMaxOrder (ω₁ : Ordinal.{w}).ToType
  -- The copies `(i, 0)` of the elements of `ω₁` are cofinal in `ω₁ ×ₗ ℚ`.
  have hcof : Order.cof ((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ) = ℵ₁ := by
    rw [← cof_congr_of_strictMono (f := fun i : (ω₁ : Ordinal.{w}).ToType => toLex (i, (0 : ℚ)))
      (fun i j h => by simp [Prod.Lex.toLex_lt_toLex, h]) ?_]
    · simp
    · rintro ⟨i, q⟩
      obtain ⟨j, hj⟩ := exists_gt i
      exact ⟨_, Set.mem_range_self j, (Prod.Lex.toLex_lt_toLex.mpr (.inl hj)).le⟩
  -- The copy of `ℚ` over the least element of `ω₁` is coinitial in `ω₁ ×ₗ ℚ`.
  have hcof_dual : Order.cof ((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ)ᵒᵈ = ℵ₀ := by
    let := WellFoundedLT.toOrderBot (ω₁ : Ordinal.{w}).ToType
    let f (q : ℚ) : ((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ)ᵒᵈ := OrderDual.toDual (toLex (⊥, -q))
    have hf : IsCofinal (Set.range f) := fun x => by
      refine ⟨_, Set.mem_range_self (-(ofLex (OrderDual.ofDual x)).2), ?_⟩
      rw [OrderDual.le_toDual, neg_neg]
      exact Prod.Lex.toLex_le_toLex.mpr (bot_le.lt_or_eq.imp id fun h => ⟨h, le_rfl⟩)
    simpa using (lift_cof_congr_of_strictMono (f := f)
      (fun q r h => by simpa [f, Prod.Lex.toLex_lt_toLex] using h) hf).symm
  refine ⟨fun e => ?_⟩
  let := StrongHomClass.toOrderIsoClass Language.order _ _
    ((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ ≃[Language.order] ((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ)ᵒᵈ)
  have h := (OrderIso.ofClass e).cof_congr
  rw [hcof, hcof_dual] at h
  exact aleph0_lt_aleph_one.ne' h

/-- Potential isomorphism, and hence `L∞ω`-equivalence, does not imply isomorphism for
uncountable structures of the same cardinality: in every universe there are two dense linear
orders without endpoints of cardinality `ℵ₁` that are potentially isomorphic, and so
`L∞ω`-equivalent (`TauCeti.InfEquivW`), but not isomorphic. The witnesses are `ω₁ ×ₗ ℚ` and its
order dual. -/
theorem exists_dlo_aleph_one_potentialIso_isEmpty_equiv :
    ∃ (M N : Type w) (_ : Language.order.Structure M) (_ : Language.order.Structure N),
      M ⊨ Language.order.dlo ∧ N ⊨ Language.order.dlo ∧ #M = ℵ₁ ∧ #N = ℵ₁ ∧
        PotentialIso (L := Language.order) M N ∧ InfEquivW (L := Language.order) M N ∧
        IsEmpty (M ≃[Language.order] N) := by
  have : Nonempty (ω₁ : Ordinal.{w}).ToType :=
    Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne'
  have hmk : #((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ) = ℵ₁ := by
    simp [Cardinal.mk_congr toLex.symm, mul_aleph0_eq]
  have hiso := potentialIso_of_dlo ((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ)
    ((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ)ᵒᵈ
  exact ⟨(ω₁ : Ordinal.{w}).ToType ×ₗ ℚ, ((ω₁ : Ordinal.{w}).ToType ×ₗ ℚ)ᵒᵈ, _, _,
    inferInstance, inferInstance, hmk, hmk, hiso, karp_theorem.mp hiso,
    isEmpty_equiv_orderDual_toType_omega_one_lex_rat⟩

end AlephOne

end TauCeti
