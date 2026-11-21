/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Fragment

/-!
# Negation-closed fragments of `L_{ω₁ω}`

A fragment of `L_{ω₁ω}` is **negation-closed** when the negation of each member is a member. The
syntax has no formal negation: `¬φ` is `φ.imp ⊥`. Since a fragment is closed under components, a
negation-closed fragment contains `⊥` at every arity at which it has a member, but at no other
arity: no `⊥` is added unconditionally. In particular the empty fragment is negation-closed, and
the negation closure of the empty set is empty.

The **negation closure** of a set `S` of formulas is the least negation-closed fragment containing
it. It contains, for instance, the iterated negations `¬φ`, `¬¬φ`, … of each member `φ` of `S`
and of its components. Unlike the formation closure, the negation closure adds no atomic formulas
and introduces no new function or relation symbols, so the negation closure of a countable set is
countable over every language, however many symbols it has. Along any language homomorphism
`g : L →ᴸ L'`, `NegationClosed` is preserved by both `map g` and `comap g`, and `negationClosure`
commutes with `map g`; reflecting `NegationClosed` along `map g` requires `g` to be injective.

## Main definitions

* `FirstOrder.Language.Fragment.NegationClosed`: a fragment containing the negation of each member.
* `FirstOrder.Language.Fragment.negationClosure`: the least negation-closed fragment containing a
  set of formulas.

## Main results

* `FirstOrder.Language.Fragment.NegationClosed.not_mem_iff`: in a negation-closed fragment, a
  negation is a member exactly when the formula is.
* `FirstOrder.Language.Fragment.NegationClosed.bot_mem`: a negation-closed fragment contains `⊥` at
  the arity of each member.
* `FirstOrder.Language.Fragment.negationClosure_le_iff`: leastness of the negation closure.
* `FirstOrder.Language.Fragment.negationClosure_empty`: the negation closure of the empty set is
  the empty fragment.
* `FirstOrder.Language.Fragment.negationClosure_countable`: over any language, a countable set has
  a countable negation closure.
* `FirstOrder.Language.Fragment.functionsIn_negationClosure`,
  `FirstOrder.Language.Fragment.relationsIn_negationClosure`: negation closure adds no occurring
  symbols.
* `FirstOrder.Language.Fragment.NegationClosed.comap`,
  `FirstOrder.Language.Fragment.NegationClosed.map`,
  `FirstOrder.Language.Fragment.map_negationClosure` and
  `FirstOrder.Language.Fragment.negationClosed_map_iff`: preservation of `NegationClosed` under
  `comap` and `map`, commutation of `negationClosure` with `map`, and reflection of
  `NegationClosed` under injective `map`.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1.
-/

public section

universe u v u' v'

namespace FirstOrder

namespace Language

namespace Fragment

variable {L : Language.{u, v}}

/-- A fragment is **negation-closed** when the negation of each member is a member. -/
structure NegationClosed (A : Fragment L) : Prop where
  /-- The negation of a member is a member. -/
  not_mem {n : ℕ} {φ : L.BoundedFormulaω Empty n} :
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A →
      (⟨n, φ.not⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A

namespace NegationClosed

variable {A : Fragment L} (hA : A.NegationClosed) {n : ℕ}
include hA

/-- In a negation-closed fragment, a negation is a member exactly when the formula is. -/
@[simp]
theorem not_mem_iff {φ : L.BoundedFormulaω Empty n} :
    (⟨n, φ.not⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ↔
      (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A :=
  ⟨A.imp_left_mem, hA.not_mem⟩

/-- A negation-closed fragment with a member of arity `n` contains `⊥` at arity `n`. -/
theorem bot_mem {φ : L.BoundedFormulaω Empty n}
    (h : (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    (⟨n, ⊥⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A :=
  A.imp_right_mem (hA.not_mem h)

end NegationClosed

/-- The empty fragment is negation-closed. -/
theorem negationClosed_bot : (⊥ : Fragment L).NegationClosed :=
  ⟨fun h => absurd h (notMem_bot _)⟩

/-- The top fragment is negation-closed. -/
theorem negationClosed_top : (⊤ : Fragment L).NegationClosed :=
  ⟨fun _ => mem_top _⟩

/-- An intersection of negation-closed fragments is negation-closed. -/
theorem NegationClosed.sInf {𝒜 : Set (Fragment L)} (h : ∀ A ∈ 𝒜, A.NegationClosed) :
    (sInf 𝒜).NegationClosed :=
  ⟨fun hφ => mem_sInf.2 fun A hA => (h A hA).not_mem (mem_sInf.1 hφ A hA)⟩

/-- The intersection of two negation-closed fragments is negation-closed. -/
theorem NegationClosed.inf {A B : Fragment L} (hA : A.NegationClosed) (hB : B.NegationClosed) :
    (A ⊓ B).NegationClosed := by
  rw [← sInf_pair]
  exact NegationClosed.sInf (by simp [hA, hB])

/-- The **negation closure** of a set of formulas: the least negation-closed fragment containing
it. -/
def negationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) : Fragment L :=
  sInf {A | A.NegationClosed ∧ S ⊆ A}

/-- A formula belongs to the negation closure of `S` exactly when it belongs to every
negation-closed fragment containing `S`. -/
theorem mem_negationClosure {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    {p : Σ n, L.BoundedFormulaω Empty n} :
    p ∈ negationClosure S ↔ ∀ A : Fragment L, A.NegationClosed → S ⊆ A → p ∈ A := by
  simp [negationClosure, and_imp]

/-- The negation closure is negation-closed. -/
theorem negationClosed_negationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (negationClosure S).NegationClosed :=
  NegationClosed.sInf fun _ hA => hA.1

/-- A set of formulas lies in its negation closure. -/
theorem subset_negationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    S ⊆ negationClosure S :=
  fun _ hp => mem_negationClosure.2 fun _ _ hS => hS hp

/-- **Leastness.** The negation closure of `S` lies below a negation-closed fragment exactly
when `S` does. -/
theorem negationClosure_le_iff {S : Set (Σ n, L.BoundedFormulaω Empty n)} {A : Fragment L}
    (hA : A.NegationClosed) : negationClosure S ≤ A ↔ S ⊆ A :=
  ⟨fun h => (subset_negationClosure S).trans (SetLike.coe_subset_coe.2 h),
    fun h => sInf_le ⟨hA, h⟩⟩

/-- The negation closure is monotone. -/
theorem negationClosure_mono {S T : Set (Σ n, L.BoundedFormulaω Empty n)} (h : S ⊆ T) :
    negationClosure S ≤ negationClosure (L := L) T :=
  (negationClosure_le_iff (negationClosed_negationClosure T)).2
    (h.trans (subset_negationClosure T))

/-- The fragment generated by `S` lies below its negation closure. -/
theorem generated_le_negationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    generated S ≤ negationClosure S :=
  generated_le_iff.2 (subset_negationClosure S)

/-- A negation-closed fragment is its own negation closure. -/
theorem NegationClosed.negationClosure_eq {A : Fragment L} (hA : A.NegationClosed) :
    negationClosure (A : Set (Σ n, L.BoundedFormulaω Empty n)) = A :=
  le_antisymm ((negationClosure_le_iff hA).2 subset_rfl) (subset_negationClosure _)

/-- The negation closure of the empty set is empty: no `⊥` is added at an arity without a
member. -/
@[simp]
theorem negationClosure_empty : negationClosure (∅ : Set (Σ n, L.BoundedFormulaω Empty n)) = ⊥ :=
  le_bot_iff.1 ((negationClosure_le_iff negationClosed_bot).2 (Set.empty_subset _))

/-! ### Countability of the negation closure

The negation closure of `S` is the union of countably many stages: start from `S`, and at each
stage add the negations of the members of the previous stage, closing under components. Each stage
of a countable set is countable, whatever the language, since generating a fragment preserves
countability. -/

/-- One stage: the members of `X` and their negations, closed under components. -/
private def negationStep (X : Set (Σ n, L.BoundedFormulaω Empty n)) : Fragment L :=
  generated (X ∪ (fun p => (⟨p.1, p.2.not⟩ : Σ n, L.BoundedFormulaω Empty n)) '' X)

private theorem subset_negationStep (X : Set (Σ n, L.BoundedFormulaω Empty n)) :
    X ⊆ negationStep X :=
  fun _ hp => subset_generated _ (Or.inl hp)

/-- The stages of the negation closure of `S`. -/
private def negationStage (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    ℕ → Set (Σ n, L.BoundedFormulaω Empty n)
  | 0 => S
  | k + 1 => negationStep (negationStage S k)

private theorem negationStage_countable {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    (hS : S.Countable) (k : ℕ) : (negationStage S k).Countable := by
  induction k with
  | zero => exact hS
  | succ k ih => exact generated_countable (ih.union (ih.image _))

/-- The union of the stages of the negation closure of `S`, as a fragment. -/
private def negationLimit (S : Set (Σ n, L.BoundedFormulaω Empty n)) : Fragment L :=
  ⨆ k, negationStep (negationStage S k)

private theorem mem_negationLimit {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    {p : Σ n, L.BoundedFormulaω Empty n} : p ∈ negationLimit S ↔ ∃ k, p ∈ negationStage S k := by
  rw [negationLimit, _root_.iSup, mem_sSup, Set.exists_range_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k + 1, hk⟩, fun ⟨k, hk⟩ => ⟨k, subset_negationStep _ hk⟩⟩

private theorem negationClosed_negationLimit (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (negationLimit S).NegationClosed :=
  ⟨fun hφ => by
    obtain ⟨k, hk⟩ := mem_negationLimit.1 hφ
    exact mem_negationLimit.2 ⟨k + 1, subset_generated _ (Or.inr ⟨_, hk, rfl⟩)⟩⟩

/-- **Countability.** The negation closure of a countable set of formulas is countable, over any
language. -/
theorem negationClosure_countable {S : Set (Σ n, L.BoundedFormulaω Empty n)} (hS : S.Countable) :
    ((negationClosure S : Fragment L) : Set (Σ n, L.BoundedFormulaω Empty n)).Countable := by
  refine ((Set.countable_iUnion (negationStage_countable hS)).mono
    fun p hp => Set.mem_iUnion.2 (mem_negationLimit.1 hp)).mono
    (SetLike.coe_subset_coe.2 ((negationClosure_le_iff (negationClosed_negationLimit S)).2 ?_))
  exact fun p hp => mem_negationLimit.2 ⟨0, hp⟩

/-! ### Occurring symbols and transport along language maps -/

/-- Every symbol-bounded fragment is negation-closed, since negation introduces no symbols. -/
theorem negationClosed_ofSymbols (F : Set (Σ k, L.Functions k)) (R : Set (Σ k, L.Relations k)) :
    (ofSymbols F R).NegationClosed :=
  ⟨fun h => by
    rw [mem_ofSymbols, BoundedFormulaInf.functionsIn_not, BoundedFormulaInf.relationsIn_not]
    exact mem_ofSymbols.1 h⟩

/-- Negation closure adds no function symbols: the function symbols of `negationClosure S` are
exactly those occurring in `S`. -/
@[simp]
theorem functionsIn_negationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (negationClosure S).functionsIn = ⋃ s ∈ S, s.2.functionsIn := by
  refine Set.Subset.antisymm ?_
    (functionsIn_generated S ▸ functionsIn_mono (generated_le_negationClosure S))
  exact (le_ofSymbols_iff.1 ((negationClosure_le_iff (negationClosed_ofSymbols _ _)).2
    fun s hs => mem_ofSymbols.2 ⟨fun _ hs' => Set.mem_iUnion₂.2 ⟨s, hs, hs'⟩,
      fun _ hs' => Set.mem_iUnion₂.2 ⟨s, hs, hs'⟩⟩)).1

/-- Negation closure adds no relation symbols: the relation symbols of `negationClosure S` are
exactly those occurring in `S`. -/
@[simp]
theorem relationsIn_negationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (negationClosure S).relationsIn = ⋃ s ∈ S, s.2.relationsIn := by
  refine Set.Subset.antisymm ?_
    (relationsIn_generated S ▸ relationsIn_mono (generated_le_negationClosure S))
  exact (le_ofSymbols_iff.1 ((negationClosure_le_iff (negationClosed_ofSymbols _ _)).2
    fun s hs => mem_ofSymbols.2 ⟨fun _ hs' => Set.mem_iUnion₂.2 ⟨s, hs, hs'⟩,
      fun _ hs' => Set.mem_iUnion₂.2 ⟨s, hs, hs'⟩⟩)).2

section LanguageMap

variable {L' : Language.{u', v'}}

/-- Pulling back a negation-closed fragment along any language homomorphism gives a negation-closed
fragment. -/
theorem NegationClosed.comap {B : Fragment L'} (hB : B.NegationClosed) (g : L →ᴸ L') :
    (B.comap g).NegationClosed :=
  ⟨fun h => by
    rw [mem_comap, LHom.onBoundedFormulaInf_not]
    exact hB.not_mem (mem_comap.1 h)⟩

/-- Mapping a negation-closed fragment along any language homomorphism gives a negation-closed
fragment. No injectivity of `g` is needed. -/
theorem NegationClosed.map {A : Fragment L} (hA : A.NegationClosed) (g : L →ᴸ L') :
    (A.map g).NegationClosed :=
  ⟨fun h => by
    obtain ⟨φ, hφ, hψ⟩ := mem_map.1 h
    exact mem_map.2 ⟨φ.not, hA.not_mem hφ, by rw [LHom.onBoundedFormulaInf_not, hψ]⟩⟩

/-- Along an injective language map, `A.map g` is negation-closed exactly when `A` is. -/
theorem negationClosed_map_iff {g : L →ᴸ L'} (hg : g.Injective) {A : Fragment L} :
    (A.map g).NegationClosed ↔ A.NegationClosed :=
  ⟨fun h => by
    rw [← comap_map_of_injective hg A]
    exact h.comap g, fun h => h.map g⟩

/-- **Mapping commutes with negation closure**, along any language homomorphism. -/
theorem map_negationClosure (g : L →ᴸ L') (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (negationClosure S).map g =
      negationClosure ((fun p : Σ n, L.BoundedFormulaω Empty n =>
        (⟨p.1, g.onBoundedFormulaInf p.2⟩ : Σ n, L'.BoundedFormulaω Empty n)) '' S) := by
  refine le_antisymm ?_ ((negationClosure_le_iff ((negationClosed_negationClosure S).map g)).2 ?_)
  · rw [map_le_iff_le_comap, negationClosure_le_iff ((negationClosed_negationClosure _).comap g)]
    exact fun p hp => mem_comap.2 (subset_negationClosure _ ⟨p, hp, rfl⟩)
  · rintro _ ⟨⟨n, φ⟩, hp, rfl⟩
    exact onBoundedFormulaInf_mem_map g (subset_negationClosure S hp)

end LanguageMap

end Fragment

namespace LEquiv

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

/-- Mapping along a language equivalence preserves and reflects negation closure. -/
@[simp]
theorem negationClosed_map_iff (e : L ≃ᴸ L') {A : Fragment L} :
    (A.map e.toLHom).NegationClosed ↔ A.NegationClosed :=
  ⟨fun h => by
    simpa only [Fragment.map_map, e.left_inv, Fragment.map_id] using h.map e.invLHom,
    fun h => h.map e.toLHom⟩

end LEquiv

end Language

end FirstOrder
