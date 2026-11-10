/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.ExtensionPair
public import TauCeti.ModelTheory.BackAndForth.Karp
public import TauCeti.ModelTheory.Infinitary.Theory

/-!
# Complete `L_{ω₁ω}`-types and their isolation

The **complete `L_{ω₁ω}`-type** of a tuple `a : Fin n → M` is the set of `L_{ω₁ω}` formulas with
`n` bound positions and no free variables that hold of `a` in `M`. The **realized types** of `M`
at arity `n` are the complete types of its `n`-tuples. A complete type contains, for every
formula, either the formula or its negation, so one complete type can lie inside another only
when the two are equal.

Isomorphic structures realize the same complete types. At arity `0` the only realized type is the
`L_{ω₁ω}` theory of the structure, so two structures satisfy the same `L_{ω₁ω}` sentences exactly
when they realize the same complete types at arity `0`.

The main result is the isolation of realized types. If `M` realizes only countably many complete
`n`-types, then each realized type `p` is isolated among them by one formula: for every other
realized type `q`, pick a formula of `p` outside `q`; the countable conjunction of these choices
holds of a tuple `b` of `M` exactly when the type of `b` is `p`. No fragment, no countability of
the language and no relational hypothesis is involved. Isolating formulas are the basic tool for
analysing structures that realize countably many types.

## Main definitions

* `FirstOrder.Language.infinitaryType`: the complete `L_{ω₁ω}`-type of a tuple.
* `FirstOrder.Language.realizedTypes`: the complete types realized in a structure at an arity.

## Main results

* `FirstOrder.Language.infinitaryType_subset_iff`: a complete type lies inside another only when
  the two are equal.
* `FirstOrder.Language.StrongHomClass.infinitaryType_comp` and
  `FirstOrder.Language.StrongHomClass.realizedTypes_eq`: isomorphisms preserve complete types and
  realized types.
* `FirstOrder.Language.omitsType_iff_forall_mem_realizedTypes_not_subset`: a structure omits a
  partial type exactly when no realized type contains it.
* `TauCeti.infEquivAt_nat_iff_realizedTypes_zero_eq`: two structures satisfy the same
  `L_{ω₁ω}` sentences exactly when they realize the same complete types at arity `0`.
* `TauCeti.SameAtomicType.infinitaryType_eq_of_isExtensionPair`: between relational structures
  forming extension pairs in both directions, such as nonempty dense linear orders without
  endpoints, tuples of the same atomic type have the same complete type.
* `FirstOrder.Language.exists_isolatingFormula`: if a structure realizes countably many complete
  `n`-types, each realized type is isolated among them by a single formula.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, for complete
  `L_{ω₁ω}`-types and structures realizing countably many of them.
* The shape of `infinitaryType` and `realizedTypes` follows Mathlib's first-order
  `FirstOrder.Language.Theory.typeOf` and `FirstOrder.Language.Theory.realizedTypes`
  (`Mathlib/ModelTheory/Types.lean`).
-/

public section

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
  {n : ℕ}

/-- The **complete `L_{ω₁ω}`-type** of a tuple `a : Fin n → M`: the formulas with `n` bound
positions and no free variables that hold of `a` in `M`. -/
def infinitaryType (M : Type w) [L.Structure M] {n : ℕ} (a : Fin n → M) :
    Set (L.BoundedFormulaω Empty n) :=
  {φ | φ.Realize Empty.elim a}

/-- A formula belongs to the complete type of a tuple exactly when it holds of the tuple. -/
@[simp]
theorem mem_infinitaryType {a : Fin n → M} {φ : L.BoundedFormulaω Empty n} :
    φ ∈ infinitaryType M a ↔ φ.Realize Empty.elim a :=
  Iff.rfl

/-- **Complete types are maximal.** The complete type of a tuple lies inside the complete type of
another tuple, possibly in another structure, only when the two types are equal: a formula of the
larger type missing from the smaller one would put its negation in the smaller one. -/
theorem infinitaryType_subset_iff {a : Fin n → M} {b : Fin n → N} :
    infinitaryType (L := L) M a ⊆ infinitaryType N b ↔
      infinitaryType (L := L) M a = infinitaryType N b := by
  refine ⟨fun h => h.antisymm fun φ hφ => ?_, fun h => h.subset⟩
  by_contra hφa
  exact (mem_infinitaryType.1 (h (mem_infinitaryType.2
    (BoundedFormulaInf.realize_not.2 hφa)))) hφ

/-- The complete types realized in `M` at arity `n`: the complete types of the `n`-tuples
of `M`. -/
def realizedTypes (M : Type w) [L.Structure M] (n : ℕ) : Set (Set (L.BoundedFormulaω Empty n)) :=
  Set.range (infinitaryType M (n := n))

/-- A set of formulas is a realized type of `M` exactly when it is the complete type of some
tuple of `M`. -/
@[simp]
theorem mem_realizedTypes {p : Set (L.BoundedFormulaω Empty n)} :
    p ∈ realizedTypes M n ↔ ∃ a : Fin n → M, infinitaryType M a = p :=
  Iff.rfl

/-- The complete type of a tuple of `M` is a realized type of `M`. -/
theorem infinitaryType_mem_realizedTypes (a : Fin n → M) :
    infinitaryType (L := L) M a ∈ realizedTypes M n :=
  ⟨a, rfl⟩

/-- At arity `0` the only realized type is the complete type of the empty tuple, which is the
`L_{ω₁ω}` theory of the structure. -/
theorem realizedTypes_zero (M : Type w) [L.Structure M] :
    realizedTypes M 0 = {infinitaryType (L := L) M Fin.elim0} := by
  rw [realizedTypes, Set.range_unique, Subsingleton.elim default Fin.elim0]

/-- A structure **omits** a partial type exactly when none of its realized types contains it. -/
theorem omitsType_iff_forall_mem_realizedTypes_not_subset
    {p : Set (L.BoundedFormulaω Empty n)} : OmitsType M p ↔ ∀ q ∈ realizedTypes M n, ¬p ⊆ q := by
  simp only [omitsType_iff, mem_realizedTypes, forall_exists_index, forall_apply_eq_imp_iff,
    Set.not_subset, mem_infinitaryType]

namespace StrongHomClass

variable {F : Type*} [EquivLike F M N] [StrongHomClass L F M N]

/-- An isomorphism preserves complete types: the image of a tuple has the type of the tuple. -/
@[simp]
theorem infinitaryType_comp (g : F) (a : Fin n → M) :
    infinitaryType (L := L) N (g ∘ a) = infinitaryType M a := by
  ext φ
  rw [mem_infinitaryType, mem_infinitaryType, ← StrongHomClass.realize_boundedFormulaInf g φ,
    Subsingleton.elim (g ∘ (Empty.elim : Empty → M)) Empty.elim]

/-- Isomorphic structures realize the same complete types. -/
theorem realizedTypes_eq (g : F) (n : ℕ) : realizedTypes (L := L) M n = realizedTypes N n := by
  ext p
  simp only [mem_realizedTypes]
  refine ⟨fun ⟨a, ha⟩ => ⟨g ∘ a, by rw [infinitaryType_comp, ha]⟩, fun ⟨b, hb⟩ =>
    ⟨EquivLike.inv g ∘ b, by
      rw [← hb, ← infinitaryType_comp g]
      exact congrArg _ (funext fun i => EquivLike.apply_inv_apply g (b i))⟩⟩

end StrongHomClass

/-! ### Isolating formulas -/

/-- **Realized types are isolated.** If `M` realizes only countably many complete `n`-types, then
the type of each tuple `a` is isolated among the realized types by a single formula `χ`: `χ` holds
of a tuple `b` of `M` exactly when `b` has the type of `a`. The formula `χ` is the countable
conjunction, over the realized types `q`, of a formula of the type of `a` that does not lie in `q`
when `q` differs from the type of `a`. -/
theorem exists_isolatingFormula (h : (realizedTypes (L := L) M n).Countable) (a : Fin n → M) :
    ∃ χ : L.BoundedFormulaω Empty n, ∀ b : Fin n → M,
      χ.Realize Empty.elim b ↔ infinitaryType (L := L) M b = infinitaryType M a := by
  -- For each realized type `q`, a formula of the type of `a` that separates it from `q`.
  have hsep : ∀ q : realizedTypes (L := L) M n, ∃ θ ∈ infinitaryType M a,
      q.1 ≠ infinitaryType M a → θ ∉ q.1 := by
    rintro ⟨_, b, rfl⟩
    by_cases hb : infinitaryType (L := L) M b = infinitaryType M a
    · exact ⟨⊤, BoundedFormulaInf.realize_top.2 trivial, fun hne => (hne hb).elim⟩
    · obtain ⟨θ, hθa, hθb⟩ := Set.not_subset.1 fun hs => hb (infinitaryType_subset_iff.1 hs).symm
      exact ⟨θ, hθa, fun _ => hθb⟩
  choose θ hθa hθq using hsep
  refine ⟨BoundedFormulaInf.iInfAlong (TauCeti.IndexCoding.ofEncodableWith h.toEncodable) θ,
    fun b => ?_⟩
  rw [BoundedFormulaInf.realize_iInfAlong]
  refine ⟨fun hb => ?_, fun hb q => ?_⟩
  · by_contra hne
    exact hθq ⟨_, infinitaryType_mem_realizedTypes b⟩ hne (hb _)
  · rw [← mem_infinitaryType, hb]
    exact hθa q

end Language

end FirstOrder

namespace TauCeti

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- **`L_{ω₁ω}`-equivalence is equality of the realized types at arity `0`.** Two structures
satisfy the same `L_{ω₁ω}` sentences exactly when they realize the same complete types at
arity `0`. -/
theorem infEquivAt_nat_iff_realizedTypes_zero_eq :
    InfEquivAt (L := L) ℕ M N ↔ realizedTypes (L := L) M 0 = realizedTypes N 0 := by
  rw [infEquivAt_iff_forall_realize, realizedTypes_zero, realizedTypes_zero,
    Set.singleton_eq_singleton_iff, Set.ext_iff]
  simp only [mem_infinitaryType]

/-- **Atomic types determine complete types along extension pairs.** In a relational language,
when `M` and `N` form an extension pair in both directions, tuples of `M` and `N` with the same
atomic type have the same complete `L_{ω₁ω}`-type: they are back-and-forth equivalent at every
level, in particular at the quantifier rank of each formula. -/
theorem SameAtomicType.infinitaryType_eq_of_isExtensionPair [L.IsRelational] {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (h : SameAtomicType (L := L) a b)
    (hMN : L.IsExtensionPair M N) (hNM : L.IsExtensionPair N M) :
    infinitaryType (L := L) M a = infinitaryType N b := by
  ext φ
  exact (h.bfEquiv_of_isExtensionPair hMN hNM φ.qrank).realize_iff_of_qrank_le φ le_rfl _ _

end TauCeti
