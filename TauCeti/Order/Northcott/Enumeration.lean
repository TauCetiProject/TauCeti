/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.OrderIsoNat
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Enumerating a family in nondecreasing order

Let `f : ι → α` be a family in a linear order whose sublevel sets `{i | f i ≤ a}` are all finite,
on an infinite index type `ι`. Then `ι` can be enumerated by `ℕ` so that the values of `f` are
listed in nondecreasing order, each value repeated as often as it is taken
(`exists_equiv_monotone_comp_of_finite_setOf_le`), and along any such enumeration the values tend
to infinity (`tendsto_comp_atTop_of_finite_setOf_le`). The finiteness hypothesis is the field of
`Northcott f`, taken as an explicit hypothesis.

This is how the eigenvalues of an operator with discrete spectrum, such as the Dirichlet
eigenvalues of an elliptic operator on a bounded domain, are written as a sequence
`λ₁ ≤ λ₂ ≤ ⋯ → ∞` counted with multiplicity: the family is indexed by an orthonormal basis of
eigenvectors, and finiteness of the sublevel sets is the discreteness of the spectrum together
with the finiteness of the multiplicities.

The enumeration sorts `ι` lexicographically by the value of `f` and, among indices with equal
values, by an arbitrary well-ordering of `ι`; each index is then sent to the number of indices
below it (`ncardIioOrderEmbedding`), which is finite. For any linear order whose strict initial
segments `Set.Iio a` are finite, `ncardIioOrderEmbedding` embeds it order-preservingly into `ℕ`, and
for a strictly increasing tail after a finite prefix, the rank equals the prefix cardinality plus
the tail index (`ncard_Iio_eq_ncard_add_of_strictMono`).
-/

public section

namespace TauCeti

open Filter Set

/-- When every strict initial segment `Set.Iio a` of a linear order is finite, the rank map
`a ↦ (Set.Iio a).ncard` is an order embedding into `ℕ`. -/
noncomputable def ncardIioOrderEmbedding {α : Type*} [LinearOrder α]
    (hfin : ∀ a : α, (Set.Iio a).Finite) : α ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun a ↦ (Set.Iio a).ncard) fun _ b hab ↦
    ncard_lt_ncard ⟨fun _ hc ↦ hc.trans hab, fun hsub ↦ lt_irrefl _ (hsub hab)⟩ (hfin b)

/-- Evaluation of `TauCeti.ncardIioOrderEmbedding`. -/
@[simp]
theorem ncardIioOrderEmbedding_apply {α : Type*} [LinearOrder α]
    (hfin : ∀ a : α, (Set.Iio a).Finite) (a : α) :
    ncardIioOrderEmbedding hfin a = (Set.Iio a).ncard :=
  (rfl)

/-- If `A : Set α` is a finite prefix strictly preceding a strictly increasing tail `z : ℕ → α`
that together exhaust `α`, then `z n` has rank `(Set.Iio (z n)).ncard = A.ncard + n`. -/
theorem ncard_Iio_eq_ncard_add_of_strictMono {α : Type*} [LinearOrder α]
    {A : Set α} (hA : A.Finite) {z : ℕ → α} (hz : StrictMono z)
    (hA_lt : ∀ a ∈ A, ∀ m, a < z m) (hexh : ∀ a : α, a ∈ A ∨ ∃ m, a = z m) (n : ℕ) :
    (Set.Iio (z n)).ncard = A.ncard + n := by
  have hIio : Set.Iio (z n) = A ∪ z '' (Finset.range n : Set ℕ) := by
    ext a
    constructor
    · intro ha
      rcases hexh a with haA | ⟨m, rfl⟩
      · exact .inl haA
      · exact .inr ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr (hz.lt_iff_lt.mp ha)), rfl⟩
    · rintro (haA | ⟨m, hm, rfl⟩)
      · exact hA_lt a haA n
      · exact hz (Finset.mem_range.mp (Finset.mem_coe.mp hm))
  have hdisj : Disjoint A (z '' (Finset.range n : Set ℕ)) :=
    Set.disjoint_left.mpr fun _ haA ⟨m, _, ham⟩ => (hA_lt _ haA m).ne ham.symm
  rw [hIio, Set.ncard_union_eq hdisj hA ((Finset.range n).finite_toSet.image z),
    Set.ncard_image_of_injective _ hz.injective, Set.ncard_coe_finset, Finset.card_range]

/-- **Nondecreasing enumeration.** If `f : ι → α` has finite sublevel sets on an infinite type
`ι`, there is a bijection `e : ℕ ≃ ι` along which `f` is nondecreasing: `f (e 0) ≤ f (e 1) ≤ ⋯`.
Every index occurs exactly once, so each value of `f` is listed as often as it is taken. -/
theorem exists_equiv_monotone_comp_of_finite_setOf_le {ι α : Type*} [Infinite ι] [LinearOrder α]
    (f : ι → α) (hf : ∀ a, {i | f i ≤ a}.Finite) : ∃ e : ℕ ≃ ι, Monotone (f ∘ e) := by
  classical
  -- Break the ties of `f` by an arbitrary well-ordering of `ι`.
  let key : ι → α ×ₗ Cardinal := fun i ↦ toLex (f i, embeddingToCardinal i)
  have hkey : Function.Injective key := fun i j h ↦
    embeddingToCardinal.injective (Prod.ext_iff.1 (toLex.injective h)).2
  have hkey_le {i j : ι} (h : key i ≤ key j) : f i ≤ f j := by
    simpa only [key, ofLex_toLex] using Prod.Lex.monotone_fst _ _ h
  let : LinearOrder ι := LinearOrder.lift' key hkey
  let r : ι ↪o ℕ := ncardIioOrderEmbedding fun i ↦
    (hf (f i)).subset fun _ hj ↦ hkey_le (le_of_lt hj)
  have : Infinite (range r) := (infinite_range_of_injective r.injective).to_subtype
  let e : ℕ ≃ ι := (Nat.Subtype.orderIsoOfNat (range r)).toEquiv.trans
    (Equiv.ofInjective r r.injective).symm
  have hre (m : ℕ) : r (e m) = Nat.Subtype.orderIsoOfNat (range r) m :=
    Equiv.apply_ofInjective_symm r.injective _
  refine ⟨e, fun m n hmn ↦ hkey_le (r.le_iff_le.mp ?_)⟩
  rw [hre, hre]
  exact (Nat.Subtype.orderIsoOfNat (range r)).monotone hmn

/-- Along any injective enumeration `e : ℕ → ι`, a family with finite sublevel sets tends to
infinity. -/
theorem tendsto_comp_atTop_of_finite_setOf_le {ι α : Type*} [LinearOrder α] {f : ι → α}
    (hf : ∀ a, {i | f i ≤ a}.Finite) {e : ℕ → ι} (he : Function.Injective e) :
    Tendsto (f ∘ e) atTop atTop := by
  rw [← Nat.cofinite_eq_atTop]
  refine tendsto_atTop.2 fun a ↦ eventually_cofinite.2 ?_
  exact ((hf a).preimage he.injOn).subset fun k hk ↦ le_of_lt (not_le.1 hk)

end TauCeti
