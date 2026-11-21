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
every rank below its extended cardinality is attained (`exists_ncard_Iio_eq_of_finite_Iio`).
-/

public section

namespace TauCeti

open Filter Set

/-- When every strict initial segment `Set.Iio a` of a linear order is finite, the rank map
`a ↦ (Set.Iio a).ncard` is an order embedding into `ℕ`. -/
@[expose] noncomputable def ncardIioOrderEmbedding {α : Type*} [LinearOrder α]
    (hfin : ∀ a : α, (Set.Iio a).Finite) : α ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun a ↦ (Set.Iio a).ncard) fun _ b hab ↦
    ncard_lt_ncard ⟨fun _ hc ↦ hc.trans hab, fun hsub ↦ lt_irrefl _ (hsub hab)⟩ (hfin b)

/-- Evaluation of `TauCeti.ncardIioOrderEmbedding`. -/
@[simp]
theorem ncardIioOrderEmbedding_apply {α : Type*} [LinearOrder α]
    (hfin : ∀ a : α, (Set.Iio a).Finite) (a : α) :
    ncardIioOrderEmbedding hfin a = (Set.Iio a).ncard :=
  rfl

/-- In a linear order whose strict initial segments `Set.Iio a` are finite, every rank `n`
strictly below `ENat.card α` is attained as `(Set.Iio a).ncard = n`. -/
theorem exists_ncard_Iio_eq_of_finite_Iio {α : Type*} [LinearOrder α]
    (hfin : ∀ a : α, (Set.Iio a).Finite) :
    ∀ {n : ℕ}, (n : ℕ∞) < ENat.card α → ∃ a : α, (Set.Iio a).ncard = n
  | 0, hn => by
    classical
    have hne : Nonempty α := by
      by_contra hempty
      have := not_nonempty_iff.mp hempty
      rw [← Set.encard_univ, Set.eq_empty_of_isEmpty (univ : Set α)] at hn
      simp at hn
    obtain ⟨x⟩ := hne
    have hIic : Set.Iic x = insert x (Set.Iio x) := by ext; simp [le_iff_eq_or_lt]
    have hF : (Set.Iic x).Finite := hIic ▸ (hfin x).insert x
    let m : α := hF.toFinset.min' (hF.toFinset_nonempty.mpr ⟨x, le_rfl⟩)
    have hIio : Set.Iio m = ∅ := by
      ext y
      simp only [Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      have hm_le : m ≤ x := hF.mem_toFinset.mp (Finset.min'_mem _ _)
      by_contra hlt
      exact (Finset.min'_le _ y (hF.mem_toFinset.mpr ((not_le.mp hlt).le.trans hm_le))).not_gt
        (not_le.mp hlt)
    exact ⟨m, by rw [hIio, Set.ncard_empty]⟩
  | n + 1, hn => by
    classical
    obtain ⟨a, ha⟩ := exists_ncard_Iio_eq_of_finite_Iio hfin
      (lt_of_le_of_lt (Nat.cast_le.mpr (Nat.le_succ n)) hn)
    have hIic : Set.Iic a = insert a (Set.Iio a) := by ext; simp [le_iff_eq_or_lt]
    have ha_fin : (Set.Iic a).Finite := hIic ▸ (hfin a).insert a
    have ha_card : (Set.Iic a).ncard = n + 1 := by
      rw [hIic, Set.ncard_insert_of_notMem (lt_irrefl a) (hfin a), ha]
    have hex : (Set.Iic a)ᶜ.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hne
      have hcard : ENat.card α = (n + 1 : ℕ) := by
        rw [← Set.encard_univ, ← hne, ha_fin.encard_eq_coe_toFinset_card,
          ← Set.ncard_eq_toFinset_card _ ha_fin, ha_card]
      rw [hcard] at hn
      exact lt_irrefl _ hn
    obtain ⟨y, hy⟩ := hex
    have hay : a < y := not_le.mp hy
    have hS : (Set.Ioc a y).Finite := ((hfin y).insert y).subset fun x hx ↦ by
      rcases hx.2.eq_or_lt with rfl | hlt
      · exact Set.mem_insert x _
      · exact Set.mem_insert_of_mem y hlt
    let b : α := hS.toFinset.min' (hS.toFinset_nonempty.mpr ⟨y, hay, le_rfl⟩)
    have hb_mem : b ∈ Set.Ioc a y := hS.mem_toFinset.mp (Finset.min'_mem _ _)
    refine ⟨b, ?_⟩
    have hIio : Set.Iio b = Set.Iic a := by
      ext x
      constructor
      · intro hxb
        by_contra hax
        exact (Finset.min'_le _ x
          (hS.mem_toFinset.mpr ⟨not_le.mp hax, hxb.le.trans hb_mem.2⟩)).not_gt hxb
      · intro hxa
        exact hxa.trans_lt hb_mem.1
    rw [hIio, ha_card]

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
