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
to infinity (`tendsto_comp_atTop_of_finite_setOf_le`).

This is how the eigenvalues of an operator with discrete spectrum, such as the Dirichlet
eigenvalues of an elliptic operator on a bounded domain, are written as a sequence
`λ₁ ≤ λ₂ ≤ ⋯ → ∞` counted with multiplicity: the family is indexed by an orthonormal basis of
eigenvectors, and finiteness of the sublevel sets is the discreteness of the spectrum together
with the finiteness of the multiplicities.

The enumeration sorts `ι` lexicographically by the value of `f` and, among indices with equal
values, by an arbitrary well-ordering of `ι`; each index is then sent to the number of indices
below it, which is finite.
-/

public section

open Filter Set

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
  have hfin (i : ι) : {j | key j < key i}.Finite :=
    (hf (f i)).subset fun _ hj ↦ hkey_le (le_of_lt hj)
  -- The rank of `i` is the number of indices below it.
  let r : ι → ℕ := fun i ↦ {j | key j < key i}.ncard
  have hr {i j : ι} (h : key i < key j) : r i < r j :=
    ncard_lt_ncard ⟨fun _ (hk : key _ < key i) ↦ hk.trans h,
      fun hsub ↦ lt_irrefl (key i) (hsub h)⟩ (hfin j)
  have hr_le {i j : ι} (h : r i ≤ r j) : key i ≤ key j := le_of_not_gt fun hlt ↦
    (hr hlt).not_ge h
  have hr_inj : Function.Injective r := fun i j h ↦
    hkey (le_antisymm (hr_le h.le) (hr_le h.ge))
  have : Infinite (range r) := (infinite_range_of_injective hr_inj).to_subtype
  let e : ℕ ≃ ι := (Nat.Subtype.orderIsoOfNat (range r)).toEquiv.trans
    (Equiv.ofInjective r hr_inj).symm
  have hre (m : ℕ) : r (e m) = Nat.Subtype.orderIsoOfNat (range r) m :=
    Equiv.apply_ofInjective_symm hr_inj _
  refine ⟨e, fun m n hmn ↦ ?_⟩
  have hkmn : key (e m) ≤ key (e n) := hr_le (by
    rw [hre, hre]
    exact (Nat.Subtype.orderIsoOfNat (range r)).monotone hmn)
  exact hkey_le hkmn

/-- Along any injective enumeration `e : ℕ → ι`, a family with finite sublevel sets tends to
infinity. -/
theorem tendsto_comp_atTop_of_finite_setOf_le {ι α : Type*} [LinearOrder α] {f : ι → α}
    (hf : ∀ a, {i | f i ≤ a}.Finite) {e : ℕ → ι} (he : Function.Injective e) :
    Tendsto (f ∘ e) atTop atTop := by
  rw [← Nat.cofinite_eq_atTop]
  refine tendsto_atTop.2 fun a ↦ eventually_cofinite.2 ?_
  exact ((hf a).preimage he.injOn).subset fun k hk ↦ le_of_lt (not_le.1 hk)
