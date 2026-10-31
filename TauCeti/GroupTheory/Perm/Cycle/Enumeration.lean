/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Enumerating a finite set along the cycles of a permutation

Let `σ` be a permutation of a finite type `α`, and let `rep : J → α` pick exactly one point on every
cycle of `σ`, that is `∀ x, ∃! j, σ.SameCycle (rep j) x`. The representatives `Quotient.out` of the
cycle quotient are one such choice (`Equiv.Perm.existsUnique_sameCycle_out`). Each point of `α` is
`σ ^ i` of exactly one representative `rep j`, with `i` less than the length
`Function.minimalPeriod σ (rep j)` of its cycle. This file packages that enumeration as an
equivalence

`Equiv.Perm.sigmaCycleEquiv σ rep hrep : (Σ j, Fin (minimalPeriod σ (rep j) - 1 + 1)) ≃ α`,
`⟨j, i⟩ ↦ (σ ^ i) (rep j)`,

under which `σ` becomes the cyclic shift `finRotate` on every fibre
(`Equiv.Perm.sigmaCycleEquiv_finRotate`). The length is written `(… - 1) + 1` because cycles of a
finite type are nonempty, and an enumeration of this form is what a decomposition of a basis into
weighted cycles takes as input: for a linear map permuting a basis up to scalars, it identifies
the fixed vectors cycle by cycle.

Mathlib's `MulAction.selfEquivSigmaOrbits` combined with `MulAction.orbitZPowersEquiv` gives the
same decomposition with fibres `ZMod (minimalPeriod σ x)` over the orbits of `Subgroup.zpowers σ`.
The form here is indexed by an arbitrary choice of cycle representatives and has `Fin` fibres, on
which `σ` is `finRotate`.

## Main definitions

* `Equiv.Perm.sigmaCycleEquiv`: the enumeration of `α` along the cycles of `σ`.

## Main results

* `Equiv.Perm.existsUnique_sameCycle_out`: the representatives `Quotient.out` of the cycle quotient
  pick exactly one point on every cycle.
* `Equiv.Perm.finite_of_existsUnique_sameCycle`: a choice of one point on every cycle of a
  permutation of a finite type is indexed by a finite type.
* `Equiv.Perm.sigmaCycleEquiv_finRotate`: `σ` acts as the cyclic shift on every cycle.
* `Equiv.Perm.sigmaCycleEquiv_symm_fst`: a point lies in the enumerated cycle it belongs to.
* `Equiv.Perm.prod_range_minimalPeriod`: a product over the iterates of a point below the length
  of its cycle is the product over the points of that cycle.
* `Equiv.Perm.prod_fin_eq_prod_range_minimalPeriod`,
  `Equiv.Perm.prod_sigmaCycleEquiv_eq_prod_range`: a product along an enumerated cycle is the
  product over the iterates of its representative below the length of the cycle.
* `Equiv.Perm.partialProd_init_sigmaCycleEquiv`: the prefix products along an enumerated cycle are
  the products over the first `i` iterates of its representative.
-/

public section

open Function

namespace Equiv.Perm

variable {α : Type*} (σ : Perm α)

/-- A point lies in the cycle `O` exactly when it lies in the cycle of the representative
`O.out`. -/
theorem sameCycle_out_iff {x : α} {O : Quotient (SameCycle.setoid σ)} :
    σ.SameCycle O.out x ↔ (⟦x⟧ : Quotient (SameCycle.setoid σ)) = O := by
  conv_rhs => rw [← Quotient.out_eq O]
  exact ⟨fun h ↦ Quotient.sound h.symm, fun h ↦ (Quotient.exact h).symm⟩

/-- The iterates of the representative of a cycle stay in that cycle. -/
@[simp]
theorem mk_pow_apply_out (O : Quotient (SameCycle.setoid σ)) (n : ℕ) :
    (⟦(σ ^ n) O.out⟧ : Quotient (SameCycle.setoid σ)) = O :=
  (σ.sameCycle_out_iff).mp ⟨(n : ℤ), by simp⟩

/-- The representatives `Quotient.out` pick exactly one point on every cycle. -/
theorem existsUnique_sameCycle_out (x : α) :
    ∃! O : Quotient (SameCycle.setoid σ), σ.SameCycle O.out x :=
  ⟨⟦x⟧, σ.sameCycle_out_iff.mpr rfl, fun _ h ↦ (σ.sameCycle_out_iff.mp h).symm⟩

variable {J : Type*} (rep : J → α) (hrep : ∀ x, ∃! j, σ.SameCycle (rep j) x)

include hrep in
/-- Distinct cycles have distinct representatives. -/
theorem injective_of_existsUnique_sameCycle : Injective rep := fun j k h ↦
  (hrep (rep k)).unique (h ▸ SameCycle.refl σ (rep j)) (SameCycle.refl σ (rep k))

variable [Finite α]

include hrep in
/-- A choice of one point on every cycle of a permutation of a finite type is indexed by a finite
type. -/
theorem finite_of_existsUnique_sameCycle : Finite J :=
  Finite.of_injective rep (σ.injective_of_existsUnique_sameCycle rep hrep)

/-- Every point of a finite type has positive period under a permutation, so its period is the
successor of its predecessor. -/
theorem minimalPeriod_sub_one_add_one (x : α) :
    minimalPeriod σ x - 1 + 1 = minimalPeriod σ x :=
  Nat.sub_add_cancel (minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x))

include hrep in
private theorem bijective_sigmaCycle :
    Bijective fun x : Σ j : J, Fin (minimalPeriod σ (rep j) - 1 + 1) ↦
      (σ ^ (x.2 : ℕ)) (rep x.1) := by
  refine ⟨?_, fun y ↦ ?_⟩
  · rintro ⟨j, i⟩ ⟨k, l⟩ h
    dsimp only at h
    obtain rfl : j = k := (hrep ((σ ^ (l : ℕ)) (rep k))).unique
      (h ▸ ⟨(i : ℤ), by simp⟩) ⟨(l : ℤ), by simp⟩
    have hi := lt_of_lt_of_eq i.isLt (σ.minimalPeriod_sub_one_add_one (rep j))
    have hl := lt_of_lt_of_eq l.isLt (σ.minimalPeriod_sub_one_add_one (rep j))
    rw [coe_pow, coe_pow, iterate_eq_iterate_iff_of_lt_minimalPeriod hi hl] at h
    rw [Fin.ext h]
  · obtain ⟨j, hj, -⟩ := hrep y
    obtain ⟨k, hk⟩ := hj.exists_nat_pow_eq
    have hpos := minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts (rep j))
    refine ⟨⟨j, ⟨k % minimalPeriod σ (rep j), ?_⟩⟩, ?_⟩
    · rw [minimalPeriod_sub_one_add_one]
      exact Nat.mod_lt k hpos
    · dsimp only
      rw [coe_pow, iterate_mod_minimalPeriod_eq, ← coe_pow, hk]

/-- **The enumeration of a finite type along the cycles of a permutation.** The pair `⟨j, i⟩` of a
cycle representative `rep j` of `σ` and an index `i` below the length
`Function.minimalPeriod σ (rep j)` of its cycle goes to the iterate `(σ ^ i) (rep j)`. The length is
written `(minimalPeriod σ (rep j) - 1) + 1`, which is the length since cycles are nonempty. -/
noncomputable def sigmaCycleEquiv :
    (Σ j : J, Fin (minimalPeriod σ (rep j) - 1 + 1)) ≃ α :=
  Equiv.ofBijective _ (σ.bijective_sigmaCycle rep hrep)

@[simp]
theorem sigmaCycleEquiv_apply (j : J) (i : Fin (minimalPeriod σ (rep j) - 1 + 1)) :
    σ.sigmaCycleEquiv rep hrep ⟨j, i⟩ = (σ ^ (i : ℕ)) (rep j) := by
  simp [sigmaCycleEquiv]

/-- `σ` acts as the cyclic shift `finRotate` on every enumerated cycle. -/
theorem sigmaCycleEquiv_finRotate (j : J) (i : Fin (minimalPeriod σ (rep j) - 1 + 1)) :
    σ.sigmaCycleEquiv rep hrep ⟨j, finRotate _ i⟩ = σ (σ.sigmaCycleEquiv rep hrep ⟨j, i⟩) := by
  rw [sigmaCycleEquiv_apply, sigmaCycleEquiv_apply, coe_pow, coe_pow,
    ← iterate_succ_apply' (⇑σ) (i : ℕ) (rep j), coe_finRotate]
  split_ifs with h
  · simp only [h, Fin.val_last, Nat.succ_eq_add_one, minimalPeriod_sub_one_add_one,
      iterate_zero_apply, iterate_minimalPeriod]
  · rfl

/-- The points enumerated along the cycle of `rep j` are points of that cycle. -/
theorem sameCycle_sigmaCycleEquiv (j : J) (i : Fin (minimalPeriod σ (rep j) - 1 + 1)) :
    σ.SameCycle (rep j) (σ.sigmaCycleEquiv rep hrep ⟨j, i⟩) :=
  ⟨(i : ℤ), by simp⟩

/-- The enumerated cycle containing a point is the cycle of that point. -/
theorem sigmaCycleEquiv_symm_fst {x : α} {j : J} (h : σ.SameCycle (rep j) x) :
    ((σ.sigmaCycleEquiv rep hrep).symm x).1 = j := by
  obtain ⟨⟨k, i⟩, rfl⟩ := (σ.sigmaCycleEquiv rep hrep).surjective x
  rw [Equiv.symm_apply_apply]
  exact (hrep _).unique (σ.sameCycle_sigmaCycleEquiv rep hrep k i) h

/-- A product over the iterates of a point below the length of its cycle is the product over the
points of that cycle. -/
@[to_additive /-- A sum over the iterates of a point below the length of its cycle is the sum over
the points of that cycle. -/]
theorem prod_range_minimalPeriod [Fintype α] [DecidableRel σ.SameCycle] {M : Type*}
    [CommMonoid M] (f : α → M) (x : α) :
    ∏ k ∈ Finset.range (minimalPeriod σ x), f ((σ ^ k) x) = ∏ y with σ.SameCycle x y, f y := by
  refine Finset.prod_bij (fun k _ ↦ (σ ^ k) x)
    (fun k _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨(k : ℤ), by simp⟩⟩)
    (fun k hk l hl h ↦ ?_) (fun y hy ↦ ?_) (fun _ _ ↦ rfl)
  · rw [coe_pow, coe_pow] at h
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod (Finset.mem_range.mp hk)
      (Finset.mem_range.mp hl)).mp h
  · obtain ⟨k, rfl⟩ := (Finset.mem_filter.mp hy).2.exists_nat_pow_eq
    have hpos := minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)
    refine ⟨k % minimalPeriod σ x, Finset.mem_range.mpr (Nat.mod_lt k hpos), ?_⟩
    rw [coe_pow, coe_pow, iterate_mod_minimalPeriod_eq]

/-- A product over the positions `Fin (minimalPeriod σ x - 1 + 1)` of the cycle of `x` is the
product over the natural numbers below the length of that cycle. -/
@[to_additive /-- A sum over the positions `Fin (minimalPeriod σ x - 1 + 1)` of the cycle of `x`
is the sum over the natural numbers below the length of that cycle. -/]
theorem prod_fin_eq_prod_range_minimalPeriod {M : Type*} [CommMonoid M] (x : α) (f : ℕ → M) :
    ∏ i : Fin (minimalPeriod σ x - 1 + 1), f i = ∏ k ∈ Finset.range (minimalPeriod σ x), f k := by
  rw [Fin.prod_univ_eq_prod_range, minimalPeriod_sub_one_add_one]

/-- A product along an enumerated cycle is the product over the iterates of its representative
below the length of the cycle. -/
@[to_additive /-- A sum along an enumerated cycle is the sum over the iterates of its
representative below the length of the cycle. -/]
theorem prod_sigmaCycleEquiv_eq_prod_range {M : Type*} [CommMonoid M] (f : α → M) (j : J) :
    ∏ i, f (σ.sigmaCycleEquiv rep hrep ⟨j, i⟩) =
      ∏ k ∈ Finset.range (minimalPeriod σ (rep j)), f ((σ ^ k) (rep j)) := by
  simpa only [sigmaCycleEquiv_apply] using
    σ.prod_fin_eq_prod_range_minimalPeriod (rep j) fun k ↦ f ((σ ^ k) (rep j))

/-- The prefix products along an enumerated cycle are the products over the first `i` iterates of
its representative. -/
theorem partialProd_init_sigmaCycleEquiv {M : Type*} [CommMonoid M] (f : α → M) (j : J)
    (i : Fin (minimalPeriod σ (rep j) - 1 + 1)) :
    Fin.partialProd (Fin.init fun l ↦ f (σ.sigmaCycleEquiv rep hrep ⟨j, l⟩)) i =
      ∏ k ∈ Finset.range i, f ((σ ^ k) (rep j)) := by
  induction i using Fin.induction with
  | zero => simp
  | succ l ih =>
    rw [Fin.partialProd_succ, ih, Fin.val_succ, Finset.prod_range_succ]
    simp [Fin.init]

end Equiv.Perm
