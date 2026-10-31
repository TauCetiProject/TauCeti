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

Let `σ` be a permutation of a finite type `α`. Choosing the representative `O.out` of every cycle
`O` of `σ`, each point of `α` is `σ ^ i` of exactly one representative, with `i` less than the
length `Function.minimalPeriod σ O.out` of the cycle. This file packages that enumeration as an
equivalence

`Equiv.Perm.sigmaCycleEquiv σ : (Σ O, Fin (minimalPeriod σ O.out - 1 + 1)) ≃ α`,
`⟨O, i⟩ ↦ (σ ^ i) O.out`,

under which `σ` becomes the cyclic shift `finRotate` on every fibre
(`Equiv.Perm.sigmaCycleEquiv_finRotate`). The length is written `(… - 1) + 1` because cycles of a
finite type are nonempty, and an enumeration of this form is what a decomposition of a basis into
weighted cycles takes as input: for a linear map permuting a basis up to scalars, it identifies
the fixed vectors cycle by cycle.

Mathlib's `MulAction.selfEquivSigmaOrbits` combined with `MulAction.orbitZPowersEquiv` gives the
same decomposition with fibres `ZMod (minimalPeriod σ x)` over the orbits of `Subgroup.zpowers σ`.
The form here is indexed by the `Equiv.Perm.SameCycle` quotient and has `Fin` fibres, on which `σ`
is `finRotate`.

## Main definitions

* `Equiv.Perm.sigmaCycleEquiv`: the enumeration of `α` along the cycles of `σ`.

## Main results

* `Equiv.Perm.sigmaCycleEquiv_finRotate`: `σ` acts as the cyclic shift on every cycle.
* `Equiv.Perm.sigmaCycleEquiv_symm_fst`: a point lies in the enumerated cycle it belongs to.
* `Equiv.Perm.prod_sigmaCycleEquiv`, `Equiv.Perm.prod_range_minimalPeriod_out`: a product along
  an enumerated cycle is the product over the points of that cycle.
* `Equiv.Perm.prod_sigmaCycleEquiv_eq_prod_range`: it is also the product over the iterates of the
  representative below the length of the cycle.
* `Equiv.Perm.partialProd_init_sigmaCycleEquiv`: the prefix products along an enumerated cycle are
  the products over the first `i` iterates of its representative.
-/

public section

open Function

namespace Equiv.Perm

variable {α : Type*} (σ : Perm α)

private theorem sameCycle_out_iff {x : α} {O : Quotient (SameCycle.setoid σ)} :
    σ.SameCycle O.out x ↔ (⟦x⟧ : Quotient (SameCycle.setoid σ)) = O := by
  conv_rhs => rw [← Quotient.out_eq O]
  exact ⟨fun h ↦ Quotient.sound h.symm, fun h ↦ (Quotient.exact h).symm⟩

private theorem mk_pow_apply_out (O : Quotient (SameCycle.setoid σ)) (n : ℕ) :
    (⟦(σ ^ n) O.out⟧ : Quotient (SameCycle.setoid σ)) = O :=
  (σ.sameCycle_out_iff).mp ⟨(n : ℤ), by simp⟩

private theorem pow_apply_eq_iterate (x : α) (n : ℕ) : (σ ^ n) x = σ^[n] x := by
  rw [← coe_pow]

variable [Finite α]

/-- Every point of a finite type has positive period under a permutation, so its period is the
successor of its predecessor. -/
theorem minimalPeriod_sub_one_add_one (x : α) :
    minimalPeriod σ x - 1 + 1 = minimalPeriod σ x :=
  Nat.sub_add_cancel (minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x))

private theorem bijective_sigmaCycle :
    Bijective fun x : Σ O : Quotient (SameCycle.setoid σ), Fin (minimalPeriod σ O.out - 1 + 1) ↦
      (σ ^ (x.2 : ℕ)) x.1.out := by
  refine ⟨?_, fun y ↦ ?_⟩
  · rintro ⟨O, i⟩ ⟨P, j⟩ h
    dsimp only at h
    obtain rfl : O = P := by rw [← σ.mk_pow_apply_out O i, ← σ.mk_pow_apply_out P j, h]
    have hi := lt_of_lt_of_eq i.isLt (σ.minimalPeriod_sub_one_add_one O.out)
    have hj := lt_of_lt_of_eq j.isLt (σ.minimalPeriod_sub_one_add_one O.out)
    rw [pow_apply_eq_iterate, pow_apply_eq_iterate,
      iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj] at h
    rw [Fin.ext h]
  · set O : Quotient (SameCycle.setoid σ) := ⟦y⟧
    obtain ⟨k, hk⟩ := ((σ.sameCycle_out_iff (O := O)).mpr rfl).exists_nat_pow_eq
    have hpos := minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts O.out)
    refine ⟨⟨O, ⟨k % minimalPeriod σ O.out, ?_⟩⟩, ?_⟩
    · rw [minimalPeriod_sub_one_add_one]
      exact Nat.mod_lt k hpos
    · dsimp only
      rw [pow_apply_eq_iterate, iterate_mod_minimalPeriod_eq, ← pow_apply_eq_iterate, hk]

/-- **The enumeration of a finite type along the cycles of a permutation.** The pair `⟨O, i⟩` of a
cycle `O` of `σ` and an index `i` below its length `Function.minimalPeriod σ O.out` goes to
`(σ ^ i) O.out`, an iterate of the chosen representative of `O`. The length is written
`(minimalPeriod σ O.out - 1) + 1`, which is the length since cycles are nonempty. -/
noncomputable def sigmaCycleEquiv :
    (Σ O : Quotient (SameCycle.setoid σ), Fin (minimalPeriod σ O.out - 1 + 1)) ≃ α :=
  Equiv.ofBijective _ σ.bijective_sigmaCycle

@[simp]
theorem sigmaCycleEquiv_apply (O : Quotient (SameCycle.setoid σ))
    (i : Fin (minimalPeriod σ O.out - 1 + 1)) :
    σ.sigmaCycleEquiv ⟨O, i⟩ = (σ ^ (i : ℕ)) O.out := by
  simp [sigmaCycleEquiv]

/-- `σ` acts as the cyclic shift `finRotate` on every enumerated cycle. -/
theorem sigmaCycleEquiv_finRotate (O : Quotient (SameCycle.setoid σ))
    (i : Fin (minimalPeriod σ O.out - 1 + 1)) :
    σ.sigmaCycleEquiv ⟨O, finRotate _ i⟩ = σ (σ.sigmaCycleEquiv ⟨O, i⟩) := by
  rw [sigmaCycleEquiv_apply, sigmaCycleEquiv_apply, pow_apply_eq_iterate, pow_apply_eq_iterate,
    ← iterate_succ_apply' (⇑σ) (i : ℕ) O.out, coe_finRotate]
  split_ifs with h
  · simp only [h, Fin.val_last, Nat.succ_eq_add_one, minimalPeriod_sub_one_add_one,
      iterate_zero_apply, iterate_minimalPeriod]
  · rfl

/-- The enumerated cycle containing a point is the cycle of that point. -/
@[simp]
theorem sigmaCycleEquiv_symm_fst (x : α) :
    (σ.sigmaCycleEquiv.symm x).1 = ⟦x⟧ := by
  obtain ⟨⟨O, i⟩, rfl⟩ := σ.sigmaCycleEquiv.surjective x
  rw [Equiv.symm_apply_apply, sigmaCycleEquiv_apply]
  exact (σ.mk_pow_apply_out O i).symm

/-- The points enumerated along a cycle `O` are exactly the points of `O`. -/
theorem sameCycle_sigmaCycleEquiv_out (O : Quotient (SameCycle.setoid σ))
    (i : Fin (minimalPeriod σ O.out - 1 + 1)) :
    σ.SameCycle (σ.sigmaCycleEquiv ⟨O, i⟩) O.out :=
  ⟨-(i : ℤ), by simp [zpow_neg, zpow_natCast]⟩

/-- A product along an enumerated cycle is the product over the points of that cycle. -/
@[to_additive /-- A sum along an enumerated cycle is the sum over the points of that cycle. -/]
theorem prod_sigmaCycleEquiv [Fintype α] [DecidableRel σ.SameCycle] {M : Type*} [CommMonoid M]
    (f : α → M) (O : Quotient (SameCycle.setoid σ)) :
    ∏ i, f (σ.sigmaCycleEquiv ⟨O, i⟩) = ∏ x with σ.SameCycle x O.out, f x := by
  refine Finset.prod_bij (fun i _ ↦ σ.sigmaCycleEquiv ⟨O, i⟩)
    (fun i _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.sameCycle_sigmaCycleEquiv_out O i⟩)
    (fun i _ j _ h ↦ eq_of_heq (Sigma.mk.inj (σ.sigmaCycleEquiv.injective h)).2)
    (fun x hx ↦ ?_) (fun _ _ ↦ rfl)
  obtain ⟨⟨P, j⟩, rfl⟩ := σ.sigmaCycleEquiv.surjective x
  obtain rfl : P = O := (σ.mk_pow_apply_out P j).symm.trans
    (by simpa using (σ.sameCycle_out_iff).mp (Finset.mem_filter.mp hx).2.symm)
  exact ⟨j, Finset.mem_univ _, rfl⟩

/-- A product along an enumerated cycle is the product over the iterates of its representative
below the length of the cycle. -/
@[to_additive /-- A sum along an enumerated cycle is the sum over the iterates of its
representative below the length of the cycle. -/]
theorem prod_sigmaCycleEquiv_eq_prod_range {M : Type*} [CommMonoid M] (f : α → M)
    (O : Quotient (SameCycle.setoid σ)) :
    ∏ i, f (σ.sigmaCycleEquiv ⟨O, i⟩) =
      ∏ k ∈ Finset.range (minimalPeriod σ O.out), f ((σ ^ k) O.out) := by
  conv_rhs => rw [← σ.minimalPeriod_sub_one_add_one O.out]
  rw [← Fin.prod_univ_eq_prod_range (fun k ↦ f ((σ ^ k) O.out))]
  simp

/-- The product over the iterates of a representative below the length of its cycle is the
product over the points of that cycle. -/
@[to_additive /-- The sum over the iterates of a representative below the length of its cycle is
the sum over the points of that cycle. -/]
theorem prod_range_minimalPeriod_out [Fintype α] [DecidableRel σ.SameCycle] {M : Type*}
    [CommMonoid M] (f : α → M) (O : Quotient (SameCycle.setoid σ)) :
    ∏ k ∈ Finset.range (minimalPeriod σ O.out), f ((σ ^ k) O.out) =
      ∏ x with σ.SameCycle x O.out, f x := by
  rw [← σ.prod_sigmaCycleEquiv f O, σ.prod_sigmaCycleEquiv_eq_prod_range]

/-- The prefix products along an enumerated cycle are the products over the first `i` iterates of
its representative. -/
theorem partialProd_init_sigmaCycleEquiv {M : Type*} [CommMonoid M] (f : α → M)
    (O : Quotient (SameCycle.setoid σ)) (i : Fin (minimalPeriod σ O.out - 1 + 1)) :
    Fin.partialProd (Fin.init fun j ↦ f (σ.sigmaCycleEquiv ⟨O, j⟩)) i =
      ∏ k ∈ Finset.range i, f ((σ ^ k) O.out) := by
  induction i using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [Fin.partialProd_succ, ih, Fin.val_succ, Finset.prod_range_succ]
    simp [Fin.init]

end Equiv.Perm
