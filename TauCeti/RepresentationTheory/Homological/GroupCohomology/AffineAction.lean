/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Abel

/-!
# Affine action of a group associated to a 1-cocycle

Given a group `G` acting linearly on an abelian group `M` and a `1`-cocycle `c : G → M`
(`groupCohomology.IsCocycle₁ c`), the assignment `g ↦ (u ↦ g • u + c g)` defines a group
homomorphism `TauCeti.cocycleAffineAction hc : G →* Equiv.Perm M`.

When an element `g : G` acts on `M` by a scalar `α : R` of a ring `R`, its `k`-th iterate acts by
`u ↦ α ^ k • u + (∑ i ∈ Finset.range k, α ^ i) • c g` (`TauCeti.cocycleAffineAction_pow_apply`),
so the affine map has `k`-th power `1` whenever `∑ i ∈ Finset.range k, α ^ i = 0`
(`TauCeti.cocycleAffineAction_pow_eq_one`). Moreover, if the affine maps at `φ` and `γ` commute,
then `φ • c γ - c γ = γ • c φ - c φ` (`TauCeti.smul_sub_eq_of_commute_cocycleAffineAction`), and
this relation passes from `φ` to `φ⁻¹` whenever `γ` acts by a scalar commuting with `G`
(`TauCeti.inv_smul_sub_eq_of_smul_eq`).

## Main results

* `TauCeti.cocycleAffineAction`: the affine permutation action `G →* Equiv.Perm M` of a 1-cocycle.
* `TauCeti.cocycleAffineAction_pow_apply`: iterate formula when `g` acts by a scalar `α`.
* `TauCeti.cocycleAffineAction_pow_eq_one`: `k`-th power triviality when `∑ i < k, α ^ i = 0`.
* `TauCeti.smul_sub_eq_of_commute_cocycleAffineAction`: commutation of affine maps yields
  `φ • c γ - c γ = γ • c φ - c φ`.
* `TauCeti.inv_smul_sub_eq_of_smul_eq`: passing the commutation relation from `φ` to `φ⁻¹`.

## Provenance

Adapted from grh-lean (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/Congruences/Selmer/Untied.lean`, declarations `New.Selmer.affineAction_pow_apply`,
`New.Selmer.affineAction_pow_eq_one`, `New.Selmer.sub_one_smul_eq_of_commute`, and
`New.Selmer.inv_sub_one_smul_eq`, generalized from Galois matrix representations to arbitrary
group actions and `groupCohomology.IsCocycle₁`.
-/

public section

namespace TauCeti

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M] {c : G → M}

/-- The affine action `g ↦ (u ↦ g • u + c g)` of a group `G` on `M` associated to a 1-cocycle
`c : G → M`. -/
def cocycleAffineAction (hc : groupCohomology.IsCocycle₁ c) : G →* Equiv.Perm M where
  toFun g :=
    { toFun := fun u ↦ g • u + c g
      invFun := fun u ↦ g⁻¹ • (u - c g)
      left_inv := fun u ↦ by simp
      right_inv := fun u ↦ by simp [smul_sub] }
  map_one' := by
    ext u
    have h1 : c 1 = 0 := by simpa using hc 1 1
    simp [h1]
  map_mul' g h := by
    ext u
    simp [hc g h, smul_add, mul_smul, add_assoc]

/-- If `g : G` acts on `M` by a scalar `α : R`, then the `k`-th iterate of its affine action
sends `u` to `α ^ k • u + (∑ i ∈ Finset.range k, α ^ i) • c g`. -/
theorem cocycleAffineAction_pow_apply {R : Type*} [Ring R] [Module R M]
    (hc : groupCohomology.IsCocycle₁ c) {g : G} {α : R} (hg : ∀ u : M, g • u = α • u)
    (k : ℕ) (u : M) :
    (cocycleAffineAction hc g ^ k) u =
      α ^ k • u + (∑ i ∈ Finset.range k, α ^ i) • c g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    change g • (α ^ k • u + (∑ i ∈ Finset.range k, α ^ i) • c g) + c g = _
    rw [hg, smul_add, smul_smul, smul_smul, ← pow_succ', geom_sum_succ, add_smul, one_smul]
    abel

/-- If `g : G` acts on `M` by a scalar `α : R` with `∑ i ∈ Finset.range k, α ^ i = 0`, then the
`k`-th power of `cocycleAffineAction hc g` is `1`. -/
theorem cocycleAffineAction_pow_eq_one {R : Type*} [Ring R] [Module R M]
    (hc : groupCohomology.IsCocycle₁ c) {g : G} {α : R} (hg : ∀ u : M, g • u = α • u) {k : ℕ}
    (hα : ∑ i ∈ Finset.range k, α ^ i = 0) :
    cocycleAffineAction hc g ^ k = 1 := by
  have hpow : α ^ k = 1 := by
    have hmul : (∑ i ∈ Finset.range k, α ^ i) * (α - 1) = α ^ k - 1 := geom_sum_mul α k
    rw [hα, zero_mul] at hmul
    exact sub_eq_zero.mp hmul.symm
  ext u
  simp [cocycleAffineAction_pow_apply hc hg, hα, hpow]

/-- If the affine maps of a 1-cocycle `c` at `φ` and `γ` commute, then
`φ • c γ - c γ = γ • c φ - c φ`. -/
theorem smul_sub_eq_of_commute_cocycleAffineAction (hc : groupCohomology.IsCocycle₁ c) {φ γ : G}
    (hcomm : Commute (cocycleAffineAction hc φ) (cocycleAffineAction hc γ)) :
    φ • c γ - c γ = γ • c φ - c φ := by
  have hswap : φ • c γ + c φ = γ • c φ + c γ := by
    simpa [cocycleAffineAction] using DFunLike.congr_fun hcomm.eq 0
  rw [sub_eq_sub_iff_add_eq_add]
  exact hswap

/-- If `γ` acts on `M` by a scalar `α : R` commuting with `G` and `φ • c γ - c γ = γ • c φ - c φ`,
then the same relation holds with `φ⁻¹` in place of `φ`. -/
theorem inv_smul_sub_eq_of_smul_eq {R : Type*} [Ring R] [Module R M] [SMulCommClass G R M]
    (hc : groupCohomology.IsCocycle₁ c) {φ γ : G} {α : R} (hγ : ∀ u : M, γ • u = α • u)
    (hrel : φ • c γ - c γ = γ • c φ - c φ) :
    φ⁻¹ • c γ - c γ = γ • c φ⁻¹ - c φ⁻¹ := by
  have hcinv : c φ⁻¹ = -(φ⁻¹ • c φ) := by
    have h0 : c 1 = 0 := by simpa using hc 1 1
    have h1 := hc φ⁻¹ φ
    rw [inv_mul_cancel, h0] at h1
    exact eq_neg_of_add_eq_zero_right h1.symm
  calc φ⁻¹ • c γ - c γ
    _ = -(φ⁻¹ • (φ • c γ - c γ)) := by rw [smul_sub, inv_smul_smul, neg_sub]
    _ = -(φ⁻¹ • (γ • c φ - c φ)) := by rw [hrel]
    _ = γ • c φ⁻¹ - c φ⁻¹ := by
      rw [hcinv, hγ, hγ, smul_neg, smul_sub, smul_comm, neg_sub, sub_neg_eq_add, neg_add_eq_sub]

end TauCeti
