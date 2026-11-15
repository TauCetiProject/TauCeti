/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.GroupTheory.SpecificGroups.Affine.Basic
import Mathlib.Data.Finite.Perm
import Mathlib.RingTheory.IntegralDomain
import TauCeti.GroupTheory.Perm.PermCongr
import TauCeti.GroupTheory.Perm.Recognition

/-!
# The affine group `AGL(1, F)` as a primitive permutation group

The one-dimensional affine group `TauCeti.AffineGroup F` of a division ring `F` acts on `F` by
`x ↦ b + a x`. This action is `2`-transitive: any two distinct points can be sent to any two
distinct points by an affine map. In particular it is primitive.

For a finite division ring with `q` elements the image of `AGL(1, F)` in the permutations of `F`
therefore has order `q (q - 1)`, which is smaller than the order `q! / 2` of the alternating group
as soon as `q ≥ 5`. It nevertheless contains long cycles, in two ways.

* For a finite field, multiplication by a generator of the cyclic group `Fˣ` is a single cycle
  of length `q - 1` fixing `0`.
* When `q` is prime, transitivity forces a cycle of length `q`.

These are the classical witnesses that the bound `p + 3 ≤ n` in Jordan's theorem
`TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` cannot be weakened to `p ≤ n` or to
`p + 1 ≤ n`: `AGL(1, 5)` is primitive of degree `5` and contains a `5`-cycle, and `AGL(1, 8)` is
primitive of degree `8` and contains a `7`-cycle, yet neither contains the alternating group. The
two counterexamples are stated in `TauCeti.GroupTheory.Perm.Jordan.Counterexamples`.

## Main results

* `TauCeti.AffineGroup.isPreprimitive`: `AGL(1, F)` acts primitively on `F`, being
  `2`-transitive.
* `TauCeti.AffineGroup.natCard_range_toPermHom`: the permutation image of `AGL(1, F)` has order
  `q (q - 1)`.
* `TauCeti.AffineGroup.not_alternatingGroup_le_range_toPermHom`: for `q ≥ 5` the image does not
  contain the alternating group.
* `TauCeti.AffineGroup.exists_isCycle_mem_range_toPermHom_support_eq_compl_zero`: over a finite
  field with at least three elements the image contains a cycle with support `{0}ᶜ`.
* `TauCeti.AffineGroup.exists_isCycle_mem_range_toPermHom_support_eq_univ`: in prime degree the
  image contains a full cycle.

## References

* H. Wielandt, *Finite Permutation Groups*, §13.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, §3.3 and §7.7.
-/

public section

open Equiv Equiv.Perm Finset MulAction

namespace TauCeti

namespace AffineGroup

section DivisionRing

variable {F : Type*} [DivisionRing F]

/-- The affine group of a division ring acts `2`-transitively on it: two distinct points can be
sent to any two distinct points by an affine map. -/
instance isMultiplyPretransitive_two : IsMultiplyPretransitive (AffineGroup F) F 2 := by
  rw [is_two_pretransitive_iff]
  intro a b c d hab hcd
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hs : (d - c) * (b - a)⁻¹ ≠ 0 := mul_ne_zero (sub_ne_zero.2 hcd.symm) (inv_ne_zero hba)
  set s := (d - c) * (b - a)⁻¹ with hs_def
  have h : s * (b - a) = d - c := by rw [hs_def, mul_assoc, inv_mul_cancel₀ hba, mul_one]
  refine ⟨⟨Multiplicative.ofAdd (c - s * a), Units.mk0 s hs⟩, ?_, ?_⟩
  · simp only [AffineGroup.smul_def, toAdd_ofAdd, Units.val_mk0, sub_add_cancel]
  · simp only [AffineGroup.smul_def, toAdd_ofAdd, Units.val_mk0]
    -- `c - s a + s b = c + s (b - a)`, and `s (b - a) = d - c` by the choice of `s`.
    rw [sub_add_eq_add_sub, add_sub_assoc, ← mul_sub, h, add_sub_cancel]

/-- The affine group of a division ring acts primitively on it. -/
instance isPreprimitive : IsPreprimitive (AffineGroup F) F :=
  isPreprimitive_of_is_two_pretransitive inferInstance

/-- The image of the affine group in the permutations of the division ring has order
`|F| (|F| - 1)`. -/
theorem natCard_range_toPermHom :
    Nat.card (toPermHom (AffineGroup F) F).range = Nat.card F * (Nat.card F - 1) :=
  (Nat.card_congr (MonoidHom.ofInjective (f := toPermHom (AffineGroup F) F)
    toPerm_injective).toEquiv.symm).trans (card_affineGroup F)

/-- **`AGL(1, F)` does not contain the alternating group** once `F` has at least five elements:
its order `q (q - 1)` is smaller than `q! / 2`. -/
theorem not_alternatingGroup_le_range_toPermHom [Fintype F] [DecidableEq F]
    (hF : 5 ≤ Nat.card F) :
    ¬ alternatingGroup F ≤ (toPermHom (AffineGroup F) F).range := by
  intro h
  have hle := Subgroup.card_le_of_le h
  have h2 := two_mul_nat_card_alternatingGroup (α := F)
  rw [natCard_range_toPermHom] at hle
  rw [Nat.card_perm] at h2
  obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 5 := ⟨Nat.card F - 5, by omega⟩
  simp only [hm, Nat.reduceSubDiff] at hle h2
  -- `(m + 5)! = (m + 5) (m + 4) (m + 3)!` with `(m + 3)! ≥ 3! = 6`.
  have h6 : 6 ≤ (m + 3).factorial := Nat.factorial_le (m := 3) (by omega)
  rw [Nat.factorial_succ, Nat.factorial_succ] at h2
  nlinarith

/-- **`AGL(1, F)` contains a full cycle in prime degree.** When the number of elements of `F` is
prime, the transitive group `AGL(1, F)` contains a cycle moving every point. -/
theorem exists_isCycle_mem_range_toPermHom_support_eq_univ [Fintype F] [DecidableEq F]
    (hp : (Nat.card F).Prime) :
    ∃ g ∈ (toPermHom (AffineGroup F) F).range, g.IsCycle ∧ g.support = univ :=
  exists_isCycle_mem_of_isPretransitive_of_prime_card
    ((isPretransitive_range_toPermHom_iff _ _).2 inferInstance)
    (Nat.card_eq_fintype_card (α := F) ▸ hp)

end DivisionRing

section Field

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`AGL(1, F)` contains a cycle of length `q - 1`.** Over a finite field with at least three
elements, multiplication by a generator of the cyclic group `Fˣ` is a single cycle moving every
nonzero element and fixing `0`. -/
theorem exists_isCycle_mem_range_toPermHom_support_eq_compl_zero (hF : 2 < Nat.card F) :
    ∃ g ∈ (toPermHom (AffineGroup F) F).range, g.IsCycle ∧ g.support = {0}ᶜ := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hu1 : u ≠ 1 := by
    rintro rfl
    have := orderOf_eq_card_of_forall_mem_zpowers hu
    rw [orderOf_one, Nat.card_units] at this
    omega
  have hu1' : (u : F) ≠ 1 := fun h ↦ hu1 (Units.ext h)
  set σ := toPermHom (AffineGroup F) F (SemidirectProduct.inr u) with hσ
  have hpow (k : ℤ) (x : F) : (σ ^ k) x = ((u ^ k : Fˣ) : F) * x := by
    -- `σ ^ k` is the image of `inr (u ^ k)`, which acts by `x ↦ 0 + u ^ k * x`.
    rw [hσ, ← map_zpow, ← map_zpow SemidirectProduct.inr]
    simp [AffineGroup.smul_def, -map_zpow]
  have hfix (x : F) : σ x = x ↔ x = 0 := by
    have := hpow 1 x
    rw [zpow_one, zpow_one] at this
    rw [this]
    refine ⟨fun h ↦ by_contra fun hx ↦ hu1' (mul_right_cancel₀ hx (h.trans (one_mul x).symm)),
      fun h ↦ by rw [h, mul_zero]⟩
  refine ⟨σ, ⟨_, rfl⟩, ⟨1, fun h ↦ one_ne_zero ((hfix 1).1 h), fun y hy ↦ ?_⟩, ?_⟩
  · have hy0 : y ≠ 0 := fun h ↦ hy ((hfix y).2 h)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hu (Units.mk0 y hy0))
    exact ⟨k, by rw [hpow, hk, Units.val_mk0, mul_one]⟩
  · ext x
    simp [mem_support, hfix]

end Field

end AffineGroup

end TauCeti
