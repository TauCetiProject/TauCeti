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
import Mathlib.FieldTheory.Finite.GaloisField
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
primitive of degree `8` and contains a `7`-cycle, yet neither contains the alternating group.

## Main results

* `TauCeti.AffineGroup.isPreprimitive`: `AGL(1, F)` acts primitively on `F`, being
  `2`-transitive.
* `TauCeti.AffineGroup.natCard_range_toPermHom`: the permutation image of `AGL(1, F)` has order
  `q (q - 1)`.
* `TauCeti.AffineGroup.not_alternatingGroup_le_range_toPermHom`: for `q ≥ 5` the image does not
  contain the alternating group.
* `TauCeti.AffineGroup.exists_isCycle_mem_range_toPermHom_support_eq_compl_zero`: over a finite
  field with at least three elements the image contains a cycle with support `{0}ᶜ`.
* `TauCeti.not_forall_alternatingGroup_le_of_isPreprimitive_of_isCycle_mem_of_card_support_eq`:
  Jordan's theorem fails for a cycle of prime length `p` in degree `p`.
* Jordan's theorem fails for a cycle of prime length `p` in degree `p + 1`:
`TauCeti.not_forall_alternatingGroup_le_of_isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq`

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
  refine ⟨⟨Multiplicative.ofAdd (c - s * a), Units.mk0 s hs⟩, ?_, ?_⟩
  · rw [AffineGroup.smul_def, toAdd_ofAdd, Units.val_mk0, sub_add_cancel]
  · have h : s * b - s * a = d - c := by
      rw [← mul_sub, hs_def, mul_assoc, inv_mul_cancel₀ hba, mul_one]
    rw [AffineGroup.smul_def, toAdd_ofAdd, Units.val_mk0,
      show c - s * a + s * b = c + (s * b - s * a) by abel, h, add_sub_cancel]

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
  rw [hm] at hle h2
  have hfac : (m + 5).factorial = (m + 5) * (m + 4) * (m + 3).factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ, mul_assoc]
  have h6 : Nat.factorial 3 ≤ (m + 3).factorial := Nat.factorial_le (by omega)
  rw [show m + 5 - 1 = m + 4 by omega] at hle
  have ha : 0 < (m + 5) * (m + 4) := by positivity
  have hk := Nat.mul_le_mul_left ((m + 5) * (m + 4)) h6
  generalize (m + 5) * (m + 4) = a at ha hk hle hfac
  generalize (m + 3).factorial = k at hk hfac
  rw [Nat.factorial_succ, Nat.factorial_two] at hk
  omega

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
    rw [hσ, ← map_zpow, ← map_zpow SemidirectProduct.inr, toPermHom_apply, toPerm_apply,
      AffineGroup.smul_def, SemidirectProduct.left_inr, SemidirectProduct.right_inr, toAdd_one,
      zero_add]
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

/-- **Jordan's theorem fails in degree `p`.** A primitive permutation group of degree `n`
containing a cycle of prime length `p` need not contain the alternating group when `p = n`: the
affine group `AGL(1, 5)` is primitive on five points and contains a `5`-cycle. This shows that the
bound `p + 3 ≤ n` of `TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` cannot be
weakened to `p ≤ n`. -/
theorem not_forall_alternatingGroup_le_of_isPreprimitive_of_isCycle_mem_of_card_support_eq :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Perm α)), IsPreprimitive G α →
      ∀ g ∈ G, g.IsCycle → (#g.support).Prime → #g.support = Nat.card α →
        alternatingGroup α ≤ G := by
  intro h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card (ZMod 5) = 5 := Nat.card_zmod 5
  obtain ⟨g, hg, hc, hs⟩ :=
    AffineGroup.exists_isCycle_mem_range_toPermHom_support_eq_univ (F := ZMod 5)
      (by rw [hcard]; exact Nat.prime_five)
  have hs' : #g.support = Nat.card (ZMod 5) := by
    rw [hs, card_univ, Nat.card_eq_fintype_card]
  refine AffineGroup.not_alternatingGroup_le_range_toPermHom (F := ZMod 5) hcard.ge
    (h _ _ ((isPreprimitive_range_toPermHom_iff _ _).2 inferInstance) g hg hc ?_ hs')
  rw [hs', hcard]
  exact Nat.prime_five

/-- **Jordan's theorem fails in degree `p + 1`.** A primitive permutation group of degree `n`
containing a cycle of prime length `p` need not contain the alternating group when `p + 1 = n`:
the affine group `AGL(1, 8)` of the field with eight elements is primitive on eight points and
contains a `7`-cycle. This shows that the bound `p + 3 ≤ n` of
`TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` cannot be weakened to
`p + 1 ≤ n`. -/
theorem not_forall_alternatingGroup_le_of_isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] (G : Subgroup (Perm α)), IsPreprimitive G α →
      ∀ g ∈ G, g.IsCycle → (#g.support).Prime → #g.support + 1 = Nat.card α →
        alternatingGroup α ≤ G := by
  intro h
  classical
  let _ : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 3) = 8 := GaloisField.card 2 3 (by norm_num)
  obtain ⟨g, hg, hc, hs⟩ :=
    AffineGroup.exists_isCycle_mem_range_toPermHom_support_eq_compl_zero
      (F := GaloisField 2 3) (by omega)
  have hs' : #g.support = 7 := by
    rw [hs, card_compl, card_singleton, ← Nat.card_eq_fintype_card, hcard]
  refine AffineGroup.not_alternatingGroup_le_range_toPermHom (F := GaloisField 2 3) (by omega)
    (h _ _ ((isPreprimitive_range_toPermHom_iff _ _).2 inferInstance) g hg hc ?_ (by omega))
  rw [hs']
  exact Nat.prime_seven

end TauCeti
