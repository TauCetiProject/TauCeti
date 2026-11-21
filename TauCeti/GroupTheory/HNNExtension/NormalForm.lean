/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.HNNExtension
public import TauCeti.GroupTheory.TrivialIntersection

/-!
# Conjugating base elements by reduced words in an HNN extension

Let `HNNExtension G A B φ` be the HNN extension of `G` along an isomorphism `φ : A ≃* B` of
subgroups, with stable letter `t`, so that `t * a * t⁻¹ = φ a` for `a ∈ A`. For `u = ±1` write
`toSubgroup A B u` for the associated subgroup of `t ^ u`, which is `A` for `u = 1` and `B` for
`u = -1`, and `toSubgroupEquiv φ u : toSubgroup A B u ≃* toSubgroup A B (-u)` for `φ` or `φ⁻¹`.
Then `t ^ u * a * (t ^ u)⁻¹ = toSubgroupEquiv φ u a` for every `a ∈ toSubgroup A B u`.

Britton's lemma (Mathlib's `HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq`) controls when the
product `w` of a reduced word `h * t ^ u * ⋯` conjugates an element `c` of `G` back into `G`: if
`w⁻¹ * c * w ∈ G`, then `h⁻¹ * c * h ∈ toSubgroup A B (-u)`. Consequently, if `toSubgroup A B u`
is malnormal in `G` and no nontrivial element of `B` is conjugate in `G` into `A`, then
`w⁻¹ * x * w ∉ G` for every nontrivial `x ∈ toSubgroup A B u` and every reduced word `w` with at
least one stable letter such that `t ^ u * w` is still reduced.

## Main results

* `HNNExtension.t_zpow_mul_of_mul_inv_t_zpow`: `t ^ u * a * (t ^ u)⁻¹ = toSubgroupEquiv φ u a`.
* `HNNExtension.isTISubgroup_toSubgroup`: if `A` and `B` are malnormal, so are the associated
  subgroups.
* `HNNExtension.eq_one_of_mul_mul_inv_mem_toSubgroup_neg`: if no nontrivial element of `B` is
  conjugate into `A`, no nontrivial element of `toSubgroup A B u` is conjugate into
  `toSubgroup A B (-u)`.
* `HNNExtension.NormalWord.ReducedWord.exists_head_eq_prod_mul`: multiplying the product of a
  nonempty reduced word on the right by an element of `G` gives the product of a reduced word
  with the same head.
* `HNNExtension.head_inv_mul_mul_head_mem_toSubgroup`: if `w = h * t ^ u * ⋯` is reduced and
  `w⁻¹ * c * w ∈ G`, then `h⁻¹ * c * h ∈ toSubgroup A B (-u)`.
* `HNNExtension.prod_inv_mul_mul_prod_notMem_range`: if `toSubgroup A B u` is malnormal and no
  nontrivial element of `B` is conjugate into `A`, then `w⁻¹ * x * w ∉ G` for every nontrivial
  `x ∈ toSubgroup A B u` and every reduced word `w` with at least one stable letter such that
  `t ^ u * w` is reduced.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer (1977), Chapter IV, §2
  (Britton's lemma).
-/

public section

open Subgroup

namespace HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- Conjugating an element `a` of the associated subgroup of `t ^ u` by `t ^ u` gives its image
`toSubgroupEquiv φ u a` in the associated subgroup of `t ^ (-u)`. -/
@[simp]
theorem t_zpow_mul_of_mul_inv_t_zpow (u : ℤˣ) (a : toSubgroup A B u) :
    (t : HNNExtension G A B φ) ^ (u : ℤ) * of (a : G) * (t ^ (u : ℤ))⁻¹ =
      of (toSubgroupEquiv φ u a : G) := by
  -- `toSubgroup A B 1` is `A` and `toSubgroup A B (-1)` is `B` by definition (`toSubgroup_one`,
  -- `toSubgroup_neg_one`), so `a` is an argument of `φ` or of `φ.symm`.
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [toSubgroupEquiv_one, Units.val_one, zpow_one]
    exact (equiv_eq_conj (φ := φ) a).symm
  · simp only [toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one, zpow_neg, zpow_one, inv_inv]
    exact (equiv_symm_eq_conj (φ := φ) a).symm

/-- If `A` and `B` are malnormal, so is the associated subgroup of every `t ^ u`. -/
theorem isTISubgroup_toSubgroup (hA : TauCeti.IsTISubgroup A) (hB : TauCeti.IsTISubgroup B)
    (u : ℤˣ) : TauCeti.IsTISubgroup (toSubgroup A B u) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using hA
  · simpa using hB

/-- If no nontrivial element of `B` is conjugate into `A`, no nontrivial element of the associated
subgroup of `t ^ u` is conjugate into that of `t ^ (-u)`. -/
theorem eq_one_of_mul_mul_inv_mem_toSubgroup_neg
    (hAB : ∀ g : G, ∀ b ∈ B, g * b * g⁻¹ ∈ A → b = 1) {u : ℤˣ} {a g : G}
    (ha : a ∈ toSubgroup A B u) (hga : g * a * g⁻¹ ∈ toSubgroup A B (-u)) : a = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact conj_eq_one_iff.1 (hAB g⁻¹ _ (by simpa using hga) (by simpa [mul_assoc] using ha))
  · exact hAB g a (by simpa using ha) (by simpa using hga)

namespace NormalWord.ReducedWord

/-- Multiplying the product of a reduced word with at least one letter on the right by an element
of the base group gives the product of a reduced word with the same head. -/
theorem exists_head_eq_prod_mul (w : NormalWord.ReducedWord G A B) (hw : w.toList ≠ []) (c : G) :
    ∃ w' : NormalWord.ReducedWord G A B, w'.head = w.head ∧ w'.prod φ = w.prod φ * of c := by
  obtain ⟨L, p, hL⟩ := (List.eq_nil_or_concat w.toList).resolve_left hw
  have hchain := w.chain
  rw [hL, List.concat_eq_append, List.isChain_append] at hchain
  refine ⟨⟨w.head, L ++ [(p.1, p.2 * c)], List.isChain_append.2
    ⟨hchain.1, List.isChain_singleton _, fun a ha b hb => ?_⟩⟩, rfl, ?_⟩
  · obtain rfl : b = (p.1, p.2 * c) := by simpa using hb.symm
    exact hchain.2.2 a ha p (by simp)
  · simp [NormalWord.ReducedWord.prod, hL, mul_assoc]

end NormalWord.ReducedWord

/-- **Britton's lemma for conjugates.** If `w = h * t ^ u * ⋯` is the product of a reduced word
and `w⁻¹ * c * w` lies in the base group for some `c` in the base group, then
`h⁻¹ * c * h` lies in the associated subgroup of `t ^ (-u)`. -/
theorem head_inv_mul_mul_head_mem_toSubgroup {w : NormalWord.ReducedWord G A B} {u : ℤˣ} {g : G}
    {L : List (ℤˣ × G)} (hw : w.toList = (u, g) :: L) {c : G}
    (hc : (w.prod φ)⁻¹ * of c * w.prod φ ∈ (of : G →* HNNExtension G A B φ).range) :
    w.head⁻¹ * c * w.head ∈ toSubgroup A B (-u) := by
  obtain ⟨c', hc'⟩ := hc
  obtain ⟨w', hw'h, hw'⟩ := w.exists_head_eq_prod_mul (φ := φ) (by simp [hw]) c'
  have h := (ReducedWord.map_fst_eq_and_of_prod_eq φ (w₁ := { w with head := c * w.head })
    (w₂ := w') ?_).2 u (by simp [hw])
  · simpa [hw'h, mul_assoc] using inv_mem h
  · rw [hw', hc']
    simp only [NormalWord.ReducedWord.prod, map_mul]
    group

/-- Let `x` be a nontrivial element of the associated subgroup of `t ^ u`, and `w` the product of
a reduced word `h * t ^ u' * ⋯` such that `t ^ u * w` is still reduced. If the associated subgroup
of `t ^ u` is malnormal and no nontrivial element of `B` is conjugate into `A`, then `w⁻¹ * x * w`
is not in the base group. -/
theorem prod_inv_mul_mul_prod_notMem_range (hAB : ∀ g : G, ∀ b ∈ B, g * b * g⁻¹ ∈ A → b = 1)
    {u : ℤˣ} (hTI : TauCeti.IsTISubgroup (toSubgroup A B u)) {x : G} (hx : x ∈ toSubgroup A B u)
    (hx1 : x ≠ 1) {w : NormalWord.ReducedWord G A B} {u' : ℤˣ} {g : G} {L : List (ℤˣ × G)}
    (hw : w.toList = (u', g) :: L)
    (hred : w.head ∈ toSubgroup A B u → u = u') :
    (w.prod φ)⁻¹ * of x * w.prod φ ∉ (of : G →* HNNExtension G A B φ).range := by
  -- `h⁻¹ * x * h` lies in the associated subgroup of `t ^ (-u')`. This contradicts the hypothesis
  -- on conjugates if `u' = u`, and malnormality if `u' = -u`, since then `h` is outside the
  -- associated subgroup of `t ^ u`.
  intro hmem
  have hx₂ := head_inv_mul_mul_head_mem_toSubgroup hw hmem
  by_cases hu : u' = u
  · subst hu
    exact hx1 (eq_one_of_mul_mul_inv_mem_toSubgroup_neg hAB (g := w.head⁻¹) hx
      (by simpa using hx₂))
  · refine hx1 (hTI.eq_one (g := w.head⁻¹)
      (by simpa using fun hb => hu (hred hb).symm) hx ?_)
    rw [Int.units_ne_iff_eq_neg.1 hu, neg_neg] at hx₂
    simpa using hx₂

end HNNExtension
