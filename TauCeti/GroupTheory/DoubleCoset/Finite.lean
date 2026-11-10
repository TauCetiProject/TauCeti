/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
public import TauCeti.Algebra.Group.Subgroup.Pointwise
public import TauCeti.GroupTheory.DoubleCoset.Orbits
public import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Finiteness of the double-coset quotient

A double coset `HgK` is a union of left cosets of `K`, so the double cosets `H \ G / K` are a
quotient of `G ⧸ K`: the map `gK ↦ HgK` is well defined and surjective
(`TauCeti.doubleCosetMk_out_mk` is the well-definedness, in the form the surjection uses).
Consequently `H \ G / K` is finite as soon as `K` has finite index, with no finiteness assumption
on `G` itself.

This is the instance that lets a sum be taken over `H \ G / K`; the Mackey decomposition
(`TauCeti.RepresentationTheory.Induction.Mackey.Basic`) uses it, where the index of the subgroup
being induced from is the only finiteness available.

The double cosets partition `G`, so their sizes add up to the order of `G`
(`Subgroup.sum_card_quotToDoubleCoset`). The size of a single double coset `KsH` is given by the
classical formula `|KsH| · |K ⊓ sHs⁻¹| = |K| · |H|`
(`TauCeti.card_doubleCoset_mul_card_inf_conj_smul`), which holds without finiteness hypotheses
for `Nat.card`.

## Main statements

* `TauCeti.finite_doubleCosetQuotient`: `H \ G / K` is finite when `K` has finite index in `G`.
* `TauCeti.card_doubleCoset_mul_card_inf_conj_smul`: the double-coset size formula
  `|KsH| · |K ⊓ sHs⁻¹| = |K| · |H|`.
* `TauCeti.card_doubleCoset_eq_card_mul_relIndex`: the same formula as an index,
  `|KsH| = |K| · [sHs⁻¹ : K ⊓ sHs⁻¹]`.
* `Subgroup.sum_card_quotToDoubleCoset`: the sizes of the double cosets add up to `|G|`.
* `Subgroup.sum_card_quotToDoubleCoset_div_card_eq_index`: the numbers `|HgK| / |H|` add up
  to the index of `H`.
-/

public section

open MulAction
open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- Replacing an element by the chosen representative of its left `K`-coset does not change its
double coset. -/
theorem doubleCosetMk_out_mk (H K : Subgroup G) (g : G) :
    DoubleCoset.mk H K (QuotientGroup.mk g : G ⧸ K).out = DoubleCoset.mk H K g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  rw [hk, DoubleCoset.mk_mul_mem]

/-- **The double cosets `H \ G / K` are finite when `K` has finite index**: they are the image of
the finite set `G ⧸ K` under `gK ↦ HgK`. -/
instance finite_doubleCosetQuotient (H K : Subgroup G) [K.FiniteIndex] :
    Finite (DoubleCoset.Quotient (H : Set G) (K : Set G)) :=
  Finite.of_surjective (fun t : G ⧸ K => DoubleCoset.mk H K t.out) fun d =>
    ⟨QuotientGroup.mk d.out, (doubleCosetMk_out_mk H K d.out).trans (DoubleCoset.out_eq' d)⟩

/-- **The double-coset size formula**: `|KsH| · |K ⊓ sHs⁻¹| = |K| · |H|`.

With `Nat.card`'s convention that an infinite type has cardinality `0`, this holds without any
finiteness hypothesis. -/
theorem card_doubleCoset_mul_card_inf_conj_smul (s : G) (H K : Subgroup G) :
    Nat.card (DoubleCoset.doubleCoset s (K : Set G) (H : Set G)) *
        Nat.card (K ⊓ MulAut.conj s • H : Subgroup G) = Nat.card K * Nat.card H := by
  -- The double coset is `(Ks)H`, so `Subgroup.card_mul_eq_card_subgroup_mul_card_quotient` counts
  -- it as `|H|` times the size of the image of `Ks` in `G ⧸ H`, and that image is the orbit.
  have himg : (QuotientGroup.mk : G → G ⧸ H) '' ((K : Set G) * {s}) = orbit K ((s : G ⧸ H)) :=
    QuotientGroup.mk_surjective.preimage_injective <| by
      rw [QuotientGroup.preimage_image_mk_eq_mul, preimage_orbit_eq_doubleCoset,
        DoubleCoset.doubleCoset]
  have hdc : Nat.card (DoubleCoset.doubleCoset s (K : Set G) (H : Set G))
      = Nat.card H * Nat.card (orbit K ((s : G ⧸ H))) := by
    rw [DoubleCoset.doubleCoset, Subgroup.card_mul_eq_card_subgroup_mul_card_quotient, himg]
  have hK : Nat.card (K ⊓ MulAut.conj s • H : Subgroup G) *
      (K ⊓ MulAut.conj s • H : Subgroup G).relIndex K = Nat.card K := by
    rw [Subgroup.relIndex,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : K ⊓ MulAut.conj s • H ≤ K)).toEquiv]
    exact Subgroup.card_mul_index _
  rw [hdc, Subgroup.card_orbit_quotientGroup_mk_eq_relIndex_inf, mul_assoc,
    mul_comm ((K ⊓ MulAut.conj s • H : Subgroup G).relIndex K), hK, mul_comm]

/-- **The double-coset size formula, as an index**: `|KsH| = |K| · [sHs⁻¹ : K ⊓ sHs⁻¹]`.

With `Nat.card`'s convention that an infinite type has cardinality `0` and the relative index
being `0` when it is infinite, this holds without any finiteness hypothesis: if `H` is infinite,
both sides are `0`. -/
theorem card_doubleCoset_eq_card_mul_relIndex (s : G) (H K : Subgroup G) :
    Nat.card (DoubleCoset.doubleCoset s (K : Set G) (H : Set G)) =
      Nat.card K * K.relIndex (MulAut.conj s • H) := by
  by_cases hH : Finite H
  · -- `[sHs⁻¹ : K ⊓ sHs⁻¹] · |K ⊓ sHs⁻¹| = |sHs⁻¹| = |H|`.
    have hrel : K.relIndex (MulAut.conj s • H) * Nat.card (K ⊓ MulAut.conj s • H : Subgroup G) =
        Nat.card H := by
      rw [Subgroup.relIndex_mul_card]
      exact card_conj_smul_eq s H
    have hpos : 0 < Nat.card (K ⊓ MulAut.conj s • H : Subgroup G) :=
      Nat.pos_of_ne_zero fun h => Nat.card_pos.ne' (by rw [← hrel, h, mul_zero])
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [card_doubleCoset_mul_card_inf_conj_smul, mul_assoc, hrel]
  · -- `H` is infinite: the double coset contains a translate of `H`, so both sides vanish.
    have hHinf : Infinite H := not_finite_iff_infinite.1 hH
    have hdc : Nat.card (DoubleCoset.doubleCoset s (K : Set G) (H : Set G)) = 0 := by
      have : Infinite (DoubleCoset.doubleCoset s (K : Set G) (H : Set G)) :=
        Infinite.of_injective
          (fun h : H => (⟨s * h, DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, h, h.2, by simp⟩⟩ :
            DoubleCoset.doubleCoset s (K : Set G) (H : Set G)))
          fun a b hab => Subtype.ext (mul_left_cancel (congrArg Subtype.val hab))
      exact Nat.card_eq_zero_of_infinite
    rw [hdc]
    by_cases hK : Finite K
    · -- `K ⊓ sHs⁻¹` is finite and nonempty while `|sHs⁻¹| = |H| = 0`, so the index is `0`.
      have hrel := Subgroup.relIndex_mul_card K (MulAut.conj s • H)
      have hconj : Nat.card (MulAut.conj s • H : Subgroup G) = 0 :=
        (card_conj_smul_eq s H).trans Nat.card_eq_zero_of_infinite
      have hfin : Finite (K ⊓ MulAut.conj s • H : Subgroup G) :=
        Finite.of_injective (Subgroup.inclusion (inf_le_left : K ⊓ MulAut.conj s • H ≤ K))
          (Subgroup.inclusion_injective _)
      rw [hconj] at hrel
      rw [(mul_eq_zero.1 hrel).resolve_right Nat.card_pos.ne', mul_zero]
    · have : Infinite K := not_finite_iff_infinite.1 hK
      rw [Nat.card_eq_zero_of_infinite (α := K), zero_mul]

end TauCeti

namespace Subgroup

variable {G : Type*} [Group G]

/-- **The double cosets partition the group**: the sizes of the double cosets `HgK` add up to the
order of `G`. For infinite `G` both sides are `0`: a finite double coset forces `H` and `K` to be
finite, and then `G`, a finite union of finite double cosets, would be finite. -/
theorem sum_card_quotToDoubleCoset (H K : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (K : Set G))] :
    ∑ q, Nat.card (DoubleCoset.quotToDoubleCoset H K q) = Nat.card G := by
  by_cases hG : Finite G
  · rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (DoubleCoset.mk H K)), Nat.card_sigma]
    exact Fintype.sum_congr _ _ fun q =>
      Nat.card_congr (Equiv.subtypeEquivRight fun a => DoubleCoset.mem_quotToDoubleCoset_iff q a)
  have hGi : Infinite G := not_finite_iff_infinite.1 hG
  rw [Nat.card_eq_zero_of_infinite]
  -- the double coset of `q` consists of the products `h * a * k`, for any representative `a`
  have hmem (q : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
      ∃ a : G, ∀ x : G, x ∈ DoubleCoset.quotToDoubleCoset H K q ↔
        ∃ h ∈ H, ∃ k ∈ K, x = h * a * k := by
    obtain ⟨a, rfl⟩ : ∃ a, DoubleCoset.mk H K a = q := ⟨q.out, DoubleCoset.out_eq' q⟩
    refine ⟨a, fun x ↦ ?_⟩
    rw [DoubleCoset.mem_quotToDoubleCoset_iff, eq_comm, DoubleCoset.eq]
  by_cases hHK : Finite H ∧ Finite K
  · -- every double coset is finite, so `G`, their union, would be finite
    obtain ⟨hH, hK⟩ := hHK
    refine absurd ?_ hG
    have hfin (q : DoubleCoset.Quotient (H : Set G) (K : Set G)) :
        (DoubleCoset.quotToDoubleCoset H K q).Finite := by
      obtain ⟨a, ha⟩ := hmem q
      refine (Set.finite_range fun p : H × K ↦ (p.1 : G) * a * p.2).subset fun x hx ↦ ?_
      obtain ⟨h, hh, k, hk, rfl⟩ := (ha x).1 hx
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
    have hall : (Set.univ : Set G).Finite := by
      rw [← DoubleCoset.iUnion_quotToDoubleCoset H K]
      exact Set.finite_iUnion hfin
    exact Set.finite_univ_iff.1 hall
  · -- some factor is infinite, and each double coset contains a translate of it
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    obtain ⟨a, ha⟩ := hmem q
    rw [not_and_or, not_finite_iff_infinite, not_finite_iff_infinite] at hHK
    have : Infinite (DoubleCoset.quotToDoubleCoset H K q) := by
      rcases hHK with hH | hK
      · exact Infinite.of_injective (fun h : H ↦ (⟨(h : G) * a,
          (ha _).2 ⟨h, h.2, 1, K.one_mem, by simp⟩⟩ : DoubleCoset.quotToDoubleCoset H K q))
          fun h h' hh ↦ Subtype.ext (mul_right_cancel (congrArg Subtype.val hh))
      · exact Infinite.of_injective (fun k : K ↦ (⟨a * k,
          (ha _).2 ⟨1, H.one_mem, k, k.2, by simp⟩⟩ : DoubleCoset.quotToDoubleCoset H K q))
          fun k k' hk ↦ Subtype.ext (mul_left_cancel (congrArg Subtype.val hk))
    exact Nat.card_eq_zero_of_infinite

/-- **The double cosets count the right cosets**: each double coset `HsK` of a finite group is a
union of `|HsK| / |H|` right cosets of `H`, and these numbers add up, over `H \ G / K`, to the
index of `H`. -/
theorem sum_card_quotToDoubleCoset_div_card_eq_index [Finite G] (H K : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (K : Set G))] :
    ∑ q, Nat.card (DoubleCoset.quotToDoubleCoset H K q) / Nat.card H = H.index := by
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H)) ?_
  rw [Finset.sum_mul, Subgroup.index_mul_card, ← sum_card_quotToDoubleCoset H K]
  refine Finset.sum_congr rfl fun q _ => Nat.div_mul_cancel ?_
  -- Inversion turns right cosets of `H` into left cosets, counted by Mathlib's formula.
  rw [DoubleCoset.quotToDoubleCoset, DoubleCoset.doubleCoset,
    ← Nat.card_image_of_injective inv_injective, Set.image_inv_eq_inv]
  simp only [mul_inv_rev, inv_coe_set, ← mul_assoc]
  rw [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient]
  exact dvd_mul_right _ _

end Subgroup
