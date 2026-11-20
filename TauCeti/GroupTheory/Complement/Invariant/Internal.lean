/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Invariant.Basic

/-!
# Invariant complements inside a subgroup

Suppose `W` and `A` are finite subgroups of an arbitrary group, with `A` normalizing `W`.
An abelian normal `p`-subgroup `N` of `W`, normalized by the `q`-group `A` for `p ≠ q`,
has an `A`-normalized local complement in `W` whenever it has a local complement in a Sylow
`p`-subgroup of `W`. Neither `W` nor `N` need be normal in the ambient group, and the orders
of `A` and `W` need not be coprime.

The conjugation action on `W` is Mathlib's `Subgroup.normalizerMonoidHom` restricted to `A`.
The result applies `Subgroup.exists_invariant_complement` to this action and transports the
complement back along the inclusion of `W`.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math.
  190 (1952), 93–107.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254, Section 1.
-/

public section

namespace Subgroup

open scoped IsMulCommutative

variable {G : Type*} [Group G] (W : Subgroup G) {N A : Subgroup G}
  [Finite W] [Finite A] [(N.subgroupOf W).Normal] [IsMulCommutative N]
  {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- An abelian normal `p`-subgroup of a finite subgroup `W` has a local complement normalized
by a finite `q`-subgroup `A` when `p ≠ q`, provided `A` normalizes both `W` and `N` and a local
complement exists in a Sylow `p`-subgroup of `W`.

Only `W` and `A` are assumed finite; normality of `N` is required inside `W`, not in `G`. -/
theorem exists_invariant_local_complement (hNW : N ≤ W)
    (hAW : A ≤ normalizer W) (hAN : A ≤ normalizer N)
    (hN : IsPGroup p N) (hA : IsPGroup q A) (hpq : p ≠ q) (P : Sylow p W)
    (hlocal : ∃ K : Subgroup G, N.IsLocalComplement K (P.toSubgroup.map W.subtype)) :
    ∃ D : Subgroup G, N.IsLocalComplement D W ∧ A ≤ normalizer D := by
  let := MulDistribMulAction.compHom W (W.normalizerMonoidHom.comp (inclusion hAW))
  have hsmul (a : A) (w : W) : ((a • w : W) : G) = a * w * (a : G)⁻¹ := rfl
  have hstable (a : A) (n : W) (hn : n ∈ N.subgroupOf W) : a • n ∈ N.subgroupOf W := by
    rw [mem_subgroupOf, hsmul]
    exact ((hAN a.property) n).mp hn
  have hlocal' : ∃ K : Subgroup W, (N.subgroupOf W).IsLocalComplement K P := by
    obtain ⟨K, hK⟩ := hlocal
    have hKW : K ≤ W := hK.right_le.trans (map_subtype_le P.toSubgroup)
    refine ⟨K.subgroupOf W, ?_, ?_⟩
    · rw [subgroupOf, subgroupOf, ← comap_inf, hK.inf_eq_bot, comap_subtype,
        bot_subgroupOf]
    · rw [← subgroupOf_sup hNW hKW, hK.sup_eq, subgroupOf, comap_map_eq_self_of_injective
        W.subtype_injective]
  obtain ⟨D, hD, hstableD⟩ := exists_invariant_complement (N.subgroupOf W)
    (hN.of_equiv (subgroupOfEquivOfLe hNW).symm) hA hpq hstable P hlocal'
  refine ⟨D.map W.subtype, ?_, ?_⟩
  · have h := (isLocalComplement_top_iff.mpr hD).map W.subtype_injective
    simpa only [map_subgroupOf_eq_of_le hNW, map_top, range_subtype] using h
  · rw [le_normalizer_iff]
    intro a ha d hd
    obtain ⟨d, hd, rfl⟩ := hd
    exact mem_map.mpr ⟨(⟨a, ha⟩ : A) • d, hstableD ⟨a, ha⟩ d hd, hsmul ⟨a, ha⟩ d⟩

end Subgroup
