/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# The Weyl group acts simply transitively on the bases

A root pairing has many bases, and the Weyl group moves them around: an automorphism carries a
base to a base (`RootPairing.Base.map`). This file proves that for a finite reduced
crystallographic root pairing the Weyl group acts **simply transitively** on its bases: for any two
bases `b` and `b'` there is exactly one Weyl-group element `w` with `b.map w = b'`
(`RootPairing.Base.existsUnique_map_eq`).

The argument is the classical one. Fix `b` and `b'`, and count the positive roots of `b` that a
Weyl-group element `w` sends to negative roots of `b'`. If that count is not zero then some simple
root `αₖ` of `b` is among them, because a positive root is built from simple roots by adding one
simple root at a time while staying a root. Replacing `w` by `w sₖ` lowers the count by one: the
simple reflection `sₖ` permutes the positive roots of `b` other than `αₖ` and negates `αₖ`. So some
`w` sends every positive root of `b` to a positive root of `b'`. Such a `w` carries the simple
roots of `b` onto those of `b'`, since the simple roots are the positive roots that are not sums of
two positive roots (`TauCeti.mem_support_iff_isPos_and_forall_ne_add`) and `w` is additive.
Uniqueness reduces to `TauCeti.eq_one_of_mapsTo_posRoots`: an element of the Weyl group keeping
every positive root of one base positive is the identity. The propagation from simple roots to all
positive roots is `TauCeti.mapsTo_posRoots_of_forall_mem_support`.

## Main results

* `TauCeti.isPos_weylGroupToPerm_iff_of_mapsTo_posRoots` and
  `TauCeti.weylGroupToPerm_mem_support_iff_of_mapsTo_posRoots`: a Weyl-group element sending the
  positive roots of `b` to positive roots of `b'` identifies the positive roots, and the simple
  roots, of the two bases.
* `RootPairing.Base.exists_mapsTo_posRoots`: some Weyl-group element sends the positive roots of
  `b` to positive roots of `b'`, and `TauCeti.eq_of_mapsTo_posRoots` says it is unique.
* `TauCeti.map_eq_iff_mapsTo_posRoots`: `b.map w = b'` exactly when `w` sends the positive roots
  of `b` to positive roots of `b'`.
* `RootPairing.Base.existsUnique_map_eq`: **the Weyl group acts simply transitively on the
  bases.**

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. III,
  §10.3, Theorem (b) and (e).
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.5, Theorem 2.
-/

public section

open Set

namespace TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [CharZero R] {b b' : P.Base} {w : P.weylGroup}

/-- An element sending the positive roots of `b` to positive roots of `b'` also sends the negative
roots of `b` to negative roots of `b'`, so it identifies the two notions of positivity. -/
theorem isPos_weylGroupToPerm_iff_of_mapsTo_posRoots
    (h : MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b')) (i : ι) :
    b'.IsPos (P.weylGroupToPerm w i) ↔ b.IsPos i := by
  refine ⟨fun hi ↦ by_contra fun hneg ↦ ?_,
    fun hi ↦ (mem_posRoots P b' _).mp (h ((mem_posRoots P b _).mpr hi))⟩
  -- Otherwise `-i` is positive for `b`, so `w (-i) = -(w i)` is positive for `b'`, as is `w i`.
  let := P.indexNeg
  have hpos := h ((mem_posRoots P b _).mpr ((RootPairing.Base.IsPos.neg_iff_not b i).mpr hneg))
  rw [mem_posRoots, P.weylGroupToPerm_neg, RootPairing.Base.IsPos.neg_iff_not] at hpos
  exact hpos hi

variable [Finite ι] [IsDomain R] [P.IsCrystallographic]

/-- **An element matching the positive roots of two bases matches their simple roots.** The simple
roots are the positive roots that are not the sum of two positive roots, and a Weyl-group element
preserves sums of roots. -/
theorem weylGroupToPerm_mem_support_iff_of_mapsTo_posRoots
    (h : MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b')) (i : ι) :
    P.weylGroupToPerm w i ∈ b'.support ↔ i ∈ b.support := by
  have hpos := isPos_weylGroupToPerm_iff_of_mapsTo_posRoots h
  have hadd (a c d : ι) : P.root (P.weylGroupToPerm w a) =
      P.root (P.weylGroupToPerm w c) + P.root (P.weylGroupToPerm w d) ↔
        P.root a = P.root c + P.root d := by
    simp only [← RootPairing.weylGroup_apply_root, ← smul_add, smul_left_cancel_iff]
  rw [mem_support_iff_isPos_and_forall_ne_add, mem_support_iff_isPos_and_forall_ne_add, hpos]
  refine and_congr_right fun _ ↦ ⟨fun H j k hj hk ↦ ?_, fun H j k hj hk ↦ ?_⟩
  · rw [Ne, ← hadd]
    exact H _ _ ((hpos j).mpr hj) ((hpos k).mpr hk)
  · obtain ⟨j, rfl⟩ := (P.weylGroupToPerm w).surjective j
    obtain ⟨k, rfl⟩ := (P.weylGroupToPerm w).surjective k
    rw [Ne, hadd]
    exact H _ _ ((hpos j).mp hj) ((hpos k).mp hk)

/-- **A Weyl-group element carries `b` to `b'` exactly when it matches their positive roots.** -/
theorem map_eq_iff_mapsTo_posRoots :
    b.map (w : P.Aut) = b' ↔ MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b') := by
  classical
  have hsupp (i : ι) :
      P.weylGroupToPerm w i ∈ (b.map (w : P.Aut)).support ↔ i ∈ b.support := by
    rw [RootPairing.Base.support_map_eq, RootPairing.weylGroupToPerm_apply]
    exact (w : P.Aut).indexEquiv.injective.mem_finset_image
  refine ⟨fun h ↦ mapsTo_posRoots_of_forall_mem_support P b fun i hi ↦ ?_, fun h ↦ ?_⟩
  · exact support_subset_posRoots P b' (h ▸ (hsupp i).mpr hi)
  · ext j
    obtain ⟨i, rfl⟩ := (P.weylGroupToPerm w).surjective j
    rw [hsupp, weylGroupToPerm_mem_support_iff_of_mapsTo_posRoots h]

variable [P.IsReduced]

/-- Right multiplication by the reflection in a simple root `αₖ` of `b` that `w` sends to a
negative root of `b'` removes `αₖ` from the positive roots of `b` that `w` sends to negative roots
of `b'`, and permutes the others by `sₖ`. -/
private theorem setOf_isPos_not_isPos_mul_ofIdx {k : ι} (hk : k ∈ b.support)
    (hk' : ¬ b'.IsPos (P.weylGroupToPerm w k)) :
    {i | b.IsPos i ∧ ¬ b'.IsPos (P.weylGroupToPerm (w * RootPairing.weylGroup.ofIdx P k) i)} =
      P.reflectionPerm k ⁻¹' ({i | b.IsPos i ∧ ¬ b'.IsPos (P.weylGroupToPerm w i)} \ {k}) := by
  ext i
  have hperm := reflectionPerm_mem_posRoots_diff_singleton_iff P b hk i
  simp only [mem_sdiff, mem_posRoots, mem_singleton_iff] at hperm
  simp only [mem_ofPred_eq, mem_preimage, mem_sdiff, mem_singleton_iff,
    RootPairing.weylGroupToPerm_mul_ofIdx_apply]
  refine ⟨fun ⟨hi, hi'⟩ ↦ ?_, fun ⟨⟨_, hi'⟩, hne⟩ ↦ ⟨(hperm.mp ⟨‹_›, hne⟩).1, hi'⟩⟩
  -- The simple root `αₖ` itself is not counted after the reflection: `w (sₖ αₖ) = -(w αₖ)` is
  -- positive for `b'`.
  have hik : i ≠ k := by
    rintro rfl
    let := P.indexNeg
    rw [← RootPairing.indexNeg_neg, P.weylGroupToPerm_neg,
      RootPairing.Base.IsPos.neg_iff_not] at hi'
    exact hi' hk'
  exact ⟨⟨(hperm.mpr ⟨hi, hik⟩).1, hi'⟩, (hperm.mpr ⟨hi, hik⟩).2⟩

/-- **Some Weyl-group element matches the positive roots of two bases.** -/
theorem _root_.RootPairing.Base.exists_mapsTo_posRoots (b b' : P.Base) :
    ∃ w : P.weylGroup, MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b') := by
  -- Induct on the number of positive roots of `b` that `w` sends to negative roots of `b'`.
  suffices ∀ n (w : P.weylGroup),
      {i | b.IsPos i ∧ ¬ b'.IsPos (P.weylGroupToPerm w i)}.ncard = n →
        ∃ w : P.weylGroup, MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b') from
    this _ 1 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw
  by_cases hmaps : MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b')
  · exact ⟨w, hmaps⟩
  -- Some simple root is sent to a negative root, and reflecting in it lowers the count.
  obtain ⟨k, hk, hk'⟩ : ∃ k ∈ b.support, ¬ b'.IsPos (P.weylGroupToPerm w k) := by
    by_contra! H
    exact hmaps <| mapsTo_posRoots_of_forall_mem_support P b fun i hi ↦
      (mem_posRoots P b' _).mpr (H i hi)
  refine ih _ ?_ (w * RootPairing.weylGroup.ofIdx P k) rfl
  rw [setOf_isPos_not_isPos_mul_ofIdx hk hk', ncard_preimage_of_injective_subset_range
    (P.reflectionPerm k).injective (by simp), ← hw]
  exact ncard_sdiff_singleton_lt_of_mem ⟨RootPairing.Base.isPos_of_mem_support hk, hk'⟩

/-- **At most one Weyl-group element matches the positive roots of two bases.** -/
theorem eq_of_mapsTo_posRoots {v : P.weylGroup}
    (hv : MapsTo (P.weylGroupToPerm v) (posRoots P b) (posRoots P b'))
    (hw : MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b')) : v = w := by
  refine inv_mul_eq_one.mp (eq_one_of_mapsTo_posRoots (b := b) fun i hi ↦ ?_)
  have hvw : P.weylGroupToPerm v (P.weylGroupToPerm (v⁻¹ * w) i) = P.weylGroupToPerm w i := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel_left]
  rw [mem_posRoots, ← isPos_weylGroupToPerm_iff_of_mapsTo_posRoots hv, hvw]
  exact (mem_posRoots P b' _).mp (hw hi)

/-- **The Weyl group acts simply transitively on the bases.** Any base `b` is carried onto any
other base `b'` by exactly one element of the Weyl group. -/
theorem _root_.RootPairing.Base.existsUnique_map_eq (b b' : P.Base) :
    ∃! w : P.weylGroup, b.map (w : P.Aut) = b' := by
  simp only [map_eq_iff_mapsTo_posRoots]
  obtain ⟨w, hw⟩ := b.exists_mapsTo_posRoots b'
  exact ⟨w, hw, fun v hv ↦ eq_of_mapsTo_posRoots hv hw⟩

end TauCeti
