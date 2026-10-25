/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Counting the balls in a valuation sphere

In a discrete valuation ring with finite residue field of cardinality `q`, the sphere of order
`s` contains exactly `q ^ (r - s) - q ^ (r - (s + 1))` congruence classes modulo the `r`-th power
of the maximal ideal, for `s < r`. Consequently every disjoint partition of this sphere into
balls of order `r` has that many members. For the uniformizers (`s = 1`) these are the finite
partitions used to integrate polynomial root counts: the number of balls, multiplied by the
common measure of a local fibre, gives the integral.

The count is purely algebraic and requires neither completeness nor a topology. It follows by
subtracting the numbers of classes in two successive ideal powers, computed using the third
isomorphism theorem and the cardinality of the quotient by an ideal power.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3.
-/

public section

open IsLocalRing IsDiscreteValuationRing

namespace TauCeti

variable {A : Type*} [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A]
  [Finite (ResidueField A)]

/-- The image of an ideal power modulo a deeper ideal power has `q ^ (r - s)` elements. -/
theorem ncard_image_quotient_mk_maximalIdeal_pow {s r : ℕ} (hsr : s ≤ r) :
    (Ideal.Quotient.mk (maximalIdeal A ^ r) '' ↑(maximalIdeal A ^ s)).ncard =
      Nat.card (ResidueField A) ^ (r - s) := by
  have hquot (k : ℕ) : Nat.card (A ⧸ maximalIdeal A ^ k) = Nat.card (ResidueField A) ^ k := by
    rw [← Submodule.cardQuot_apply, cardQuot_pow_of_prime
      (_root_.IsDiscreteValuationRing.not_a_field A), Submodule.cardQuot_apply]
    rfl
  have h := Submodule.card_quotient_mul_card_quotient
    (maximalIdeal A ^ s) (maximalIdeal A ^ r) (Ideal.pow_le_pow_right hsr)
  rw [hquot s, hquot r] at h
  have himage :
      (Submodule.map (maximalIdeal A ^ r).mkQ (maximalIdeal A ^ s) :
        Set (A ⧸ maximalIdeal A ^ r)) =
          Ideal.Quotient.mk (maximalIdeal A ^ r) '' ↑(maximalIdeal A ^ s) :=
    Submodule.map_coe _ _
  have hcard : Nat.card (Submodule.map (maximalIdeal A ^ r).mkQ (maximalIdeal A ^ s)) =
      (Ideal.Quotient.mk (maximalIdeal A ^ r) '' ↑(maximalIdeal A ^ s)).ncard := by
    rw [← himage]
    exact Nat.card_coe_set_eq _
  rw [hcard] at h
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos (α := ResidueField A)) s)
  rw [h, ← pow_add, Nat.sub_add_cancel hsr]

/-- There are `q ^ (r - s) - q ^ (r - (s + 1))` classes of valuation exactly `s` modulo
`𝓂 ^ r`. The assumption `s < r` makes valuation `s` independent of the representative. -/
theorem ncard_image_quotient_mk_addVal_eq {s r : ℕ} (hsr : s < r) :
    (Ideal.Quotient.mk (maximalIdeal A ^ r) '' {x : A | addVal A x = s}).ncard =
      Nat.card (ResidueField A) ^ (r - s) -
        Nat.card (ResidueField A) ^ (r - (s + 1)) := by
  classical
  let f := Ideal.Quotient.mk (maximalIdeal A ^ r)
  have hquot : Nat.card (A ⧸ maximalIdeal A ^ r) = Nat.card (ResidueField A) ^ r := by
    rw [← Submodule.cardQuot_apply, cardQuot_pow_of_prime
      (_root_.IsDiscreteValuationRing.not_a_field A), Submodule.cardQuot_apply]
    rfl
  have : Finite (A ⧸ maximalIdeal A ^ r) :=
    Nat.finite_of_card_ne_zero (hquot ▸ pow_ne_zero r Nat.card_pos.ne')
  have hmem (k : ℕ) (hkr : k ≤ r) (x : A) :
      f x ∈ f '' ↑(maximalIdeal A ^ k) ↔ x ∈ maximalIdeal A ^ k := by
    rw [← Ideal.map_eq_image_of_surjective f Ideal.Quotient.mk_surjective]
    exact Ideal.mem_quotient_iff_mem (Ideal.pow_le_pow_right hkr)
  have himage : f '' {x : A | addVal A x = s} =
      (f '' ↑(maximalIdeal A ^ s)) \
        (f '' ↑(maximalIdeal A ^ (s + 1))) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq] at hx
      simp only [Set.mem_sdiff, hmem s hsr.le, hmem (s + 1) hsr,
        IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, hx]
      exact ⟨le_rfl, (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self s)).not_ge⟩
    · rintro ⟨⟨x, hx, rfl⟩, hx'⟩
      refine ⟨x, ?_, rfl⟩
      rw [hmem (s + 1) hsr, IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal] at hx'
      have hxval := IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal.mp hx
      exact le_antisymm (Order.le_of_lt_add_one (by simpa using lt_of_not_ge hx')) hxval
  rw [himage, Set.ncard_sdiff (Set.image_mono (Ideal.pow_le_pow_right (Nat.le_succ s))),
    ncard_image_quotient_mk_maximalIdeal_pow hsr.le,
    ncard_image_quotient_mk_maximalIdeal_pow hsr]

/-- Every disjoint partition of the sphere of order `s` into balls of order `r > s` has the
same cardinality, computed from the residue cardinality. -/
theorem card_finset_of_addVal_eq_biUnion {s r : ℕ} (hsr : s < r) (C : Finset A)
    (hcover : {x : A | addVal A x = s} =
      ⋃ c ∈ C, {x : A | (r : ℕ∞) ≤ addVal A (x - c)})
    (hdisj : (C : Set A).PairwiseDisjoint
      (fun c ↦ {x : A | (r : ℕ∞) ≤ addVal A (x - c)})) :
    C.card = Nat.card (ResidueField A) ^ (r - s) -
      Nat.card (ResidueField A) ^ (r - (s + 1)) := by
  classical
  let f := Ideal.Quotient.mk (maximalIdeal A ^ r)
  have heq (x y : A) : f x = f y ↔ (r : ℕ∞) ≤ addVal A (x - y) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]
  have hinj : Set.InjOn f C := by
    intro c hc d hd hcd
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hc hd hne) (by simp)
      ((heq c d).mp hcd)
  have himage : f '' (C : Set A) = f '' {x : A | addVal A x = s} := by
    apply Set.Subset.antisymm
    · refine Set.image_mono fun c hc ↦ ?_
      rw [hcover]
      exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, by simp⟩⟩
    · rintro z ⟨x, hx, rfl⟩
      rw [hcover, Set.mem_iUnion] at hx
      obtain ⟨c, hc⟩ := hx
      obtain ⟨hc, hxc⟩ := Set.mem_iUnion.mp hc
      exact ⟨c, hc, ((heq x c).mpr hxc).symm⟩
  rw [← Set.ncard_coe_finset, ← hinj.ncard_image, himage]
  exact ncard_image_quotient_mk_addVal_eq hsr

end TauCeti
