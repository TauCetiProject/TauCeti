/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Basic.ENNReal.Inv

/-!
# Counting the balls in a valuation sphere

In a discrete valuation ring with finite residue field of cardinality `q`, the sphere of order
`s` contains exactly `q ^ (r - s) - q ^ (r - (s + 1))` congruence classes modulo the `r`-th power
of the maximal ideal, for `s < r`. Consequently every disjoint partition of this sphere into
balls of order `r` has that many members. For the uniformizers (`s = 1`) these are the finite
partitions used to integrate polynomial root counts: the number of balls, multiplied by the
common measure of a local fibre, gives the integral. Equivalently, if each ball of order `r` is
given mass `q ^ (-r)`, the partition has total mass `q ^ (-s) (1 - q⁻¹)`, independently of `r`.

The count is purely algebraic and requires neither completeness nor a topology. It follows by
subtracting the numbers of classes in two successive ideal powers, computed using the third
isomorphism theorem and the cardinality of the quotient by an ideal power.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3.
-/

public section

open IsLocalRing IsDiscreteValuationRing
open scoped ENNReal

namespace TauCeti

variable {A : Type*} [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A]
  [Finite (ResidueField A)]

/-- The image of an ideal power modulo a deeper ideal power has `q ^ (r - s)` elements. -/
theorem ncard_image_quotient_mk_maximalIdeal_pow {s r : ℕ} (hsr : s ≤ r) :
    (Ideal.Quotient.mk (maximalIdeal A ^ r) '' ↑(maximalIdeal A ^ s)).ncard =
      Nat.card (ResidueField A) ^ (r - s) := by
  have h := Submodule.card_quotient_mul_card_quotient
    (maximalIdeal A ^ s) (maximalIdeal A ^ r) (Ideal.pow_le_pow_right hsr)
  rw [IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow] at h
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
  have heq (x y : A) : f x = f y ↔ (r : ℕ∞) ≤ addVal A (x - y) :=
    IsDiscreteValuationRing.quotient_mk_eq_iff_le_addVal
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

/-- Every disjoint partition of the sphere of order `s` into balls of order `r > s` has total
mass `q ^ (-s) (1 - q⁻¹)` when each ball has mass `q ^ (-r)`, where `q` is the residue
cardinality. -/
theorem card_finset_div_pow_of_addVal_eq_biUnion {s r : ℕ} (hsr : s < r) (C : Finset A)
    (hcover : {x : A | addVal A x = s} =
      ⋃ c ∈ C, {x : A | (r : ℕ∞) ≤ addVal A (x - c)})
    (hdisj : (C : Set A).PairwiseDisjoint
      (fun c ↦ {x : A | (r : ℕ∞) ≤ addVal A (x - c)})) :
    (C.card : ℝ≥0∞) / (Nat.card (ResidueField A) : ℝ≥0∞) ^ r =
      1 / (Nat.card (ResidueField A) : ℝ≥0∞) ^ s *
        (1 - 1 / (Nat.card (ResidueField A) : ℝ≥0∞)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hsr
  have hq : (Nat.card (ResidueField A) : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hq' : (Nat.card (ResidueField A) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [card_finset_of_addVal_eq_biUnion hsr C hcover hdisj,
    show s + m + 1 - s = m + 1 by omega, show s + m + 1 - (s + 1) = m by omega,
    ENNReal.natCast_sub, Nat.cast_pow, Nat.cast_pow]
  generalize (Nat.card (ResidueField A) : ℝ≥0∞) = q at hq hq' ⊢
  have hdiv (k l : ℕ) : q ^ k / q ^ (l + k) = 1 / q ^ l := by
    rw [pow_add, mul_comm, ← ENNReal.mul_div_mul_left 1 (q ^ l) (pow_ne_zero k hq)
      (ENNReal.pow_ne_top hq'), mul_one]
  rw [ENNReal.sub_div fun _ _ ↦ pow_ne_zero _ hq, show s + m + 1 = s + (m + 1) by omega, hdiv,
    show s + (m + 1) = s + 1 + m by omega, hdiv,
    ENNReal.mul_sub fun _ _ ↦ ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ hq), mul_one,
    pow_succ]
  simp only [one_div]
  rw [ENNReal.mul_inv (.inl (pow_ne_zero _ hq)) (.inl (ENNReal.pow_ne_top hq'))]

end TauCeti
