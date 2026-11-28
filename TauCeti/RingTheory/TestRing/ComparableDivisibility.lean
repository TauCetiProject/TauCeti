/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TestRing

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Idempotent divisibility outside maximal ideals in test rings

When a map `f : E → B` into a commutative ring `B` splits every pair of elements `a, b : B` along
an idempotent `e : E` (meaning `a ∣ f e * b` and `b ∣ (1 - f e) * a`), any element `g` outside a
maximal ideal `m` of `B` divides `f e` for some idempotent `e : E` with `f e ∉ m`. In particular,
in a test ring `A` (`TauCeti.IsTestRing A`), every element outside a maximal ideal `m` divides an
idempotent `e ∉ m`, and hence an idempotent `e` with `1 - e ∈ m`.

## Main results

* `TauCeti.exists_dvd_idempotent_of_notMem`: general idempotent divisibility outside a maximal
  ideal for a map `f : E → B` satisfying the comparable-divisibility property.
* `TauCeti.IsTestRing.exists_dvd_idempotent_of_notMem`: in a test ring `A`, any `g ∉ m` for a
  maximal ideal `m` divides an idempotent `e ∉ m`.
* `TauCeti.IsTestRing.exists_isIdempotentElem_dvd_and_one_sub_mem`: in a test ring `A`, any
  `g ∉ m` for a maximal ideal `m` divides an idempotent `e` with `1 - e ∈ m`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean at commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, file
  `src/Lib/Cohomology/Etale/DenseSubfunctors.lean` (declaration
  `New.Variety.exists_dvd_idempotent_of_notMem`); Apache 2.0, Copyright 2026 Anthropic, PBC.
-/

public section

namespace TauCeti

/-- If `f : E → B` splits every pair `(a, b)` in a commutative ring `B` along an idempotent
`e : E` (`a ∣ f e * b` and `b ∣ (1 - f e) * a`), then any element `g` outside a maximal ideal `m`
divides `f e` for some idempotent `e : E` with `f e ∉ m`. -/
theorem exists_dvd_idempotent_of_notMem {E B : Type*} [Mul E] [CommRing B] {f : E → B}
    (h_compare : ∀ a b : B, ∃ e : E, IsIdempotentElem e ∧ a ∣ f e * b ∧ b ∣ (1 - f e) * a)
    {m : Ideal B} {g : B} (hm : m.IsMaximal) (hg : g ∉ m) :
    ∃ e : E, f e ∉ m ∧ IsIdempotentElem e ∧ g ∣ f e := by
  obtain ⟨b, d, hd, h_one⟩ := hm.exists_inv hg
  obtain ⟨e, he, ⟨a, ha⟩, h_dvd⟩ := h_compare g d
  refine ⟨e, fun hfe ↦ hg ?_, he, a + b * f e, ?_⟩
  · have h_split : g = (1 - f e) * g + f e * g := by ring
    rw [h_split]
    exact m.add_mem (m.mem_of_dvd h_dvd hd) (m.mul_mem_right g hfe)
  · linear_combination ha - f e * h_one

namespace IsTestRing

/-- In a test ring `A`, every element `g` outside a maximal ideal `m` divides an idempotent
`e ∉ m`. -/
theorem exists_dvd_idempotent_of_notMem {A : Type*} [CommRing A] [IsTestRing A]
    {m : Ideal A} {g : A} (hm : m.IsMaximal) (hg : g ∉ m) :
    ∃ e : A, e ∉ m ∧ IsIdempotentElem e ∧ g ∣ e :=
  TauCeti.exists_dvd_idempotent_of_notMem (f := id)
    IsTestRing.exists_isIdempotentElem_dvd_mul hm hg

/-- In a test ring `A`, every element `g` outside a maximal ideal `m` divides an idempotent `e`
satisfying `1 - e ∈ m`. -/
theorem exists_isIdempotentElem_dvd_and_one_sub_mem {A : Type*} [CommRing A] [IsTestRing A]
    {m : Ideal A} {g : A} (hm : m.IsMaximal) (hg : g ∉ m) :
    ∃ e : A, IsIdempotentElem e ∧ g ∣ e ∧ 1 - e ∈ m := by
  obtain ⟨e, he_notMem, he_idem, hge⟩ := exists_dvd_idempotent_of_notMem hm hg
  have hmul : e * (1 - e) ∈ m := by
    have : e * (1 - e) = 0 := by
      rw [mul_sub, mul_one, he_idem.eq, sub_self]
    rw [this]
    exact m.zero_mem
  exact ⟨e, he_idem, hge, (hm.isPrime.mem_or_mem hmul).resolve_left he_notMem⟩

end IsTestRing

end TauCeti
