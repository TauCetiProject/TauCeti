/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-!
# Infinite-place counts from roots of unity

If a number field contains a primitive `n`-th root of unity with `n > 2`, the cyclotomic
subfield is totally complex. Each of its `φ(n) / 2` infinite places has the same number
of extensions to the ambient field. In particular, a primitive eighth root of unity
forces an even number of infinite places, as needed in the signature conditions for
unitary groups.

The parity application is `New.Data.f_even` in `grh/src/New/Reduction/Data/Sizes.lean`
of lsernau/grh-lean at `72fead1`.
-/

public section

open NumberField InfinitePlace

namespace IsPrimitiveRoot

/-- If a number field contains a primitive `n`-th root of unity for `n > 2`, its number of
infinite places is divisible by `φ(n) / 2`. -/
theorem totient_div_two_dvd_card_infinitePlace {K : Type*} [Field K] [NumberField K]
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : 2 < n) :
    n.totient / 2 ∣ Fintype.card (InfinitePlace K) := by
  let : NeZero n := ⟨by omega⟩
  let L := IntermediateField.adjoin ℚ ({ζ} : Set K)
  have : IsCyclotomicExtension {n} ℚ L := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let := IsCyclotomicExtension.numberField {n} ℚ L
  have : IsTotallyComplex L := IsCyclotomicExtension.Rat.isTotallyComplex L hn
  have : IsTotallyComplex K := isTotallyComplex_of_algebra L K
  have h := Module.finrank_mul_finrank ℚ L K
  rw [IsTotallyComplex.finrank (K := L), IsTotallyComplex.finrank (K := K), mul_assoc] at h
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  refine ⟨Module.finrank L K, ?_⟩
  rw [← IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two n L]
  omega

/-- A primitive root of order divisible by eight forces an even number of infinite places. -/
theorem even_card_infinitePlace_of_eight_dvd {K : Type*} [Field K] [NumberField K]
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) (h8 : 8 ∣ n) :
    Even (Fintype.card (InfinitePlace K)) := by
  have htotient : Nat.totient 8 = 4 := by decide
  have hφ : 4 ∣ n.totient := htotient ▸ Nat.totient_dvd_of_dvd h8
  have hn' : 2 < n := (by decide : 2 < 8).trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h8)
  obtain ⟨k, hk⟩ := hφ
  have h₂ : 2 ∣ n.totient / 2 := ⟨k, by omega⟩
  exact even_iff_two_dvd.mpr (h₂.trans (hζ.totient_div_two_dvd_card_infinitePlace hn'))

end IsPrimitiveRoot
