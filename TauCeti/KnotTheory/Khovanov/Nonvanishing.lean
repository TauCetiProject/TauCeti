/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.EulerCharacteristic
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Nonvanishing of Khovanov homology

This file proves the nonvanishing of Khovanov homology for every planar oriented link diagram,
including the empty diagram.

Over every Noetherian commutative ring `R` satisfying rank-nullity—and in particular over `ℤ` and
`ℚ`—the graded Euler characteristic `χ_q Kh(D; R)` has a nonzero coefficient in some quantum degree
`j ≡ c (mod 2)` (`TauCeti.OrientedPDCode.exists_coeff_khovanovEulerChar_ne_zero` in
`TauCeti.KnotTheory.Khovanov.EulerCharacteristic`). Together with the cochain support interval
`[-n₋, n₊]`, this implies that `Khⁱʲ(D; R)` has positive rank (and is nonzero) in at least one
bidegree `(i, j)` with `i ∈ [-n₋, n₊]` and `j ≡ c (mod 2)` for every planar link diagram,
including the empty diagram.

## Main results

* `TauCeti.OrientedPDCode.exists_finrank_khovanovHomology_pos` and
  `TauCeti.OrientedPDCode.exists_not_isZero_khovanovHomology` (with explicit specializations to `ℤ`
  and `ℚ`): Khovanov homology is nonzero in some parity-compatible bidegree `(i, j)` with
  `i ∈ [-n₋, n₊]` and `j ≡ c (mod 2)` for every planar oriented link diagram, including the empty
  diagram.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359–426.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337–370.
-/

public section

open CategoryTheory CategoryTheory.Limits Finset

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ}

/-! ### Nonvanishing of Khovanov homology -/

section Homology

variable (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- **Khovanov homology has positive rank in at least one parity-compatible bidegree `(i, j)`**
with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`, for every planar oriented diagram
(including the empty diagram) over any Noetherian commutative ring `R` satisfying rank-nullity. -/
theorem exists_finrank_khovanovHomology_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank R (D.khovanovHomology hD R i j) := by
  obtain ⟨j, hj, hne⟩ := D.exists_coeff_khovanovEulerChar_ne_zero hD R
  rw [D.coeff_khovanovEulerChar_eq_sum hD R j] at hne
  obtain ⟨i, hi, hi_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨i, hi, j, hj, Nat.pos_of_ne_zero fun hz ↦ hi_ne ?_⟩
  simp [hz]

/-- **Nonvanishing of Khovanov homology**: for every planar oriented diagram (including the empty
diagram) over any Noetherian commutative ring `R` satisfying rank-nullity, `Khⁱʲ(D; R)` is nonzero
in at least one parity-compatible bidegree `(i, j)` with `i ∈ [-n₋, n₊]` and
`j ≡ D.componentCount (mod 2)`. -/
theorem exists_not_isZero_khovanovHomology :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        ¬IsZero (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hj, hpos⟩ := D.exists_finrank_khovanovHomology_pos hD R
  exact ⟨i, hi, j, hj, fun hz ↦ hpos.ne' (ModuleCat.finrank_eq_zero_of_isZero hz)⟩

end Homology

section IntAndRat

variable (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)

/-- **Integral Khovanov homology has positive free rank in some parity-compatible bidegree
`(i, j)`** with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`, for every planar oriented
diagram including the empty diagram. -/
theorem exists_finrank_khovanovHomology_int_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank ℤ (D.khovanovHomology hD ℤ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℤ

/-- **Integral Khovanov homology is nonzero** in some parity-compatible bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`, for every planar oriented diagram including the
empty diagram. -/
theorem exists_not_isZero_khovanovHomology_int :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        ¬IsZero (D.khovanovHomology hD ℤ i j) :=
  D.exists_not_isZero_khovanovHomology hD ℤ

/-- **Rational Khovanov homology has positive dimension in some parity-compatible bidegree
`(i, j)`** with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`, for every planar oriented
diagram including the empty diagram. -/
theorem exists_finrank_khovanovHomology_rat_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank ℚ (D.khovanovHomology hD ℚ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℚ

/-- **Rational Khovanov homology is nonzero** in some parity-compatible bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`, for every planar oriented diagram including the
empty diagram. -/
theorem exists_not_isZero_khovanovHomology_rat :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        ¬IsZero (D.khovanovHomology hD ℚ i j) :=
  D.exists_not_isZero_khovanovHomology hD ℚ

end IntAndRat

end TauCeti.OrientedPDCode
