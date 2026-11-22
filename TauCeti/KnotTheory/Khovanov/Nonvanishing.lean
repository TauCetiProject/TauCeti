/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.EuclideanDomain.Int
public import TauCeti.KnotTheory.Khovanov.EulerCharacteristic

/-!
# Nonvanishing of Khovanov homology

Over every Noetherian commutative ring `R` satisfying rank-nullity—and in particular over `ℤ` and
`ℚ`—the graded Euler characteristic `χ_q Kh(D; R)` is nonzero
(`TauCeti.OrientedPDCode.khovanovEulerChar_ne_zero` in
`TauCeti.KnotTheory.Khovanov.EulerCharacteristic`). Together with the cochain support interval
`[-n₋, n₊]` and the quantum-grading parity vanishing theorem
`TauCeti.OrientedPDCode.isZero_khovanovHomology_of_mod_two_ne`, this implies that `Khⁱʲ(D; R)` is
nonzero (in fact `Nontrivial` of positive rank) in at least one bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` and `j ≡ c (mod 2)` for every planar link diagram, including the empty diagram.

## Main results

* `TauCeti.OrientedPDCode.exists_finrank_khovanovHomology_pos`,
  `TauCeti.OrientedPDCode.exists_not_isZero_khovanovHomology`,
  `TauCeti.OrientedPDCode.exists_finrank_khovanovHomology_pos_and_mod_two`,
  `TauCeti.OrientedPDCode.exists_not_isZero_khovanovHomology_and_mod_two`, and
  `TauCeti.OrientedPDCode.exists_nontrivial_khovanovHomology` (with explicit specializations to `ℤ`
  and `ℚ`): Khovanov homology is nonzero (in fact `Nontrivial` in some parity-compatible
  bidegree `(i, j)` with `i ∈ [-n₋, n₊]` and `j ≡ c (mod 2)`) for every planar oriented link
  diagram, including the empty diagram.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359–426.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337–370.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ}

section Homology

variable (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- **Khovanov homology has positive rank in at least one bidegree `(i, j)` with `i ∈ [-n₋, n₊]`**,
for every planar oriented diagram (including the empty diagram) over any Noetherian commutative
ring `R` satisfying rank-nullity. -/
theorem exists_finrank_khovanovHomology_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, 0 < Module.finrank R (D.khovanovHomology hD R i j) := by
  by_contra h
  refine D.khovanovEulerChar_ne_zero hD R
    (AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun j ↦ ?_)
  rw [D.coeff_khovanovEulerChar_eq_sum hD R j]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hzero : Module.finrank R (D.khovanovHomology hD R i j) = 0 :=
    Nat.eq_zero_of_not_pos fun hpos ↦ h ⟨i, hi, j, hpos⟩
  simp [hzero]

/-- **Khovanov homology has positive rank in at least one parity-compatible bidegree `(i, j)`**
with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_finrank_khovanovHomology_pos_and_mod_two :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank R (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hpos⟩ := D.exists_finrank_khovanovHomology_pos hD R
  refine ⟨i, hi, j, ?_, hpos⟩
  by_contra hmod
  exact hpos.ne' (ModuleCat.finrank_eq_zero_of_isZero
    (D.isZero_khovanovHomology_of_mod_two_ne hD R i hmod))

/-- **Nonvanishing of Khovanov homology**: for every planar oriented diagram (including the empty
diagram) over any Noetherian commutative ring `R` satisfying rank-nullity, `Khⁱʲ(D; R)` is nonzero
in at least one bidegree `(i, j)` with `i ∈ [-n₋, n₊]`. -/
theorem exists_not_isZero_khovanovHomology :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, ¬IsZero (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hpos⟩ := D.exists_finrank_khovanovHomology_pos hD R
  exact ⟨i, hi, j, fun hz ↦ hpos.ne' (ModuleCat.finrank_eq_zero_of_isZero hz)⟩

/-- **Nonvanishing of Khovanov homology (parity-qualified categorical form)**: some `Khⁱʲ(D; R)`
with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)` is non-zero in `ModuleCat R`. -/
theorem exists_not_isZero_khovanovHomology_and_mod_two :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        ¬IsZero (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hj, hpos⟩ := D.exists_finrank_khovanovHomology_pos_and_mod_two hD R
  exact ⟨i, hi, j, hj, fun hz ↦ hpos.ne' (ModuleCat.finrank_eq_zero_of_isZero hz)⟩

/-- **Nonvanishing of Khovanov homology (module form)**: for every planar oriented PD-code `D` and
every nontrivial Noetherian commutative ring `R` with the rank-nullity property, some underlying
`R`-module `Khⁱʲ(D; R)` with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)` is
`Nontrivial`. -/
theorem exists_nontrivial_khovanovHomology :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        Nontrivial (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hj, hpos⟩ := D.exists_finrank_khovanovHomology_pos_and_mod_two hD R
  exact ⟨i, hi, j, hj, Module.nontrivial_of_finrank_pos hpos⟩

end Homology

section IntAndRat

variable (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)

/-- **Integral Khovanov homology has positive free rank in some bidegree `(i, j)`**, for every
planar oriented diagram including the empty diagram. -/
theorem exists_finrank_khovanovHomology_int_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, 0 < Module.finrank ℤ (D.khovanovHomology hD ℤ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℤ

/-- **Integral Khovanov homology is nonzero** for every planar oriented diagram, including the
empty diagram. -/
theorem exists_not_isZero_khovanovHomology_int :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, ¬IsZero (D.khovanovHomology hD ℤ i j) :=
  D.exists_not_isZero_khovanovHomology hD ℤ

/-- **Integral Khovanov homology is nontrivial** in at least one bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_nontrivial_khovanovHomology_int :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        Nontrivial (D.khovanovHomology hD ℤ i j) :=
  D.exists_nontrivial_khovanovHomology hD ℤ

/-- **Rational Khovanov homology has positive dimension in some bidegree `(i, j)`**, for every
planar oriented diagram including the empty diagram. -/
theorem exists_finrank_khovanovHomology_rat_pos :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, 0 < Module.finrank ℚ (D.khovanovHomology hD ℚ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℚ

/-- **Rational Khovanov homology is nonzero** for every planar oriented diagram, including the
empty diagram. -/
theorem exists_not_isZero_khovanovHomology_rat :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, ¬IsZero (D.khovanovHomology hD ℚ i j) :=
  D.exists_not_isZero_khovanovHomology hD ℚ

/-- **Rational Khovanov homology is nontrivial** in at least one bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_nontrivial_khovanovHomology_rat :
    ∃ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        Nontrivial (D.khovanovHomology hD ℚ i j) :=
  D.exists_nontrivial_khovanovHomology hD ℚ

end IntAndRat

end TauCeti.OrientedPDCode
