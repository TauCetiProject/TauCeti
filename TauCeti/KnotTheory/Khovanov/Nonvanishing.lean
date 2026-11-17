/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import TauCeti.KnotTheory.Khovanov.EulerCharacteristic
import TauCeti.KnotTheory.Khovanov.StateSum

/-! # Nonvanishing of Khovanov homology

Combining the graded Euler characteristic theorem
(`TauCeti.OrientedPDCode.khovanovEulerChar_eq_enhancedStateSum`) with the `q = 1` specialization
`eval₂ (Int.castRingHom ℤ) (1 : ℤˣ) D.enhancedStateSum = 2 ^ D.componentCount` from
`TauCeti.KnotTheory.Khovanov.StateSum` shows that for every planar oriented PD-code `D` with `m`
link components and every nontrivial Noetherian commutative ring `R` with the rank-nullity
property, evaluating `D.khovanovEulerChar hD R` at `q = 1` yields `2 ^ m`
(`eval₂_one_khovanovEulerChar_eq_two_pow`).

Since `2 ^ m ≠ 0`, `χ_q Kh(D; R) ≠ 0` (`khovanovEulerChar_ne_zero`), so over every nontrivial
Noetherian commutative ring `R` with rank-nullity (in particular `ℤ` and `ℚ`), every planar
oriented PD-code has a bidegree `(i, j)` with `i ∈ [-n₋, n₊]`, `j ≡ m (mod 2)`, and
`0 < Module.finrank R (D.khovanovHomology hD R i j)` (`exists_finrank_khovanovHomology_pos`,
`exists_not_isZero_khovanovHomology`, `exists_nontrivial_khovanovHomology`).

References: M. Khovanov, Duke Math. J. 101 (2000), 359–426; D. Bar-Natan, Algebr. Geom. Topol. 2
(2002), 337–370, §§1–2.
-/

public section

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

namespace TauCeti.OrientedPDCode
universe u

section Nonvanishing
variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)

section RankNullity
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- For a planar oriented PD-code `D` over a nontrivial Noetherian commutative ring `R` with the
rank-nullity property, evaluating the graded Euler characteristic `χ_q Kh(D; R)` at `q = 1` gives
`2 ^ D.componentCount`. -/
theorem eval₂_one_khovanovEulerChar_eq_two_pow :
    eval₂ (Int.castRingHom ℤ) (1 : ℤˣ) (D.khovanovEulerChar hD R) = 2 ^ D.componentCount := by
  rw [D.khovanovEulerChar_eq_enhancedStateSum hD R, D.eval₂_one_enhancedStateSum_eq_two_pow hD]

/-- **Nonvanishing of the graded Euler characteristic of Khovanov homology**: for every planar
oriented PD-code `D` (including the empty diagram), `χ_q Kh(D; R) ≠ 0` over any nontrivial
Noetherian commutative ring `R` with the rank-nullity property. -/
theorem khovanovEulerChar_ne_zero : D.khovanovEulerChar hD R ≠ 0 := fun h0 ↦ by
  have h := D.eval₂_one_khovanovEulerChar_eq_two_pow hD R
  rw [h0, map_zero] at h
  exact pow_ne_zero D.componentCount (by decide : (2 : ℤ) ≠ 0) h.symm

/-- For every planar oriented PD-code `D`, some quantum degree `j ≡ D.componentCount (mod 2)` has a
nonzero coefficient in `D.khovanovEulerChar hD R`. -/
theorem exists_coeff_khovanovEulerChar_ne_zero :
    ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧ (D.khovanovEulerChar hD R).coeff j ≠ 0 := by
  have ⟨j, hj⟩ : ∃ j : ℤ, (D.khovanovEulerChar hD R).coeff j ≠ 0 := by
    by_contra! hall
    exact D.khovanovEulerChar_ne_zero hD R
      (AddMonoidAlgebra.coeff_injective <| Finsupp.ext hall)
  exact ⟨j, by_contra fun hmod ↦ hj (D.coeff_khovanovEulerChar_eq_zero_of_mod_two_ne hD R hmod), hj⟩

/-- **Nonvanishing of Khovanov homology (positive rank)**: for every planar oriented PD-code `D`
(including the empty diagram) and every nontrivial Noetherian commutative ring `R` with the
rank-nullity property, there exist a cochain degree `i ∈ [-n₋, n₊]` and a quantum degree
`j ≡ D.componentCount (mod 2)` such that `0 < Module.finrank R (D.khovanovHomology hD R i j)`. -/
theorem exists_finrank_khovanovHomology_pos :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank R (D.khovanovHomology hD R i j) := by
  obtain ⟨j, hjmod, hjne⟩ := D.exists_coeff_khovanovEulerChar_ne_zero hD R
  rw [D.coeff_khovanovEulerChar_eq_sum hD R j] at hjne
  obtain ⟨i, himem, hine⟩ := Finset.exists_ne_zero_of_sum_ne_zero hjne
  exact ⟨i, Finset.mem_Icc.mp himem, j, hjmod, Nat.pos_of_ne_zero fun h0 ↦ hine (by simp [h0])⟩

/-- **Nonvanishing of Khovanov homology (categorical form)**: for every planar oriented PD-code `D`
and every nontrivial Noetherian commutative ring `R` with the rank-nullity property, some
`Khⁱʲ(D; R)` with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)` is non-zero as an object of
`ModuleCat R`. -/
theorem exists_not_isZero_khovanovHomology :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        ¬ IsZero (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hj, hpos⟩ := D.exists_finrank_khovanovHomology_pos hD R
  exact ⟨i, hi, j, hj, fun hZ ↦ hpos.ne' (ModuleCat.finrank_eq_zero_of_isZero hZ)⟩

/-- **Nonvanishing of Khovanov homology (module form)**: for every planar oriented PD-code `D` and
every nontrivial Noetherian commutative ring `R` with the rank-nullity property, some underlying
`R`-module `Khⁱʲ(D; R)` with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)` is `Nontrivial`. -/
theorem exists_nontrivial_khovanovHomology :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        Nontrivial (D.khovanovHomology hD R i j) := by
  obtain ⟨i, hi, j, hj, hpos⟩ := D.exists_finrank_khovanovHomology_pos hD R
  exact ⟨i, hi, j, hj, Module.nontrivial_of_finrank_pos hpos⟩

end RankNullity

/-! ### Integral and rational specializations -/

/-- The integral graded Euler characteristic `χ_q Kh(D; ℤ)` of any planar oriented PD-code is
nonzero. -/
theorem khovanovEulerChar_int_ne_zero : D.khovanovEulerChar hD ℤ ≠ 0 :=
  D.khovanovEulerChar_ne_zero hD ℤ

/-- Integral Khovanov homology `Kh(D; ℤ)` has positive free rank in at least one bidegree `(i, j)`
with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_finrank_khovanovHomology_int_pos :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank ℤ (D.khovanovHomology hD ℤ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℤ

/-- Integral Khovanov homology `Kh(D; ℤ)` is nontrivial in at least one bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_nontrivial_khovanovHomology_int :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        Nontrivial (D.khovanovHomology hD ℤ i j) :=
  D.exists_nontrivial_khovanovHomology hD ℤ

/-- The rational graded Euler characteristic `χ_q Kh(D; ℚ)` of any planar oriented PD-code is
nonzero. -/
theorem khovanovEulerChar_rat_ne_zero : D.khovanovEulerChar hD ℚ ≠ 0 :=
  D.khovanovEulerChar_ne_zero hD ℚ

/-- Rational Khovanov homology `Kh(D; ℚ)` has positive dimension in at least one bidegree `(i, j)`
with `i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_finrank_khovanovHomology_rat_pos :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        0 < Module.finrank ℚ (D.khovanovHomology hD ℚ i j) :=
  D.exists_finrank_khovanovHomology_pos hD ℚ

/-- Rational Khovanov homology `Kh(D; ℚ)` is nontrivial in at least one bidegree `(i, j)` with
`i ∈ [-n₋, n₊]` and `j ≡ D.componentCount (mod 2)`. -/
theorem exists_nontrivial_khovanovHomology_rat :
    ∃ i ∈ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
      ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧
        Nontrivial (D.khovanovHomology hD ℚ i j) :=
  D.exists_nontrivial_khovanovHomology hD ℚ

end Nonvanishing

end TauCeti.OrientedPDCode
