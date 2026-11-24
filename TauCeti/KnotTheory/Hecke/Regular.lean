/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Regular
public import TauCeti.KnotTheory.Burau.Skein
public import TauCeti.KnotTheory.Hecke.Homfly
import TauCeti.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Regularity of the normalized Ocneanu braid trace across zero-factor specializations

For a unit `q : Rˣ` with `u = q - q⁻¹ : Rˣ` and a generic writhe unit `l`, normalizing the Ocneanu
trace requires strand-number factor `C = (l⁻¹ - l) * u⁻¹` and Markov parameter
`z = u * ((l⁻¹ - l) * l)⁻¹`. At the two zero-factor specializations `l = 1` and `l = -1`, the
strand factor `C` vanishes and the parameter `z` has a pole, while their product `C * z = l⁻¹`
remains regular.

Over every commutative ring `R`, `T (-1) - T 1` is regular (`LaurentPolynomial.isRegular_T_sub_T`),
so `LaurentPolynomial R` embeds injectively into
`Localization.Away (T (-1) - T 1 : LaurentPolynomial R)`
(`IsLocalization.Away.injective_iff_isRegular`). Pole cancellation on each finite stage of
`InfiniteTypeAHeckeAlgebra` (`TauCeti.InfiniteTypeAHeckeAlgebra.pow_mul_ocneanuTrace_map_mem`) shows
that the generic normalized Ocneanu braid trace `MarkovBraid.heckeUniversalTrace` equals the image
of a unique Laurent polynomial `MarkovBraid.heckeRegularExtension` in `LaurentPolynomial R`.

Evaluating `heckeRegularExtension` at any writhe unit `l₀ : Rˣ` satisfies the evaluated
strand-inclusion and skein relations (`MarkovBraid.eval₂_heckeRegularExtension_strandIncl` and
`MarkovBraid.eval₂_heckeRegularExtension_skein`), and recovers `MarkovBraid.heckeTrace` for any
normalized Markov trace over `R` (`MarkovBraid.eval₂_heckeRegularExtension_eq_heckeTrace`).
Specializing to `l₀ = 1` or `l₀ = -1` kills added uncrossed strands (split unknot components) and
recovers `MarkovBraid.normalizedBurauAlexander`
(`MarkovBraid.eval₂_one_heckeRegularExtension_eq_normalizedBurauAlexander` and
`MarkovBraid.eval₂_neg_one_heckeRegularExtension_eq_normalizedBurauAlexander`).

## Main definitions

* `TauCeti.MarkovBraid.heckeUniversalTrace`: the normalized Ocneanu braid trace at the generic
  writhe parameter in `Localization.Away (T (-1) - T 1 : LaurentPolynomial R)`.
* `TauCeti.MarkovBraid.heckeRegularExtension`: the unique regular Laurent polynomial in
  `LaurentPolynomial R` extending `heckeUniversalTrace` across `T (-1) - T 1 = 0`.

## Main results

* `TauCeti.localizationAway_T_sub_T_mul_mul_eq_one` and
  `TauCeti.localizationAway_T_sub_T_mul_inv_mul_sub_eq_one`: the positive and negative Markov
  stabilization identities for the universal localization parameters.
* `TauCeti.MarkovBraid.existsUnique_algebraMap_eq_heckeUniversalTrace`: existence and uniqueness of
  the regular Laurent polynomial extension across `l = ±1` over any commutative ring.
* `TauCeti.MarkovBraid.eval₂_heckeRegularExtension_strandIncl`,
  `TauCeti.MarkovBraid.eval₂_heckeRegularExtension_skein`, and
  `TauCeti.MarkovBraid.eval₂_heckeRegularExtension_eq_heckeTrace`: strand-inclusion, skein, and
  universal specialization relations at an arbitrary writhe unit `l₀ : Rˣ`.
* `TauCeti.MarkovBraid.eval₂_one_heckeRegularExtension_eq_normalizedBurauAlexander`,
  `TauCeti.MarkovBraid.eval₂_neg_one_heckeRegularExtension_skein`, and
  `TauCeti.MarkovBraid.eval₂_neg_one_heckeRegularExtension_eq_normalizedBurauAlexander`: evaluations
  at the two zero-factor specializations `l = 1` and `l = -1`.

## References

* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett, A. Ocneanu, *A new polynomial
  invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public noncomputable section

namespace TauCeti

open LaurentPolynomial
open InfiniteTypeAHeckeAlgebra (IsMarkovTrace ocneanuTrace isMarkovTrace_ocneanuTrace)

variable {R : Type*} [CommRing R]

section LocalizationSetup

/-- The localization of `LaurentPolynomial R` away from the generic zero-factor element
`T (-1) - T 1`. -/
private abbrev Away (R : Type*) [CommRing R] : Type _ :=
  Localization.Away (T (-1) - T 1 : LaurentPolynomial R)

/-- A base-ring unit `q : Rˣ` mapped into `(Away R)ˣ`. -/
private abbrev scalarUnit (q : Rˣ) : (Away R)ˣ :=
  Units.map (algebraMap R (Away R) : R →* Away R) q

/-- The generic writhe unit `T 1` mapped into `(Away R)ˣ`. -/
private abbrev writheUnit (R : Type*) [CommRing R] : (Away R)ˣ :=
  Units.map (algebraMap (LaurentPolynomial R) (Away R) : LaurentPolynomial R →* Away R)
    (genericUnit R)

/-- The inverted Laurent-monomial difference `T (-1) - T 1` as a unit of `Away R`. -/
private noncomputable abbrev diffUnit (R : Type*) [CommRing R] : (Away R)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (T (-1) - T 1 : LaurentPolynomial R)).unit

private theorem coe_scalarUnit (q : Rˣ) :
    (scalarUnit q : Away R) = algebraMap R (Away R) q := by
  simp

private theorem coe_scalarUnit_inv (q : Rˣ) :
    (↑(scalarUnit q)⁻¹ : Away R) = algebraMap R (Away R) ↑q⁻¹ := by
  simp

private theorem algebraMap_C_eq (r : R) :
    algebraMap (LaurentPolynomial R) (Away R) (C r) = algebraMap R (Away R) r := by
  rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply R (LaurentPolynomial R) (Away R)]

private theorem coe_scalarUnit_eq_sub {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) :
    (scalarUnit u : Away R) = (scalarUnit q : Away R) - ↑(scalarUnit q)⁻¹ := by
  rw [coe_scalarUnit, hu, map_sub, ← coe_scalarUnit, ← coe_scalarUnit_inv]

private theorem coe_writheUnit :
    (writheUnit R : Away R) = algebraMap (LaurentPolynomial R) (Away R) (T 1) := by
  simp

private theorem coe_writheUnit_inv :
    (↑(writheUnit R)⁻¹ : Away R) = algebraMap (LaurentPolynomial R) (Away R) (T (-1)) := by
  simp

private theorem coe_writheUnit_zpow (w : ℤ) :
    (↑(writheUnit R ^ w) : Away R) = algebraMap (LaurentPolynomial R) (Away R) (T w) := by
  simp [← _root_.map_zpow]

private theorem coe_diffUnit :
    (diffUnit R : Away R) = (↑(writheUnit R)⁻¹ : Away R) - writheUnit R := by
  rw [diffUnit, IsUnit.unit_spec, map_sub, coe_writheUnit_inv, coe_writheUnit]

private theorem algebraMap_strandFactor (u : Rˣ) :
    algebraMap (LaurentPolynomial R) (Away R) ((T (-1) - T 1) * C (↑u⁻¹ : R)) =
      ↑(diffUnit R * (scalarUnit u)⁻¹) := by
  rw [map_mul, Units.val_mul, diffUnit, IsUnit.unit_spec, algebraMap_C_eq, coe_scalarUnit_inv]

private theorem strandFactor_mul_param (u : Rˣ) :
    algebraMap (LaurentPolynomial R) (Away R) (T (-1)) =
      (↑(diffUnit R * (scalarUnit u)⁻¹) : Away R) *
        ↑(scalarUnit u * (diffUnit R * writheUnit R)⁻¹) := by
  have hmul :
      diffUnit R * (scalarUnit u)⁻¹ * (scalarUnit u * (diffUnit R * writheUnit R)⁻¹) =
        (writheUnit R)⁻¹ := by
    rw [mul_comm (diffUnit R) (writheUnit R)]
    group
  rw [← Units.val_mul, hmul, coe_writheUnit_inv]

end LocalizationSetup

/-- Positive Markov stabilization identity `C * l * z = 1` for the generic normalization parameters
in `Localization.Away (T (-1) - T 1 : LaurentPolynomial R)`. -/
theorem localizationAway_T_sub_T_mul_mul_eq_one (u : Rˣ) :
    let s : LaurentPolynomial R := T (-1) - T 1
    let S := Localization.Away s
    let uS : Sˣ := Units.map (algebraMap R S : R →* S) u
    let lS : Sˣ := Units.map (algebraMap (LaurentPolynomial R) S : LaurentPolynomial R →* S)
      (genericUnit R)
    let vS : Sˣ := (IsLocalization.Away.algebraMap_isUnit s).unit
    (↑(vS * uS⁻¹) : S) * (lS : S) * ↑(uS * (vS * lS)⁻¹) = 1 := by
  intro s S uS lS vS
  have hmul : vS * uS⁻¹ * lS * (uS * (vS * lS)⁻¹) = 1 := by
    rw [mul_right_comm vS uS⁻¹ lS]
    group
  rw [← Units.val_mul, ← Units.val_mul]
  exact (congrArg Units.val hmul).trans Units.val_one

/-- Negative Markov stabilization identity `C * l⁻¹ * (z - (q - q⁻¹)) = 1` for the generic
normalization parameters in `Localization.Away (T (-1) - T 1 : LaurentPolynomial R)` when
`u = q - q⁻¹`. -/
theorem localizationAway_T_sub_T_mul_inv_mul_sub_eq_one {q u : Rˣ}
    (hu : (u : R) = (q : R) - ↑q⁻¹) :
    let s : LaurentPolynomial R := T (-1) - T 1
    let S := Localization.Away s
    let qS : Sˣ := Units.map (algebraMap R S : R →* S) q
    let uS : Sˣ := Units.map (algebraMap R S : R →* S) u
    let lS : Sˣ := Units.map (algebraMap (LaurentPolynomial R) S : LaurentPolynomial R →* S)
      (genericUnit R)
    let vS : Sˣ := (IsLocalization.Away.algebraMap_isUnit s).unit
    (↑(vS * uS⁻¹) : S) * (↑lS⁻¹ : S) * (↑(uS * (vS * lS)⁻¹) - ((qS : S) - ↑qS⁻¹)) = 1 := by
  dsimp only
  -- Rewrite `q - q⁻¹` as `u` and compute `z - u = u * v⁻¹ * l` using `v = l⁻¹ - l`.
  rw [← coe_scalarUnit_eq_sub hu]
  have hsub :
      (↑(scalarUnit u * (diffUnit R * writheUnit R)⁻¹) : Away R) - scalarUnit u =
        ↑(scalarUnit u * (diffUnit R)⁻¹ * writheUnit R) := by
    have hv : (↑(diffUnit R)⁻¹ : Away R) * ((↑(writheUnit R)⁻¹ : Away R) - writheUnit R) = 1 := by
      rw [← coe_diffUnit]
      exact (diffUnit R).inv_mul
    simp only [mul_inv_rev, Units.val_mul]
    linear_combination (scalarUnit u : Away R) * hv
  have hmul :
      diffUnit R * (scalarUnit u)⁻¹ * (writheUnit R)⁻¹ *
        (scalarUnit u * (diffUnit R)⁻¹ * writheUnit R) = 1 := by
    rw [mul_right_comm (diffUnit R) (scalarUnit u)⁻¹ (writheUnit R)⁻¹,
      mul_right_comm (scalarUnit u) (diffUnit R)⁻¹ (writheUnit R)]
    group
  rw [hsub, ← Units.val_mul, ← Units.val_mul]
  exact (congrArg Units.val hmul).trans Units.val_one

namespace MarkovBraid

open KnotTheory BraidGroup

/-- The normalized Ocneanu braid trace at the generic writhe unit `l = T 1` inside
`Localization.Away (T (-1) - T 1 : LaurentPolynomial R)`, where the strand factor
`C = (T (-1) - T 1) * u⁻¹` is invertible and the Ocneanu parameter is
`z = u * ((T (-1) - T 1) * T 1)⁻¹`. -/
def heckeUniversalTrace (β : MarkovBraid) (q u : Rˣ) :
    Localization.Away (T (-1) - T 1 : LaurentPolynomial R) :=
  β.heckeTrace
    (ocneanuTrace (Away R) (scalarUnit q) ↑(scalarUnit u * (diffUnit R * writheUnit R)⁻¹))
    ↑(diffUnit R * (scalarUnit u)⁻¹) (writheUnit R)

/-- Unfolding formula for `MarkovBraid.heckeUniversalTrace`. -/
theorem heckeUniversalTrace_def (β : MarkovBraid) (q u : Rˣ) :
    β.heckeUniversalTrace q u =
      let s : LaurentPolynomial R := T (-1) - T 1
      let S := Localization.Away s
      let qS : Sˣ := Units.map (algebraMap R S : R →* S) q
      let uS : Sˣ := Units.map (algebraMap R S : R →* S) u
      let lS : Sˣ := Units.map (algebraMap (LaurentPolynomial R) S : LaurentPolynomial R →* S)
        (genericUnit R)
      let vS : Sˣ := (IsLocalization.Away.algebraMap_isUnit s).unit
      β.heckeTrace (ocneanuTrace S qS ↑(uS * (vS * lS)⁻¹)) ↑(vS * uS⁻¹) lS := (rfl)

/-- Over every commutative ring `R`, `β.heckeUniversalTrace q u` lies in the image of
`LaurentPolynomial R` inside `Localization.Away (T (-1) - T 1)`. -/
private theorem exists_algebraMap_eq_heckeUniversalTrace (β : MarkovBraid) (q u : Rˣ) :
    ∃ P : LaurentPolynomial R,
      algebraMap (LaurentPolynomial R)
          (Localization.Away (T (-1) - T 1 : LaurentPolynomial R)) P =
        β.heckeUniversalTrace q u := by
  -- Apply finite-stage pole cancellation to the image `A` of `LaurentPolynomial R` inside `Away R`.
  let A : Subalgebra R (Away R) := (IsScalarTower.toAlgHom R (LaurentPolynomial R) (Away R)).range
  have hC : (↑(diffUnit R * (scalarUnit u)⁻¹) : Away R) ∈ A := by
    rw [← algebraMap_strandFactor, ← IsScalarTower.toAlgHom_apply (R := R)]
    exact AlgHom.mem_range_self _ _
  have hCz : (↑(diffUnit R * (scalarUnit u)⁻¹) : Away R) *
      ↑(scalarUnit u * (diffUnit R * writheUnit R)⁻¹) ∈ A := by
    rw [← strandFactor_mul_param, ← IsScalarTower.toAlgHom_apply (R := R)]
    exact AlgHom.mem_range_self _ _
  obtain ⟨P, hP⟩ := InfiniteTypeAHeckeAlgebra.pow_mul_ocneanuTrace_map_mem
    (coe_scalarUnit q).symm A hC hCz (InfiniteTypeAHeckeAlgebra.braidHom_mem_stage β.braid)
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, IsScalarTower.toAlgHom_apply,
    InfiniteTypeAHeckeAlgebra.map_braidHom] at hP
  -- Reassemble the writhe monomial `T w` with the scaled Ocneanu trace `P`.
  let w : ℤ := Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)
  refine ⟨T w * P, ?_⟩
  rw [map_mul, hP, ← coe_writheUnit_zpow, heckeUniversalTrace, heckeTrace_def]
  ring

/-- The unique regular Laurent polynomial in `LaurentPolynomial R` extending
`MarkovBraid.heckeUniversalTrace` across the zero-factor locus `T (-1) - T 1 = 0`. -/
def heckeRegularExtension (β : MarkovBraid) (q u : Rˣ) : LaurentPolynomial R :=
  (exists_algebraMap_eq_heckeUniversalTrace β q u).choose

/-- **Regularity of the generic normalized Ocneanu trace across `l = ±1`.** Inside
`Localization.Away (T (-1) - T 1 : LaurentPolynomial R)`, `β.heckeUniversalTrace q u` equals the
image of `β.heckeRegularExtension q u` over every commutative ring `R`. -/
@[simp]
theorem algebraMap_heckeRegularExtension (β : MarkovBraid) (q u : Rˣ) :
    algebraMap (LaurentPolynomial R)
        (Localization.Away (T (-1) - T 1 : LaurentPolynomial R))
        (β.heckeRegularExtension q u) =
      β.heckeUniversalTrace q u :=
  (exists_algebraMap_eq_heckeUniversalTrace β q u).choose_spec

/-- Any Laurent polynomial in `LaurentPolynomial R` whose image in
`Localization.Away (T (-1) - T 1)` agrees with `β.heckeUniversalTrace q u` equals
`β.heckeRegularExtension q u`. -/
theorem eq_heckeRegularExtension_of_algebraMap_eq {β : MarkovBraid} {q u : Rˣ}
    {P : LaurentPolynomial R}
    (hP : algebraMap (LaurentPolynomial R)
        (Localization.Away (T (-1) - T 1 : LaurentPolynomial R)) P =
      β.heckeUniversalTrace q u) :
    P = β.heckeRegularExtension q u :=
  (IsLocalization.Away.injective_iff_isRegular (T (-1) - T 1 : LaurentPolynomial R)).2
    (isRegular_T_sub_T (by decide : (-1 : ℤ) ≠ 1))
    (hP.trans (β.algebraMap_heckeRegularExtension q u).symm)

/-- **Existence and uniqueness of the regular Laurent polynomial extension** of the generic
normalized Ocneanu braid trace across `T (-1) - T 1 = 0`, over every commutative ring `R`. -/
theorem existsUnique_algebraMap_eq_heckeUniversalTrace (β : MarkovBraid) (q u : Rˣ) :
    ∃! P : LaurentPolynomial R,
      algebraMap (LaurentPolynomial R)
          (Localization.Away (T (-1) - T 1 : LaurentPolynomial R)) P =
        β.heckeUniversalTrace q u :=
  ⟨β.heckeRegularExtension q u, β.algebraMap_heckeRegularExtension q u,
    fun _ hP ↦ eq_heckeRegularExtension_of_algebraMap_eq hP⟩

/-- On the `(n + 1)`-strand identity braid, `heckeRegularExtension` is
`((T (-1) - T 1) * C ↑u⁻¹) ^ n`. -/
@[simp]
theorem heckeRegularExtension_one (q u : Rˣ) (n : ℕ) :
    heckeRegularExtension ⟨n, 1⟩ q u = ((T (-1) - T 1) * C (↑u⁻¹ : R)) ^ n := by
  symm
  refine eq_heckeRegularExtension_of_algebraMap_eq ?_
  rw [map_pow, algebraMap_strandFactor, heckeUniversalTrace]
  exact (heckeTrace_one (isMarkovTrace_ocneanuTrace _).map_one _ _).symm

/-- On a one-strand braid, `heckeRegularExtension` is `1`. -/
@[simp]
theorem heckeRegularExtension_one_strand (q u : Rˣ) (b : BraidGroup 1) :
    heckeRegularExtension ⟨0, b⟩ q u = 1 := by
  symm
  refine eq_heckeRegularExtension_of_algebraMap_eq ?_
  rw [map_one, heckeUniversalTrace]
  exact (heckeTrace_one_strand (isMarkovTrace_ocneanuTrace _).map_one _ _ b).symm

/-- Adding an uncrossed strand multiplies `heckeRegularExtension` by `(T (-1) - T 1) * C ↑u⁻¹`. -/
@[simp]
theorem heckeRegularExtension_strandIncl (q u : Rˣ) {n : ℕ} (b : BraidGroup (n + 1)) :
    heckeRegularExtension ⟨n + 1, strandIncl b⟩ q u =
      (T (-1) - T 1) * C (↑u⁻¹ : R) * heckeRegularExtension ⟨n, b⟩ q u := by
  symm
  refine eq_heckeRegularExtension_of_algebraMap_eq ?_
  rw [map_mul, algebraMap_heckeRegularExtension, algebraMap_strandFactor,
    heckeUniversalTrace, heckeUniversalTrace]
  exact ((ocneanuTrace (Away R) _ _).heckeTrace_strandIncl _ _ b).symm

/-- Skein relation of `heckeRegularExtension` in `LaurentPolynomial R`. -/
theorem heckeRegularExtension_skein (q u : Rˣ) {n : ℕ} (b c : BraidGroup (n + 1)) (i : Fin n) :
    T (-1) * heckeRegularExtension ⟨n, b * sigma (n := n + 1) i * c⟩ q u -
        T 1 * heckeRegularExtension ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ q u =
      C ((q : R) - ↑q⁻¹) * heckeRegularExtension ⟨n, b * c⟩ q u := by
  apply (IsLocalization.Away.injective_iff_isRegular (S := Away R)
      (T (-1) - T 1 : LaurentPolynomial R)).2
    (isRegular_T_sub_T (by decide : (-1 : ℤ) ≠ 1))
  simp only [map_sub, map_mul, algebraMap_heckeRegularExtension, ← coe_writheUnit_inv,
    ← coe_writheUnit, algebraMap_C_eq, ← coe_scalarUnit, map_inv, heckeUniversalTrace]
  exact heckeTrace_skein _ (writheUnit R) b c i

end MarkovBraid

/-- Markov-equivalent braids have equal `heckeUniversalTrace` when `u = q - q⁻¹`. -/
theorem MarkovEquiv.heckeUniversalTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) :
    β.heckeUniversalTrace q u = γ.heckeUniversalTrace q u := by
  rw [β.heckeUniversalTrace_def, γ.heckeUniversalTrace_def]
  exact h.heckeTrace_eq (isMarkovTrace_ocneanuTrace _) _ _
    (localizationAway_T_sub_T_mul_mul_eq_one u)
    (localizationAway_T_sub_T_mul_inv_mul_sub_eq_one hu)

/-- Markov-equivalent braids have equal `heckeRegularExtension` over any commutative ring when
`u = q - q⁻¹`. -/
theorem MarkovEquiv.heckeRegularExtension_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) :
    β.heckeRegularExtension q u = γ.heckeRegularExtension q u :=
  MarkovBraid.eq_heckeRegularExtension_of_algebraMap_eq
    ((β.algebraMap_heckeRegularExtension q u).trans (h.heckeUniversalTrace_eq hu))

namespace MarkovBraid

open KnotTheory BraidGroup

/-- When `R` receives a ring homomorphism `φ` from a field `K` and `u = q - q⁻¹`, the intrinsic
regular extension `β.heckeRegularExtension q u` agrees with evaluating `β.reducedHomfly K` at inner
variable `u` and outer variable `(genericUnit R)⁻¹`. -/
theorem heckeRegularExtension_eq_eval₂_reducedHomfly {K : Type*} [Field K] (φ : K →+* R)
    {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    β.heckeRegularExtension q u =
      eval₂ (C.comp (eval₂ φ u)) (genericUnit R)⁻¹ (β.reducedHomfly K) := by
  symm
  refine eq_heckeRegularExtension_of_algebraMap_eq ?_
  let ι : LaurentPolynomial R →+* Away R := algebraMap (LaurentPolynomial R) (Away R)
  have hu_map :
      Units.map (ι : LaurentPolynomial R →* Away R)
          (Units.map ((C : R →+* LaurentPolynomial R) : R →* LaurentPolynomial R) u) =
        scalarUnit u := by
    ext
    simp [ι, algebraMap_C_eq]
  have hιC : ι.comp (C.comp φ) = (algebraMap R (Away R)).comp φ :=
    RingHom.ext fun x ↦ by simp [ι, algebraMap_C_eq]
  have hcomp :
      ι.comp (C.comp (eval₂ φ u)) = eval₂ ((algebraMap R (Away R)).comp φ) (scalarUnit u) :=
    RingHom.ext fun p ↦ by simp [hom_eval₂, hιC, hu_map]
  have hl_inv :
      Units.map (ι : LaurentPolynomial R →* Away R) (genericUnit R)⁻¹ = (writheUnit R)⁻¹ := by
    ext
    simp [ι]
  have hC : (↑(diffUnit R * (scalarUnit u)⁻¹) : Away R) =
      ((↑(writheUnit R)⁻¹ : Away R) - writheUnit R) * ↑(scalarUnit u)⁻¹ := by
    rw [Units.val_mul, coe_diffUnit]
  have hz : ((↑(writheUnit R)⁻¹ : Away R) - writheUnit R) * ↑(scalarUnit u)⁻¹ *
      ↑(scalarUnit u * (diffUnit R * writheUnit R)⁻¹) = ↑(writheUnit R)⁻¹ := by
    rw [← hC, ← strandFactor_mul_param, coe_writheUnit_inv]
  rw [hom_eval₂, hcomp, hl_inv, heckeUniversalTrace, hC]
  exact eval₂_reducedHomfly_eq_heckeTrace β ((algebraMap R (Away R)).comp φ) (scalarUnit q)
    (scalarUnit u) (writheUnit R) (coe_scalarUnit_eq_sub hu) hz

/-- Evaluating `β.heckeRegularExtension q u` at any writhe unit `l₀ : Rˣ` agrees with
`eval₂ (eval₂ φ u) l₀⁻¹ (β.reducedHomfly K)` whenever `φ : K →+* R` is a ring homomorphism from a
field `K`. -/
theorem eval₂_heckeRegularExtension_eq_eval₂_reducedHomfly {K : Type*} [Field K] (φ : K →+* R)
    {q u : Rˣ} (hu : (u : R) = (q : R) - ↑q⁻¹) (l₀ : Rˣ) (β : MarkovBraid) :
    eval₂ (RingHom.id R) l₀ (β.heckeRegularExtension q u) =
      eval₂ (eval₂ φ u) l₀⁻¹ (β.reducedHomfly K) := by
  rw [heckeRegularExtension_eq_eval₂_reducedHomfly φ hu]
  have hcomp : (eval₂ (RingHom.id R) l₀).comp (C.comp (eval₂ φ u)) = eval₂ φ u :=
    RingHom.ext fun p ↦ by simp
  have hl : Units.map (eval₂ (RingHom.id R) l₀ : LaurentPolynomial R →* R) (genericUnit R)⁻¹ =
      l₀⁻¹ := by
    ext
    simp
  rw [hom_eval₂, hcomp, hl]

/-- Evaluating `heckeRegularExtension` at an arbitrary writhe unit `l₀ : Rˣ` multiplies by
`(l₀⁻¹ - l₀) * u⁻¹` when an uncrossed strand is added. -/
theorem eval₂_heckeRegularExtension_strandIncl (q u l₀ : Rˣ) {n : ℕ} (b : BraidGroup (n + 1)) :
    eval₂ (RingHom.id R) l₀ (heckeRegularExtension ⟨n + 1, strandIncl b⟩ q u) =
      ((↑l₀⁻¹ : R) - l₀) * ↑u⁻¹ * eval₂ (RingHom.id R) l₀ (heckeRegularExtension ⟨n, b⟩ q u) := by
  simp

/-- Evaluating `heckeRegularExtension` at an arbitrary writhe unit `l₀ : Rˣ` satisfies the skein
relation `l₀⁻¹ * F(L₊) - l₀ * F(L₋) = (q - q⁻¹) * F(L₀)` over every commutative ring `R`. -/
theorem eval₂_heckeRegularExtension_skein (q u l₀ : Rˣ) {n : ℕ} (b c : BraidGroup (n + 1))
    (i : Fin n) :
    (↑l₀⁻¹ : R) *
          eval₂ (RingHom.id R) l₀ (heckeRegularExtension ⟨n, b * sigma (n := n + 1) i * c⟩ q u) -
        (l₀ : R) * eval₂ (RingHom.id R) l₀
          (heckeRegularExtension ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ q u) =
      ((q : R) - ↑q⁻¹) * eval₂ (RingHom.id R) l₀ (heckeRegularExtension ⟨n, b * c⟩ q u) := by
  simpa only [map_sub, map_mul, eval₂_T, eval₂_C, zpow_neg_one, zpow_one, RingHom.id_apply] using
    congrArg (eval₂ (RingHom.id R) l₀) (heckeRegularExtension_skein q u b c i)

/-- **Universal specialization of `heckeRegularExtension` back to `heckeTrace`.** Over any
commutative ring `R`, for any Markov trace `τ` with parameter `z` normalized by `C * l₀ * z = 1`
and `C * l₀⁻¹ * (z - (q - q⁻¹)) = 1`, where `u = q - q⁻¹` is a unit, evaluating
`β.heckeRegularExtension q u` at `l₀` recovers `β.heckeTrace τ C l₀`. -/
theorem eval₂_heckeRegularExtension_eq_heckeTrace {q u l₀ : Rˣ} {z C : R}
    {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} (hτ : IsMarkovTrace z τ)
    (hpos : C * (l₀ : R) * z = 1)
    (hneg : C * (↑l₀⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    eval₂ (RingHom.id R) l₀ (β.heckeRegularExtension q u) = β.heckeTrace τ C l₀ := by
  have hC : ((↑l₀⁻¹ : R) - l₀) * ↑u⁻¹ = C := by
    rw [← hu] at hneg
    linear_combination -(↑l₀⁻¹ : R) * ↑u⁻¹ * hpos + (l₀ : R) * ↑u⁻¹ * hneg +
      C * ↑u⁻¹ * (u : R) * l₀.mul_inv + C * u.mul_inv
  refine congrFun (eq_heckeTrace_of_skein hτ hpos hneg
    (F := fun γ ↦ eval₂ (RingHom.id R) l₀ (γ.heckeRegularExtension q u))
    (fun _ _ h ↦ congrArg _ (h.heckeRegularExtension_eq hu))
    (fun n c i ↦ by
      simpa only [one_mul] using
        eval₂_heckeRegularExtension_skein q u l₀ (1 : BraidGroup (n + 1)) c i)
    (fun n b ↦ by rw [eval₂_heckeRegularExtension_strandIncl, hC])
    (by simp)) β

/-- At the `l = 1` zero-factor specialization (`C = 0`), adding an uncrossed strand kills the
invariant over every commutative ring `R`. -/
theorem eval₂_one_heckeRegularExtension_strandIncl (q u : Rˣ) {n : ℕ} (b : BraidGroup (n + 1)) :
    eval₂ (RingHom.id R) 1 (heckeRegularExtension ⟨n + 1, strandIncl b⟩ q u) = 0 := by
  simp

/-- At the `l = 1` zero-factor specialization, `heckeRegularExtension` satisfies the Conway skein
relation `F(L₊) - F(L₋) = (q - q⁻¹) * F(L₀)` over every commutative ring `R`. -/
theorem eval₂_one_heckeRegularExtension_skein (q u : Rˣ) {n : ℕ} (b c : BraidGroup (n + 1))
    (i : Fin n) :
    eval₂ (RingHom.id R) 1 (heckeRegularExtension ⟨n, b * sigma (n := n + 1) i * c⟩ q u) -
        eval₂ (RingHom.id R) 1
          (heckeRegularExtension ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ q u) =
      ((q : R) - ↑q⁻¹) * eval₂ (RingHom.id R) 1 (heckeRegularExtension ⟨n, b * c⟩ q u) := by
  simpa using eval₂_heckeRegularExtension_skein q u 1 b c i

/-- **Comparison with the normalized Burau Alexander invariant at `l = 1`.** Over every commutative
ring `R`, when `u = q - q⁻¹` and `s⁻¹ - s = q - q⁻¹` (for instance `s = q⁻¹`), evaluating the
regular extension at `l = 1` recovers `β.normalizedBurauAlexander s`. -/
theorem eval₂_one_heckeRegularExtension_eq_normalizedBurauAlexander {q u s : Rˣ}
    (hu : (u : R) = (q : R) - ↑q⁻¹)
    (hs : ((s⁻¹ : Rˣ) : R) - (s : R) = (q : R) - ↑q⁻¹) (β : MarkovBraid) :
    eval₂ (RingHom.id R) 1 (β.heckeRegularExtension q u) =
      β.normalizedBurauAlexander s := by
  refine congrFun (eq_of_skein (R := R) (M := R) 1 ((q : R) - ↑q⁻¹) 0
    (F := fun γ ↦ eval₂ (RingHom.id R) 1 (γ.heckeRegularExtension q u))
    (G := fun γ ↦ γ.normalizedBurauAlexander s)
    (fun _ _ h ↦ congrArg _ (h.heckeRegularExtension_eq hu))
    (fun _ _ h ↦ h.normalizedBurauAlexander_eq s)
    (fun n c i ↦ ?_) (fun n c i ↦ ?_) (fun n b ↦ ?_) (fun n b ↦ ?_) (by simp)) β
  · simpa using eval₂_one_heckeRegularExtension_skein q u (1 : BraidGroup (n + 1)) c i
  · simpa [hs] using normalizedBurauAlexander_skein (1 : BraidGroup (n + 1)) c i s
  · simp
  · simp

/-- At the `l = -1` zero-factor specialization (`C = 0`), adding an uncrossed strand kills the
invariant over every commutative ring `R`. -/
theorem eval₂_neg_one_heckeRegularExtension_strandIncl (q u : Rˣ) {n : ℕ}
    (b : BraidGroup (n + 1)) :
    eval₂ (RingHom.id R) (-1) (heckeRegularExtension ⟨n + 1, strandIncl b⟩ q u) = 0 := by
  simp

/-- At the `l = -1` zero-factor specialization, `heckeRegularExtension` satisfies the signed Conway
skein relation `-F(L₊) + F(L₋) = (q - q⁻¹) * F(L₀)` over every commutative ring `R`. -/
theorem eval₂_neg_one_heckeRegularExtension_skein (q u : Rˣ) {n : ℕ} (b c : BraidGroup (n + 1))
    (i : Fin n) :
    -eval₂ (RingHom.id R) (-1) (heckeRegularExtension ⟨n, b * sigma (n := n + 1) i * c⟩ q u) +
        eval₂ (RingHom.id R) (-1)
          (heckeRegularExtension ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ q u) =
      ((q : R) - ↑q⁻¹) * eval₂ (RingHom.id R) (-1) (heckeRegularExtension ⟨n, b * c⟩ q u) := by
  simpa [sub_neg_eq_add] using eval₂_heckeRegularExtension_skein q u (-1) b c i

/-- **Comparison with the normalized Burau Alexander invariant at `l = -1`.** Over every
commutative ring `R`, when `u = q - q⁻¹` and `s⁻¹ - s = q⁻¹ - q` (for instance `s = q`),
evaluating the regular extension at `l = -1` recovers `β.normalizedBurauAlexander s`. -/
theorem eval₂_neg_one_heckeRegularExtension_eq_normalizedBurauAlexander {q u s : Rˣ}
    (hu : (u : R) = (q : R) - ↑q⁻¹)
    (hs : ((s⁻¹ : Rˣ) : R) - (s : R) = (↑q⁻¹ : R) - q) (β : MarkovBraid) :
    eval₂ (RingHom.id R) (-1) (β.heckeRegularExtension q u) =
      β.normalizedBurauAlexander s := by
  refine congrFun (eq_of_skein (R := R) (M := R) 1 ((↑q⁻¹ : R) - q) 0
    (F := fun γ ↦ eval₂ (RingHom.id R) (-1) (γ.heckeRegularExtension q u))
    (G := fun γ ↦ γ.normalizedBurauAlexander s)
    (fun _ _ h ↦ congrArg _ (h.heckeRegularExtension_eq hu))
    (fun _ _ h ↦ h.normalizedBurauAlexander_eq s)
    (fun n c i ↦ ?_) (fun n c i ↦ ?_) (fun n b ↦ ?_) (fun n b ↦ ?_) (by simp)) β
  · have h := eval₂_neg_one_heckeRegularExtension_skein q u (1 : BraidGroup (n + 1)) c i
    simp only [one_mul] at h
    simp only [Units.val_one, inv_one, smul_eq_mul]
    linear_combination -h
  · simpa [hs] using normalizedBurauAlexander_skein (1 : BraidGroup (n + 1)) c i s
  · simp
  · simp

end MarkovBraid

end TauCeti
