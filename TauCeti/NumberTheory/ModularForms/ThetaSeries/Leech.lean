/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.ModelShell
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Minimum
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.RankTwentyFour

/-!
# The theta series of the Leech lattice

The real model of `TauCeti.leechLattice` has theta series
`Θ_Λ = E₄³ - 720 Δ = E₁₂ - (65520/691) Δ`, where `E₁₂` is the normalized Eisenstein series of
weight `12`. Consequently, writing `τ(m)` for the `m`-th `q`-coefficient of `Δ` (Ramanujan's
function), the Leech lattice has

`r_Λ(2m) = (65520/691) (σ₁₁(m) - τ(m))`

vectors of rational norm `2m` for every `m ≥ 1`. With `σ₁₁(2) = 2049` and `τ(2) = -24`, the case
`m = 2` is `(65520/691) · 2073 = 196560`, the kissing number. The same value comes out of the
quadratic coefficient of `E₄³ - 720 Δ` (`ZLattice.IsEven.representationNumber_four_of_rootless`),
independently of the enumeration of minimal vectors in
`TauCeti.ncard_vectorsOfNorm_four_leechLattice`.

The lattice is the existing Construction B model. Its positive definiteness, evenness,
unimodularity and rank pass to `IntegralLattice.realModel`, and its rootlessness
(`TauCeti.vectorsOfNorm_two_leechLattice`) is the only coefficient that enters: the identities are
the rootless case of the rank-`24` formulas
`ZLattice.IsEven.thetaSeries_eq_E₄_cube_add_mul_discriminant` and
`ZLattice.IsEven.thetaSeries_eq_E_twelve_add_mul_discriminant`. The shell comparison
`IntegralLattice.representationNumber_realModel` transfers coefficients between the rational
lattice and its real model.

## Main results

* `TauCeti.IntegralLattice.thetaSeries_realModel_leechLattice_eq_E₄_cube_sub_mul_discriminant`:
  `Θ_Λ = E₄³ - 720 Δ`.
* `TauCeti.IntegralLattice.thetaSeries_realModel_leechLattice_eq_E_twelve_sub_mul_discriminant`:
  `Θ_Λ = E₁₂ - (65520/691) Δ`.
* `TauCeti.IntegralLattice.representationNumber_leechLattice_two_mul`:
  `r_Λ(2m) = (65520/691) (σ₁₁(m) - τ(m))` for `m ≠ 0`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VII, §6.6.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11.
-/

public section

open UpperHalfPlane ModularForm
open scoped ArithmeticFunction.sigma

namespace TauCeti.IntegralLattice

private theorem isEven_realModel_leechLattice :
    ZLattice.IsEven (leechLattice.realModel isPosDef_leechLattice) :=
  (leechLattice.isEven_realModel_iff _).mpr isEven_leechLattice

private theorem isUnimodular_realModel_leechLattice :
    ZLattice.IsUnimodular (leechLattice.realModel isPosDef_leechLattice) :=
  (leechLattice.isUnimodular_realModel_iff _).mpr isUnimodular_leechLattice

private theorem finrank_realModelSpace_leechLattice :
    Module.finrank ℝ (leechLattice.RealModelSpace isPosDef_leechLattice) = 24 := by
  rw [RealModelSpace.finrank_eq, finrank_leechLattice]

/-- The real model of the Leech lattice has no vector of squared norm `2`. -/
private theorem representationNumber_realModel_leechLattice_two :
    ZLattice.representationNumber (leechLattice.realModel isPosDef_leechLattice) 2 = 0 := by
  have h := leechLattice.representationNumber_realModel isPosDef_leechLattice 2
  rw [Rat.cast_ofNat, representationNumber_def, vectorsOfNorm_two_leechLattice,
    Set.ncard_empty] at h
  exact h

/-- **The theta series of the Leech lattice is `E₄³ - 720 Δ`.** -/
theorem thetaSeries_realModel_leechLattice_eq_E₄_cube_sub_mul_discriminant (τ : ℍ) :
    ZLattice.thetaSeries (leechLattice.realModel isPosDef_leechLattice) τ =
      E₄ τ ^ 3 - 720 * ModularForm.discriminant τ := by
  rw [isEven_realModel_leechLattice.thetaSeries_eq_E₄_cube_add_mul_discriminant
    isUnimodular_realModel_leechLattice finrank_realModelSpace_leechLattice,
    representationNumber_realModel_leechLattice_two]
  ring

/-- **The theta series of the Leech lattice is `E₁₂ - (65520/691) Δ`**, where `E₁₂` is the
normalized Eisenstein series of weight `12`. -/
theorem thetaSeries_realModel_leechLattice_eq_E_twelve_sub_mul_discriminant (τ : ℍ) :
    ZLattice.thetaSeries (leechLattice.realModel isPosDef_leechLattice) τ =
      ModularForm.E (by norm_num : 3 ≤ 12) τ - 65520 / 691 * ModularForm.discriminant τ := by
  rw [isEven_realModel_leechLattice.thetaSeries_eq_E_twelve_add_mul_discriminant
    isUnimodular_realModel_leechLattice finrank_realModelSpace_leechLattice,
    representationNumber_realModel_leechLattice_two]
  ring

/-- **Representation numbers of the Leech lattice**: for every `m ≥ 1`, the Leech lattice has
`(65520/691) (σ₁₁(m) - τ(m))` vectors of norm `2m`, where `τ(m)` is the `m`-th `q`-coefficient of
`Δ`. -/
theorem representationNumber_leechLattice_two_mul {m : ℕ} (hm : m ≠ 0) :
    (leechLattice.representationNumber (2 * m) : ℂ) =
      65520 / 691 * (σ 11 m - (qExpansion 1 ModularForm.discriminant).coeff m) := by
  have h := isEven_realModel_leechLattice.representationNumber_two_mul_of_finrank_eq_twenty_four
    isUnimodular_realModel_leechLattice finrank_realModelSpace_leechLattice hm
  have hq := leechLattice.representationNumber_realModel isPosDef_leechLattice (2 * m)
  rw [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] at hq
  rw [representationNumber_realModel_leechLattice_two, hq] at h
  rw [h]
  ring

end TauCeti.IntegralLattice
