/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere

/-!
# The signature of the level-one modular curve

The orbifold signature of a cofinite Fuchsian group `Γ` records the genus `g` of its compactified
quotient `X(Γ)`, the orders `mₑ` of its elliptic orbits and its number `s` of cusps. The area of
the quotient is then `2π (2g - 2 + ∑ₑ (1 - 1 / mₑ) + s)`. This file computes the data of the
level-one modular curve `X(1)`, the compactified quotient of `ℍ` by the effective image of
`PSL(2, ℤ)` in `PSL(2, ℝ)`, and checks that formula for it. The signature is `(0; 2, 3; 1)`.

* The topological genus is read off the Euler characteristic, through `χ = 2 - 2g`. The
  normalized modular invariant identifies `X(1)` biholomorphically with the Riemann sphere
  (`TauCeti.ModularGroup.jBiholomorph`), which is homeomorphic to the `2`-sphere. Hence `X(1)` has
  finite CW type and Euler characteristic `2`, so genus zero.
* The elliptic orbits are the orbits of `ρ = e^{2πi/3}` and `i`, with stabilizers of orders `3`
  and `2`, so `∑ₑ (1 - 1 / mₑ) = 7 / 6`.
* There is exactly one cusp (`TauCeti.ModularGroup.instUniqueCuspOrbit`).
* The covolume of the group is `π / 3` (`TauCeti.ModularGroup.covolume_psl2zToPSL2RRange`), which
  is `2π (-χ(X(1)) + 7 / 6 + 1)`.

The Euler characteristic is the finite-CW Euler characteristic `TauCeti.eulerChar` of the
topological space `X(1)`. It is transported through the biholomorphism constructed from `j`, after
the compactified quotient and its complex structure already exist.

## Main results

* `TauCeti.ModularGroup.eulerChar_compactifiedQuotient`: `χ(X(1)) = 2`.
* `TauCeti.ModularGroup.ellipticOrbits_psl2zToPSL2RRange`: the elliptic orbits are those of `ρ`
  and `i`.
* `TauCeti.ModularGroup.finsum_mem_ellipticOrbits_psl2zToPSL2RRange`:
  `∑ₑ (1 - 1 / mₑ) = 7 / 6` over the elliptic orbits.
* `TauCeti.ModularGroup.covolume_psl2zToPSL2RRange_eq_two_pi_mul`: the orbifold area formula
  `covolume = 2π (-χ(X(1)) + ∑ₑ (1 - 1 / mₑ) + s)` for the level-one group.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.3 and 3.1 (the elliptic points, cusp and genus of `X(1)`).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.3 (the signature and the area of a fundamental region).
-/

public section

noncomputable section

open MulAction UpperHalfPlane
open scoped MatrixGroups Real

namespace TauCeti.ModularGroup

/-- The level-one modular curve has finite CW type: the normalized modular invariant identifies it
with the Riemann sphere. -/
instance finiteCWType_compactifiedQuotient :
    FiniteCWType psl2zToPSL2R.range.CompactifiedQuotient :=
  jBiholomorph.toHomeomorph.finiteCWType

/-- **The Euler characteristic of the level-one modular curve** is `2`, that of the Riemann sphere,
with which the normalized modular invariant identifies it. Through `χ = 2 - 2g`, the curve has
topological genus zero. -/
@[simp]
theorem eulerChar_compactifiedQuotient :
    eulerChar psl2zToPSL2R.range.CompactifiedQuotient = 2 := by
  rw [jBiholomorph.toHomeomorph.eulerChar_eq, eulerChar_onePoint, Complex.finrank_real_complex]
  norm_num

/-- **The elliptic orbits of the modular group** are the orbits of `ρ` and of `i`. -/
theorem ellipticOrbits_psl2zToPSL2RRange :
    psl2zToPSL2R.range.ellipticOrbits =
      {Quotient.mk (orbitRel psl2zToPSL2R.range ℍ) ρ, Quotient.mk _ I} := by
  ext q
  induction q using Quotient.inductionOn with
  | h z =>
    rw [Subgroup.quotientMk_mem_ellipticOrbits_iff, mem_freeLocus,
      stabilizer_psl2zToPSL2RRange_eq_bot_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- The elliptic defect sum of the modular group: its elliptic orbits, of orders `3` and `2`, give
`(1 - 1 / 3) + (1 - 1 / 2) = 7 / 6`. This is the elliptic term subtracted from the Euler
characteristic in the orbifold Euler characteristic, and added in the area formula. -/
theorem finsum_mem_ellipticOrbits_psl2zToPSL2RRange :
    ∑ᶠ e ∈ psl2zToPSL2R.range.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) = 7 / 6 := by
  have hne : Quotient.mk (orbitRel psl2zToPSL2R.range ℍ) ρ ≠ Quotient.mk _ I := fun h ↦
    orbit_mk_I_ne_orbit_mk_ρ (quotientMk_psl2zToPSL2RRange_eq_iff_quotientMk_sl_eq.mp h).symm
  rw [ellipticOrbits_psl2zToPSL2RRange, finsum_mem_pair hne,
    cardStabilizerOnOrbit_mk ρ, cardStabilizerOnOrbit_mk I, card_stabilizer_psl2zToPSL2RRange_ρ,
    card_stabilizer_psl2zToPSL2RRange_I]
  norm_num

/-- **The orbifold area formula for the modular group.** The covolume of the effective level-one
group is `2π (2g - 2 + ∑ₑ (1 - 1 / mₑ) + s)`, where `2 - 2g` is the Euler characteristic of the
level-one modular curve, `e` runs over the elliptic orbits with stabilizer orders `mₑ`, and `s` is
the number of cusps. Both sides equal `π / 3`. -/
theorem covolume_psl2zToPSL2RRange_eq_two_pi_mul :
    MeasureTheory.covolume psl2zToPSL2R.range ℍ = ENNReal.ofReal (2 * π *
      (-eulerChar psl2zToPSL2R.range.CompactifiedQuotient +
        ∑ᶠ e ∈ psl2zToPSL2R.range.ellipticOrbits, (1 - (cardStabilizerOnOrbit e : ℝ)⁻¹) +
          Nat.card psl2zToPSL2R.range.CuspOrbit)) := by
  rw [covolume_psl2zToPSL2RRange, eulerChar_compactifiedQuotient,
    finsum_mem_ellipticOrbits_psl2zToPSL2RRange, Nat.card_unique]
  congr 1
  push_cast
  ring

end TauCeti.ModularGroup
