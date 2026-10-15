/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Coordinates
public import TauCeti.Analysis.Normed.Field.ZPowers

/-!
# Multiplicative parameters for Tate uniformisation

The two Tate coordinate series descend to `Kˣ ⧸ Subgroup.zpowers q` by their established
periodicity. `tateQuotientCoordinates` records the pair of descended coordinates, and
`tateQuotientCoordinates_eq_normalized` evaluates them at the unique representative in the
fundamental annulus `‖q‖ < ‖u‖ ≤ 1`.

The identity coset is the exceptional parameter intended to map to the point at infinity.
The descended coordinates at the identity retain the totalised values of the series; they are
not asserted to be coordinates of a point on the curve. Neither the Weierstrass equation nor the
group homomorphism property of uniformisation is asserted in this file.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K]

/-- The pair of Tate coordinate series on the multiplicative quotient. At the identity coset
these are totalised series values, not a representation of the point at infinity. -/
noncomputable def tateQuotientCoordinates (q : Kˣ) :
    (Kˣ ⧸ Subgroup.zpowers q) → K × K :=
  Quotient.lift (fun u ↦ (tateUniformizationX q u, tateUniformizationY q u)) fun u v huv ↦ by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.leftRel_apply.mp huv)
    have hv : v = q ^ n * u := by
      rw [hn]
      simp
    rw [hv, tateUniformizationX_zpow_mul, tateUniformizationY_zpow_mul]

/-- Descending the coordinates preserves their values on every representative. -/
@[simp]
theorem tateQuotientCoordinates_mk (q u : Kˣ) :
    tateQuotientCoordinates q (u : Kˣ ⧸ Subgroup.zpowers q) =
      (tateUniformizationX q u, tateUniformizationY q u) :=
  (rfl)

/-- The descended coordinate series can be evaluated on the unique representative in the
half-open fundamental annulus. This does not require a discrete value group. -/
theorem tateQuotientCoordinates_eq_normalized (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Kˣ ⧸ Subgroup.zpowers q) :
    tateQuotientCoordinates q x =
      (tateUniformizationX q (unitsQuotientZPowersEquivAnnulus q hq x).val,
        tateUniformizationY q (unitsQuotientZPowersEquivAnnulus q hq x).val) := by
  rw [← tateQuotientCoordinates_mk, mk_unitsQuotientZPowersEquivAnnulus]

/-- Inversion on the quotient gives the negation formula of the Tate Weierstrass equation. -/
@[simp]
theorem tateQuotientCoordinates_inv [CompleteSpace K] [IsUltrametricDist K]
    (q : Kˣ) (hq : ‖(q : K)‖ < 1) (x : Kˣ ⧸ Subgroup.zpowers q) :
    tateQuotientCoordinates q x⁻¹ =
      ((tateQuotientCoordinates q x).1,
        -(tateQuotientCoordinates q x).2 - (tateQuotientCoordinates q x).1) := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_inv, tateQuotientCoordinates_mk, tateQuotientCoordinates_mk]
    simp [tateUniformizationY_inv q hq]

end TauCeti
