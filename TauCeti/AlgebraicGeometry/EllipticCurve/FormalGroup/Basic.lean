/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Fin2
public import Mathlib.RingTheory.FormalGroup.Basic
public import TauCeti.RingTheory.FormalGroup.NSMul.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Inverse
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# The formal group law of a Weierstrass curve

The chord construction at the point at infinity gives an addition series `formalAdd W`. This file
packages that series as Mathlib's one-dimensional `FormalGroup`: the two variables are reindexed
from the named sum `Unit ⊕ Unit` to `Fin 2`, and the previously established constant, linear, and
associativity identities supply the structure fields.

The resulting formal group is commutative because the chord addition series is symmetric. Thus
Mathlib's `FormalGroup.Point` construction gives an additive commutative monoid of
power-series-valued points whose constant coefficient is nilpotent.

## Main definitions

* `WeierstrassCurve.formalGroup`: the one-dimensional formal group law attached to a Weierstrass
  curve.

## Main results

* `WeierstrassCurve.isComm_formalGroup`: the elliptic formal group law is commutative.
* `WeierstrassCurve.map_formalGroup`: the construction commutes with base change.
* `WeierstrassCurve.formalGroup_addInvX`: the abstract inverse is the geometric inverse parameter.
* `WeierstrassCurve.nsmulSeries_two_formalGroup`: doubling is the inverse of the third
  intersection parameter of the tangent.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

The addition series and its laws are adapted in the imported modules from Michael Stoll's
`EllipticCurves` project (`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`. The packaging here is original: that source uses its
own formal-group-law structure, whereas this development refounds the construction on Mathlib's
`RingTheory/FormalGroup` API.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries TauCeti

variable {R : Type*} [CommRing R]

/-- The one-dimensional commutative formal group law of a Weierstrass curve, obtained by
reindexing the chord addition series from `Unit ⊕ Unit` to Mathlib's `Fin 2` convention. -/
noncomputable def formalGroup (W : WeierstrassCurve R) : FormalGroup R where
  toPowerSeries := rename unitSumUnitEquivFinTwo (formalAdd W)
  zero_constantCoeff := by simp
  lin_coeff_X := coeff_single_zero_rename_unitSumUnitEquivFinTwo_formalAdd W
  lin_coeff_Y := coeff_single_one_rename_unitSumUnitEquivFinTwo_formalAdd W
  assoc := rename_unitSumUnitEquivFinTwo_assoc (formalAdd W) (constantCoeff_formalAdd W)
    (formalAdd_assoc W)

/-- The underlying `Fin 2`-indexed series of the formal group law is the reindexed chord addition
series. -/
@[simp]
theorem formalGroup_toPowerSeries (W : WeierstrassCurve R) :
    (formalGroup W).toPowerSeries = rename unitSumUnitEquivFinTwo (formalAdd W) :=
  by simp [formalGroup]

/-- Base change of a Weierstrass curve commutes with passage to its formal group law. -/
@[simp]
theorem map_formalGroup {S : Type*} [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S) :
    formalGroup (W.map φ) = (formalGroup W).map φ := by
  apply FormalGroup.ext
  simp [formalGroup, MvPowerSeries.rename_map]

/-- The formal group law of a Weierstrass curve is commutative. This makes its power-series-valued
points whose constant coefficient is nilpotent an additive commutative monoid through Mathlib's
standard instance. -/
noncomputable instance isComm_formalGroup (W : WeierstrassCurve R) :
    (formalGroup W).IsComm where
  comm := by
    rw [formalGroup_toPowerSeries,
      MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _ HasSubst.X_X]
    nth_rw 1 [← rename_swap_formalAdd W]
    rw [rename_rename, rename_eq_subst]
    congr 1
    funext s
    rcases s with u | u <;> cases u <;>
      simp [Function.comp_def]

/-- The inverse series of the formal group is the parameter of geometric negation. -/
theorem formalGroup_addInvX (W : WeierstrassCurve R) :
    (formalGroup W).addInvX = W.formalInverse := by
  apply Eq.symm
  apply ((formalGroup W).eq_addInvX_iff_subst_right_eq_zero W.hasSubst_formalInverse).mpr
  rw [formalGroup_toPowerSeries,
    MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (by
        intro i
        fin_cases i
        · exact PowerSeries.constantCoeff_X
        · exact W.constantCoeff_formalInverse))]
  convert W.subst_invPair_formalAdd using 1
  congr 1
  funext i
  rcases i with i | i <;> cases i <;> simp
  -- The one-variable `PowerSeries.X` is `MvPowerSeries.X ()`.
  rfl

/-- The doubling series is the geometric inverse of the tangent's third intersection parameter.
This identity holds for every Weierstrass curve over a commutative ring. -/
theorem nsmulSeries_two_formalGroup (W : WeierstrassCurve R) :
    (formalGroup W).nsmulSeries 2 = PowerSeries.subst
      (subst (fun _ : Unit ⊕ Unit => (PowerSeries.X : PowerSeries R)) W.formalThirdRoot)
      W.formalInverse := by
  have hX : HasSubst (fun _ : Unit ⊕ Unit => (PowerSeries.X : PowerSeries R)) :=
    hasSubst_of_constantCoeff_zero fun _ => PowerSeries.constantCoeff_X
  rw [FormalGroup.nsmulSeries_succ, FormalGroup.nsmulSeries_one,
    formalGroup_toPowerSeries, subst_rename _ _ (PowerSeries.hasSubst_pair
      PowerSeries.constantCoeff_X PowerSeries.constantCoeff_X)]
  have hfamily : (![PowerSeries.X, PowerSeries.X] : Fin 2 → PowerSeries R) ∘
      unitSumUnitEquivFinTwo = fun _ => PowerSeries.X := by
    funext s
    rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp
  rw [hfamily, formalAdd_def, ← PowerSeries.subst_def,
    subst_powerSeriesSubst hX
      (PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_formalThirdRoot)]

end WeierstrassCurve
