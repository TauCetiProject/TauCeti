/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Basic

/-!
# The Frobenius over an extension of the finite base

Let `W` be a Weierstrass curve over a finite field `F` with `q` elements, and `K` an extension of
`F`. The `q`-power Frobenius isogeny of `W` base-changes along `F → K` to an isogeny `π` of `W⁄K`,
`TauCeti.Isogeny.baseChangeFrobenius`. Its pullback raises the functions defined over `F`, the
generic coordinates in particular, to the `q`-th power. Over `K` itself the `q`-power map is not
the identity, and it is this base change that acts on the points of `W` over `K`.

## Main definitions

* `TauCeti.Isogeny.baseChangeFrobenius`: the `q`-power Frobenius of `W`, as an isogeny of `W⁄K`.

## Main results

* `TauCeti.Isogeny.baseChangeFrobenius_pullback`: its coordinate pullback is the base change of the
  `q`-power Frobenius pullback of `W`.
* `TauCeti.Isogeny.baseChangeFrobenius_def`: identifies the base-changed Frobenius with
  `Isogeny.map`, allowing scalar-extension results to transfer to `W⁄K`.
* `TauCeti.Isogeny.fieldPullback_baseChangeFrobenius_map`: its pullback raises the functions
  defined over `F` to the `q`-th power.
* `TauCeti.Isogeny.fieldPullback_baseChangeFrobenius_genericX` and
  `TauCeti.Isogeny.fieldPullback_baseChangeFrobenius_genericY`: in particular the generic
  coordinates.
* `TauCeti.Isogeny.fieldPullback_baseChangeFrobenius_mapBaseChange`: following coefficient
  Frobenius by pullback raises every function to the `#F`-th power, by extensionality on the
  constants and generic coordinates.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

section

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K] (W : WeierstrassCurve.Affine F)

variable (K) in
/-- **The Frobenius of `W` over an extension `K` of its finite base**: the base change of the
`q`-power Frobenius isogeny, read as an isogeny of `W⁄K`. -/
noncomputable def baseChangeFrobenius : Isogeny (W⁄K).toAffine (W⁄K).toAffine :=
  (frobeniusIsogeny W).map (algebraMap F K)

/-- Identify `baseChangeFrobenius K W` with the `Isogeny.map` presentation over
`W.map (algebraMap F K)`, so scalar-extension results transfer to `W⁄K` without unfolding
the definition in an importing module. -/
theorem baseChangeFrobenius_def :
    baseChangeFrobenius K W = (frobeniusIsogeny W).map (algebraMap F K) := (rfl)

/-- **The coordinate pullback of `baseChangeFrobenius`** is the base change along `F → K` of the
`q`-power Frobenius pullback of `W`. -/
@[simp]
theorem baseChangeFrobenius_pullback :
    (baseChangeFrobenius K W).pullback = (frobeniusPullback W).map (algebraMap F K) := by
  rw [baseChangeFrobenius, map_pullback, frobeniusIsogeny_pullback]

/-- **The pullback of `baseChangeFrobenius` raises the functions defined over `F` to the `q`-th
power.** -/
-- Not `@[simp]`: `FunctionField.map W (algebraMap F K) z` lives in the function field of
-- `W.map (algebraMap F K)`, which is `W⁄K` only after unfolding `WeierstrassCurve.baseChange`, so
-- the rewritten goal `a ^ q = a ^ q` compares powers in two syntactically different fields and
-- `simp` cannot close the lemma's own statement. The generic-coordinate forms below are simp.
theorem fieldPullback_baseChangeFrobenius_map (z : W.FunctionField) :
    (baseChangeFrobenius K W).fieldPullback (FunctionField.map W (algebraMap F K) z) =
      FunctionField.map W (algebraMap F K) z ^ Nat.card F := by
  refine (map_fieldPullback_map (frobeniusIsogeny W) (algebraMap F K) z).trans ?_
  rw [fieldPullback_frobeniusIsogeny_apply, map_pow]

/-- **The pullback of `baseChangeFrobenius` raises the generic `x`-coordinate to the `q`-th
power.** -/
@[simp]
theorem fieldPullback_baseChangeFrobenius_genericX :
    (baseChangeFrobenius K W).fieldPullback (genericX (W⁄K).toAffine) =
      genericX (W⁄K).toAffine ^ Nat.card F :=
  FunctionField.map_genericX W (algebraMap F K) ▸ fieldPullback_baseChangeFrobenius_map W _

/-- **The pullback of `baseChangeFrobenius` raises the generic `y`-coordinate to the `q`-th
power.** -/
@[simp]
theorem fieldPullback_baseChangeFrobenius_genericY :
    (baseChangeFrobenius K W).fieldPullback (genericY (W⁄K).toAffine) =
      genericY (W⁄K).toAffine ^ Nat.card F :=
  FunctionField.map_genericY W (algebraMap F K) ▸ fieldPullback_baseChangeFrobenius_map W _

end

section ArithmeticFrobenius

variable {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
  (W : WeierstrassCurve.Affine F)

/-- The pullback of base-field Frobenius after Frobenius on coefficients is the
`#F`-power map on the entire function field, for any extension field `K`. -/
theorem fieldPullback_baseChangeFrobenius_mapBaseChange
    (z : (W⁄K).toAffine.FunctionField) :
    (baseChangeFrobenius K W).fieldPullback
      (W.functionFieldMapBaseChange (FiniteField.frobeniusAlgHom F K) z) =
      z ^ Fintype.card F := by
  obtain ⟨hc, hx, hy⟩ := W.functionFieldMapBaseChange_spec (FiniteField.frobeniusAlgHom F K)
  have h : (baseChangeFrobenius K W).fieldPullback.toRingHom.comp
      (W.functionFieldMapBaseChange (FiniteField.frobeniusAlgHom F K)) =
      (FiniteField.frobeniusAlgHom F (W⁄K).toAffine.FunctionField).toRingHom := by
    apply FunctionField.ringHom_ext <;>
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hc, hx, hy,
        AlgHom.commutes, FiniteField.frobeniusAlgHom_apply, map_pow,
        fieldPullback_baseChangeFrobenius_genericX, fieldPullback_baseChangeFrobenius_genericY,
        Fintype.card_eq_nat_card]
    exact fun _ ↦ trivial
  exact RingHom.congr_fun h z

end ArithmeticFrobenius

end TauCeti.Isogeny

end
