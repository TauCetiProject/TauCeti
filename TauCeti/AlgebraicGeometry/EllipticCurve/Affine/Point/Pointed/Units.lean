/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.Data.ZMod.ValMinAbs
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Pointed.Basic

/-!
# Units acting on marked elliptic curves

Units modulo `N` act on elliptic curves with a marked point of exact order `N` by multiplying
that point through any integer representative. This action commutes with changes of variables
and with level lowering after reducing the unit to the lower level. At positive levels over ℂ,
a choice of primitive `N`-th root identifies this with the diamond action on μ-markings.

## Main results

* `TauCeti.PointedWeierstrassCurve.val_units_smul_of_intCast_eq`: computation through any integer
  representative of a unit.
* `TauCeti.PointedWeierstrassCurve.nsmulExactOrder_units_smul`: compatibility with level lowering.
-/

public section

namespace TauCeti.PointedWeierstrassCurve

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (X : PointedWeierstrassCurve F) {N : ℕ}

/-- Multiplying a marked point of exact order `N` by an integer `n` that is a unit modulo `N`
gives a point of exact order `N`. -/
theorem mk_zsmul_point_mem_exactOrder (hX : X ∈ exactOrder F N) {n : ℤ}
    (hn : IsUnit (n : ZMod N)) :
    (⟨X.curve, n • X.point⟩ : PointedWeierstrassCurve F) ∈ exactOrder F N := by
  obtain ⟨hE, hN⟩ := (mem_exactOrder_iff X).mp hX
  refine (mem_exactOrder_iff _).mpr ⟨hE, ?_⟩
  rw [← addOrderOf_nsmul_natAbs, Nat.Coprime.addOrderOf_nsmul, hN]
  rw [hN]
  exact Int.isCoprime_iff_gcd_eq_one.mp ((ZMod.isUnit_intCast_iff_isCoprime n N).mp hn)

section Units

/-- On a point of exact order `N`, multiplication by `n : ℤ` only depends on `n` modulo `N`. -/
private theorem zsmul_point_eq_of_intCast_eq (hX : X ∈ exactOrder F N) {m n : ℤ}
    (h : (m : ZMod N) = n) : m • X.point = n • X.point := by
  rw [zsmul_eq_zsmul_iff_modEq, ((mem_exactOrder_iff X).mp hX).2, ← ZMod.intCast_eq_intCast_iff,
    h]

/-- **Multiplying the marked point by a unit modulo `N`**: `d ∈ (ℤ/Nℤ)ˣ` sends an elliptic
curve `E` with a point `P` of exact order `N` to `(E, d • P)`, where `d` acts on `P` through any
integer representative (`TauCeti.PointedWeierstrassCurve.val_units_smul_of_intCast_eq`).
At positive level this acts on constant cyclic markings. Over ℂ, after choosing a primitive
`N`-th root `ζ_N`, the embedding `α : μ_N ↪ E[N]` with `α(ζ_N) = P` transforms as
`α ↦ α ∘ [d]`, the diamond operator `⟨d⟩`. -/
instance instSMulUnitsZModExactOrder : SMul (ZMod N)ˣ (exactOrder F N) where
  smul d X := ⟨⟨X.val.curve, (d : ZMod N).valMinAbs • X.val.point⟩,
    mk_zsmul_point_mem_exactOrder X.val X.property (by rw [ZMod.coe_valMinAbs]; exact d.isUnit)⟩

variable (d : (ZMod N)ˣ) (Y : exactOrder F N)

/-- The unit `d` multiplies the marked point by the representative `(d : ZMod N).valMinAbs`. -/
@[simp]
theorem val_units_smul :
    ((d • Y : exactOrder F N) : PointedWeierstrassCurve F) =
      ⟨Y.val.curve, (d : ZMod N).valMinAbs • Y.val.point⟩ :=
  (rfl)

/-- The unit `d` multiplies the marked point by any integer representative of `d`. -/
theorem val_units_smul_of_intCast_eq {n : ℤ} (hn : (n : ZMod N) = d) :
    ((d • Y : exactOrder F N) : PointedWeierstrassCurve F) = ⟨Y.val.curve, n • Y.val.point⟩ := by
  rw [val_units_smul, mk_inj]
  exact zsmul_point_eq_of_intCast_eq Y.val Y.property (by rw [ZMod.coe_valMinAbs, hn])

/-- The units modulo `N` act on the elliptic curves with a point of exact order `N` by
multiplying the marked point. -/
instance instMulActionUnitsZModExactOrder : MulAction (ZMod N)ˣ (exactOrder F N) where
  one_smul X := Subtype.ext <| by
    rw [val_units_smul_of_intCast_eq 1 X (n := 1) (by simp), one_zsmul]
  mul_smul d e X := Subtype.ext <| by
    have h : (((d : ZMod N).valMinAbs * (e : ZMod N).valMinAbs : ℤ) : ZMod N) = (d * e : _) := by
      rw [Int.cast_mul, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs, Units.val_mul]
    rw [val_units_smul_of_intCast_eq (d * e) X h, val_units_smul d, val_units_smul e, mul_zsmul]

/-- Changes of variables commute with multiplying the marked point by a unit modulo `N`, so the
units act on the isomorphism classes of elliptic curves with a point of exact order `N`. -/
instance instSMulCommClassVariableChangeUnitsZModExactOrder :
    SMulCommClass (VariableChange F) (ZMod N)ˣ (exactOrder F N) where
  smul_comm C d X := Subtype.ext <| by
    rw [SubMulAction.val_smul, val_units_smul, val_units_smul, SubMulAction.val_smul]
    exact smul_mk_zsmul_point C X.val _

/-- Multiplication of the marked point by `M` commutes with diamonds after reducing
units from modulus `N * M` to modulus `N`. -/
@[simp]
theorem nsmulExactOrder_units_smul (M : ℕ) [NeZero M] (d : (ZMod (N * M))ˣ)
    (X : exactOrder F (N * M)) :
    nsmulExactOrder N M (d • X) =
      ZMod.unitsMap (dvd_mul_right N M) d • nsmulExactOrder N M X := by
  have hd : (((d : ZMod (N * M)).valMinAbs : ℤ) : ZMod N) =
      ZMod.unitsMap (dvd_mul_right N M) d := by
    rw [ZMod.unitsMap_val, ← ZMod.cast_intCast (dvd_mul_right N M), ZMod.coe_valMinAbs]
  apply Subtype.ext
  rw [val_nsmulExactOrder_apply, val_units_smul,
    val_units_smul_of_intCast_eq _ _ hd, val_nsmulExactOrder_apply]
  exact mk_inj.mpr (smul_comm _ _ _)

end Units

end TauCeti.PointedWeierstrassCurve
