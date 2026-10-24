/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.MvPowerSeries.Substitution
import Mathlib.Tactic.LinearCombination

/-!
# The formal inverse of a formal group law

Let `F(X, Y)` be a one-dimensional formal group law over a commutative ring `R`. Its **formal
inverse** is the power series `i(X)` with zero constant coefficient such that

  `F(i(X), X) = 0 = F(X, i(X))`.

It exists over every commutative ring and is unique. Writing `F(X, Y) = X + Y + ⋯`, the
coefficient of `Xⁿ` in `F(f(X), X)` for a series `f` without constant term depends only on the
coefficients of `f` up to degree `n`, and the coefficient of `Xⁿ` in `f` enters it with the
linear coefficient `1` of `F` in its first variable
(`PowerSeries.coeff_subst_update_add_X_pow_mul`). So the coefficients of `i` are determined one
degree at a time, each killing the next coefficient of `F(i(X), X)`.

Substituting into the formal inverse negates the power-series points of `F`: for `x` in Mathlib's
monoid `F.Point σ` of series with nilpotent constant coefficient, `-x = i(x)`. This makes
`F.Point σ` a group, commutative when `F` is, and from the group laws the formal inverse is also
a right inverse, is unique on either side, and is an involution, `i(i(X)) = X`.

## Main definitions

* `FormalGroup.tautologicalPoint`: the tautological point `X` of `F` in `F.Point Unit`.
* `FormalGroup.addInvX`: the formal inverse `i(X)` of `F`.
* `FormalGroup.Point` carries `Neg`, `AddGroup` and, for commutative `F`, `AddCommGroup`
  instances, with `-x = i(x)`.

## Main results

* `FormalGroup.hasSubst_subst_pair`: `F(x, y)` is substitutable for substitutable `x, y`.
* `FormalGroup.subst_addInvX_X_eq_zero`: `F(i(X), X) = 0`.
* `FormalGroup.val_neg_tautologicalPoint`: `-X = i(X)` in `F.Point Unit`.
* `FormalGroup.subst_X_addInvX_eq_zero`: `F(X, i(X)) = 0`.
* `FormalGroup.eq_addInvX_iff_subst_left_eq_zero`, `FormalGroup.eq_addInvX_iff_subst_right_eq_zero`:
  uniqueness of the inverse on either side.
* `FormalGroup.coeff_one_addInvX`: `i(X) = -X + ⋯`.
* `FormalGroup.subst_addInvX_addInvX`: `i(i(X)) = X`.
* `FormalGroup.map_addInvX`: the formal inverse commutes with base change.
* `FormalGroup.addInvX_𝔾ₐ`, `FormalGroup.addInvX_𝔾ₘ`: the inverses `-X` of the additive and
  `-X / (1 + X)` of the multiplicative formal group law.

## Implementation notes

The name `addInvX` and the group structure on `F.Point σ` follow the design proposed by Wenrong
Zou in Mathlib PR [#36167](https://github.com/leanprover-community/mathlib4/pull/36167), which
defines the inverse there through a recursion on its coefficients. Here `i` is instead the limit
of the polynomial approximations of each degree, and the degree-by-degree step is the general
perturbation lemma `PowerSeries.coeff_subst_update_add_X_pow_mul`.

## References

* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978].
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R)

/-- The tautological point `X` of `F`, with values in the power series ring `R⟦X⟧`. -/
noncomputable def tautologicalPoint : F.Point Unit :=
  ⟨PowerSeries.X, PowerSeries.HasSubst.X'⟩

@[simp]
theorem val_tautologicalPoint : F.tautologicalPoint.val = PowerSeries.X := (rfl)

/-- Perturbing `f` by `X ^ m * r` in `F(f(X), X)` changes the coefficient of degree `m` by `r(0)`,
and no coefficient of lower degree. -/
private theorem coeff_subst_add_X_pow_mul_X {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (r : PowerSeries R) {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≤ m) :
    PowerSeries.coeff n (F.toPowerSeries.subst ![f + PowerSeries.X ^ m * r, PowerSeries.X]) =
      PowerSeries.coeff n (F.toPowerSeries.subst ![f, PowerSeries.X]) +
        if n = m then PowerSeries.constantCoeff r else 0 := by
  have h := PowerSeries.coeff_subst_update_add_X_pow_mul F.toPowerSeries
    (PowerSeries.hasSubst_pair hf PowerSeries.constantCoeff_X)
    (fun s ↦ by fin_cases s <;> simp [hf]) 0 r hm hn
  have hu : Function.update ![f, PowerSeries.X] 0 (f + PowerSeries.X ^ m * r) =
      ![f + PowerSeries.X ^ m * r, PowerSeries.X] := by
    ext i : 1
    fin_cases i <;> rfl
  rwa [Matrix.cons_val_zero, hu, F.lin_coeff_X, map_one, one_mul] at h

/-- The approximation of degree `n` to the formal inverse: each step adds the multiple of
`X ^ (n + 1)` that kills the coefficient of degree `n + 1` of `F(i(X), X)`. -/
private noncomputable def addInvApprox : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => addInvApprox n + PowerSeries.X ^ (n + 1) * PowerSeries.C
      (-PowerSeries.coeff (n + 1) (F.toPowerSeries.subst ![addInvApprox n, PowerSeries.X]))

private theorem constantCoeff_addInvApprox (n : ℕ) :
    PowerSeries.constantCoeff (F.addInvApprox n) = 0 := by
  induction n with
  | zero => simp [addInvApprox]
  | succ n ih => simp [addInvApprox, ih]

private theorem coeff_addInvApprox_of_le {k n : ℕ} (h : k ≤ n) :
    PowerSeries.coeff k (F.addInvApprox n) = PowerSeries.coeff k (F.addInvApprox k) := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n hkn ih =>
    simp [addInvApprox, show k ≠ n + 1 by omega, ih]

private theorem coeff_subst_addInvApprox (n : ℕ) :
    PowerSeries.coeff n (F.toPowerSeries.subst ![F.addInvApprox n, PowerSeries.X]) = 0 := by
  cases n with
  | zero => simp [addInvApprox, F.zero_add PowerSeries.HasSubst.X']
  | succ n =>
    rw [addInvApprox, F.coeff_subst_add_X_pow_mul_X (F.constantCoeff_addInvApprox n) _
      n.succ_ne_zero le_rfl]
    simp

/-- The **formal inverse** of a formal group law `F`: the power series `i(X)` with
`F(i(X), X) = 0` (`FormalGroup.subst_addInvX_X_eq_zero`). It is the negation of the tautological
point `X` in the group `F.Point Unit` of power-series points of `F`. -/
noncomputable def addInvX : PowerSeries R :=
  PowerSeries.mk fun n ↦ PowerSeries.coeff n (F.addInvApprox n)

private theorem X_pow_dvd_addInvX_sub (n : ℕ) :
    PowerSeries.X ^ (n + 1) ∣ F.addInvX - F.addInvApprox n :=
  PowerSeries.X_pow_dvd_iff.mpr fun k hk ↦ by
    rw [map_sub, addInvX, PowerSeries.coeff_mk, F.coeff_addInvApprox_of_le (n := n) (by omega),
      sub_self]

@[simp]
theorem constantCoeff_addInvX : PowerSeries.constantCoeff F.addInvX = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, addInvX, PowerSeries.coeff_mk,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_addInvApprox]

/-- The formal inverse has linear coefficient `-1`: `i(X) = -X + ⋯`. -/
@[simp]
theorem coeff_one_addInvX : PowerSeries.coeff 1 F.addInvX = -1 := by
  simp [addInvX, addInvApprox, F.zero_add PowerSeries.HasSubst.X']

/-- The formal inverse can be substituted into power series. -/
theorem hasSubst_addInvX : PowerSeries.HasSubst F.addInvX :=
  .of_constantCoeff_zero' F.constantCoeff_addInvX

private theorem hasSubst_addInvX_X : MvPowerSeries.HasSubst ![F.addInvX, PowerSeries.X] :=
  PowerSeries.hasSubst_pair F.constantCoeff_addInvX PowerSeries.constantCoeff_X

/-- **The formal inverse is a left inverse**: `F(i(X), X) = 0`. -/
@[simp]
theorem subst_addInvX_X_eq_zero :
    F.toPowerSeries.subst ![F.addInvX, PowerSeries.X] = 0 := by
  ext n
  obtain ⟨r, hr⟩ := F.X_pow_dvd_addInvX_sub n
  rw [sub_eq_iff_eq_add'.mp hr, F.coeff_subst_add_X_pow_mul_X (F.constantCoeff_addInvApprox n) _
    n.succ_ne_zero (by omega), coeff_subst_addInvApprox]
  simp

variable {σ : Type*}

/-- The value `F(x, y)` of a formal group law at substitutable `x, y` is substitutable: it is the
sum of the power-series points `x` and `y` of `F`. -/
theorem hasSubst_subst_pair {x y : MvPowerSeries σ R} (hx : PowerSeries.HasSubst x)
    (hy : PowerSeries.HasSubst y) : PowerSeries.HasSubst (F.toPowerSeries.subst ![x, y]) :=
  IsNilpotent_subst (hasSubst_finTwo hx hy) (F.zero_constantCoeff ▸ IsNilpotent.zero)

/-- Negation of power-series points of `F`: `-x = i(x)`, substituting `x` into the formal
inverse. -/
noncomputable instance instNegPoint : Neg (F.Point σ) where
  neg x := ⟨PowerSeries.subst x.val F.addInvX,
    IsNilpotent_subst x.prop.const (F.constantCoeff_addInvX ▸ IsNilpotent.zero)⟩

@[simp]
lemma neg_apply {x : F.Point σ} : (-x).val = PowerSeries.subst x.val F.addInvX := rfl

/-- The power-series points of a formal group law form a group under `x + y = F(x, y)`. -/
noncomputable instance instAddGroupPoint : AddGroup (F.Point σ) where
  zsmul := zsmulRec
  neg_add_cancel x := Subtype.ext <| by
    have h := congrArg (PowerSeries.substAlgHom x.prop) F.subst_addInvX_X_eq_zero
    rw [map_zero, PowerSeries.coe_substAlgHom, PowerSeries.subst_def,
      subst_comp_subst_apply F.hasSubst_addInvX_X x.prop.const] at h
    rw [add_apply, neg_apply, zero_apply, ← h]
    congr! 2 with s
    fin_cases s <;> simp [← PowerSeries.subst_def, PowerSeries.subst_X x.prop]

noncomputable instance instAddCommGroupPoint [F.IsComm] : AddCommGroup (F.Point σ) :=
  { (inferInstance : AddGroup (F.Point σ)) with add_comm := add_comm }

/-- The formal inverse is the negation of the tautological point: `-X = i(X)`. -/
theorem val_neg_tautologicalPoint : (-F.tautologicalPoint).val = F.addInvX := by
  rw [neg_apply, val_tautologicalPoint, PowerSeries.X_subst]

/-- **The formal inverse is a right inverse**: `F(X, i(X)) = 0`. -/
@[simp]
theorem subst_X_addInvX_eq_zero :
    F.toPowerSeries.subst ![PowerSeries.X, F.addInvX] = 0 := by
  have h := congrArg Subtype.val (add_neg_cancel F.tautologicalPoint)
  rwa [add_apply, val_neg_tautologicalPoint, zero_apply, val_tautologicalPoint] at h

/-- The formal inverse is the only left inverse of `X`: a substitutable `f` satisfies
`F(f(X), X) = 0` exactly when `f = i`. -/
theorem eq_addInvX_iff_subst_left_eq_zero {f : PowerSeries R} (hf : PowerSeries.HasSubst f) :
    f = F.addInvX ↔ F.toPowerSeries.subst ![f, PowerSeries.X] = 0 := by
  refine ⟨fun h ↦ h ▸ F.subst_addInvX_X_eq_zero, fun h ↦ ?_⟩
  let x : F.Point Unit := ⟨f, hf⟩
  have h' := congrArg Subtype.val <| eq_neg_of_add_eq_zero_left
    (a := x) (b := F.tautologicalPoint) <|
      Subtype.ext (by rw [add_apply, zero_apply, val_tautologicalPoint]; exact h)
  rwa [val_neg_tautologicalPoint] at h'

/-- The formal inverse is the only right inverse of `X`: a substitutable `f` satisfies
`F(X, f(X)) = 0` exactly when `f = i`. -/
theorem eq_addInvX_iff_subst_right_eq_zero {f : PowerSeries R} (hf : PowerSeries.HasSubst f) :
    f = F.addInvX ↔ F.toPowerSeries.subst ![PowerSeries.X, f] = 0 := by
  refine ⟨fun h ↦ h ▸ F.subst_X_addInvX_eq_zero, fun h ↦ ?_⟩
  let x : F.Point Unit := ⟨f, hf⟩
  have h' := congrArg Subtype.val <| eq_neg_of_add_eq_zero_right
    (a := F.tautologicalPoint) (b := x) <|
      Subtype.ext (by rw [add_apply, zero_apply, val_tautologicalPoint]; exact h)
  rwa [val_neg_tautologicalPoint] at h'

/-- The formal inverse is an involution: `i(i(X)) = X`. -/
@[simp]
theorem subst_addInvX_addInvX : PowerSeries.subst F.addInvX F.addInvX = PowerSeries.X := by
  have h := congrArg Subtype.val (neg_neg F.tautologicalPoint)
  rwa [neg_apply, val_neg_tautologicalPoint, val_tautologicalPoint] at h

/-- The formal inverse commutes with base change of the coefficient ring. -/
@[simp]
theorem map_addInvX (φ : R →+* S) : PowerSeries.map φ F.addInvX = (F.map φ).addInvX := by
  have hφ : PowerSeries.constantCoeff (PowerSeries.map φ F.addInvX) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simp
  refine ((F.map φ).eq_addInvX_iff_subst_left_eq_zero (.of_constantCoeff_zero' hφ)).mpr ?_
  have h := congrArg (MvPowerSeries.map φ) F.subst_addInvX_X_eq_zero
  rw [MvPowerSeries.map_subst F.hasSubst_addInvX_X, map_zero] at h
  rw [map_toPowerSeries, ← h]
  congr 1
  funext i
  fin_cases i
  · -- `PowerSeries.map` is by definition `MvPowerSeries.map` in the unique variable
    rfl
  · exact (PowerSeries.map_X φ).symm

/-- The formal inverse of the additive formal group law `X + Y` is `-X`. -/
@[simp]
theorem addInvX_𝔾ₐ : (𝔾ₐ (R := R)).addInvX = -PowerSeries.X := by
  refine (((𝔾ₐ (R := R)).eq_addInvX_iff_subst_left_eq_zero
    (.of_constantCoeff_zero' (by simp))).mpr ?_).symm
  have ha : MvPowerSeries.HasSubst ![-PowerSeries.X, (PowerSeries.X : PowerSeries R)] :=
    PowerSeries.hasSubst_pair (by simp) PowerSeries.constantCoeff_X
  simp [subst_add ha, subst_X ha]

/-- The formal inverse of the multiplicative formal group law `X + Y + XY` is
`-X / (1 + X) = X * (-1 - X)⁻¹`. -/
@[simp]
theorem addInvX_𝔾ₘ : (𝔾ₘ (R := R)).addInvX = PowerSeries.X * PowerSeries.invUnitsSub (-1) := by
  refine (((𝔾ₘ (R := R)).eq_addInvX_iff_subst_left_eq_zero
    (.of_constantCoeff_zero' (by simp))).mpr ?_).symm
  have ha : MvPowerSeries.HasSubst
      ![PowerSeries.X * PowerSeries.invUnitsSub (-1), (PowerSeries.X : PowerSeries R)] :=
    PowerSeries.hasSubst_pair (by simp) PowerSeries.constantCoeff_X
  have h := PowerSeries.invUnitsSub_mul_sub (-1 : Rˣ)
  simp only [Units.val_neg, Units.val_one, map_neg, map_one] at h
  simp only [𝔾ₘ_toPowerSeries, subst_add ha, subst_mul ha, subst_X ha, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  linear_combination (-PowerSeries.X) * h

end FormalGroup
