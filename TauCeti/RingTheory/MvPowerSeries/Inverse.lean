/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Monoid homomorphisms, `invOfUnit`, and local ring structure of power series

`MvPowerSeries.invOfUnit D u` inverts a power series whose constant coefficient is the unit `u`.
Monoid homomorphisms between power series rings preserve this inverse, provided the constant
coefficient of the image is also a specified unit. The inverse of `1 - Xᵢ` is the geometric series
`∑ₙ Xᵢⁿ`, and the coefficients of its powers `Xᵢⁿ` are all `1`.

Because invertibility in `MvPowerSeries σ R` is detected by the constant coefficient
(`MvPowerSeries.isUnit_iff_constantCoeff`), the constant-series inclusion `C` is a local
homomorphism (`MvPowerSeries.isLocalHom_C`, `MvPowerSeries.isLocalHom_algebraMap`), and over a local
commutative ring `R` the maximal ideal of `MvPowerSeries σ R` consists of series with constant
coefficient in `𝔪_R` (`MvPowerSeries.mem_maximalIdeal_iff_constantCoeff`). Consequently every
coordinate indeterminate `X i` lies in the maximal ideal (`MvPowerSeries.X_mem_maximalIdeal`) and
every series is congruent to `C (constantCoeff f)` modulo the maximal ideal
(`MvPowerSeries.residue_C_constantCoeff`).

## Main results

* `MvPowerSeries.map_invOfUnit`: for a monoid homomorphism `φ` between multivariate power
  series rings, `φ (invOfUnit D u) = invOfUnit (φ D) v`, given `constantCoeff D = u` and
  `constantCoeff (φ D) = v`.
* `MvPowerSeries.map_inv_aux`, `MvPowerSeries.map_invOfUnit_ringHom`, `MvPowerSeries.map_inv`:
  coefficient ring homomorphisms `MvPowerSeries.map f` commute with `inv.aux`, `invOfUnit`
  (without any hypothesis on `constantCoeff`), and field inverses `φ⁻¹`.
* `PowerSeries.map_invOfUnit`, `PowerSeries.map_inv_aux`, `PowerSeries.map_invOfUnit_ringHom`,
  `PowerSeries.map_inv`: the corresponding statements in one variable.
* `MvPowerSeries.coeff_single_eq_one_of_one_sub_X_mul_eq_one`: a right inverse of `1 - Xᵢ` has
  coefficient `1` at every power `Xᵢⁿ`.
* `MvPowerSeries.isLocalHom_C`, `MvPowerSeries.isLocalHom_algebraMap`: the constant-series map and
  canonical algebra map from a local base into `MvPowerSeries σ A` are local homomorphisms.
* `MvPowerSeries.mem_maximalIdeal_iff_constantCoeff`,
  `MvPowerSeries.mem_maximalIdeal_iff_constantCoeff_eq_zero`,
  `MvPowerSeries.X_mem_maximalIdeal`, `MvPowerSeries.residue_C_constantCoeff`: maximal-ideal
  membership and residue-class reduction in `MvPowerSeries σ R`.

## Implementation notes

Only multiplication and `1` are needed for `map_invOfUnit`, so it uses `MonoidHomClass`. It applies
to coefficient maps, variable renamings, and substitution algebra homomorphisms. The source and
target variable types and coefficient rings may differ; neither coefficient ring needs to be
commutative. The two units independently certify the source and image constant coefficients:
no compatibility between the homomorphism and `constantCoeff` is assumed. For `MvPowerSeries.map f`
induced by a ring homomorphism `f : R →+* S`, compatibility with `inv.aux` holds unconditionally
by induction on the multi-index.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project (Apache-2.0),
[`EllipticCurves/WeierstrassFormalGroup/Chord.lean`](https://github.com/MichaelStollBayreuth/EllipticCurves/blob/66889eada51a/EllipticCurves/WeierstrassFormalGroup/Chord.lean),
the private `ringHom_invOfUnit` and its specialisation `rename_swap_invOfUnit`. The source fixes
the constant coefficients to `1` and works over a commutative ring; here the units are arbitrary
and the coefficient rings need not be commutative.
-/

public section

section Inverse

variable {σ τ R S : Type*} [Ring R] [Ring S]

namespace MvPowerSeries

/-- A monoid homomorphism between multivariate power series rings carries `invOfUnit` to the
`invOfUnit` of the image. -/
theorem map_invOfUnit {F : Type*} [FunLike F (MvPowerSeries σ R) (MvPowerSeries τ S)]
    [MonoidHomClass F (MvPowerSeries σ R) (MvPowerSeries τ S)] (φ : F) {D : MvPowerSeries σ R}
    {u : Rˣ} {v : Sˣ} (hD : constantCoeff D = u) (hD' : constantCoeff (φ D) = v) :
    φ (invOfUnit D u) = invOfUnit (φ D) v :=
  left_inv_eq_right_inv
    (map_mul_eq_one φ (invOfUnit_mul D u hD))
    (mul_invOfUnit (φ D) v hD')

/-- Applying a coefficient ring homomorphism to the recursive inverse series `inv.aux` is the
recursive inverse series of the image. -/
@[simp]
theorem map_inv_aux (f : R →+* S) (a : R) (φ : MvPowerSeries σ R) :
    map f (inv.aux a φ) = inv.aux (f a) (map f φ) := by
  classical
  ext n
  induction n using WellFoundedLT.induction with | ind n ih =>
  rw [coeff_map, coeff_inv_aux, coeff_inv_aux]
  split_ifs with hn
  · rfl
  · rw [map_mul, map_neg, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs with hlt
    · rw [map_mul, ← coeff_map, ← coeff_map, ih x.2 hlt]
    · exact f.map_zero

/-- For a unit `u : (MvPowerSeries σ R)ˣ`, its inverse in `MvPowerSeries σ R` is `invOfUnit` with
respect to the unit constant coefficient. -/
theorem val_inv_eq_invOfUnit (u : (MvPowerSeries σ R)ˣ) :
    (↑u⁻¹ : MvPowerSeries σ R) =
      invOfUnit (u : MvPowerSeries σ R)
        (Units.map (constantCoeff (σ := σ) (R := R)).toMonoidHom u) :=
  Units.inv_eq_of_mul_eq_one_right (mul_invOfUnit (u : MvPowerSeries σ R) _ rfl)

/-- Applying a coefficient ring homomorphism to `invOfUnit` is `invOfUnit` of the image with the
mapped unit, without any hypothesis on the constant coefficient of `φ`. -/
@[simp]
theorem map_invOfUnit_ringHom (f : R →+* S) (φ : MvPowerSeries σ R) (u : Rˣ) :
    map f (invOfUnit φ u) = invOfUnit (map f φ) (Units.map f u) :=
  map_inv_aux f (↑u⁻¹) φ

/-- Over fields, a coefficient ring homomorphism commutes with the totalized inverse `φ⁻¹` of a
multivariate power series. -/
@[simp]
protected theorem map_inv {k l : Type*} [Field k] [Field l] (f : k →+* l) (φ : MvPowerSeries σ k) :
    map f φ⁻¹ = (map f φ)⁻¹ := by
  -- The field inverse is defined as inv.aux with the inverse constant coefficient
  -- (MvPowerSeries.inv); Mathlib has no multivariate inv_eq_inv_aux rewrite lemma.
  change map f (inv.aux (constantCoeff φ)⁻¹ φ) =
    inv.aux (constantCoeff (map f φ))⁻¹ (map f φ)
  rw [map_inv_aux, constantCoeff_map, map_inv₀]

/-- **A right inverse of `1 - Xᵢ` has coefficient `1` at every power `Xᵢⁿ`**: it is the geometric
series `∑ₙ Xᵢⁿ`. -/
theorem coeff_single_eq_one_of_one_sub_X_mul_eq_one {g : MvPowerSeries σ R} {i : σ}
    (hg : (1 - X i) * g = 1) (n : ℕ) : coeff (Finsupp.single i n) g = 1 := by
  classical
  have hg' : g = 1 + X i * g := by
    rwa [sub_mul, one_mul, sub_eq_iff_eq_add] at hg
  induction n with
  | zero => rw [hg']; simp
  | succ n ih =>
    have hX : coeff (Finsupp.single i (n + 1)) (X i * g) = coeff (Finsupp.single i n) g := by
      rw [X_def, show Finsupp.single i (n + 1) = Finsupp.single i 1 + Finsupp.single i n by
          rw [← Finsupp.single_add, add_comm],
        coeff_add_monomial_mul, one_mul]
    conv_lhs => rw [hg']
    rw [map_add, hX, ih]
    simp [coeff_one]

end MvPowerSeries

namespace PowerSeries

/-- The one-variable form of `MvPowerSeries.map_invOfUnit`, expressed with
`PowerSeries.invOfUnit` and `PowerSeries.constantCoeff`. -/
theorem map_invOfUnit {F : Type*} [FunLike F (PowerSeries R) (PowerSeries S)]
    [MonoidHomClass F (PowerSeries R) (PowerSeries S)] (φ : F) {D : PowerSeries R}
    {u : Rˣ} {v : Sˣ} (hD : constantCoeff D = u) (hD' : constantCoeff (φ D) = v) :
    φ (invOfUnit D u) = invOfUnit (φ D) v :=
  MvPowerSeries.map_invOfUnit φ hD hD'

/-- For a unit `u : R⟦X⟧ˣ`, its inverse in `R⟦X⟧` is `invOfUnit` with respect to the unit
constant coefficient. -/
theorem val_inv_eq_invOfUnit (u : R⟦X⟧ˣ) :
    (↑u⁻¹ : R⟦X⟧) = invOfUnit (u : R⟦X⟧) (Units.map (constantCoeff (R := R)).toMonoidHom u) :=
  MvPowerSeries.val_inv_eq_invOfUnit u

/-- Applying a coefficient ring homomorphism to `PowerSeries.inv.aux` is `PowerSeries.inv.aux` of
the image. -/
@[simp]
theorem map_inv_aux (f : R →+* S) (a : R) (φ : R⟦X⟧) :
    map f (PowerSeries.inv.aux a φ) = PowerSeries.inv.aux (f a) (map f φ) :=
  MvPowerSeries.map_inv_aux f a φ

/-- Applying a coefficient ring homomorphism to `PowerSeries.invOfUnit` is `PowerSeries.invOfUnit`
of the image with the mapped unit. -/
@[simp]
theorem map_invOfUnit_ringHom (f : R →+* S) (φ : R⟦X⟧) (u : Rˣ) :
    map f (invOfUnit φ u) = invOfUnit (map f φ) (Units.map f u) :=
  MvPowerSeries.map_invOfUnit_ringHom f φ u

/-- Over fields, a coefficient ring homomorphism commutes with the totalized inverse `φ⁻¹` of a
power series. -/
@[simp]
protected theorem map_inv {k l : Type*} [Field k] [Field l] (f : k →+* l) (φ : k⟦X⟧) :
    map f φ⁻¹ = (map f φ)⁻¹ :=
  MvPowerSeries.map_inv f φ

end PowerSeries

end Inverse

namespace MvPowerSeries

/-- The constant-series embedding `C : R →+* MvPowerSeries σ R` is a local homomorphism. -/
instance isLocalHom_C {σ R : Type*} [Semiring R] : IsLocalHom (C (σ := σ) (R := R)) :=
  isLocalHom_of_leftInverse constantCoeff constantCoeff_C

/-- For any local algebra `R → A`, the canonical algebra map `R →+* MvPowerSeries σ A` is a local
homomorphism. -/
instance isLocalHom_algebraMap {σ R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [IsLocalHom (algebraMap R A)] :
    IsLocalHom (algebraMap R (MvPowerSeries σ A)) where
  map_nonunit r hr := by
    rw [algebraMap_apply] at hr
    exact IsLocalHom.map_nonunit r (IsLocalHom.map_nonunit _ hr)

section LocalRing

variable {σ R : Type*} [CommRing R] [IsLocalRing R]

/-- Over a local commutative ring `R`, a power series lies in the maximal ideal of
`MvPowerSeries σ R` if and only if its constant coefficient lies in the maximal ideal of `R`. -/
theorem mem_maximalIdeal_iff_constantCoeff {f : MvPowerSeries σ R} :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ R) ↔
      constantCoeff f ∈ IsLocalRing.maximalIdeal R := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]

/-- Every coordinate indeterminate `X i` belongs to the maximal ideal of `MvPowerSeries σ R`. -/
theorem X_mem_maximalIdeal (i : σ) :
    (X i : MvPowerSeries σ R) ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ R) := by
  rw [mem_maximalIdeal_iff_constantCoeff, constantCoeff_X]
  exact zero_mem _

/-- Every power series is congruent to its constant term modulo the maximal ideal of
`MvPowerSeries σ R`. -/
@[simp]
theorem residue_C_constantCoeff (f : MvPowerSeries σ R) :
    IsLocalRing.residue (MvPowerSeries σ R) (C (constantCoeff f)) =
      IsLocalRing.residue (MvPowerSeries σ R) f := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    mem_maximalIdeal_iff_constantCoeff]
  simp

end LocalRing

/-- Over a field `K`, a power series belongs to the maximal ideal of `MvPowerSeries σ K` if and
only if its constant coefficient is zero. -/
theorem mem_maximalIdeal_iff_constantCoeff_eq_zero {σ K : Type*} [Field K]
    {f : MvPowerSeries σ K} :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ↔ constantCoeff f = 0 := by
  rw [mem_maximalIdeal_iff_constantCoeff]
  simp

end MvPowerSeries
