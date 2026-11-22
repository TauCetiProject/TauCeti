/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Inverse

/-!
# Parametrized affine points from formal-group parameters

Over a field `KK` equipped with a faithful `MvPowerSeries σ O`-algebra structure (for instance a
fraction field of the series ring), a nonzero parameter `q : MvPowerSeries σ O` with vanishing
constant coefficient determines a nonsingular affine point `WeierstrassCurve.thetaPoint` of the
base-changed curve `WeierstrassCurve.fracCurve W σ KK`, with coordinates `(q / w(q), -1 / w(q))`
in the `(z, w)`-chart of `WeierstrassCurve.formalW`.

## Main definitions

* `WeierstrassCurve.fracCurve`: base change of `W` along `O → MvPowerSeries σ O → KK`.
* `WeierstrassCurve.thetaPoint`: the parametrized affine point `(q / w(q), -1 / w(q))` of
  `fracCurve W σ KK`.

## Main results

* `WeierstrassCurve.fracCurve_eq_baseChange`: identifies `fracCurve W σ KK` with `W⁄KK` whenever
  `O → MvPowerSeries σ O → KK` is a scalar tower.
* `WeierstrassCurve.fracCurve_a₁`, `WeierstrassCurve.fracCurve_a₂`,
  `WeierstrassCurve.fracCurve_a₃`, `WeierstrassCurve.fracCurve_a₄`,
  `WeierstrassCurve.fracCurve_a₆`, and `WeierstrassCurve.fracCurve_Δ`: the Weierstrass coefficients
  and discriminant of `fracCurve W σ KK`.
* `WeierstrassCurve.fracCurve_Δ_ne_zero`: nonzero discriminant passes to `fracCurve W σ KK`
  whenever `MvPowerSeries σ O` acts faithfully on `KK`.
* `WeierstrassCurve.thetaPoint_nonsingular`, `WeierstrassCurve.thetaPoint_eq_some`,
  `WeierstrassCurve.xCoord_thetaPoint`, `WeierstrassCurve.yCoord_thetaPoint`,
  `WeierstrassCurve.thetaPoint_inj`, and `WeierstrassCurve.thetaPoint_neg`: nonsingularity,
  affine coordinates, injectivity, and negation of `θ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`,
`EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean` (`Domain` section), declarations
`fracCurve`, `thetaPoint`, `thetaPoint_inj`, and `thetaPoint_neg`.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {O : Type*} [CommRing O]

/-- The curve `W` base changed to a commutative ring `KK` over the series ring
`MvPowerSeries σ O`. The parameters of the chord construction are series, so the group law they
satisfy is the group law of this curve; the group-law arguments specialize `KK` to a fraction
field of the series ring, which is where the chord construction needs division, but the base change
itself asks only for a commutative algebra. There is no `Algebra O KK` to run
`WeierstrassCurve.baseChange` along, so this is the composite `map`, and it is Mathlib's `map_*`
lemmas that unfolding it exposes. -/
noncomputable def fracCurve (W : WeierstrassCurve O) (σ : Type*) (KK : Type*)
    [CommRing KK] [Algebra (MvPowerSeries σ O) KK] : WeierstrassCurve KK :=
  W.map <| (algebraMap (MvPowerSeries σ O) KK).comp (algebraMap O (MvPowerSeries σ O))

/-- `fracCurve W σ KK` is the base change of `W` along `O → MvPowerSeries σ O → KK`. -/
theorem fracCurve_def (W : WeierstrassCurve O) (σ : Type*) (KK : Type*) [CommRing KK]
    [Algebra (MvPowerSeries σ O) KK] : fracCurve W σ KK =
      W.map ((algebraMap (MvPowerSeries σ O) KK).comp (algebraMap O (MvPowerSeries σ O))) :=
  (rfl)

/-- When `O → MvPowerSeries σ O → KK` is a scalar tower, `fracCurve W σ KK` is the base change
`W⁄KK`. -/
theorem fracCurve_eq_baseChange (W : WeierstrassCurve O) {σ : Type*} {KK : Type*} [CommRing KK]
    [Algebra O KK] [Algebra (MvPowerSeries σ O) KK] [IsScalarTower O (MvPowerSeries σ O) KK] :
    fracCurve W σ KK = W⁄KK := by
  rw [fracCurve_def, WeierstrassCurve.baseChange,
    ← IsScalarTower.algebraMap_eq O (MvPowerSeries σ O) KK]

/-- The `a₁`-coefficient of `fracCurve W σ KK`. -/
@[simp]
theorem fracCurve_a₁ (W : WeierstrassCurve O) (σ : Type*) (KK : Type*)
    [CommRing KK] [Algebra (MvPowerSeries σ O) KK] :
    (fracCurve W σ KK).a₁ = algebraMap (MvPowerSeries σ O) KK (C W.a₁) := by
  rw [fracCurve_def, map_a₁, RingHom.comp_apply, c_eq_algebraMap]

/-- The `a₂`-coefficient of `fracCurve W σ KK`. -/
@[simp]
theorem fracCurve_a₂ (W : WeierstrassCurve O) (σ : Type*) (KK : Type*)
    [CommRing KK] [Algebra (MvPowerSeries σ O) KK] :
    (fracCurve W σ KK).a₂ = algebraMap (MvPowerSeries σ O) KK (C W.a₂) := by
  rw [fracCurve_def, map_a₂, RingHom.comp_apply, c_eq_algebraMap]

/-- The `a₃`-coefficient of `fracCurve W σ KK`. -/
@[simp]
theorem fracCurve_a₃ (W : WeierstrassCurve O) (σ : Type*) (KK : Type*)
    [CommRing KK] [Algebra (MvPowerSeries σ O) KK] :
    (fracCurve W σ KK).a₃ = algebraMap (MvPowerSeries σ O) KK (C W.a₃) := by
  rw [fracCurve_def, map_a₃, RingHom.comp_apply, c_eq_algebraMap]

/-- The `a₄`-coefficient of `fracCurve W σ KK`. -/
@[simp]
theorem fracCurve_a₄ (W : WeierstrassCurve O) (σ : Type*) (KK : Type*)
    [CommRing KK] [Algebra (MvPowerSeries σ O) KK] :
    (fracCurve W σ KK).a₄ = algebraMap (MvPowerSeries σ O) KK (C W.a₄) := by
  rw [fracCurve_def, map_a₄, RingHom.comp_apply, c_eq_algebraMap]

/-- The `a₆`-coefficient of `fracCurve W σ KK`. -/
@[simp]
theorem fracCurve_a₆ (W : WeierstrassCurve O) (σ : Type*) (KK : Type*)
    [CommRing KK] [Algebra (MvPowerSeries σ O) KK] :
    (fracCurve W σ KK).a₆ = algebraMap (MvPowerSeries σ O) KK (C W.a₆) := by
  rw [fracCurve_def, map_a₆, RingHom.comp_apply, c_eq_algebraMap]

/-- The discriminant of `fracCurve W σ KK`. -/
@[simp]
theorem fracCurve_Δ (W : WeierstrassCurve O) (σ : Type*) (KK : Type*)
    [CommRing KK] [Algebra (MvPowerSeries σ O) KK] :
    (fracCurve W σ KK).Δ = algebraMap (MvPowerSeries σ O) KK (C W.Δ) := by
  rw [fracCurve_def, map_Δ, RingHom.comp_apply, c_eq_algebraMap]

variable (W : WeierstrassCurve O) {σ : Type*}

variable {KK : Type*} [Field KK] [Algebra (MvPowerSeries σ O) KK]
  [FaithfulSMul (MvPowerSeries σ O) KK]

/-- A curve with nonzero discriminant stays nonsingular over a field on which its series ring
acts faithfully: `Δ` is carried there by the injective maps `C` and
`algebraMap (MvPowerSeries σ O) KK`. -/
theorem fracCurve_Δ_ne_zero (hΔ : W.Δ ≠ 0) : (fracCurve W σ KK).Δ ≠ 0 := by
  rw [fracCurve_Δ,
    map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (MvPowerSeries σ O) KK),
    map_ne_zero_iff _ C_injective]
  exact hΔ

/-- The affine coordinates `(q / w(q), -1 / w(q))` of the parametrized point `θ(q)` define a
nonsingular point of `fracCurve W σ KK`. -/
theorem thetaPoint_nonsingular (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (fracCurve W σ KK).toAffine.Nonsingular
      (algebraMap (MvPowerSeries σ O) KK q /
        algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W)))
      (-1 / algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W))) :=
  nonsingular_of_wEquation (fracCurve W σ KK)
    (by
      simpa [fracCurve_def] using
        W.algebraMap_subst_formalW_wEquation (T := KK)
          (PowerSeries.HasSubst.of_constantCoeff_zero hq))
    (W.algebraMap_subst_formalW_ne_zero hq hq0)
    hΔ

/-- The point of the base-changed curve carried by the parameter `q`: the solution `(q, w(q))` of
the `w`-equation, read in `KK` and in the affine coordinates `(q / w, -1 / w)` of the chart. -/
noncomputable def thetaPoint (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (fracCurve W σ KK).toAffine.Point :=
  Affine.Point.some _ _ (W.thetaPoint_nonsingular hΔ hq hq0)

/-- The coordinates of the parametrized point: `θ(q)` is the affine point
`(q / w(q), -1 / w(q))`, read in `KK`. The nonsingularity proof is taken rather than built. -/
theorem thetaPoint_eq_some (hΔ : (fracCurve W σ KK).Δ ≠ 0) {q : MvPowerSeries σ O}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0)
    (h : (fracCurve W σ KK).toAffine.Nonsingular
      (algebraMap (MvPowerSeries σ O) KK q /
        algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W)))
      (-1 / algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W)))) :
    W.thetaPoint hΔ hq hq0 = .some _ _ h :=
  (rfl)

/-- The parametrized point `θ(q)` is not the point at infinity. -/
@[simp]
theorem thetaPoint_ne_zero (hΔ : (fracCurve W σ KK).Δ ≠ 0) {q : MvPowerSeries σ O}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    W.thetaPoint hΔ hq hq0 ≠ 0 :=
  Affine.Point.some_ne_zero _

/-- The `x`-coordinate of the parametrized point `θ(q)` is `q / w(q)` in `KK`. -/
@[simp]
theorem xCoord_thetaPoint (hΔ : (fracCurve W σ KK).Δ ≠ 0) {q : MvPowerSeries σ O}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (W.thetaPoint hΔ hq hq0).xCoord =
      algebraMap (MvPowerSeries σ O) KK q /
        algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W)) :=
  Affine.Point.xCoord_some _

/-- The `y`-coordinate of the parametrized point `θ(q)` is `-1 / w(q)` in `KK`. -/
@[simp]
theorem yCoord_thetaPoint (hΔ : (fracCurve W σ KK).Δ ≠ 0) {q : MvPowerSeries σ O}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (W.thetaPoint hΔ hq hq0).yCoord =
      -1 / algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q (formalW W)) :=
  Affine.Point.yCoord_some _

/-- **The parametrized point determines the parameter**: `θ` is injective.

The `y`-coordinate `-1 / w(q)` already pins down `w(q)`, and the `x`-coordinate `q / w(q)` then
pins down `q`. -/
@[simp]
theorem thetaPoint_inj (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0) :
    W.thetaPoint hΔ h₁ hq₁0 = W.thetaPoint hΔ h₂ hq₂0 ↔ q₁ = q₂ := by
  refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
  classical
  set ρ := algebraMap (MvPowerSeries σ O) KK with hρ
  have hinj : Function.Injective ρ := FaithfulSMul.algebraMap_injective (MvPowerSeries σ O) KK
  simp only [thetaPoint, Affine.Point.some.injEq] at h
  simp only [← hρ] at h
  have hw₁0 : ρ (PowerSeries.subst q₁ (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero h₁ hq₁0
  have hw₂0 : ρ (PowerSeries.subst q₂ (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero h₂ hq₂0
  have hw : ρ (PowerSeries.subst q₁ (formalW W)) = ρ (PowerSeries.subst q₂ (formalW W)) := by
    have h2 := h.2
    field_simp at h2
    linear_combination h2
  refine hinj ?_
  have h1 := h.1
  rw [div_eq_div_iff hw₁0 hw₂0, hw] at h1
  exact mul_right_cancel₀ hw₂0 h1

/-- **The parametrized point of the inverted parameter is the negative**: `θ(ι(q)) = -θ(q)`.

The formal inverse was built to be the parameter of the reflected point, so this identifies that
construction with the group inverse of `fracCurve W`. Both coordinates come out of the two
readings of the inverse, `ι(q) = -(q * u(q)⁻¹)` and `w(ι(q)) = -(w(q) * u(q)⁻¹)`. -/
theorem thetaPoint_neg (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    W.thetaPoint hΔ
        (PowerSeries.constantCoeff_subst_eq_zero hq (formalInverse W)
          (constantCoeff_formalInverse W))
        (by
          have := IsDomain.of_faithfulSMul (MvPowerSeries σ O) KK
          exact W.subst_formalInverse_ne_zero hq hq0) =
      -W.thetaPoint hΔ hq hq0 := by
  classical
  set ρ := algebraMap (MvPowerSeries σ O) KK with hρ
  have hs : PowerSeries.HasSubst q := PowerSeries.HasSubst.of_constantCoeff_zero hq
  -- the readings of the formal inverse at `q`, pushed into `KK`
  have hu := congrArg ρ (W.subst_formalInverseDenom_mul hs)
  have hIeq := congrArg ρ (W.subst_formalInverse_eq hs)
  have hwIeq := congrArg ρ (W.subst_formalW_subst_formalInverse hs)
  simp only [map_neg, map_mul, map_one] at hu hIeq hwIeq
  have hsp0 := right_ne_zero_of_mul_eq_one hu
  have hueq : ρ (PowerSeries.subst q (formalInverseDenom W)) =
      1 - (fracCurve W σ KK).a₁ * ρ q -
        (fracCurve W σ KK).a₃ * ρ (PowerSeries.subst q (formalW W)) := by
    simpa [← fracCurve_def] using W.algebraMap_subst_formalInverseDenom_eq (T := KK) hs
  have hw0 : ρ (PowerSeries.subst q (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero hq hq0
  have hi : constantCoeff (PowerSeries.subst q (formalInverse W)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hq (formalInverse W) (constantCoeff_formalInverse W)
  have hi0 : PowerSeries.subst q (formalInverse W) ≠ 0 := by
    have := IsDomain.of_faithfulSMul (MvPowerSeries σ O) KK
    exact W.subst_formalInverse_ne_zero hq hq0
  rw [W.thetaPoint_eq_some hΔ hi hi0 (W.thetaPoint_nonsingular hΔ hi hi0),
    W.thetaPoint_eq_some hΔ hq hq0 (W.thetaPoint_nonsingular hΔ hq hq0)]
  simp only [Affine.Point.neg_some, Affine.Point.some.injEq]
  simp only [← hρ]
  constructor
  · rw [hIeq, hwIeq]
    field_simp
  · rw [hwIeq, Affine.negY]
    field_simp
    linear_combination
      ρ (PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) * hueq - hu

end WeierstrassCurve

end
