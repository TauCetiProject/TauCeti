/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Series
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Parameter
public import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Unit
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.ThirdPoint
import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors

/-!
# The chord group law over the fraction field of the series ring

**Associativity of the chord addition series**, `F(F(t₁, t₂), t₃) = F(t₁, F(t₂, t₃))`, proved by
transporting the honest group law of a Weierstrass curve. The parameters are power series, so the
curve has to be read over a field containing them: `FormalGroup/Point/Parameter.lean` base changes
`W` along `O → MvPowerSeries σ O → KK` (`WeierstrassCurve.fracCurve`), records the `w`-equation
there, and identifies a parameter with the point `(q, w(q))` it names
(`WeierstrassCurve.thetaPoint`). Chord addition of those points *is* the addition series, so
associativity of the curve's group law is associativity of the series.

That argument needs a domain, so it runs over the universal curve, whose base `ℤ[A₁, ⋯, A₆]`
supplies one; `map_specialize` carries the conclusion to every `W` over every commutative ring.

## Main statements

* `WeierstrassCurve.formalAdd_assoc` : **the associativity of the addition series**, for every
  Weierstrass curve over every commutative ring.
* `WeierstrassCurve.thetaPoint_add_of_subst_separates` : the chord addition of parametrized
  points, `θ(q₁) + θ(q₂) = θ(F(q₁, q₂))` on the curve `WeierstrassCurve.fracCurve` over a fraction
  field of the series ring, whenever a substitution separates `q₁` from `q₂`. It is exported
  because it is also how the addition series is compared with other descriptions of the group law
  of `W`, such as the projective addition laws.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`,
`EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean`, sections `Domain` and `Assembly`,
declarations `rho_weierstrass`, `thetaPoint_add`, and `pair_intercept_ne_zero_of_ne`.

Two of those are proved differently here, because this repository already has the content in a
more usable form. `pair_intercept_ne_zero_of_ne` collapses the cross combination with the single
rewrite `subst_pair_formalIntercept_mul_sub` where the source combines its two intercept readings
by hand; and Stoll's `hA` step inside `thetaPoint_add` argues through the constant coefficient,
whereas `subst_pair_thirdRootDenom_mul` already exhibits an explicit inverse.

The source's `wSeries` and `vSeries` are `formalW` and `formalU` here, continuing the renaming
this repository applies to that development.

The `Universal` section of the same file (declaration `assoc_addSeries_universal`) is
`assoc_formalAdd_universal`. Four of that section's nine declarations are not
ported, because this repository already has them: `universal`, `exists_map_universal` and
`universal_Δ_ne_zero` are `Universal.curve`, `map_specialize` and `Universal.curve_Δ_ne_zero`,
and the source's `X_ne_X` and `X_ne_zero'` are Mathlib's `MvPowerSeries.X_inj` and
`nonZeroDivisors.ne_zero MvPowerSeries.X_mem_nonZeroDivisors`.

The source's `interceptSeries_ne_zero` and `X_pair_intercept_ne_zero` have no counterpart. The
source needs them only because it supplies the nonvanishing intercept two different ways, an
elementary one at a pair of distinct variables and `pair_intercept_ne_zero_of_ne` elsewhere; here
`pair_intercept_ne_zero_of_ne` covers the variable pairs too, so `thetaPoint_add_of_ne` serves
all four chord additions of the assembly.

The assembly also runs two specializations of the three parameters where the source runs one.
The source separates the middle parameter from the third with `X_ne_X`, a syntactic argument; the
corresponding hypothesis here is `q₂ ≠ ι(q₃)`, which no syntactic argument reaches, so the second
substitution `g'` of `subst_formalAdd_assoc_of_subst_separates` sends the middle parameter to
`X` and the third to `0`, exactly as the first substitution `g` does for the first parameter.

The statement is adapted rather than transcribed, because this repository states the `w`-equation
differently. Stoll carries a second copy of the equation as a private `def mvWStepAt` and phrases
the fixed-point property as `subst_wSeries_fix`; here `wEquationRHS` is already stated over an
arbitrary algebra, so reading it in `KK` *is* that definition, and `subst_formalW_wEquation`
supplies the fixed-point property. Stoll's proof is `congrArg` followed by unfolding `mvWStepAt`;
the corresponding step here has to move the coefficients across the base change instead, which is
what `fracCurve` in the statement records.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {O : Type*} [CommRing O]

variable (W : WeierstrassCurve O) {σ : Type*} {KK : Type*} [Field KK]
  [Algebra (MvPowerSeries σ O) KK]

/-! ### Reading a pair through a further substitution -/

/-- Base change commutes with reading the addition series at a pair of variables: the variables
are fixed by `MvPowerSeries.map`, so only `map_formalAdd` is doing any work. -/
private theorem map_subst_pair_X_formalAdd {σ' S : Type*} [CommRing S] (φ : O →+* S)
    (s₁ s₂ : σ') :
    MvPowerSeries.map φ (subst (pairSubstitution (X s₁ : MvPowerSeries σ' O) (X s₂))
        (formalAdd W)) =
      subst (pairSubstitution (X s₁ : MvPowerSeries σ' S) (X s₂)) (formalAdd (W.map φ)) := by
  rw [MvPowerSeries.map_subst (hasSubst_pair (constantCoeff_X _) (constantCoeff_X _)),
    map_formalAdd]
  congr 1
  funext i
  rcases i with u | u <;> simp

/-- The addition series at a pair, read through a further substitution `g` that sends the first
parameter to `X` and the second to `0`: the right unit law makes the result `X`. -/
private theorem subst_subst_pair_formalAdd_eq_X {σ' : Type*}
    {g : σ' → MvPowerSeries Unit O} (hg : HasSubst g) {a b : MvPowerSeries σ' O}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (hga : subst g a = PowerSeries.X) (hgb : subst g b = 0) :
    subst g (subst (pairSubstitution a b)
      (formalAdd W)) = PowerSeries.X := by
  -- The composite family is pointwise `X` and `0`, but only pointwise: the reshape below is
  -- `funext`, not a definitional equality, and it is needed because `subst_unitR_formalAdd` is
  -- stated for the `Sum.elim` spelling that `rw` must match syntactically.
  rw [subst_comp_subst_apply (hasSubst_pair ha hb) hg,
    show (fun s : Unit ⊕ Unit ↦ subst g (Sum.elim (fun _ ↦ a) (fun _ ↦ b) s)) =
      (Sum.elim X (fun _ ↦ 0) : Unit ⊕ Unit → MvPowerSeries Unit O) from
      funext fun s ↦ by rcases s with _ | _; exacts [hga, hgb]]
  exact subst_unitR_formalAdd W

/-- The addition series at a pair of parameters is nonzero, as soon as some substitution
separates the two: it sends the sum to `X` and the zero series to `0`. -/
theorem subst_pair_formalAdd_ne_zero [Nontrivial O] {σ' : Type*}
    {g : σ' → MvPowerSeries Unit O} (hg : HasSubst g) {a b : MvPowerSeries σ' O}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (hga : subst g a = PowerSeries.X) (hgb : subst g b = 0) :
    subst (pairSubstitution a b) (formalAdd W) ≠ 0 :=
  ne_of_subst_eq_X_of_subst_eq_zero (subst_subst_pair_formalAdd_eq_X W hg ha hb hga hgb)
    (by rw [← coe_substAlgHom hg, map_zero])

/-! ### Chord addition of parametrized points -/

variable [IsFractionRing (MvPowerSeries σ O) KK]

variable [DecidableEq KK] in
/-- The sum of the parametrized points `θ(q₁)` and `θ(q₂)` is the point with affine coordinates
`(T / w(T), (1 - a₁ T - a₃ w(T)) / w(T))`, where `T` is the third root of the chord. -/
private theorem thetaPoint_add_eq_some (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hN : subst (pairSubstitution q₁ q₂)
      (formalIntercept W) ≠ 0)
    (hx : q₁ * PowerSeries.subst q₂ (formalW W) - q₂ * PowerSeries.subst q₁ (formalW W) ≠ 0)
    {Tp : MvPowerSeries σ O} (hTp : Tp = subst (pairSubstitution q₁ q₂) (formalThirdRoot W)) :
    ∃ h₃ : (fracCurve W σ KK).toAffine.Nonsingular
      (algebraMap (MvPowerSeries σ O) KK Tp /
        algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst Tp (formalW W)))
      ((1 - (fracCurve W σ KK).a₁ * algebraMap (MvPowerSeries σ O) KK Tp -
        (fracCurve W σ KK).a₃ *
          algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst Tp (formalW W))) /
        algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst Tp (formalW W))),
      W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 = Affine.Point.some _ _ h₃ := by
  have := IsDomain.of_faithfulSMul (MvPowerSeries σ O) KK
  have := MvPowerSeries.isDomain_of_isDomain (σ := σ) (R := O)
  classical
  set ρ := algebraMap (MvPowerSeries σ O) KK
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ O) KK
  set Λp := subst (pairSubstitution q₁ q₂) (formalSlope W)
  set Np := subst (pairSubstitution q₁ q₂) (formalIntercept W)
  subst hTp
  set Tp := subst (pairSubstitution q₁ q₂) (formalThirdRoot W)
  set w₁ := PowerSeries.subst q₁ (formalW W)
  set w₂ := PowerSeries.subst q₂ (formalW W)
  set wT := PowerSeries.subst Tp (formalW W)
  -- the chord identities, read in `KK`
  have hslope : ρ Λp * (ρ q₂ - ρ q₁) = ρ w₂ - ρ w₁ := by
    rw [← map_sub, ← map_sub, ← map_mul]
    exact congrArg ρ (subst_pair_formalSlope_mul W h₁ h₂)
  have hNint : ρ Np = ρ w₁ - ρ Λp * ρ q₁ := by
    rw [← map_mul, ← map_sub]
    exact congrArg ρ (subst_pair_formalIntercept_eq_inl W h₁ h₂)
  have hwTeq : ρ wT = ρ Λp * ρ Tp + ρ Np := by
    have h := congrArg ρ (subst_pair_formalThirdRoot_formalW W h₁ h₂)
    simp only [map_add, map_mul] at h
    exact h
  have hT₃ : (1 + (fracCurve W σ KK).a₂ * ρ Λp + (fracCurve W σ KK).a₄ * ρ Λp ^ 2 +
      (fracCurve W σ KK).a₆ * ρ Λp ^ 3) * (ρ Tp + ρ q₁ + ρ q₂) =
      -((fracCurve W σ KK).a₁ * ρ Λp + (fracCurve W σ KK).a₂ * ρ Np +
        (fracCurve W σ KK).a₃ * ρ Λp ^ 2 + 2 * (fracCurve W σ KK).a₄ * ρ Λp * ρ Np +
        3 * (fracCurve W σ KK).a₆ * ρ Λp ^ 2 * ρ Np) := by
    have h := congrArg ρ (subst_pair_formalThirdRoot_relation W h₁ h₂)
    simp only [map_add, map_mul, map_neg, map_pow, map_one, map_ofNat] at h
    rw [fracCurve_a₁, fracCurve_a₂, fracCurve_a₃, fracCurve_a₄, fracCurve_a₆]
    exact h
  -- nonvanishing
  have hA : (1 + (fracCurve W σ KK).a₂ * ρ Λp + (fracCurve W σ KK).a₄ * ρ Λp ^ 2 +
      (fracCurve W σ KK).a₆ * ρ Λp ^ 3) ≠ 0 := by
    intro h
    refine subst_pair_thirdRootDenom_ne_zero W h₁ h₂ (hinj ?_)
    rw [fracCurve_a₂, fracCurve_a₄, fracCurve_a₆] at h
    simpa [map_zero] using h
  have hTp0 : Tp ≠ 0 := subst_pair_formalThirdRoot_ne_zero W h₁ h₂ hN
  have hTc : constantCoeff Tp = 0 := constantCoeff_subst_pair_formalThirdRoot W h₁ h₂
  have hwT0 : ρ wT ≠ 0 := W.algebraMap_subst_formalW_ne_zero hTc hTp0
  have hxρ : ρ q₁ * ρ w₂ - ρ q₂ * ρ w₁ ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact fun h ↦ hx (hinj (by rw [h, map_zero]))
  -- the two parametrized points satisfy the Weierstrass equation of `fracCurve W`
  have hwq₁ := W.algebraMap_subst_formalW_wEquation (T := KK)
    (PowerSeries.HasSubst.of_constantCoeff_zero h₁)
  have hwq₂ := W.algebraMap_subst_formalW_wEquation (T := KK)
    (PowerSeries.HasSubst.of_constantCoeff_zero h₂)
  rw [← fracCurve_def W σ KK, wEquationRHS_def] at hwq₁ hwq₂
  -- the honest group law of `fracCurve W`, applied to the two points
  obtain ⟨h₃, hadd⟩ := chord_point_add (fracCurve W σ KK) hwq₁ hwq₂ hslope hNint hT₃ hwTeq hA
    hwT0 hxρ (W.thetaPoint_nonsingular hΔ h₁ hq₁0) (W.thetaPoint_nonsingular hΔ h₂ hq₂0)
  rw [W.thetaPoint_eq_some hΔ h₁ hq₁0 (W.thetaPoint_nonsingular hΔ h₁ hq₁0),
    W.thetaPoint_eq_some hΔ h₂ hq₂0 (W.thetaPoint_nonsingular hΔ h₂ hq₂0)]
  exact ⟨h₃, hadd⟩

/-- The point with affine coordinates `(T / w(T), (1 - a₁ T - a₃ w(T)) / w(T))`, for `T` the third
root of the chord of `θ(q₁)` and `θ(q₂)`, is the parametrized point of the addition series
`F(q₁, q₂)`. -/
private theorem some_eq_thetaPoint_formalAdd (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hN : subst (pairSubstitution q₁ q₂)
      (formalIntercept W) ≠ 0)
    (hF : constantCoeff (subst (pairSubstitution q₁ q₂) (formalAdd W)) = 0)
    (hF0 : subst (pairSubstitution q₁ q₂)
      (formalAdd W) ≠ 0)
    {Tp : MvPowerSeries σ O} (hTp : Tp = subst (pairSubstitution q₁ q₂) (formalThirdRoot W))
    (h₃ : (fracCurve W σ KK).toAffine.Nonsingular
      (algebraMap (MvPowerSeries σ O) KK Tp /
        algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst Tp (formalW W)))
      ((1 - (fracCurve W σ KK).a₁ * algebraMap (MvPowerSeries σ O) KK Tp -
        (fracCurve W σ KK).a₃ *
          algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst Tp (formalW W))) /
        algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst Tp (formalW W)))) :
    Affine.Point.some _ _ h₃ = W.thetaPoint hΔ hF hF0 := by
  classical
  subst hTp
  -- `h₃` is reverted so that the `set`s rewrite its type along with the goal, which depends on it
  revert h₃
  set ρ := algebraMap (MvPowerSeries σ O) KK
  set Tp := subst (pairSubstitution q₁ q₂) (formalThirdRoot W)
  set wT := PowerSeries.subst Tp (formalW W)
  intro h₃
  have hTp0 : Tp ≠ 0 := subst_pair_formalThirdRoot_ne_zero W h₁ h₂ hN
  have hTc : constantCoeff Tp = 0 := constantCoeff_subst_pair_formalThirdRoot W h₁ h₂
  have hwT0 : ρ wT ≠ 0 := W.algebraMap_subst_formalW_ne_zero hTc hTp0
  -- identify the third point with the point of parameter `F(q₁, q₂)`
  set sp := PowerSeries.subst Tp (PowerSeries.invOfUnit (formalInverseDenom W) 1)
  have hu : ρ (PowerSeries.subst Tp (formalInverseDenom W)) * ρ sp = 1 := by
    rw [← map_mul, ← map_one ρ]
    exact congrArg ρ (subst_pair_formalInverseDenom_mul W h₁ h₂)
  have hsp0 := right_ne_zero_of_mul_eq_one hu
  have hueq : ρ (PowerSeries.subst Tp (formalInverseDenom W)) =
      1 - (fracCurve W σ KK).a₁ * ρ Tp - (fracCurve W σ KK).a₃ * ρ wT := by
    simpa [← fracCurve_def] using W.algebraMap_subst_formalInverseDenom_eq (T := KK)
      (PowerSeries.HasSubst.of_constantCoeff_zero hTc)
  have hFeq : ρ (subst (pairSubstitution q₁ q₂) (formalAdd W)) = -(ρ Tp * ρ sp) := by
    have h := congrArg ρ (subst_pair_formalAdd_eq W h₁ h₂)
    simp only [map_neg, map_mul] at h
    exact h
  have hwFeq : ρ (PowerSeries.subst (subst (pairSubstitution q₁ q₂) (formalAdd W)) (formalW W))
      = -(ρ wT * ρ sp) := by
    have h := congrArg ρ (subst_pair_formalW_formalAdd W h₁ h₂)
    simp only [map_neg, map_mul] at h
    exact h
  rw [W.thetaPoint_eq_some hΔ hF hF0 (W.thetaPoint_nonsingular hΔ hF hF0)]
  simp only [Affine.Point.some.injEq]
  constructor
  · rw [hFeq, hwFeq]
    field_simp
  · rw [hwFeq, div_eq_div_iff hwT0 (neg_ne_zero.mpr (mul_ne_zero hwT0 hsp0))]
    linear_combination (-(ρ wT)) * hu + (ρ wT * ρ sp) * hueq

variable [DecidableEq KK] in
/-- **The chord addition of parametrized points**: `θ(q₁) + θ(q₂) = θ(F(q₁, q₂))`.

The two parametrized points lie on `fracCurve W`, the chord through them meets the curve again at
the parameter `z₃`, and the addition series is exactly the reflection of that third point. So the
group law of an honest Weierstrass curve, applied to the two points, computes `F(q₁, q₂)`. -/
private theorem thetaPoint_add (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hN : subst (pairSubstitution q₁ q₂)
      (formalIntercept W) ≠ 0)
    (hx : q₁ * PowerSeries.subst q₂ (formalW W) - q₂ * PowerSeries.subst q₁ (formalW W) ≠ 0)
    (hF : constantCoeff (subst (pairSubstitution q₁ q₂) (formalAdd W)) = 0)
    (hF0 : subst (pairSubstitution q₁ q₂)
      (formalAdd W) ≠ 0) :
    W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 = W.thetaPoint hΔ hF hF0 := by
  classical
  obtain ⟨h₃, hadd⟩ := thetaPoint_add_eq_some W hΔ h₁ h₂ hq₁0 hq₂0 hN hx rfl
  exact hadd.trans (some_eq_thetaPoint_formalAdd W hΔ h₁ h₂ hN hF hF0 rfl h₃)

/-- The intercept at a pair is nonzero as soon as the two parameters are distinct and not
mutually inverse.

If the intercept vanished, the cross combination `q₁ w(q₂) - q₂ w(q₁)` would vanish with it, so
the two parametrized points would share an `x`-coordinate and hence agree up to sign. Injectivity
of `θ` then contradicts one of the two hypotheses. -/
private theorem pair_intercept_ne_zero_of_ne (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0) (hne₁ : q₁ ≠ q₂)
    (hne₂ : q₁ ≠ PowerSeries.subst q₂ (formalInverse W)) :
    subst (pairSubstitution q₁ q₂)
      (formalIntercept W) ≠ 0 := by
  have := IsDomain.of_faithfulSMul (MvPowerSeries σ O) KK
  have := MvPowerSeries.isDomain_of_isDomain (σ := σ) (R := O)
  classical
  intro h0
  set ρ := algebraMap (MvPowerSeries σ O) KK
  -- a vanishing intercept collapses the cross combination, so the `x`-coordinates agree
  have hqw : q₁ * PowerSeries.subst q₂ (formalW W) -
      q₂ * PowerSeries.subst q₁ (formalW W) = 0 := by
    rw [subst_pair_formalIntercept_mul_sub W h₁ h₂, h0, zero_mul]
  have hw₁0 : ρ (PowerSeries.subst q₁ (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero h₁ hq₁0
  have hw₂0 : ρ (PowerSeries.subst q₂ (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero h₂ hq₂0
  have hx : ρ q₁ / ρ (PowerSeries.subst q₁ (formalW W)) =
      ρ q₂ / ρ (PowerSeries.subst q₂ (formalW W)) := by
    rw [div_eq_div_iff hw₁0 hw₂0, ← map_mul, ← map_mul]
    exact congrArg ρ (by linear_combination hqw)
  -- `xRep` is the projective `x`-coordinate, so the dichotomy comes out on the points themselves
  have hxr : (W.thetaPoint hΔ h₁ hq₁0).xRep = (W.thetaPoint hΔ h₂ hq₂0).xRep := by
    rw [W.thetaPoint_eq_some hΔ h₁ hq₁0 (W.thetaPoint_nonsingular hΔ h₁ hq₁0),
      W.thetaPoint_eq_some hΔ h₂ hq₂0 (W.thetaPoint_nonsingular hΔ h₂ hq₂0)]
    simp only [Affine.Point.xRep_some, Matrix.vecCons_inj, and_true]
    exact hx
  have hcase := Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxr
  have hi : constantCoeff (PowerSeries.subst q₂ (formalInverse W)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h₂ (formalInverse W) (constantCoeff_formalInverse W)
  have hi0 : PowerSeries.subst q₂ (formalInverse W) ≠ 0 :=
    W.subst_formalInverse_ne_zero h₂ hq₂0
  rcases hcase with hc | hc
  · exact hne₁ ((W.thetaPoint_inj hΔ h₁ h₂ hq₁0 hq₂0).mp hc)
  · rw [← W.thetaPoint_neg hΔ h₂ hq₂0] at hc
    exact hne₂ ((W.thetaPoint_inj hΔ h₁ hi hq₁0 hi0).mp hc)

variable [DecidableEq KK] in
/-- **The chord addition of parametrized points, from distinctness alone**: `θ(q₁) + θ(q₂) =
θ(F(q₁, q₂))` as soon as `q₁` is neither `q₂` nor its formal inverse.

This is the form the associativity argument uses. Both nondegeneracy hypotheses of
`thetaPoint_add` come out of those two: the intercept is nonzero by
`pair_intercept_ne_zero_of_ne`, and the cross combination is then nonzero too, since
`subst_pair_formalIntercept_mul_sub` factors it as `ν(q₁, q₂) (q₁ - q₂)`. -/
private theorem thetaPoint_add_of_ne (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0) (hne₁ : q₁ ≠ q₂)
    (hne₂ : q₁ ≠ PowerSeries.subst q₂ (formalInverse W))
    (hF : constantCoeff (subst (pairSubstitution q₁ q₂) (formalAdd W)) = 0)
    (hF0 : subst (pairSubstitution q₁ q₂)
      (formalAdd W) ≠ 0) :
    W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 = W.thetaPoint hΔ hF hF0 := by
  have := IsDomain.of_faithfulSMul (MvPowerSeries σ O) KK
  have := MvPowerSeries.isDomain_of_isDomain (σ := σ) (R := O)
  have hN := W.pair_intercept_ne_zero_of_ne hΔ h₁ h₂ hq₁0 hq₂0 hne₁ hne₂
  refine W.thetaPoint_add hΔ h₁ h₂ hq₁0 hq₂0 hN ?_ hF hF0
  rw [subst_pair_formalIntercept_mul_sub W h₁ h₂]
  exact mul_ne_zero hN (sub_ne_zero.mpr hne₁)


variable [DecidableEq KK] in
/-- **The chord addition of parametrized points, from a separating substitution.**

A single substitution sending `q₁` to `X` and `q₂` to `0` supplies both distinctness hypotheses of
`thetaPoint_add_of_ne` at once: `q₁ ≠ q₂` directly, and `q₁ ≠ ι(q₂)` because the formal inverse of
`q₂` has no constant term either, so the substitution kills it too. This is the form the
associativity assembly uses, where the separating substitution is a `coordSpecialize`. -/
theorem thetaPoint_add_of_subst_separates (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {g : σ → MvPowerSeries Unit O} (hg : HasSubst g)
    {q₁ q₂ : MvPowerSeries σ O} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hg₁ : subst g q₁ = PowerSeries.X) (hg₂ : subst g q₂ = 0)
    (hF : constantCoeff (subst (pairSubstitution q₁ q₂) (formalAdd W)) = 0)
    (hF0 : subst (pairSubstitution q₁ q₂)
      (formalAdd W) ≠ 0) :
    W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 = W.thetaPoint hΔ hF hF0 := by
  have := IsDomain.of_faithfulSMul (MvPowerSeries σ O) KK
  have := MvPowerSeries.isDomain_of_isDomain (σ := σ) (R := O)
  exact W.thetaPoint_add_of_ne hΔ h₁ h₂ hq₁0 hq₂0 (ne_of_subst_eq_X_of_subst_eq_zero hg₁ hg₂)
    (ne_of_subst_eq_X_of_subst_eq_zero hg₁ <| by
      rw [PowerSeries.subst_def]
      exact subst_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ ↦ h₂) hg
        (fun _ ↦ hg₂) (constantCoeff_formalInverse W)) hF hF0

/-! ### Associativity -/

/-- **Associativity of the addition series, from two separating substitutions.**

If a substitution `g` sends `q₁` to `X` and `q₂`, `q₃` to `0`, and a substitution `g'` sends `q₂`
to `X` and `q₃` to `0`, then each of the four chord additions in the two bracketings is licensed by
`thetaPoint_add_of_subst_separates`, both bracketings compute `θ(q₁) + θ(q₂) + θ(q₃)`, and
injectivity of `θ` gives `F(F(q₁, q₂), q₃) = F(q₁, F(q₂, q₃))`. -/
private theorem subst_formalAdd_assoc_of_subst_separates (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {g g' : σ → MvPowerSeries Unit O} (hg : HasSubst g) (hg' : HasSubst g')
    {q₁ q₂ q₃ : MvPowerSeries σ O} (hc₁ : constantCoeff q₁ = 0) (hc₂ : constantCoeff q₂ = 0)
    (hc₃ : constantCoeff q₃ = 0) (h10 : q₁ ≠ 0) (h20 : q₂ ≠ 0) (h30 : q₃ ≠ 0)
    (hg1 : subst g q₁ = PowerSeries.X) (hg2 : subst g q₂ = 0) (hg3 : subst g q₃ = 0)
    (hg'2 : subst g' q₂ = PowerSeries.X) (hg'3 : subst g' q₃ = 0) :
    subst (pairSubstitution (subst (pairSubstitution q₁ q₂) (formalAdd W)) q₃) (formalAdd W) =
      subst (pairSubstitution q₁ (subst (pairSubstitution q₂ q₃) (formalAdd W))) (formalAdd W) := by
  have := IsDomain.of_faithfulSMul (MvPowerSeries σ O) KK
  have := MvPowerSeries.isDomain_of_isDomain (σ := σ) (R := O)
  classical
  -- the two inner sums
  set F₁₂ := subst (pairSubstitution q₁ q₂) (formalAdd W)
  set F₂₃ := subst (pairSubstitution q₂ q₃) (formalAdd W)
  have hF₁₂c : constantCoeff F₁₂ = 0 := constantCoeff_subst_pair_formalAdd W hc₁ hc₂
  have hF₂₃c : constantCoeff F₂₃ = 0 := constantCoeff_subst_pair_formalAdd W hc₂ hc₃
  have hgF₁₂ : subst g F₁₂ = PowerSeries.X := subst_subst_pair_formalAdd_eq_X W hg hc₁ hc₂ hg1 hg2
  have hgF₂₃ : subst g F₂₃ = 0 :=
    subst_subst_eq_zero (hasSubst_pair hc₂ hc₃) hg
      (fun s ↦ by rcases s with _ | _; exacts [hg2, hg3]) (constantCoeff_formalAdd W)
  -- each inner sum is nonzero, via the specialization separating its own two parameters
  have hF₁₂0 : F₁₂ ≠ 0 := subst_pair_formalAdd_ne_zero W hg hc₁ hc₂ hg1 hg2
  have hF₂₃0 : F₂₃ ≠ 0 := subst_pair_formalAdd_ne_zero W hg' hc₂ hc₃ hg'2 hg'3
  -- the two bracketed sums are again legitimate parameters
  have hLc := constantCoeff_subst_eq_zero (hasSubst_pair hF₁₂c hc₃)
    (by rintro (j | j) <;> simp [hF₁₂c, hc₃]) (constantCoeff_formalAdd W)
  have hRc := constantCoeff_subst_eq_zero (hasSubst_pair hc₁ hF₂₃c)
    (by rintro (j | j) <;> simp [hF₂₃c, hc₁]) (constantCoeff_formalAdd W)
  have hL0 := subst_pair_formalAdd_ne_zero W hg hF₁₂c hc₃ hgF₁₂ hg3
  have hR0 := subst_pair_formalAdd_ne_zero W hg hc₁ hF₂₃c hg1 hgF₂₃
  -- the θ-chain: both bracketings compute the same sum of three points, each addition licensed
  -- by the specialization that separates its two summands
  have e₁₂ := thetaPoint_add_of_subst_separates W hΔ hg hc₁ hc₂ h10 h20 hg1 hg2 hF₁₂c hF₁₂0
  have e₂₃ := thetaPoint_add_of_subst_separates W hΔ hg' hc₂ hc₃ h20 h30 hg'2 hg'3 hF₂₃c hF₂₃0
  have eL := thetaPoint_add_of_subst_separates W hΔ hg hF₁₂c hc₃ hF₁₂0 h30 hgF₁₂ hg3 hLc hL0
  have eR := thetaPoint_add_of_subst_separates W hΔ hg hc₁ hF₂₃c h10 hF₂₃0 hg1 hgF₂₃ hRc hR0
  have hpts : W.thetaPoint hΔ hLc hL0 = W.thetaPoint hΔ hRc hR0 := by
    rw [← eL, ← e₁₂, ← eR, ← e₂₃, add_assoc]
  exact (thetaPoint_inj W hΔ hLc hRc hL0 hR0).mp hpts

/-- **Associativity of the addition series for the universal curve.**

The three parameters are the three coordinate variables of
`ℤ[A₁, ⋯, A₆]⟦t₁, t₂, t₃⟧`, and the two ways of bracketing them are compared as points of the
honest elliptic curve `fracCurve Universal.curve` over that ring's fraction field: `θ` turns each
bracketing into a sum of three points, `thetaPoint_add_of_ne` computes both, associativity of the
curve's group law identifies them, and `thetaPoint_inj` brings the equality back to the series. -/
private theorem assoc_formalAdd_universal :
    subst (pairSubstitution
        (subst (pairSubstitution (X (Sum.inl ()) :
            MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ))
          (X (Sum.inr (Sum.inl ())))) (formalAdd Universal.curve))
        (X (Sum.inr (Sum.inr ()))))
      (formalAdd Universal.curve) =
    subst (pairSubstitution (X (Sum.inl ()) :
        MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial Coeff ℤ))
        (subst (pairSubstitution (X (Sum.inr (Sum.inl ()))) (X (Sum.inr (Sum.inr ()))))
          (formalAdd Universal.curve)))
      (formalAdd Universal.curve) := by
  classical
  set R := MvPolynomial Coeff ℤ
  set KK := FractionRing (MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)
  have hΔ := fracCurve_Δ_ne_zero Universal.curve (σ := Unit ⊕ Unit ⊕ Unit) (KK := KK)
    Universal.curve_Δ_ne_zero
  have h10 : (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) ≠ 0 :=
    nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have h20 : (X (Sum.inr (Sum.inl ())) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) ≠ 0 :=
    nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have h30 : (X (Sum.inr (Sum.inr ())) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) ≠ 0 :=
    nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  -- the specialization separating the first parameter from the other two
  have hχ1 := subst_coordSpecialize_X_self (O := R) (Sum.inl () : Unit ⊕ Unit ⊕ Unit)
  have hχ2 := subst_coordSpecialize_X_of_ne (O := R)
    (i := (Sum.inl () : Unit ⊕ Unit ⊕ Unit)) (j := Sum.inr (Sum.inl ())) (by simp)
  have hχ3 := subst_coordSpecialize_X_of_ne (O := R)
    (i := (Sum.inl () : Unit ⊕ Unit ⊕ Unit)) (j := Sum.inr (Sum.inr ())) (by simp)
  -- the specialization separating the middle parameter from the other two
  have hχ'2 := subst_coordSpecialize_X_self (O := R) (Sum.inr (Sum.inl ()) : Unit ⊕ Unit ⊕ Unit)
  have hχ'3 := subst_coordSpecialize_X_of_ne (O := R)
    (i := (Sum.inr (Sum.inl ()) : Unit ⊕ Unit ⊕ Unit)) (j := Sum.inr (Sum.inr ())) (by simp)
  exact subst_formalAdd_assoc_of_subst_separates Universal.curve hΔ (hasSubst_coordSpecialize _)
    (hasSubst_coordSpecialize _) (constantCoeff_X _) (constantCoeff_X _) (constantCoeff_X _)
    h10 h20 h30 hχ1 hχ2 hχ3 hχ'2 hχ'3

/-- **Associativity of the chord addition series**, for every Weierstrass curve over every
commutative ring: `F(F(t₁, t₂), t₃) = F(t₁, F(t₂, t₃))`.

The chord construction proves this only where the curve has a group law to borrow, so the
identity is proved for the universal curve — whose base `ℤ[A₁, ⋯, A₆]` is a domain, and whose
series ring therefore has a fraction field — and `map_specialize` carries it to every `W`.

The three variables are indexed by `Unit ⊕ Unit ⊕ Unit`, with the two bracketings written as
nested substitutions of `formalAdd` into itself. -/
theorem formalAdd_assoc :
    subst (pairSubstitution
        (subst (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O)
          (X (Sum.inr (Sum.inl ())))) (formalAdd W))
        (X (Sum.inr (Sum.inr ()))))
      (formalAdd W) =
    subst (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) O)
        (subst (pairSubstitution (X (Sum.inr (Sum.inl ()))) (X (Sum.inr (Sum.inr ()))))
          (formalAdd W)))
      (formalAdd W) := by
  have h := congrArg (MvPowerSeries.map W.specialize) assoc_formalAdd_universal
  rw [MvPowerSeries.map_subst (hasSubst_pair
      (constantCoeff_subst_pair_formalAdd Universal.curve (constantCoeff_X _)
        (constantCoeff_X _)) (constantCoeff_X _)),
    MvPowerSeries.map_subst (hasSubst_pair (constantCoeff_X _)
      (constantCoeff_subst_pair_formalAdd Universal.curve (constantCoeff_X _)
        (constantCoeff_X _))),
    ← map_formalAdd] at h
  refine .trans ?_ (.trans h ?_)
  all_goals
    congr 1
    · funext i
      rcases i with u | u <;> simp [map_subst_pair_X_formalAdd, map_specialize]
    · simp [map_specialize]

end WeierstrassCurve

end
