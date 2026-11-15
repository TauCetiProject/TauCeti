/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Equation
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# The Bosma–Lenstra projective addition law at formal points

Let `W` be a Weierstrass curve over a commutative ring `R`, with `w`-expansion `w = formalW W` in
the local parameter `z = -X / Y` at the point at infinity and chord addition series
`F = formalAdd W`. A formal parameter `q ∈ MvPowerSeries σ R` with `constantCoeff q = 0` defines
the projective formal point `[q : -1 : w(q)]`.

This file evaluates the Bosma–Lenstra addition law `dblAddXYZ`, attached to the line `Y = 0`, at
pairs of formal points `[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]`:

1. Its `Y`-coordinate `dblAddY` is a unit in `MvPowerSeries σ R`
   (`WeierstrassCurve.isUnit_dblAddY_subst_formalW`), since at `q₁ = q₂ = 0` both points specialize
   to `[0 : -1 : 0]`, where `dblAddXYZ` takes the value `[0 : 1 : 0]`.
2. Over any commutative ring `R` and without any nonsingularity hypothesis on `W`, `dblAddXYZ` at
   `[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]` equals `-Y` times
   `(F(q₁, q₂), -1, w(F(q₁, q₂)))` (`WeierstrassCurve.dblAddXYZ_subst_formalW_eq_smul`). This is
   proved first over a domain with nonzero discriminant—in particular for `Universal.curve` over
   `ℤ[A₁, …, A₆]`—by comparing `dblAddXYZ` with `WeierstrassCurve.thetaPoint` over the fraction
   field of `O⟦z₁, z₂⟧`, then specialized along `WeierstrassCurve.specialize` and
   `pairSubstitution`.
3. Passing to an algebra `KK` (a field) over `MvPowerSeries σ O` where `fracCurve W σ KK` has
   nonzero discriminant, the projective-to-affine map sends `[q : -1 : w(q)]` uniformly for `q = 0`
   and `q ≠ 0` to `WeierstrassCurve.formalThetaPoint`, carrying formal-group addition to the group
   law of `(fracCurve W σ KK).toAffine.Point` (`WeierstrassCurve.formalThetaPoint_add`).

## Main definitions

* `WeierstrassCurve.formalThetaPoint`: the affine point on `fracCurve W σ KK` associated to the
  projective formal point `[q : -1 : w(q)]`, defined uniformly for `q = 0` and `q ≠ 0`.

## Main results

* `WeierstrassCurve.isUnit_dblAddY_subst_formalW` and `WeierstrassCurve.isUnit_dblAddY_formalW`:
  the `Y`-coordinate of `dblAddXYZ` at formal points `[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]` is
  a unit.
* `WeierstrassCurve.nonsingular_fracCurve_algebraMap_comp_subst_formalW` and
  `WeierstrassCurve.toAffine_algebraMap_comp_subst_formalW_eq_thetaPoint`: nonsingularity of
  `[q : -1 : w(q)]` on `fracCurve W σ KK` when `(fracCurve W σ KK).Δ ≠ 0`, and identification of
  its affine point with `WeierstrassCurve.thetaPoint` when `q ≠ 0`.
* `WeierstrassCurve.dblAddXYZ_formalW_eq_smul` and
  `WeierstrassCurve.dblAddXYZ_subst_formalW_eq_smul`: `dblAddXYZ` at formal points is a unit
  multiple of `(F(q₁, q₂), -1, w(F(q₁, q₂)))`.
* `WeierstrassCurve.formalThetaPoint_zero`, `WeierstrassCurve.formalThetaPoint_eq_some`,
  `WeierstrassCurve.formalThetaPoint_inj`, and `WeierstrassCurve.formalThetaPoint_add`: zero value,
  explicit affine coordinates for `q ≠ 0`, injectivity, and compatibility with formal-group
  addition for `WeierstrassCurve.formalThetaPoint`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

public section

open MvPowerSeries TauCeti

namespace WeierstrassCurve

section Algebra

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The `Y`-coordinate of the Bosma–Lenstra addition law `dblAddXYZ` at any pair of formal points
`[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]` with vanishing constant coefficients is a unit of
`MvPowerSeries σ R`: at the origin both points specialize to `[0 : -1 : 0]`, where the law takes
the value `[0 : 1 : 0]`. -/
theorem isUnit_dblAddY_subst_formalW {σ : Type*} {q₁ q₂ : MvPowerSeries σ R}
    (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0) :
    IsUnit ((W.toProjective.map (algebraMap R (MvPowerSeries σ R))).dblAddY
      ![q₁, -1, PowerSeries.subst q₁ W.formalW]
      ![q₂, -1, PowerSeries.subst q₂ W.formalW]) := by
  have hc (q : MvPowerSeries σ R) (hq : constantCoeff q = 0) :
      constantCoeff ∘ ![q, -1, PowerSeries.subst q W.formalW] = ![0, -1, 0] := by
    funext k
    fin_cases k
    · simpa using hq
    · simp
    · simpa using PowerSeries.constantCoeff_subst_eq_zero hq _ W.constantCoeff_formalW
  rw [isUnit_iff_constantCoeff, ← Projective.map_dblAddY, hc _ hq₁, hc _ hq₂]
  simp [Projective.dblAddY]

/-- The `Y`-coordinate of the Bosma–Lenstra addition law `dblAddXYZ` at the points
`[z₁ : -1 : w(z₁)]` and `[z₂ : -1 : w(z₂)]` with parameters the two variables of `R⟦z₁, z₂⟧` is a
unit: at `z₁ = z₂ = 0` it is the value `1` of the law at the point at infinity, taken twice. -/
theorem isUnit_dblAddY_formalW :
    IsUnit ((W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R))).dblAddY
      ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
      ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW]) :=
  W.isUnit_dblAddY_subst_formalW (constantCoeff_X _) (constantCoeff_X _)

section FractionField

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O) {σ : Type*}
  {KK : Type*} [Field KK] [Algebra (MvPowerSeries σ O) KK] [IsFractionRing (MvPowerSeries σ O) KK]

omit [IsFractionRing (MvPowerSeries σ O) KK] in
/-- The formal point `[q : -1 : w(q)]` with `constantCoeff q = 0`, read over an algebra `KK` where
`fracCurve W σ KK` has nonzero discriminant, is nonsingular on the projective curve. -/
theorem nonsingular_fracCurve_algebraMap_comp_subst_formalW (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) :
    (fracCurve W σ KK).toProjective.Nonsingular
      (algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]) := by
  refine (Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero hΔ
    fun h ↦ by simpa using congrFun h 1).mp ?_
  rw [fracCurve_def, ← map_map]
  exact ((W.toProjective.equation_neg_one_iff_wEquation q _).mpr
    (W.subst_formalW_wEquation (PowerSeries.HasSubst.of_constantCoeff_zero hq))).map _

/-- For a nonzero parameter `q` with `constantCoeff q = 0`, the affine point associated to
`[q : -1 : w(q)]` over a fraction field `KK` of `MvPowerSeries σ O` where `fracCurve W σ KK` has
nonzero discriminant is `W.thetaPoint`. -/
theorem toAffine_algebraMap_comp_subst_formalW_eq_thetaPoint (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Projective.Point.toAffine (fracCurve W σ KK).toProjective
      (algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]) =
        W.thetaPoint hΔ hq hq0 := by
  have hz : (algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]) 2 ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero hq hq0
  have hN := W.nonsingular_fracCurve_algebraMap_comp_subst_formalW hΔ hq
  rw [Projective.Point.toAffine_of_Z_ne_zero hN hz, W.thetaPoint_eq_some hΔ hq hq0
    (by simpa using (Projective.nonsingular_of_Z_ne_zero hz).mp hN)]
  simp

end FractionField

-- Over a domain, with nonzero discriminant, the identity is read off the group law of the curve
-- over a fraction field `KK` of `O⟦z₁, z₂⟧`, where `dblAddXYZ` represents the sum of the two
-- points, which is the point with parameter `F`.
private theorem dblAddXYZ_formalW_eq_smul_of_Δ_ne_zero {O : Type*} [CommRing O] [IsDomain O]
    (W : WeierstrassCurve O) (hΔ : W.Δ ≠ 0) :
    (W.toProjective.map (algebraMap O (MvPowerSeries (Unit ⊕ Unit) O))).dblAddXYZ
        ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
        ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW] =
      -(W.toProjective.map (algebraMap O (MvPowerSeries (Unit ⊕ Unit) O))).dblAddY
        ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
        ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW] •
        ![formalAdd W, -1, PowerSeries.subst (formalAdd W) W.formalW] := by
  classical
  let KK := FractionRing (MvPowerSeries (Unit ⊕ Unit) O)
  set ρ := algebraMap (MvPowerSeries (Unit ⊕ Unit) O) KK
  set z₁ : MvPowerSeries (Unit ⊕ Unit) O := X (Sum.inl ())
  set z₂ : MvPowerSeries (Unit ⊕ Unit) O := X (Sum.inr ())
  set D := (W.toProjective.map (algebraMap O (MvPowerSeries (Unit ⊕ Unit) O))).dblAddXYZ
    ![z₁, -1, PowerSeries.subst z₁ W.formalW] ![z₂, -1, PowerSeries.subst z₂ W.formalW] with hDdef
  set F := subst (pairSubstitution z₁ z₂) (formalAdd W)
  have hF : F = formalAdd W := by
    have h : pairSubstitution z₁ z₂ = X := funext fun i ↦ by rcases i with ⟨⟩ | ⟨⟩ <;> rfl
    simp only [F, h, subst_self, id_eq]
  have hΔ' := W.fracCurve_Δ_ne_zero (σ := Unit ⊕ Unit) (KK := KK) hΔ
  set W' := fracCurve W (Unit ⊕ Unit) KK with hW'
  have hz₁ : constantCoeff z₁ = 0 := constantCoeff_X _
  have hz₂ : constantCoeff z₂ = 0 := constantCoeff_X _
  have hz₁0 : z₁ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hz₂0 : z₂ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  -- the specialization `z₁ ↦ X`, `z₂ ↦ 0` separates the two parameters
  have hχ := hasSubst_coordSpecialize (O := O) (Sum.inl () : Unit ⊕ Unit)
  have hχ₁ : subst (coordSpecialize (Sum.inl ())) z₁ = PowerSeries.X :=
    subst_coordSpecialize_X_self _
  have hχ₂ : subst (coordSpecialize (Sum.inl ())) z₂ = 0 :=
    subst_coordSpecialize_X_of_ne (by simp)
  have hFc : constantCoeff F = 0 := constantCoeff_subst_pair_formalAdd W hz₁ hz₂
  have hF0 : F ≠ 0 := W.subst_pair_formalAdd_ne_zero hχ hz₁ hz₂ hχ₁ hχ₂
  -- read in `KK`, the law `dblAddXYZ` is nonzero, since its `Y`-coordinate is a unit, so it
  -- represents the sum of the two points, which is the parametrized point `θ(F)`
  have hN₁ := W.nonsingular_fracCurve_algebraMap_comp_subst_formalW hΔ' hz₁
  have hN₂ := W.nonsingular_fracCurve_algebraMap_comp_subst_formalW hΔ' hz₂
  have hD : W'.toProjective.dblAddXYZ (ρ ∘ ![z₁, -1, PowerSeries.subst z₁ W.formalW])
      (ρ ∘ ![z₂, -1, PowerSeries.subst z₂ W.formalW]) = ρ ∘ D := by
    rw [hW', fracCurve_def, ← map_map]
    exact Projective.map_dblAddXYZ ..
  have hDu : IsUnit (D 1) := by simpa [D] using W.isUnit_dblAddY_formalW
  have hD0 : ρ ∘ D ≠ 0 := fun h ↦ (hDu.map ρ).ne_zero (congrFun h 1)
  have hsum : Projective.Point.toAffine W'.toProjective (ρ ∘ D) =
      Projective.Point.toAffine W'.toProjective (ρ ∘ ![F, -1, PowerSeries.subst F W.formalW]) := by
    rw [← hD,
      Projective.Point.toAffine_of_equiv (Projective.dblAddXYZ_equiv_add hN₁ hN₂ (hD ▸ hD0)),
      Projective.Point.toAffine_add hN₁ hN₂,
      W.toAffine_algebraMap_comp_subst_formalW_eq_thetaPoint hΔ' hz₁ hz₁0,
      W.toAffine_algebraMap_comp_subst_formalW_eq_thetaPoint hΔ' hz₂ hz₂0,
      W.toAffine_algebraMap_comp_subst_formalW_eq_thetaPoint hΔ' hFc hF0]
    exact W.thetaPoint_add_of_subst_separates hΔ' hχ hz₁ hz₂ hz₁0 hz₂0 hχ₁ hχ₂ hFc hF0
  have hDN : W'.toProjective.Nonsingular (ρ ∘ D) :=
    (Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero hΔ' hD0).mp
      (hD ▸ hN₁.left.dblAddXYZ hN₂.left)
  -- equal affine points are projectively equivalent: `ρ ∘ D = u • ρ ∘ (F, -1, w(F))`
  obtain ⟨u, hu⟩ := (Projective.Point.toAffine_eq_toAffine_iff hDN
    (W.nonsingular_fracCurve_algebraMap_comp_subst_formalW hΔ' hFc)).mp hsum
  have h₁ : ρ (D 1) = -u := by simpa [Units.smul_def] using (congrFun hu 1).symm
  rw [← hF, ← Projective.dblAddXYZ_Y, ← hDdef]
  clear_value D
  funext k
  refine IsFractionRing.injective _ KK ?_
  have hk : ρ (D k) = u * ρ (![F, -1, PowerSeries.subst F W.formalW] k) := by
    simpa [Units.smul_def] using (congrFun hu k).symm
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_neg]
  linear_combination hk + ρ (![F, -1, PowerSeries.subst F W.formalW] k) * h₁

/-- **The Bosma–Lenstra addition law at the formal points.** Let `z₁` and `z₂` be the two variables
of `R⟦z₁, z₂⟧`. At the points `[z₁ : -1 : w(z₁)]` and `[z₂ : -1 : w(z₂)]`, where `w` is the
`w`-expansion of `W`, the addition law `dblAddXYZ` attached to the line `Y = 0` is `-Y` times
`(F, -1, w(F))`, where `Y` is its `Y`-coordinate, a unit (`isUnit_dblAddY_formalW`), and
`F = formalAdd W` is the addition series of the chord construction. No hypothesis is placed on `W`
or on `R`. -/
theorem dblAddXYZ_formalW_eq_smul :
    (W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R))).dblAddXYZ
        ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
        ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW] =
      -(W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R))).dblAddY
        ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
        ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW] •
        ![formalAdd W, -1, PowerSeries.subst (formalAdd W) W.formalW] := by
  -- specialize the identity for the universal curve, whose base `ℤ[A₁, ⋯, A₆]` is a domain
  have key := dblAddXYZ_formalW_eq_smul_of_Δ_ne_zero Universal.curve Universal.curve_Δ_ne_zero
  set φ := MvPowerSeries.map (σ := Unit ⊕ Unit) W.specialize
  have hcurve : (Universal.curve.toProjective.map (algebraMap (MvPolynomial Coeff ℤ)
      (MvPowerSeries (Unit ⊕ Unit) (MvPolynomial Coeff ℤ)))).map φ =
        W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R)) := by
    have h : φ.comp (algebraMap (MvPolynomial Coeff ℤ) _) =
        (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R)).comp W.specialize :=
      RingHom.ext fun a ↦ by simp [φ, ← c_eq_algebraMap]
    refine (Universal.curve.map_map _ _).trans ?_
    rw [h, ← map_map]
    exact congrArg (fun V : WeierstrassCurve R ↦ V.map _) W.map_specialize
  have hpt (q : MvPowerSeries (Unit ⊕ Unit) (MvPolynomial Coeff ℤ)) (hq : constantCoeff q = 0) :
      φ ∘ ![q, -1, PowerSeries.subst q Universal.curve.formalW] =
        ![φ q, -1, PowerSeries.subst (φ q) W.formalW] := by
    funext k
    fin_cases k
    · rfl
    · simp
    · simp [φ, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq),
        ← map_formalW]
  have h₁ := hpt (X (Sum.inl ())) (constantCoeff_X _)
  have h₂ := hpt (X (Sum.inr ())) (constantCoeff_X _)
  have hF := hpt _ (constantCoeff_formalAdd Universal.curve)
  simp only [φ, map_X, ← map_formalAdd, map_specialize] at h₁ h₂ hF
  rw [← h₁, ← h₂, ← hF, ← hcurve, Projective.map_dblAddXYZ, Projective.map_dblAddY, key]
  funext k
  fin_cases k <;> simp [φ]

/-- **The Bosma–Lenstra addition law at any pair of formal points.** For parameters `q₁, q₂` in
`MvPowerSeries σ R` with vanishing constant coefficients, the value of `dblAddXYZ` at
`[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]` is `-Y` times `(F(q₁, q₂), -1, w(F(q₁, q₂)))`, where
`Y` is its `Y`-coordinate (`isUnit_dblAddY_subst_formalW`) and `F = formalAdd W`. -/
theorem dblAddXYZ_subst_formalW_eq_smul {σ : Type*} {q₁ q₂ : MvPowerSeries σ R}
    (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0) :
    (W.toProjective.map (algebraMap R (MvPowerSeries σ R))).dblAddXYZ
        ![q₁, -1, PowerSeries.subst q₁ W.formalW]
        ![q₂, -1, PowerSeries.subst q₂ W.formalW] =
      -(W.toProjective.map (algebraMap R (MvPowerSeries σ R))).dblAddY
        ![q₁, -1, PowerSeries.subst q₁ W.formalW]
        ![q₂, -1, PowerSeries.subst q₂ W.formalW] •
        ![subst (pairSubstitution q₁ q₂) (formalAdd W), -1,
          PowerSeries.subst (subst (pairSubstitution q₁ q₂) (formalAdd W)) W.formalW] := by
  have hp : HasSubst (pairSubstitution q₁ q₂) := hasSubst_pair hq₁ hq₂
  set ψ : MvPowerSeries (Unit ⊕ Unit) R →ₐ[R] MvPowerSeries σ R := substAlgHom hp
  have hcurve : (W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R))).map
      ψ.toRingHom = W.toProjective.map (algebraMap R (MvPowerSeries σ R)) := by
    have hcomp : ψ.toRingHom.comp (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R)) =
        algebraMap R (MvPowerSeries σ R) := RingHom.ext fun c ↦ by simp [ψ]
    exact congrArg WeierstrassCurve.toProjective ((W.map_map _ _).trans (congrArg W.map hcomp))
  have hpt (t : MvPowerSeries (Unit ⊕ Unit) R) (ht : constantCoeff t = 0) :
      ψ.toRingHom ∘ ![t, -1, PowerSeries.subst t W.formalW] =
        ![ψ t, -1, PowerSeries.subst (ψ t) W.formalW] := by
    funext k
    fin_cases k
    · rfl
    · simp
    · simp only [Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ψ,
        coe_substAlgHom hp]
      exact subst_powerSeriesSubst hp (.of_constantCoeff_zero ht) W.formalW
  have h₁ := hpt (X (Sum.inl ())) (constantCoeff_X _)
  have h₂ := hpt (X (Sum.inr ())) (constantCoeff_X _)
  have hF := hpt (formalAdd W) (constantCoeff_formalAdd W)
  have hψ₁ : ψ (X (Sum.inl ())) = q₁ := by simp [ψ, subst_X hp, pairSubstitution]
  have hψ₂ : ψ (X (Sum.inr ())) = q₂ := by simp [ψ, subst_X hp, pairSubstitution]
  have hψF : ψ (formalAdd W) = subst (pairSubstitution q₁ q₂) (formalAdd W) := by simp [ψ]
  rw [hψ₁] at h₁
  rw [hψ₂] at h₂
  rw [hψF] at hF
  rw [← h₁, ← h₂, ← hF, ← hcurve, Projective.map_dblAddXYZ, Projective.map_dblAddY,
    W.dblAddXYZ_formalW_eq_smul]
  funext k
  fin_cases k <;> simp

end Algebra

section FormalThetaPoint

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O) {σ : Type*}
  (KK : Type*) [Field KK] [Algebra (MvPowerSeries σ O) KK]

/-- **The affine formal point `[q : -1 : w(q)]` on `fracCurve W σ KK`**, defined uniformly for
`q = 0` (giving `0`, the point at infinity) and `q ≠ 0` (giving `W.thetaPoint` when
`constantCoeff q = 0` and `(fracCurve W σ KK).Δ ≠ 0`). -/
noncomputable def formalThetaPoint (q : MvPowerSeries σ O) : (fracCurve W σ KK).toAffine.Point :=
  Projective.Point.toAffine (fracCurve W σ KK).toProjective
    (algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW])

/-- At `q = 0`, `W.formalThetaPoint KK 0` is `0` (the point at infinity `[0 : -1 : 0]`). -/
@[simp]
theorem formalThetaPoint_zero : W.formalThetaPoint KK (0 : MvPowerSeries σ O) = 0 := by
  have hw0 : PowerSeries.subst (0 : MvPowerSeries σ O) W.formalW = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalW
  exact Projective.Point.toAffine_of_Z_eq_zero (by simp [hw0])

variable {KK} [IsFractionRing (MvPowerSeries σ O) KK]

/-- For a nonzero parameter `q` with `constantCoeff q = 0`, over a fraction field `KK` of
`MvPowerSeries σ O` where `fracCurve W σ KK` has nonzero discriminant, `W.formalThetaPoint KK q` is
the finite nonsingular point `(q / w(q), -1 / w(q))`. -/
theorem formalThetaPoint_eq_some (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    ∃ hns : (fracCurve W σ KK).toAffine.Nonsingular
      (algebraMap (MvPowerSeries σ O) KK q /
        algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q W.formalW))
      (-1 / algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q W.formalW)),
      W.formalThetaPoint KK q = .some _ _ hns := by
  have hz : (algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]) 2 ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero hq hq0
  have hN := (Projective.nonsingular_of_Z_ne_zero hz).mp
    (W.nonsingular_fracCurve_algebraMap_comp_subst_formalW hΔ hq)
  exact ⟨by simpa using hN,
    (W.toAffine_algebraMap_comp_subst_formalW_eq_thetaPoint hΔ hq hq0).trans
      (W.thetaPoint_eq_some hΔ hq hq0 (by simpa using hN))⟩

/-- Over a fraction field `KK` of `MvPowerSeries σ O` where `fracCurve W σ KK` has nonzero
discriminant, `W.formalThetaPoint KK` is injective on parameters with vanishing constant
coefficient. -/
theorem formalThetaPoint_inj (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0) :
    W.formalThetaPoint KK q₁ = W.formalThetaPoint KK q₂ ↔ q₁ = q₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  rcases eq_or_ne q₁ 0 with rfl | hq₁0
  · rcases eq_or_ne q₂ 0 with rfl | hq₂0
    · rfl
    · obtain ⟨_, hθ⟩ := W.formalThetaPoint_eq_some hΔ hq₂ hq₂0
      rw [W.formalThetaPoint_zero KK, hθ] at h
      simp at h
  · rcases eq_or_ne q₂ 0 with rfl | hq₂0
    · obtain ⟨_, hθ⟩ := W.formalThetaPoint_eq_some hΔ hq₁ hq₁0
      rw [W.formalThetaPoint_zero KK, hθ] at h
      simp at h
    · rw [formalThetaPoint, formalThetaPoint,
        W.toAffine_algebraMap_comp_subst_formalW_eq_thetaPoint hΔ hq₁ hq₁0,
        W.toAffine_algebraMap_comp_subst_formalW_eq_thetaPoint hΔ hq₂ hq₂0] at h
      exact (W.thetaPoint_inj hΔ hq₁ hq₂ hq₁0 hq₂0).mp h

omit [IsFractionRing (MvPowerSeries σ O) KK] in
/-- **Addition of formal points via the Bosma–Lenstra law.** Over a field `KK` that is an
`MvPowerSeries σ O`-algebra in which `fracCurve W σ KK` has nonzero discriminant, for any `q₁, q₂`
with vanishing constant coefficients, the group-law sum of `W.formalThetaPoint KK q₁` and
`W.formalThetaPoint KK q₂` is `W.formalThetaPoint KK` evaluated at the formal-group sum of `q₁` and
`q₂`. -/
theorem formalThetaPoint_add [DecidableEq KK] (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ O} (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0) :
    W.formalThetaPoint KK q₁ + W.formalThetaPoint KK q₂ =
      W.formalThetaPoint KK (subst ![q₁, q₂] (formalGroup W).toPowerSeries) := by
  set ρ := algebraMap (MvPowerSeries σ O) KK
  -- Identify the `Unit ⊕ Unit` pair substitution of `formalAdd W` with the `Fin 2` substitution
  -- of `(formalGroup W).toPowerSeries`.
  set G := subst ![q₁, q₂] (formalGroup W).toPowerSeries
  have hFG : subst (pairSubstitution q₁ q₂) (formalAdd W) = G := by
    dsimp only [G]
    rw [formalGroup_toPowerSeries, MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _
      (hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨hq₁, hq₂⟩))]
    congr 1
    funext i
    rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp
  -- Push the pair-substituted Bosma–Lenstra identity from `MvPowerSeries σ O` into `KK`;
  -- its scalar factor `-Y` is a unit, so `dblAddXYZ` represents the affine group-law sum.
  have hdbl := W.dblAddXYZ_subst_formalW_eq_smul hq₁ hq₂
  rw [hFG] at hdbl
  have hu : IsUnit
      (-ρ ((W.toProjective.map (algebraMap O (MvPowerSeries σ O))).dblAddY
        ![q₁, -1, PowerSeries.subst q₁ W.formalW]
        ![q₂, -1, PowerSeries.subst q₂ W.formalW])) :=
    ((W.isUnit_dblAddY_subst_formalW hq₁ hq₂).map ρ).neg
  have hN₁ := W.nonsingular_fracCurve_algebraMap_comp_subst_formalW hΔ hq₁
  have hN₂ := W.nonsingular_fracCurve_algebraMap_comp_subst_formalW hΔ hq₂
  have hD : (fracCurve W σ KK).toProjective.dblAddXYZ
      (ρ ∘ ![q₁, -1, PowerSeries.subst q₁ W.formalW])
      (ρ ∘ ![q₂, -1, PowerSeries.subst q₂ W.formalW]) =
      hu.unit • (ρ ∘ ![G, -1, PowerSeries.subst G W.formalW]) := by
    have hmap : (fracCurve W σ KK).toProjective =
        (W.toProjective.map (algebraMap O (MvPowerSeries σ O))).map ρ :=
      congrArg WeierstrassCurve.toProjective ((fracCurve_def W σ KK).trans (W.map_map _ _).symm)
    rw [hmap, Projective.map_dblAddXYZ, hdbl]
    funext k
    fin_cases k <;> simp [Units.smul_def, IsUnit.unit_spec]
  have hD0 : (fracCurve W σ KK).toProjective.dblAddXYZ
      (ρ ∘ ![q₁, -1, PowerSeries.subst q₁ W.formalW])
      (ρ ∘ ![q₂, -1, PowerSeries.subst q₂ W.formalW]) ≠ 0 := by
    rw [hD]
    intro h0
    exact hu.ne_zero (by simpa [Units.smul_def, IsUnit.unit_spec] using congrFun h0 1)
  rw [formalThetaPoint, formalThetaPoint, formalThetaPoint,
    ← Projective.Point.toAffine_add hN₁ hN₂,
    ← Projective.Point.toAffine_of_equiv (Projective.dblAddXYZ_equiv_add hN₁ hN₂ hD0), hD,
    Projective.Point.toAffine_of_equiv ⟨hu.unit, rfl⟩]

end FormalThetaPoint

end WeierstrassCurve
