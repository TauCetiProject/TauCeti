/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Series
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FormalPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal

/-!
# The addition morphism at the formal point

Let `W` be a Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its projective
model, and let `z₁` and `z₂` be the two variables of `R⟦z₁, z₂⟧ = MvPowerSeries (Unit ⊕ Unit) R`.
In the parameter `z = -X / Y` at the zero section, the formal point of `E`
(`WeierstrassCurve.projModelFormalPoint`) reparametrised by `X ↦ zᵢ` has homogeneous coordinates
`[zᵢ : -1 : w(zᵢ)]`, where `w` is the `w`-expansion `formalW W`. This file proves that the
Bosma–Lenstra addition morphism `E ×_{Spec R} E ⟶ E` sends this pair of points to the formal point
reparametrised by `X ↦ F(z₁, z₂)`, where `F = formalAdd W` is the addition series of the chord
construction (`WeierstrassCurve.lift_projModelFormalPoint_additionMorphism`). In other words, the
group law of `E`, written in the formal parameter along the zero section, is the formal group law
`F` (packaged as Mathlib's `FormalGroup` in `WeierstrassCurve.formalGroup`). It is the input for
reading statements about closed subschemes of `E` supported on the zero section, such as the
divisors `n[0]` being subgroup schemes, as statements about `F`.

The computation is algebraic. The `Y`-coordinate of the addition law `dblAddXYZ`, attached to the
line `Y = 0`, is a unit at the two points (`WeierstrassCurve.isUnit_dblAddY_formalW`): both points
restrict to `[0 : -1 : 0]` at `z₁ = z₂ = 0`, where the law takes the value `[0 : 1 : 0]`. So the
addition morphism is computed by that law, and its value is a unit multiple of
`(F(z₁, z₂), -1, w(F(z₁, z₂)))` (`WeierstrassCurve.dblAddXYZ_formalW_eq_smul`). That identity is
first proved over a domain with nonzero discriminant, in particular for the universal curve over
`ℤ[A₁, ⋯, A₆]`. There, over a fraction field of the power series ring, `dblAddXYZ` represents the
sum of the two points in the group law of the curve
(`WeierstrassCurve.Projective.dblAddXYZ_equiv_add`), and that sum is the point with parameter `F`
(`WeierstrassCurve.thetaPoint_add_of_subst_separates`). Base change along
`WeierstrassCurve.specialize` then gives it for every `W`. No hypothesis is placed on `R`; in
particular `R` need not be reduced.

## Main results

* `WeierstrassCurve.isUnit_dblAddY_formalW` and
  `WeierstrassCurve.isUnit_dblAddY_subst_formalW`: the `Y`-coordinate of `dblAddXYZ` at formal
  points `[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]` is a unit.
* `WeierstrassCurve.dblAddXYZ_formalW_eq_smul` and
  `WeierstrassCurve.dblAddXYZ_subst_formalW_eq_smul`: the value of `dblAddXYZ` at formal points is a
  unit multiple of `(F(q₁, q₂), -1, w(F(q₁, q₂)))`.
* `WeierstrassCurve.lift_projModelFormalPoint_additionMorphism`: the addition morphism sends the
  pair of formal points reparametrised by `X ↦ z₁` and `X ↦ z₂` to the formal point
  reparametrised by `X ↦ F(z₁, z₂)`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §5.3, where the formal group law of an elliptic curve in a
  parameter along the zero section is used to study subgroup schemes supported on the zero section.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MvPowerSeries

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
theorem nonsingular_algebraMap_comp (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) :
    (fracCurve W σ KK).toProjective.Nonsingular
      (algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]) := by
  refine (Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero hΔ
    fun h ↦ by simpa using congrFun h 1).mp ?_
  rw [fracCurve_def, ← map_map]
  exact ((W.toProjective.equation_neg_one_iff_wEquation q _).mpr
    (W.subst_formalW_wEquation (PowerSeries.HasSubst.of_constantCoeff_zero hq))).map _

/-- For a nonzero parameter `q` with `constantCoeff q = 0`, the affine point associated to
`[q : -1 : w(q)]` over a fraction field `KK` of `MvPowerSeries σ O` is `W.thetaPoint`. -/
theorem toAffine_algebraMap_comp_eq_thetaPoint (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Projective.Point.toAffine (fracCurve W σ KK).toProjective
      (algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]) =
        W.thetaPoint hΔ hq hq0 := by
  have hz : (algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]) 2 ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero hq hq0
  have hN := W.nonsingular_algebraMap_comp hΔ hq
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
  have hN₁ := W.nonsingular_algebraMap_comp hΔ' hz₁
  have hN₂ := W.nonsingular_algebraMap_comp hΔ' hz₂
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
      Projective.Point.toAffine_add hN₁ hN₂, W.toAffine_algebraMap_comp_eq_thetaPoint hΔ' hz₁ hz₁0,
      W.toAffine_algebraMap_comp_eq_thetaPoint hΔ' hz₂ hz₂0,
      W.toAffine_algebraMap_comp_eq_thetaPoint hΔ' hFc hF0]
    exact W.thetaPoint_add_of_subst_separates hΔ' hχ hz₁ hz₂ hz₁0 hz₂0 hχ₁ hχ₂ hFc hF0
  have hDN : W'.toProjective.Nonsingular (ρ ∘ D) :=
    (Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero hΔ' hD0).mp
      (hD ▸ hN₁.left.dblAddXYZ hN₂.left)
  -- equal affine points are projectively equivalent: `ρ ∘ D = u • ρ ∘ (F, -1, w(F))`
  obtain ⟨u, hu⟩ := (Projective.Point.toAffine_eq_toAffine_iff hDN
    (W.nonsingular_algebraMap_comp hΔ' hFc)).mp hsum
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

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- **The addition morphism at the formal point.** Let `z₁` and `z₂` be the two variables of
`R⟦z₁, z₂⟧`. The Bosma–Lenstra addition morphism `E ×_{Spec R} E ⟶ E` of the projective model
`E = projModel W` sends the pair of formal points reparametrised by `X ↦ z₁` and by `X ↦ z₂` to
the formal point reparametrised by `X ↦ F(z₁, z₂)`, where `F = formalAdd W` is the addition series
of the chord construction. That is, the group law of `E`, written in the parameter `z = -X / Y`
at the zero section, is the formal group law `F`. -/
theorem lift_projModelFormalPoint_additionMorphism [W.IsElliptic] :
    pullback.lift
        (Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom
          (PowerSeries.HasSubst.X (S := R) (Sum.inl () : Unit ⊕ Unit))).toRingHom) ≫
            W.projModelFormalPoint)
        (Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom
          (PowerSeries.HasSubst.X (S := R) (Sum.inr () : Unit ⊕ Unit))).toRingHom) ≫
            W.projModelFormalPoint)
        (by simp only [Category.assoc, projModelFormalPoint_projModelOver, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]) ≫
          W.additionMorphism =
      Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom
        (PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_formalAdd)).toRingHom) ≫
          W.projModelFormalPoint := by
  simp only [SpecMap_substAlgHom_projModelFormalPoint]
  -- the `Y`-coordinate of `dblAddXYZ` is a unit, so the addition morphism is computed by that law,
  -- whose value is a unit multiple of `(F, -1, w(F))`
  have hY := W.isUnit_dblAddY_formalW
  rw [W.lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ (m := 1) _ _
    (by simpa using hY), projModelPoint_eq_projModelPoint_iff]
  exact ⟨rfl, -hY.unit, by rw [dblAddXYZ_formalW_eq_smul, Units.smul_def, Units.val_neg,
    IsUnit.unit_spec]⟩

end WeierstrassCurve
