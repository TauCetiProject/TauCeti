/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.FormalPoint
import TauCeti.RingTheory.MvPowerSeries.Rename
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The formal-point homomorphism over multivariate power series

Let `W` be a Weierstrass curve over a commutative ring `R`, with `w`-expansion `w = formalW W` and
formal group law `formalGroup W`. Over any field `KK` equipped with a compatible
`MvPowerSeries σ R`-algebra structure such that `W.baseChange KK` is elliptic, sending a
formal-group point `q : (formalGroup W).Point σ` to the affine point represented by the homogeneous
triple `[q : -1 : w(q)]` defines a group homomorphism `WeierstrassCurve.mvPowerSeriesPointHom :
(formalGroup W).Point σ →+ (W.baseChange KK).toAffine.Point`.

Unlike `WeierstrassCurve.formalPointHom` for adic ideals, additivity holds without auxiliary-point
or distinctness hypotheses: specializing the universal Bosma–Lenstra formal-point identities
`WeierstrassCurve.isUnit_dblAddY_formalW` and `WeierstrassCurve.dblAddXYZ_formalW_eq_smul` along
`MvPowerSeries.pairSubstitution q₁ q₂` shows that `dblAddXYZ` has invertible `Y`-coordinate at every
pair of formal-group points and represents `(formalGroup W)(q₁, q₂)` up to that unit scalar. When
`MvPowerSeries σ R` embeds faithfully into `KK`, `mvPowerSeriesPointHom` is injective
(`WeierstrassCurve.mvPowerSeriesPointHom_injective`). Over a ground field `K`, any `K`-algebra map
`K(W) →ₐ[K] KK` expanding `-x / y` to `q` and `-1 / y` to `w(q)` carries `W.toAffine.genericPoint`
to `mvPowerSeriesPointHom q` (`WeierstrassCurve.map_genericPoint_eq_mvPowerSeriesPointHom`).

## Main definitions

* `WeierstrassCurve.mvPowerSeriesPointHom`: the additive homomorphism
  `(formalGroup W).Point σ →+ (W.baseChange KK).toAffine.Point` sending `q` to `[q : -1 : w(q)]`.

## Main results

* `WeierstrassCurve.isUnit_dblAddY_subst_formalW` and
  `WeierstrassCurve.dblAddXYZ_subst_formalW_eq_smul`: the Bosma–Lenstra addition law `dblAddXYZ`
  evaluated at `[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]` over `MvPowerSeries σ R`.
* `WeierstrassCurve.mvPowerSeriesPointHom_injective`: injectivity of `mvPowerSeriesPointHom` when
  `[FaithfulSMul (MvPowerSeries σ R) KK]`.
* `WeierstrassCurve.map_genericPoint_eq_mvPowerSeriesPointHom`: evaluating `W.toAffine.genericPoint`
  along an expansion `K(W) →ₐ[K] KK` at a nonzero formal point `q` gives
  `W.mvPowerSeriesPointHom σ KK q`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1 and IV.4.
-/

public section

open MvPowerSeries WeierstrassCurve.Affine

namespace WeierstrassCurve

section PairSubst

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {σ : Type*}
  {q₁ q₂ : MvPowerSeries σ R}

private theorem hasSubst_pair_of_hasSubst (hq₁ : PowerSeries.HasSubst q₁)
    (hq₂ : PowerSeries.HasSubst q₂) :
    MvPowerSeries.HasSubst (pairSubstitution q₁ q₂) :=
  hasSubst_of_constantCoeff_nilpotent fun i ↦ by
    rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simpa [pairSubstitution]

private theorem substAlgHom_pair_comp_formalVec (hq₁ : PowerSeries.HasSubst q₁)
    (hq₂ : PowerSeries.HasSubst q₂) (z : MvPowerSeries (Unit ⊕ Unit) R)
    (hz : PowerSeries.HasSubst z) :
    (MvPowerSeries.substAlgHom (R := R) (hasSubst_pair_of_hasSubst hq₁ hq₂) :
        MvPowerSeries (Unit ⊕ Unit) R →+* MvPowerSeries σ R) ∘
      ![z, -1, PowerSeries.subst z W.formalW] =
    ![MvPowerSeries.subst (pairSubstitution q₁ q₂) z, -1,
      PowerSeries.subst (MvPowerSeries.subst (pairSubstitution q₁ q₂) z) W.formalW] := by
  set s : MvPowerSeries (Unit ⊕ Unit) R →ₐ[R] MvPowerSeries σ R :=
    MvPowerSeries.substAlgHom (hasSubst_pair_of_hasSubst hq₁ hq₂)
  funext k
  fin_cases k
  · simp [s, coe_substAlgHom]
  · simp
  · simp only [Function.comp_apply, AlgHom.coe_toRingHom, s, coe_substAlgHom]
    exact subst_powerSeriesSubst (hasSubst_pair_of_hasSubst hq₁ hq₂) hz W.formalW

/-- **The `Y`-coordinate of `dblAddXYZ` at `[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]` is a unit**
in `MvPowerSeries σ R` for any substitutable parameters `q₁, q₂`, without smoothness or domain
hypotheses on `W` or `R`. -/
theorem isUnit_dblAddY_subst_formalW (hq₁ : PowerSeries.HasSubst q₁)
    (hq₂ : PowerSeries.HasSubst q₂) :
    IsUnit (Projective.dblAddY (W.toProjective.map (algebraMap R (MvPowerSeries σ R)))
      ![q₁, -1, PowerSeries.subst q₁ W.formalW]
      ![q₂, -1, PowerSeries.subst q₂ W.formalW]) := by
  have hpair := hasSubst_pair_of_hasSubst hq₁ hq₂
  let s : MvPowerSeries (Unit ⊕ Unit) R →ₐ[R] MvPowerSeries σ R := MvPowerSeries.substAlgHom hpair
  have hs_curve :
      (W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R))).map
          (s : MvPowerSeries (Unit ⊕ Unit) R →+* MvPowerSeries σ R) =
        W.toProjective.map (algebraMap R (MvPowerSeries σ R)) := by
    ext : 1 <;> exact s.commutes _
  have hv₁ := W.substAlgHom_pair_comp_formalVec hq₁ hq₂ (X (Sum.inl ()))
    (PowerSeries.HasSubst.X _)
  have hv₂ := W.substAlgHom_pair_comp_formalVec hq₁ hq₂ (X (Sum.inr ()))
    (PowerSeries.HasSubst.X _)
  simp only [subst_X hpair, pairSubstitution, Sum.elim_inl, Sum.elim_inr] at hv₁ hv₂
  have hY_eq :
      (s : MvPowerSeries (Unit ⊕ Unit) R →+* MvPowerSeries σ R)
        (Projective.dblAddY (W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R)))
          ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
          ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW]) =
        Projective.dblAddY (W.toProjective.map (algebraMap R (MvPowerSeries σ R)))
          ![q₁, -1, PowerSeries.subst q₁ W.formalW]
          ![q₂, -1, PowerSeries.subst q₂ W.formalW] := by
    rw [← Projective.map_dblAddY, hs_curve, hv₁, hv₂]
  rw [← hY_eq]
  exact W.isUnit_dblAddY_formalW.map (s : MvPowerSeries (Unit ⊕ Unit) R →+* MvPowerSeries σ R)

/-- **The Bosma–Lenstra addition law `dblAddXYZ` at `[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]`** is
`-dblAddY` times `[(formalGroup W)(q₁, q₂) : -1 : w((formalGroup W)(q₁, q₂))]` for any substitutable
parameters `q₁, q₂ : MvPowerSeries σ R`, without smoothness or domain hypotheses on `W` or `R`. -/
theorem dblAddXYZ_subst_formalW_eq_smul (hq₁ : PowerSeries.HasSubst q₁)
    (hq₂ : PowerSeries.HasSubst q₂) :
    Projective.dblAddXYZ (W.toProjective.map (algebraMap R (MvPowerSeries σ R)))
        ![q₁, -1, PowerSeries.subst q₁ W.formalW]
        ![q₂, -1, PowerSeries.subst q₂ W.formalW] =
      -Projective.dblAddY (W.toProjective.map (algebraMap R (MvPowerSeries σ R)))
        ![q₁, -1, PowerSeries.subst q₁ W.formalW]
        ![q₂, -1, PowerSeries.subst q₂ W.formalW] •
        ![MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries, -1,
          PowerSeries.subst (MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries)
            W.formalW] := by
  have hpair := hasSubst_pair_of_hasSubst hq₁ hq₂
  let s : MvPowerSeries (Unit ⊕ Unit) R →ₐ[R] MvPowerSeries σ R := MvPowerSeries.substAlgHom hpair
  have hs_curve :
      (W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R))).map
          (s : MvPowerSeries (Unit ⊕ Unit) R →+* MvPowerSeries σ R) =
        W.toProjective.map (algebraMap R (MvPowerSeries σ R)) := by
    ext : 1 <;> exact s.commutes _
  have hv₁ := W.substAlgHom_pair_comp_formalVec hq₁ hq₂ (X (Sum.inl ()))
    (PowerSeries.HasSubst.X _)
  have hv₂ := W.substAlgHom_pair_comp_formalVec hq₁ hq₂ (X (Sum.inr ()))
    (PowerSeries.HasSubst.X _)
  have hvF := W.substAlgHom_pair_comp_formalVec hq₁ hq₂ (formalAdd W)
    (.of_constantCoeff_zero (constantCoeff_formalAdd W))
  simp only [subst_X hpair, pairSubstitution, Sum.elim_inl, Sum.elim_inr] at hv₁ hv₂
  have hsF : MvPowerSeries.subst (pairSubstitution q₁ q₂) (formalAdd W) =
      MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries := by
    have hcomp : (![q₁, q₂] : Fin 2 → MvPowerSeries σ R) ∘ TauCeti.unitSumUnitEquivFinTwo =
        pairSubstitution q₁ q₂ := by
      funext i
      rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [pairSubstitution]
    rw [formalGroup_toPowerSeries,
      MvPowerSeries.subst_rename TauCeti.unitSumUnitEquivFinTwo _ (hasSubst_finTwo hq₁ hq₂), hcomp]
  rw [hsF] at hvF
  have key := congrArg (fun v ↦ (s : MvPowerSeries (Unit ⊕ Unit) R →+* MvPowerSeries σ R) ∘ v)
    W.dblAddXYZ_formalW_eq_smul
  rw [← Projective.map_dblAddXYZ, hs_curve, hv₁, hv₂] at key
  rw [key]
  funext k
  have hk := congrFun hvF k
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_neg] at hk ⊢
  rw [← Projective.map_dblAddY, hs_curve, hv₁, hv₂, hk]

end PairSubst

section PointHom

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (σ : Type*) (KK : Type*)
  [Field KK] [Algebra R KK] [Algebra (MvPowerSeries σ R) KK]
  [IsScalarTower R (MvPowerSeries σ R) KK]

private theorem baseChange_toProjective_eq_map :
    (W.baseChange KK).toProjective =
      (W.toProjective.map (algebraMap R (MvPowerSeries σ R))).map
        (algebraMap (MvPowerSeries σ R) KK) := by
  ext <;> exact IsScalarTower.algebraMap_apply R (MvPowerSeries σ R) KK _

private theorem nonsingular_formalPointVec [(W.baseChange KK).IsElliptic]
    (q : (formalGroup W).Point σ) :
    (W.baseChange KK).toProjective.Nonsingular
      (algebraMap (MvPowerSeries σ R) KK ∘ ![q.val, -1, PowerSeries.subst q.val W.formalW]) := by
  have hΔ : (W.baseChange KK).toProjective.Δ ≠ 0 := (W.baseChange KK).isUnit_Δ.ne_zero
  refine (Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero hΔ
    fun h ↦ by simpa using congrFun h 1).mp ?_
  rw [baseChange_toProjective_eq_map W σ KK]
  exact ((W.toProjective.equation_neg_one_iff_wEquation q.val _).mpr
    (W.subst_formalW_wEquation q.prop)).map _

private theorem algebraMap_subst_formalW_ne_zero_of_faithfulSMul
    [FaithfulSMul (MvPowerSeries σ R) KK] {q : (formalGroup W).Point σ} (hq0 : q.val ≠ 0) :
    algebraMap (MvPowerSeries σ R) KK (PowerSeries.subst q.val W.formalW) ≠ 0 := by
  have hρ := FaithfulSMul.algebraMap_injective (MvPowerSeries σ R) KK
  have hR : Function.Injective (algebraMap R KK) := by
    rw [IsScalarTower.algebraMap_eq R (MvPowerSeries σ R) KK, RingHom.coe_comp]
    exact hρ.comp MvPowerSeries.C_injective
  have : IsDomain R := Function.Injective.isDomain (algebraMap R KK) hR
  have : IsDomain (MvPowerSeries σ R) :=
    Function.Injective.isDomain (algebraMap (MvPowerSeries σ R) KK) hρ
  have : FaithfulSMul R (MvPowerSeries σ R) :=
    (faithfulSMul_iff_algebraMap_injective R (MvPowerSeries σ R)).mpr MvPowerSeries.C_injective
  have hw0 : W.formalW ≠ 0 := fun h ↦ by
    have hc := congrArg (PowerSeries.coeff 3) h
    rw [coeff_formalW, formalWCoeff_three, map_zero] at hc
    exact one_ne_zero hc
  exact (map_ne_zero_iff _ hρ).mpr ((PowerSeries.subst_eq_zero_iff q.prop.eq_zero hq0).not.mpr hw0)

variable [DecidableEq KK] [(W.baseChange KK).IsElliptic]

/-- **Sending a formal-group point `q : (formalGroup W).Point σ` to the affine point with
homogeneous coordinates `[q : -1 : w(q)]` in `(W.baseChange KK).toAffine.Point` is an additive
homomorphism**, whenever `W.baseChange KK` is elliptic. -/
noncomputable def mvPowerSeriesPointHom :
    (formalGroup W).Point σ →+ (W.baseChange KK).toAffine.Point where
  toFun q := Projective.Point.toAffine (W.baseChange KK).toProjective
    (algebraMap (MvPowerSeries σ R) KK ∘ ![q.val, -1, PowerSeries.subst q.val W.formalW])
  map_zero' := by
    refine Projective.Point.toAffine_of_Z_eq_zero ?_
    simp [PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalW]
  map_add' q₁ q₂ := by
    -- Push `dblAddXYZ_subst_formalW_eq_smul` and `isUnit_dblAddY_subst_formalW` along `ρ`.
    set ρ := algebraMap (MvPowerSeries σ R) KK
    set P₁ := ρ ∘ ![q₁.val, -1, PowerSeries.subst q₁.val W.formalW]
    set P₂ := ρ ∘ ![q₂.val, -1, PowerSeries.subst q₂.val W.formalW]
    set P₁₂ := ρ ∘ ![(q₁ + q₂).val, -1, PowerSeries.subst (q₁ + q₂).val W.formalW]
    set u : KK := ρ (-Projective.dblAddY
      (W.toProjective.map (algebraMap R (MvPowerSeries σ R)))
      ![q₁.val, -1, PowerSeries.subst q₁.val W.formalW]
      ![q₂.val, -1, PowerSeries.subst q₂.val W.formalW])
    have hu : IsUnit u := ((W.isUnit_dblAddY_subst_formalW q₁.prop q₂.prop).neg).map ρ
    have keyKK : (W.baseChange KK).toProjective.dblAddXYZ P₁ P₂ = u • P₁₂ := by
      rw [baseChange_toProjective_eq_map W σ KK, Projective.map_dblAddXYZ,
        W.dblAddXYZ_subst_formalW_eq_smul q₁.prop q₂.prop]
      funext k
      simp only [P₁₂, u, ρ, Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_neg,
        FormalGroup.add_apply]
    have hD0 : (W.baseChange KK).toProjective.dblAddXYZ P₁ P₂ ≠ 0 := by
      rw [keyKK]
      intro h0
      have h1 := congrFun h0 1
      simp [P₁₂, hu.ne_zero] at h1
    have hN₁ := nonsingular_formalPointVec W σ KK q₁
    have hN₂ := nonsingular_formalPointVec W σ KK q₂
    symm
    rw [← Projective.Point.toAffine_add hN₁ hN₂,
      ← Projective.Point.toAffine_of_equiv (Projective.dblAddXYZ_equiv_add hN₁ hN₂ hD0), keyKK]
    exact Projective.Point.toAffine_of_equiv
      ⟨hu.unit, by simp only [Units.smul_def, IsUnit.unit_spec]⟩

@[simp]
theorem mvPowerSeriesPointHom_apply (q : (formalGroup W).Point σ) :
    W.mvPowerSeriesPointHom σ KK q = Projective.Point.toAffine (W.baseChange KK).toProjective
      (algebraMap (MvPowerSeries σ R) KK ∘ ![q.val, -1, PowerSeries.subst q.val W.formalW]) :=
  (rfl)

/-- **When `MvPowerSeries σ R` embeds faithfully into `KK` and `W.baseChange KK` is elliptic,
`mvPowerSeriesPointHom` is injective.** -/
theorem mvPowerSeriesPointHom_injective [FaithfulSMul (MvPowerSeries σ R) KK] :
    Function.Injective (W.mvPowerSeriesPointHom σ KK) := by
  -- At any nonzero `q` the `Z`-coordinate `w(q)` is nonzero in `KK`, so `toAffine` is nonzero.
  refine (injective_iff_map_eq_zero _).mpr fun q hq0 ↦ ?_
  by_contra hq
  have hval : q.val ≠ 0 := fun h ↦ hq (Subtype.ext h)
  have hz : (algebraMap (MvPowerSeries σ R) KK ∘
      ![q.val, -1, PowerSeries.subst q.val W.formalW]) 2 ≠ 0 :=
    algebraMap_subst_formalW_ne_zero_of_faithfulSMul W σ KK hval
  rw [mvPowerSeriesPointHom_apply,
    Projective.Point.toAffine_of_Z_ne_zero (nonsingular_formalPointVec W σ KK q) hz] at hq0
  exact Affine.Point.some_ne_zero _ hq0

end PointHom

section GenericPoint

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (σ : Type*) (KK : Type*)
  [Field KK] [DecidableEq KK] [Algebra K KK] [Algebra (MvPowerSeries σ K) KK]
  [IsScalarTower K (MvPowerSeries σ K) KK] [FaithfulSMul (MvPowerSeries σ K) KK]

/-- **Any `K`-algebra homomorphism `A : K(W) →ₐ[K] KK` sending `-x / y` to `q` and `-1 / y` to
`w(q)` at a nonzero formal point `q` carries `W.toAffine.genericPoint` to
`W.mvPowerSeriesPointHom σ KK q`** for an elliptic curve `W`. -/
theorem map_genericPoint_eq_mvPowerSeriesPointHom
    (A : W.toAffine.FunctionField →ₐ[K] KK) {q : (formalGroup W).Point σ} (hq0 : q.val ≠ 0)
    (hparam : A (-W.toAffine.genericX / W.toAffine.genericY) =
      algebraMap (MvPowerSeries σ K) KK q.val)
    (hw : A (-W.toAffine.genericY⁻¹) =
      algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q.val W.formalW)) :
    Point.map A W.toAffine.genericPoint = W.mvPowerSeriesPointHom σ KK q := by
  let ρ := algebraMap (MvPowerSeries σ K) KK
  let w := ρ (PowerSeries.subst q.val W.formalW)
  have hw0 : w ≠ 0 := algebraMap_subst_formalW_ne_zero_of_faithfulSMul W σ KK hq0
  have hAy : A W.toAffine.genericY = -1 / w := by
    rw [map_neg, map_inv₀] at hw
    have h1 : (A W.toAffine.genericY)⁻¹ = -w := neg_eq_iff_eq_neg.mp hw
    rw [← inv_inv (A W.toAffine.genericY), h1, neg_div, one_div, inv_neg]
  have hAx : A W.toAffine.genericX = ρ q.val / w := by
    rw [map_div₀, map_neg, hAy] at hparam
    field_simp [hw0] at hparam
    exact eq_div_of_mul_eq hw0 hparam
  have hz : (ρ ∘ ![q.val, -1, PowerSeries.subst q.val W.formalW]) 2 ≠ 0 := hw0
  rw [mvPowerSeriesPointHom_apply,
    Projective.Point.toAffine_of_Z_ne_zero (nonsingular_formalPointVec W σ KK q) hz]
  refine Point.eq_of_coords ?_ (Affine.Point.some_ne_zero _) ?_ ?_
  · rw [genericPoint_eq_some, Point.map_some]
    exact Affine.Point.some_ne_zero _
  · rw [Point.xCoord_map, xCoord_genericPoint, Point.xCoord_some]
    exact hAx
  · rw [Point.yCoord_map, yCoord_genericPoint, Point.yCoord_some]
    simpa [w] using hAy

end GenericPoint

end WeierstrassCurve

end
