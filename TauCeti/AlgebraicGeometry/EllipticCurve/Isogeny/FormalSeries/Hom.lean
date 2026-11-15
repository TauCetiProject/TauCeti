/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
public import TauCeti.RingTheory.FormalGroup.Hom.Basic
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.FormalPoint
import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Formal power series of morphisms and induced formal-group homomorphisms

Let `W₁` and `W₂` be Weierstrass curves over a field `K`. Every isogeny `φ : W₁ → W₂` has a
formal power series `φ.formalSeries ∈ K⟦X⟧` expanding `φ*(-x₂ / y₂)` in the parameter
`z₁ = -x₁ / y₁` at infinity (`TauCeti.Isogeny.formalSeries`). Extending by zero on the zero
morphism defines `f.formalSeries` for every morphism `f : Hom W₁.toAffine W₂.toAffine`.

When `W₂` is elliptic, addition of morphisms becomes addition in the formal group law of `W₂`
(`TauCeti.Isogeny.Hom.formalSeries_add`), and every isogeny (or morphism) induces a homomorphism
of formal group laws `formalGroup W₁ → formalGroup W₂` (`TauCeti.Isogeny.formalGroupHom`,
`TauCeti.Isogeny.Hom.formalGroupHom`; Silverman IV.4.2(b)). In particular, the formal series of
multiplication by `n` on an elliptic curve `W` is the multiplication series `[n]_{Ê}` of its
formal group (`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`,
`TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`).

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries`: the formal series of a morphism `W₁ → W₂`, zero at `0`.
* `TauCeti.Isogeny.formalGroupHom`: the formal-group homomorphism induced by an isogeny.
* `TauCeti.Isogeny.Hom.formalGroupHom`: the formal-group homomorphism induced by a morphism.

## Main results

* `TauCeti.Isogeny.formalSeries_map` and `TauCeti.Isogeny.Hom.formalSeries_map`: `formalSeries`
  commutes with base change of the coefficient field.
* `TauCeti.Isogeny.formalSeries_negIsogeny`: negation induces the formal inverse series.
* `TauCeti.Isogeny.Hom.formalSeries_add`, `TauCeti.Isogeny.Hom.formalSeries_zsmul` and
  `TauCeti.Isogeny.Hom.formalSeries_nsmul`: the formal series of a sum or integer multiple of
  morphisms is computed in `formalGroup W₂`.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny` and
  `TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`: the formal series of `[n]` on an
  elliptic curve is `(formalGroup W).zsmulSeries n` (and `(formalGroup W).nsmulSeries n` for
  natural `n`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4.2.
-/

public section

open WeierstrassCurve HahnSeries MvPowerSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.Isogeny

-- `Affine.Point.map` expects `IsScalarTower K K K⸨X⸩` for the `Algebra.toSMul` action rather
-- than `HahnSeries`'s default coefficientwise `SMul`.
private local instance {K : Type*} [Field K] :
    @IsScalarTower K K K⸨X⸩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  @IsScalarTower.mk K K K⸨X⸩ Algebra.toSMul Algebra.toSMul Algebra.toSMul fun a b f ↦ by
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, map_mul, mul_assoc]

section BaseChangeAndNeg

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

/-- Base change of an isogeny along a field homomorphism `σ` maps the coefficients of its formal
series by `σ`. -/
@[simp]
theorem formalSeries_map {L : Type*} [Field L] (φ : Isogeny W₁.toAffine W₂.toAffine)
    (σ : K →+* L) :
    (φ.map σ).formalSeries = PowerSeries.map σ φ.formalSeries := by
  apply (formalSeries_eq_iff (W₁ := W₁.map σ) (W₂ := W₂.map σ) (φ.map σ) _).mpr
  rw [← HahnSeries.map_ofPowerSeries, ← HahnSeries.mapRingHom_apply, coe_formalSeries,
    ← W₁.functionFieldLaurentExpansion_map, ← map_fieldPullback_map]
  simp [Affine.FunctionField.map_genericX, Affine.FunctionField.map_genericY]

/-- The formal series of the negation isogeny is the inverse series of the formal group law. -/
@[simp]
theorem formalSeries_negIsogeny (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = (formalGroup W).addInvX := by
  rw [formalGroup_addInvX, formalInverse_def]
  apply (formalSeries_eq_iff _ _).mpr
  have hy : W.functionFieldLaurentExpansion W.toAffine.genericY ≠ 0 :=
    (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr W.toAffine.genericY_ne_zero
  have hny : W.functionFieldLaurentExpansion
      ((negIsogeny W.toAffine).fieldPullback W.toAffine.genericY) ≠ 0 :=
    (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr <|
      (map_ne_zero_iff _ (negIsogeny W.toAffine).fieldPullback.injective).mpr
        W.toAffine.genericY_ne_zero
  have hdenom : W.functionFieldLaurentExpansion
        ((negIsogeny W.toAffine).fieldPullback W.toAffine.genericY) *
        (-W.functionFieldLaurentExpansion W.toAffine.genericY⁻¹) =
      (W.formalInverseDenom : K⸨X⸩) := by
    rw [fieldPullback_negIsogeny_genericY, Affine.negY, map_sub, map_sub, map_neg, map_mul]
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃, AlgHom.commutes]
    have hx := W.functionFieldLaurentExpansion_neg_genericX_div_genericY
    have hw := W.functionFieldLaurentExpansion_neg_inv_genericY
    rw [map_div₀, map_neg] at hx
    rw [map_neg, map_inv₀] at hw
    rw [map_inv₀, formalInverseDenom_def, map_sub, map_sub, map_one, map_mul, map_mul, ← hw, ← hx]
    simp only [PowerSeries.coe_C, LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
    field_simp [hy]
    ring
  have hkey : W.functionFieldLaurentExpansion
        ((negIsogeny W.toAffine).fieldPullback (-W.toAffine.genericX / W.toAffine.genericY)) *
        (W.formalInverseDenom : K⸨X⸩) =
      -((PowerSeries.X : K⟦X⟧) : K⸨X⸩) := by
    rw [← hdenom, ← W.functionFieldLaurentExpansion_neg_genericX_div_genericY]
    simp only [map_div₀, map_neg, map_inv₀, fieldPullback_negIsogeny_genericX]
    field_simp [hy, hny]
  have hunit : (W.formalInverseDenom : K⸨X⸩) *
      (PowerSeries.invOfUnit W.formalInverseDenom 1 : K⸨X⸩) = 1 := by
    rw [← map_mul, W.mul_invOfUnit_formalInverseDenom, map_one]
  calc
    ((- (PowerSeries.X * PowerSeries.invOfUnit W.formalInverseDenom 1) : K⟦X⟧) : K⸨X⸩)
      = -((PowerSeries.X : K⟦X⟧) : K⸨X⸩) *
          (PowerSeries.invOfUnit W.formalInverseDenom 1 : K⸨X⸩) := by
        rw [map_neg, map_mul, neg_mul]
    _ = W.functionFieldLaurentExpansion
          ((negIsogeny W.toAffine).fieldPullback (-W.toAffine.genericX / W.toAffine.genericY)) := by
        rw [← hkey, mul_assoc, hunit, mul_one]

/-! ### Formal series on the morphism carrier -/

namespace Hom

open scoped Classical in
/-- The formal power series of a morphism `f : W₁ → W₂`: `0` at the zero morphism, and the
underlying isogeny's formal series otherwise. -/
noncomputable def formalSeries (f : Hom W₁.toAffine W₂.toAffine) : K⟦X⟧ :=
  if hf : f = 0 then 0 else (toIsogeny hf).formalSeries

open scoped Classical in
/-- Unfold `Hom.formalSeries`. -/
theorem formalSeries_def (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalSeries = if hf : f = 0 then 0 else (toIsogeny hf).formalSeries :=
  (rfl)

/-- The formal power series of the zero morphism is zero. -/
@[simp]
theorem formalSeries_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalSeries = 0 :=
  dite_eq_left_of_eq_true (eq_true rfl)

/-- On an isogeny viewed as a morphism, `Hom.formalSeries` agrees with `Isogeny.formalSeries`. -/
@[simp]
theorem formalSeries_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalSeries = φ.formalSeries := by
  rw [formalSeries_def, dite_eq_right_of_eq_false (eq_false (ofIsogeny_ne_zero φ)),
    toIsogeny_ofIsogeny]

/-- A morphism vanishes if and only if its formal power series vanishes. -/
@[simp]
theorem formalSeries_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact iff_of_true formalSeries_zero rfl
  · exact iff_of_false (formalSeries_ofIsogeny φ ▸ φ.formalSeries_ne_zero) (ofIsogeny_ne_zero φ)

/-- Every morphism's formal power series has zero constant coefficient. -/
@[simp]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

/-- The formal power series of the identity morphism is `X`. -/
@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (Hom.id W.toAffine).formalSeries = PowerSeries.X := by
  rw [Hom.id_def, formalSeries_ofIsogeny, Isogeny.formalSeries_id]

/-- Composition of morphisms induces substitution of their formal power series. -/
@[simp]
theorem formalSeries_comp (g : Hom W₂.toAffine W₃.toAffine)
    (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalSeries = PowerSeries.subst f.formalSeries g.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [comp_zero, formalSeries_zero, formalSeries_zero,
      PowerSeries.subst_zero_of_constantCoeff_zero g.constantCoeff_formalSeries]
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · rw [zero_comp, formalSeries_zero, formalSeries_zero, PowerSeries.subst_zero]
  rw [ofIsogeny_comp_ofIsogeny, formalSeries_ofIsogeny, formalSeries_ofIsogeny,
    formalSeries_ofIsogeny, Isogeny.formalSeries_comp]

/-- Base change of a morphism maps the coefficients of its formal series. -/
@[simp]
theorem formalSeries_map {L : Type*} [Field L] (f : Hom W₁.toAffine W₂.toAffine) (σ : K →+* L) :
    (f.map σ).formalSeries = PowerSeries.map σ f.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [zero_map, formalSeries_zero, formalSeries_zero, map_zero]
  · rw [ofIsogeny_map, formalSeries_ofIsogeny, formalSeries_ofIsogeny, Isogeny.formalSeries_map]

/-- Negation of a morphism composes its formal series with the formal inverse of the target. -/
@[simp]
theorem formalSeries_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries (formalGroup W₂).addInvX := by
  rw [neg_def, formalSeries_comp, formalSeries_ofIsogeny, formalSeries_negIsogeny]

end Hom

end BaseChangeAndNeg

/-! ### Projective formal points over `K⸨X⸩` and addition of formal series -/

section FormalPointAddition

variable {K : Type*} [Field K]

/-- The projective point representative `[q : -1 : w(q)]` over `K⸨X⸩` attached to a power series
`q ∈ K⟦X⟧`. -/
private noncomputable def formalPointRep (W : WeierstrassCurve K) (q : K⟦X⟧) : Fin 3 → K⸨X⸩ :=
  ofPowerSeries ℤ K ∘ ![q, -1, PowerSeries.subst q (formalW W)]

private theorem map_ofPowerSeries_map_algebraMap (W : WeierstrassCurve K) :
    (W.map (algebraMap K K⟦X⟧)).map (ofPowerSeries ℤ K) = W⁄K⸨X⸩ := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map,
    HahnSeries.ofPowerSeries_comp_algebraMap]

private theorem nonsingular_formalPointRep (W : WeierstrassCurve K) [W.IsElliptic] {q : K⟦X⟧}
    (hq : PowerSeries.constantCoeff q = 0) :
    (W⁄K⸨X⸩).toProjective.Nonsingular (formalPointRep W q) := by
  refine (Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero (W⁄K⸨X⸩).isUnit_Δ.ne_zero
    fun h ↦ by simpa [formalPointRep] using congrFun h 1).mp ?_
  have heq :=
    (W.toProjective.equation_neg_one_iff_wEquation q (PowerSeries.subst q (formalW W))).mpr
      (W.subst_formalW_wEquation (.of_constantCoeff_zero' hq))
  simpa only [map_ofPowerSeries_map_algebraMap, formalPointRep] using heq.map (ofPowerSeries ℤ K)

private theorem formalPointRep_eq_of_toAffine_eq (W : WeierstrassCurve K) [W.IsElliptic]
    {q₁ q₂ : K⟦X⟧} (hq₁ : PowerSeries.constantCoeff q₁ = 0)
    (hq₂ : PowerSeries.constantCoeff q₂ = 0)
    (h : Projective.Point.toAffine (W⁄K⸨X⸩).toProjective (formalPointRep W q₁) =
      Projective.Point.toAffine (W⁄K⸨X⸩).toProjective (formalPointRep W q₂)) :
    q₁ = q₂ := by
  obtain ⟨u, hu⟩ := (Projective.Point.toAffine_eq_toAffine_iff
    (nonsingular_formalPointRep W hq₁) (nonsingular_formalPointRep W hq₂)).mp h
  have hu1 : (u : K⸨X⸩) = 1 := by
    have h1 := congrFun hu 1
    simp only [formalPointRep, Function.comp_apply, Pi.smul_apply, Units.smul_def, smul_eq_mul,
      Matrix.cons_val_one, Matrix.cons_val_zero, map_neg, map_one, mul_neg, mul_one,
      neg_inj] at h1
    exact h1
  apply ofPowerSeries_injective (Γ := ℤ)
  have h0 := congrFun hu 0
  simpa only [formalPointRep, Function.comp_apply, Pi.smul_apply, Units.smul_def, smul_eq_mul,
    Matrix.cons_val_zero, hu1, one_mul] using h0.symm

/-- Specializing `dblAddXYZ_formalW_eq_smul` and `isUnit_dblAddY_formalW` along two power series
`q₁, q₂ ∈ K⟦X⟧` with vanishing constant coefficient. -/
private theorem exists_dblAddXYZ_formalW_powerSeries_eq_smul (W : WeierstrassCurve K)
    {q₁ q₂ : K⟦X⟧} (hq₁ : PowerSeries.constantCoeff q₁ = 0)
    (hq₂ : PowerSeries.constantCoeff q₂ = 0) :
    ∃ u : K⟦X⟧, IsUnit u ∧
      (W.toProjective.map (algebraMap K K⟦X⟧)).dblAddXYZ
          ![q₁, -1, PowerSeries.subst q₁ W.formalW]
          ![q₂, -1, PowerSeries.subst q₂ W.formalW] =
        u • ![MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries, -1,
          PowerSeries.subst (MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries)
            W.formalW] := by
  have hs := (PowerSeries.hasSubst_pair hq₁ hq₂).comp_tendstoCofinite
    TauCeti.unitSumUnitEquivFinTwo
  let ev : MvPowerSeries (Unit ⊕ Unit) K →+* K⟦X⟧ := (MvPowerSeries.substAlgHom hs).toRingHom
  have hev_curve : (W.toProjective.map (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K))).map ev =
      W.toProjective.map (algebraMap K K⟦X⟧) :=
    congrArg WeierstrassCurve.toProjective
      ((W.map_map (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K)) ev).trans
        (congrArg W.map (MvPowerSeries.substAlgHom hs).comp_algebraMap))
  have hev_pt (u : MvPowerSeries (Unit ⊕ Unit) K) (hu : constantCoeff u = 0) :
      ev ∘ ![u, -1, PowerSeries.subst u W.formalW] =
        ![ev u, -1, PowerSeries.subst (ev u) W.formalW] := by
    funext k
    fin_cases k
    · rfl
    · simp
    · simpa [ev] using MvPowerSeries.subst_powerSeriesSubst hs (.of_constantCoeff_zero hu) W.formalW
  have h₁ := hev_pt (X (Sum.inl ())) (constantCoeff_X _)
  have h₂ := hev_pt (X (Sum.inr ())) (constantCoeff_X _)
  have hF := hev_pt (formalAdd W) (constantCoeff_formalAdd W)
  have hev₁ : ev (X (Sum.inl ())) = q₁ := by simp [ev, MvPowerSeries.subst_X hs]
  have hev₂ : ev (X (Sum.inr ())) = q₂ := by simp [ev, MvPowerSeries.subst_X hs]
  have hevF : ev (formalAdd W) = MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries := by
    simp only [ev, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.coe_substAlgHom]
    rw [formalGroup_toPowerSeries, MvPowerSeries.subst_rename _ _
      (PowerSeries.hasSubst_pair hq₁ hq₂)]
  refine ⟨-ev ((W.toProjective.map (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K))).dblAddY
      ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
      ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW]),
    (W.isUnit_dblAddY_formalW.map ev).neg, ?_⟩
  have hdbl := congrArg (ev ∘ ·) W.dblAddXYZ_formalW_eq_smul
  rw [← Projective.map_dblAddXYZ, hev_curve, h₁, h₂, hev₁, hev₂] at hdbl
  refine hdbl.trans ?_
  funext k
  have hk := congrFun hF k
  rw [hevF] at hk
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_neg, ← hk]

/-- On `W⁄K⸨X⸩`, adding the affine points of `[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]` yields
the affine point of `[F(q₁, q₂) : -1 : w(F(q₁, q₂))]`. -/
private theorem toAffine_formalPointRep_add [DecidableEq K⸨X⸩] (W : WeierstrassCurve K)
    [W.IsElliptic] {q₁ q₂ : K⟦X⟧} (hq₁ : PowerSeries.constantCoeff q₁ = 0)
    (hq₂ : PowerSeries.constantCoeff q₂ = 0) :
    (Projective.Point.toAffine (W⁄K⸨X⸩).toProjective (formalPointRep W q₁) :
        (W⁄K⸨X⸩).toAffine.Point) +
      Projective.Point.toAffine (W⁄K⸨X⸩).toProjective (formalPointRep W q₂) =
    Projective.Point.toAffine (W⁄K⸨X⸩).toProjective
      (formalPointRep W (MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries)) := by
  obtain ⟨u, hu_unit, hu_eq⟩ := exists_dblAddXYZ_formalW_powerSeries_eq_smul W hq₁ hq₂
  have hu' : IsUnit (ofPowerSeries ℤ K u) := hu_unit.map (ofPowerSeries ℤ K)
  have hD : (W⁄K⸨X⸩).toProjective.dblAddXYZ (formalPointRep W q₁) (formalPointRep W q₂) =
      ofPowerSeries ℤ K u •
        formalPointRep W (MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries) := by
    have hcurve : (W.toProjective.map (algebraMap K K⟦X⟧)).map (ofPowerSeries ℤ K) =
        (W⁄K⸨X⸩).toProjective :=
      congrArg WeierstrassCurve.toProjective (map_ofPowerSeries_map_algebraMap W)
    have hmap := Projective.map_dblAddXYZ (W' := W.toProjective.map (algebraMap K K⟦X⟧))
      (ofPowerSeries ℤ K) ![q₁, -1, PowerSeries.subst q₁ W.formalW]
      ![q₂, -1, PowerSeries.subst q₂ W.formalW]
    rw [hcurve] at hmap
    refine hmap.trans ?_
    rw [hu_eq]
    funext k
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, formalPointRep]
  have hD0 : (W⁄K⸨X⸩).toProjective.dblAddXYZ (formalPointRep W q₁) (formalPointRep W q₂) ≠ 0 := by
    intro h0
    have h1 := congrFun (hD.symm.trans h0) 1
    simp [formalPointRep, hu'.ne_zero] at h1
  have hN₁ := nonsingular_formalPointRep W hq₁
  have hN₂ := nonsingular_formalPointRep W hq₂
  rw [← Projective.Point.toAffine_add hN₁ hN₂,
    ← Projective.Point.toAffine_of_equiv (Projective.dblAddXYZ_equiv_add hN₁ hN₂ hD0), hD,
    Projective.Point.toAffine_of_equiv (Projective.smul_equiv _ hu')]

/-- For a nonzero power series `q` with zero constant coefficient, `[q : -1 : w(q)]` represents
the generic point evaluated along Laurent substitution by `q`. -/
private theorem toAffine_formalPointRep_eq_map_genericPoint [DecidableEq K⸨X⸩]
    (W : WeierstrassCurve K) [W.IsElliptic] {q : K⟦X⟧}
    (hq₀ : PowerSeries.constantCoeff q = 0) (hq : q ≠ 0) :
    Projective.Point.toAffine (W⁄K⸨X⸩).toProjective (formalPointRep W q) =
      Affine.Point.map ((LaurentSeries.substAlgHom hq₀ hq).comp W.functionFieldLaurentExpansion)
        (Affine.genericPoint W.toAffine) := by
  have hw0 : (formalPointRep W q) 2 ≠ 0 := by
    simpa [formalPointRep] using
      W.algebraMap_subst_formalW_ne_zero (σ := Unit) (KK := K⸨X⸩) hq₀ hq
  have hN := nonsingular_formalPointRep W hq₀
  rw [Projective.Point.toAffine_of_Z_ne_zero hN hw0, Affine.genericPoint_eq_some,
    Affine.Point.map_some]
  let σ := (LaurentSeries.substAlgHom hq₀ hq).comp W.functionFieldLaurentExpansion
  have hY0 : σ W.toAffine.genericY ≠ 0 :=
    (map_ne_zero_iff σ σ.injective).mpr W.toAffine.genericY_ne_zero
  have hw : σ (-W.toAffine.genericY⁻¹) = ofPowerSeries ℤ K (PowerSeries.subst q (formalW W)) := by
    simp [σ, LaurentSeries.substAlgHom_coe]
  have hz : σ (-W.toAffine.genericX / W.toAffine.genericY) = ofPowerSeries ℤ K q := by
    rw [AlgHom.comp_apply, W.functionFieldLaurentExpansion_neg_genericX_div_genericY,
      LaurentSeries.substAlgHom_coe, PowerSeries.subst_X (.of_constantCoeff_zero' hq₀)]
  have hY : -1 / ofPowerSeries ℤ K (PowerSeries.subst q (formalW W)) = σ W.toAffine.genericY := by
    rw [← hw, map_neg, map_inv₀]
    field_simp [hY0]
  have hX : ofPowerSeries ℤ K q / ofPowerSeries ℤ K (PowerSeries.subst q (formalW W)) =
      σ W.toAffine.genericX := by
    rw [← hz, ← hw, map_div₀, map_neg, map_neg, map_inv₀]
    field_simp [hY0]
  simp only [formalPointRep, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, map_neg, map_one, Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

/-- For every morphism `f : W₁ → W₂`, `[f.formalSeries : -1 : w₂(f.formalSeries)]` represents the
tautological point of `f` expanded at infinity on `W₁`. -/
private theorem toAffine_formalPointRep_formalSeries [DecidableEq K⸨X⸩]
    {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    Projective.Point.toAffine (W₂⁄K⸨X⸩).toProjective (formalPointRep W₂ f.formalSeries) =
      Affine.Point.map W₁.functionFieldLaurentExpansion f.tautologicalPoint := by
  rcases Hom.eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · have hz : (formalPointRep W₂ (0 : K⟦X⟧)) 2 = 0 := by
      simp [formalPointRep,
        PowerSeries.subst_zero_of_constantCoeff_zero W₂.constantCoeff_formalW]
    rw [Hom.formalSeries_zero, Hom.tautologicalPoint_zero, map_zero,
      Projective.Point.toAffine_of_Z_eq_zero hz]
  · rw [Hom.formalSeries_ofIsogeny, Hom.tautologicalPoint_ofIsogeny,
      tautologicalPoint_eq_map_genericPoint,
      toAffine_formalPointRep_eq_map_genericPoint W₂ φ.constantCoeff_formalSeries
        φ.formalSeries_ne_zero, Affine.Point.map_map]
    have hσ : (LaurentSeries.substAlgHom φ.constantCoeff_formalSeries φ.formalSeries_ne_zero).comp
          W₂.functionFieldLaurentExpansion =
        W₁.functionFieldLaurentExpansion.comp φ.fieldPullback :=
      AlgHom.ext fun z ↦ (φ.functionFieldLaurentExpansion_fieldPullback z).symm
    rw [hσ]

namespace Hom

variable {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- **Addition of morphisms induces formal-group addition of their formal series**: the formal
series of `f + g` is the formal-group sum of `f.formalSeries` and `g.formalSeries` in
`formalGroup W₂`. -/
@[simp]
theorem formalSeries_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      MvPowerSeries.subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries := by
  classical
  have hfg : PowerSeries.constantCoeff
      (MvPowerSeries.subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries) =
      0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero
      (PowerSeries.hasSubst_pair f.constantCoeff_formalSeries g.constantCoeff_formalSeries)
      (fun i ↦ by
        fin_cases i
        · exact f.constantCoeff_formalSeries
        · exact g.constantCoeff_formalSeries)
      (formalGroup W₂).zero_constantCoeff
  apply formalPointRep_eq_of_toAffine_eq W₂ (f + g).constantCoeff_formalSeries hfg
  rw [toAffine_formalPointRep_formalSeries, Hom.tautologicalPoint_add, _root_.map_add,
    ← toAffine_formalPointRep_formalSeries, ← toAffine_formalPointRep_formalSeries]
  exact toAffine_formalPointRep_add W₂ f.constantCoeff_formalSeries g.constantCoeff_formalSeries

/-- Subtraction of morphisms induces formal-group subtraction of their formal series. -/
theorem formalSeries_sub (f g : Hom W₁.toAffine W₂.toAffine) :
    (f - g).formalSeries =
      MvPowerSeries.subst
        ![f.formalSeries, PowerSeries.subst g.formalSeries (formalGroup W₂).addInvX]
        (formalGroup W₂).toPowerSeries := by
  rw [sub_eq_add_neg, formalSeries_add, formalSeries_neg]

/-- Natural scalar multiplication of a morphism composes its formal series with the natural
multiplication series of `formalGroup W₂`. -/
@[simp]
theorem formalSeries_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) := by
  induction n with
  | zero =>
    rw [zero_smul, formalSeries_zero, FormalGroup.nsmulSeries_zero, PowerSeries.subst_zero]
  | succ n ih =>
    let x : (formalGroup W₂).Point Unit :=
      ⟨f.formalSeries, isNilpotent_iff_eq_zero.mpr f.constantCoeff_formalSeries⟩
    have hx := (formalGroup W₂).subst_nsmulSeries x (n + 1)
    have hxn := (formalGroup W₂).subst_nsmulSeries x n
    rw [succ_nsmul, FormalGroup.add_apply] at hx
    rw [succ_nsmul, formalSeries_add, ih]
    exact (hx.trans
      (congrArg (fun g ↦ subst ![g, f.formalSeries] (formalGroup W₂).toPowerSeries)
        hxn.symm)).symm

/-- Integer scalar multiplication of a morphism composes its formal series with the integer
multiplication series of `formalGroup W₂`. -/
@[simp]
theorem formalSeries_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [natCast_zsmul, formalSeries_nsmul, FormalGroup.zsmulSeries_natCast]
  · rw [neg_zsmul, formalSeries_neg, natCast_zsmul, formalSeries_nsmul,
      FormalGroup.zsmulSeries_neg, FormalGroup.zsmulSeries_natCast,
      PowerSeries.subst_comp_subst_apply
        (.of_constantCoeff_zero' ((formalGroup W₂).constantCoeff_nsmulSeries k))
        (.of_constantCoeff_zero' f.constantCoeff_formalSeries)]

end Hom

/-- **The formal series of `[n]` is the `n`-multiplication series of the formal group**
(`n : ℤ`). -/
@[simp]
theorem formalSeries_mulByIntIsogeny (W : WeierstrassCurve K) [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← Hom.formalSeries_ofIsogeny, ofIsogeny_mulByIntIsogeny, Hom.formalSeries_zsmul,
    Hom.formalSeries_id, PowerSeries.X_subst]

/-- **The formal series of `[n]` (`n ≠ 0` in `ℤ`) is `(formalGroup W).zsmulSeries n`.** -/
theorem formalSeries_mulByIntIsogenyOfNeZero (W : WeierstrassCurve K) [W.IsElliptic] {n : ℤ}
    (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n :=
  formalSeries_mulByIntIsogeny W _

/-- For a natural number `n` with `(n : ℤ) ≠ 0`, the formal series of `[n]` is
`(formalGroup W).nsmulSeries n`. -/
theorem formalSeries_mulByIntIsogenyOfNeZero_natCast (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : ℤ) ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = (formalGroup W).nsmulSeries n := by
  rw [formalSeries_mulByIntIsogenyOfNeZero, FormalGroup.zsmulSeries_natCast]

end FormalPointAddition

/-! ### Formal-group homomorphisms from isogenies and morphisms -/

section FormalGroupHom

variable {K : Type*} [Field K]

/-- On `W₁⁄K⸨X⸩`, the point action of an isogeny sends the formal point `[q : -1 : w₁(q)]` to
`[φ.formalSeries(q) : -1 : w₂(φ.formalSeries(q))]`. -/
private theorem pointMap_toAffine_formalPointRep {W₁ W₂ : WeierstrassCurve K}
    [W₁.IsElliptic] [W₂.IsElliptic] [DecidableEq K⸨X⸩]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {q : K⟦X⟧}
    (hq₀ : PowerSeries.constantCoeff q = 0) (hq : q ≠ 0) :
    ((Hom.ofIsogeny φ).map (algebraMap K K⸨X⸩)).pointMap
        (Projective.Point.toAffine (W₁⁄K⸨X⸩).toProjective (formalPointRep W₁ q)) =
      Projective.Point.toAffine (W₂⁄K⸨X⸩).toProjective
        (formalPointRep W₂ (PowerSeries.subst q φ.formalSeries)) := by
  classical
  let σ : W₁.toAffine.FunctionField →ₐ[K] K⸨X⸩ :=
    (LaurentSeries.substAlgHom hq₀ hq).comp W₁.functionFieldLaurentExpansion
  have hpm := Hom.pointMap_map_algebraMap_map (Hom.ofIsogeny φ) σ
    (Affine.genericPoint W₁.toAffine)
  rw [toAffine_formalPointRep_eq_map_genericPoint W₁ hq₀ hq]
  refine hpm.trans ?_
  rw [Hom.pointMap_map_algebraMap_genericPoint, Hom.tautologicalPoint_ofIsogeny,
    tautologicalPoint_eq_map_genericPoint, Affine.Point.map_map]
  have hφq₀ : PowerSeries.constantCoeff (PowerSeries.subst q φ.formalSeries) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hq₀ _ φ.constantCoeff_formalSeries
  have hφq : PowerSeries.subst q φ.formalSeries ≠ 0 :=
    (PowerSeries.subst_eq_zero_iff hq₀ hq).not.mpr φ.formalSeries_ne_zero
  rw [toAffine_formalPointRep_eq_map_genericPoint W₂ hφq₀ hφq]
  have hσ : σ.comp φ.fieldPullback =
      (LaurentSeries.substAlgHom hφq₀ hφq).comp W₂.functionFieldLaurentExpansion :=
    AlgHom.ext fun z ↦ by
      simp only [σ, AlgHom.comp_apply, φ.functionFieldLaurentExpansion_fieldPullback]
      exact LaurentSeries.substAlgHom_comp_substAlgHom_apply φ.constantCoeff_formalSeries
        φ.formalSeries_ne_zero hq₀ hq _
  rw [hσ]

variable {W₁ W₂ W₃ : WeierstrassCurve K}

private theorem map_homDefect_formalSeries {L : Type*} [Field L]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (ι : K →+* L) :
    ((formalGroup W₁).homDefect (formalGroup W₂) φ.formalSeries).map ι =
      (formalGroup (W₁.map ι)).homDefect (formalGroup (W₂.map ι)) (φ.map ι).formalSeries := by
  rw [FormalGroup.homDefect_def, FormalGroup.homDefect_def, map_sub, formalSeries_map,
    map_formalGroup, map_formalGroup, FormalGroup.map_toPowerSeries,
    FormalGroup.map_toPowerSeries,
    PowerSeries.map_subst (.of_constantCoeff_zero (formalGroup W₁).zero_constantCoeff),
    MvPowerSeries.map_subst
      (MvPowerSeries.HasSubst.toMvPowerSeries φ.constantCoeff_formalSeries)]
  congr 2
  funext i
  exact PowerSeries.map_toMvPowerSeries ι i φ.formalSeries

variable [W₂.IsElliptic]

private theorem homDefect_formalSeries (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (formalGroup W₁).homDefect (formalGroup W₂) φ.formalSeries = 0 := by
  classical
  have : W₁.IsElliptic := φ.isElliptic
  let ι : K →+* K⸨X⸩ := algebraMap K K⸨X⸩
  let φ' : Isogeny (W₁.map ι).toAffine (W₂.map ι).toAffine := φ.map ι
  set q₀ : K⸨X⸩⟦X⟧ := PowerSeries.X
  set q₁ : K⸨X⸩⟦X⟧ := (HahnSeries.single 1 (1 : K) : K⸨X⸩) • PowerSeries.X
  have hq₀c : PowerSeries.constantCoeff q₀ = 0 := PowerSeries.constantCoeff_X
  have hq₁c : PowerSeries.constantCoeff q₁ = 0 := by simp [q₁, PowerSeries.constantCoeff_X]
  have hq₀ : q₀ ≠ 0 := PowerSeries.X_ne_zero
  have hq₁ : q₁ ≠ 0 := fun h ↦ by
    simpa [q₁, PowerSeries.coeff_X] using
      congrArg (fun g : K⸨X⸩⟦X⟧ ↦ (PowerSeries.coeff 1 g).coeff 1) h
  set F₁ := MvPowerSeries.subst ![q₀, q₁] (formalGroup (W₁.map ι)).toPowerSeries
  have hF₁c : PowerSeries.constantCoeff F₁ = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero (PowerSeries.hasSubst_pair hq₀c hq₁c)
      (fun i ↦ by fin_cases i; exacts [hq₀c, hq₁c]) (formalGroup (W₁.map ι)).zero_constantCoeff
  have hF₁ : F₁ ≠ 0 := fun h0 ↦ by
    dsimp only [F₁, q₀, q₁, ι] at h0
    rw [map_formalGroup, FormalGroup.map_toPowerSeries] at h0
    have h1 := (formalGroup W₁).lin_coeff_X
    rw [LaurentSeries.eq_zero_of_subst_X_single_smul_X h0, map_zero] at h1
    exact zero_ne_one h1
  have hφq₀c : PowerSeries.constantCoeff (PowerSeries.subst q₀ φ'.formalSeries) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hq₀c _ φ'.constantCoeff_formalSeries
  have hφq₁c : PowerSeries.constantCoeff (PowerSeries.subst q₁ φ'.formalSeries) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hq₁c _ φ'.constantCoeff_formalSeries
  apply LaurentSeries.eq_zero_of_subst_X_single_smul_X
  rw [map_homDefect_formalSeries φ ι, FormalGroup.subst_homDefect _ _ φ'.constantCoeff_formalSeries
    (.of_constantCoeff_zero' hq₀c) (.of_constantCoeff_zero' hq₁c), sub_eq_zero]
  apply formalPointRep_eq_of_toAffine_eq (W₂.map ι)
    (PowerSeries.constantCoeff_subst_eq_zero hF₁c _ φ'.constantCoeff_formalSeries)
    (MvPowerSeries.constantCoeff_subst_eq_zero (PowerSeries.hasSubst_pair hφq₀c hφq₁c)
      (fun i ↦ by fin_cases i; exacts [hφq₀c, hφq₁c]) (formalGroup (W₂.map ι)).zero_constantCoeff)
  rw [← pointMap_toAffine_formalPointRep φ' hF₁c hF₁,
    ← toAffine_formalPointRep_add (W₂.map ι) hφq₀c hφq₁c,
    ← pointMap_toAffine_formalPointRep φ' hq₀c hq₀,
    ← pointMap_toAffine_formalPointRep φ' hq₁c hq₁]
  refine (congrArg ((Hom.ofIsogeny φ').map (algebraMap K⸨X⸩ K⸨X⸩⸨X⸩)).pointMap
    (toAffine_formalPointRep_add (W₁.map ι) hq₀c hq₁c).symm).trans ?_
  exact Hom.pointMap_add ((Hom.ofIsogeny φ').map (algebraMap K⸨X⸩ K⸨X⸩⸨X⸩)) _ _

/-- **Every isogeny induces a homomorphism of formal group laws** (Silverman IV.4.2(b)). -/
noncomputable def formalGroupHom (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) :=
  FormalGroupHom.ofHomDefectEqZero φ.constantCoeff_formalSeries φ.homDefect_formalSeries

/-- The underlying power series of `φ.formalGroupHom` is `φ.formalSeries`. -/
@[simp]
theorem formalGroupHom_toPowerSeries (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries :=
  FormalGroupHom.ofHomDefectEqZero_toPowerSeries _ _

omit [W₂.IsElliptic] in
/-- The identity isogeny induces the identity formal-group homomorphism. -/
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Isogeny.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext : 1
  simp

/-- Composition of isogenies induces composition of formal-group homomorphisms. -/
@[simp]
theorem formalGroupHom_comp [W₃.IsElliptic] (ψ : Isogeny W₂.toAffine W₃.toAffine)
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).formalGroupHom = ψ.formalGroupHom.comp φ.formalGroupHom := by
  ext : 1
  simp

namespace Hom

/-- **Every morphism `f : W₁ → W₂` induces a homomorphism of formal group laws**, sending the zero
morphism to the zero series. -/
noncomputable def formalGroupHom (f : Hom W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) :=
  FormalGroupHom.ofHomDefectEqZero f.constantCoeff_formalSeries <| by
    rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
    · rw [formalSeries_zero, FormalGroup.homDefect_zero]
    · rw [formalSeries_ofIsogeny]
      exact φ.homDefect_formalSeries

/-- The underlying power series of `f.formalGroupHom` is `f.formalSeries`. -/
@[simp]
theorem formalGroupHom_toPowerSeries (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalGroupHom.toPowerSeries = f.formalSeries :=
  FormalGroupHom.ofHomDefectEqZero_toPowerSeries _ _

/-- On an isogeny viewed as a morphism, `Hom.formalGroupHom` agrees with
`Isogeny.formalGroupHom`. -/
@[simp]
theorem formalGroupHom_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalGroupHom = φ.formalGroupHom := by
  ext : 1
  simp

omit [W₂.IsElliptic] in
/-- The identity morphism induces the identity formal-group homomorphism. -/
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Hom.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext : 1
  simp

/-- Composition of morphisms induces composition of formal-group homomorphisms. -/
@[simp]
theorem formalGroupHom_comp [W₃.IsElliptic] (g : Hom W₂.toAffine W₃.toAffine)
    (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalGroupHom = g.formalGroupHom.comp f.formalGroupHom := by
  ext : 1
  simp

end Hom

end FormalGroupHom

end TauCeti.Isogeny

end
