/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
public import TauCeti.RingTheory.FormalGroup.Hom.Basic
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Order
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.FormalPoint
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Formal power series of morphisms and formal-group homomorphisms

Let `W₁` and `W₂` be elliptic curves over a field `K`. Expanding the pulled-back parameter
`-x₂ / y₂` at the point at infinity in `-x₁ / y₁` attaches a formal power series
`φ.formalSeries : K⟦X⟧` to every isogeny `φ : W₁ → W₂`; extending by `0` on the zero morphism gives
`Hom.formalSeries : Hom W₁ W₂ → K⟦X⟧`. This file proves the two compatibility laws between this
local expansion and the formal group laws `formalGroup W₁` and `formalGroup W₂` (Silverman IV.4):

1. **Additivity in the morphism (`Hom.formalPointAddHom`, `Hom.formalSeries_add`).** Sending a
   morphism `f : Hom W₁ W₂` to `f.formalSeries` is an injective group homomorphism into the group
   `(formalGroup W₂).Point Unit` of power-series points of `formalGroup W₂`. Consequently, the
   formal series of `f + g` is `(formalGroup W₂)(f.formalSeries, g.formalSeries)`, the formal series
   of `-f` is `(formalGroup W₂).addInvX(f.formalSeries)`, and the formal series of the
   multiplication-by-`n` isogeny `[n]` on `W` is `(formalGroup W).zsmulSeries n` (in particular
   `(formalGroup W).nsmulSeries n` for natural `n ≠ 0`).
2. **The formal-group homomorphism of an isogeny (`Isogeny.formalGroupHom`).** Every isogeny
   `φ : W₁ → W₂` satisfies `φ.formalSeries((formalGroup W₁)(X, Y)) =
   (formalGroup W₂)(φ.formalSeries(X), φ.formalSeries(Y))`, packaged as a bundled
   `FormalGroupHom (formalGroup W₁) (formalGroup W₂)` functorial in `φ`. When `φ` is separable its
   linear coefficient is a unit (`Isogeny.isUnit_coeff_one_formalSeries_iff_isSeparable`), yielding
   a `FormalGroupIso` (`Isogeny.formalGroupIso`).

Both statements are read off a single formal-point map `mvPowerSeriesPointHom`: over any fraction
field `KK` of `MvPowerSeries σ K`, the homogeneous triple `[q : -1 : w(q)]` sends `(formalGroup W)`
points `q` injectively and additively into `(W⁄KK).toAffine.Point`, additivity holding without case
distinctions by specializing `WeierstrassCurve.dblAddXYZ_formalW_eq_smul`. Over
`FractionRing (MvPowerSeries Unit K)` (`σ = Unit`) this identifies the Laurent expansion of
`f.tautologicalPoint` with the formal point `f.formalSeries`, proving (1). Over
`FractionRing (MvPowerSeries (Fin 2) K)` (`σ = Fin 2`), evaluating `Hom.pointMap` on the two formal
coordinate points `X 0`, `X 1` and their sum `(formalGroup W₁)(X 0, X 1)` via `Hom.pointMap_add` and
`Hom.pointMap_map_algebraMap_genericPoint` proves (2).

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries`: the formal power series of a morphism in `Hom W₁ W₂`, `0` on
  the zero morphism and `Isogeny.formalSeries` on an isogeny.
* `TauCeti.Isogeny.Hom.formalPointAddHom`: `Hom W₁ W₂ →+ (formalGroup W₂).Point Unit`.
* `TauCeti.Isogeny.formalGroupHom`: the `FormalGroupHom (formalGroup W₁) (formalGroup W₂)` induced
  by an isogeny `φ : W₁ → W₂`.
* `TauCeti.Isogeny.formalGroupIso`: the `FormalGroupIso (formalGroup W₁) (formalGroup W₂)` induced
  by a separable isogeny `φ : W₁ → W₂`.

## Main results

* `TauCeti.Isogeny.Hom.formalSeries_add`, `TauCeti.Isogeny.Hom.formalSeries_neg`,
  `TauCeti.Isogeny.Hom.formalSeries_nsmul`, `TauCeti.Isogeny.Hom.formalSeries_zsmul`: formal-group
  addition, inversion and scalar multiplication of formal series of morphisms.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny` and
  `TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero_natCast`: the formal series of `[n]` is
  `(formalGroup W).zsmulSeries n` (and `(formalGroup W).nsmulSeries n` for `n : ℕ`).
* `TauCeti.Isogeny.formalGroupHom_id` and `TauCeti.Isogeny.formalGroupHom_comp`: functoriality of
  `Isogeny.formalGroupHom`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and IV.4.
-/

public section

open MvPowerSeries WeierstrassCurve WeierstrassCurve.Affine
open scoped LaurentSeries PowerSeries nonZeroDivisors

namespace TauCeti.Isogeny

/-! ### Formal power series points in fraction fields of power series rings -/

section FormalPoints

variable {K : Type*} [Field K]

private theorem constantCoeff_point_eq_zero (W : WeierstrassCurve K) {σ : Type*}
    (q : (formalGroup W).Point σ) : constantCoeff q.val = 0 :=
  q.prop.eq_zero

private theorem baseChange_toProjective_eq_map (W : WeierstrassCurve K) (σ : Type*) (KK : Type*)
    [Field KK] [Algebra K KK] [Algebra (MvPowerSeries σ K) KK]
    [IsScalarTower K (MvPowerSeries σ K) KK] :
    (W.baseChange KK).toProjective =
      (W.toProjective.map (algebraMap K (MvPowerSeries σ K))).map
        (algebraMap (MvPowerSeries σ K) KK) := by
  ext <;> exact IsScalarTower.algebraMap_apply K (MvPowerSeries σ K) KK _

private theorem nonsingular_formalPointVec (W : WeierstrassCurve K) [W.IsElliptic] (σ : Type*)
    (KK : Type*) [Field KK] [Algebra K KK] [Algebra (MvPowerSeries σ K) KK]
    [IsScalarTower K (MvPowerSeries σ K) KK] (q : (formalGroup W).Point σ) :
    (W.baseChange KK).toProjective.Nonsingular
      (algebraMap (MvPowerSeries σ K) KK ∘ ![q.val, -1, PowerSeries.subst q.val W.formalW]) := by
  have hΔ : (W.baseChange KK).toProjective.Δ ≠ 0 := (W.baseChange KK).isUnit_Δ.ne_zero
  refine (Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero hΔ
    fun h ↦ by simpa using congrFun h 1).mp ?_
  rw [baseChange_toProjective_eq_map W σ KK]
  exact ((W.toProjective.equation_neg_one_iff_wEquation q.val _).mpr
    (W.subst_formalW_wEquation q.prop)).map _

section FractionField

variable (W : WeierstrassCurve K) [W.IsElliptic] (σ : Type*) (KK : Type*) [Field KK]
  [DecidableEq KK] [Algebra K KK] [Algebra (MvPowerSeries σ K) KK]
  [IsScalarTower K (MvPowerSeries σ K) KK]

/-- Sending a formal-group point `q` over `MvPowerSeries σ K` to the affine point with homogeneous
coordinates `[q : -1 : w(q)]` in `(W.baseChange KK).toAffine.Point` is an additive homomorphism. -/
private noncomputable def mvPowerSeriesPointHom :
    (formalGroup W).Point σ →+ (W.baseChange KK).toAffine.Point where
  toFun q := Projective.Point.toAffine (W.baseChange KK).toProjective
    (algebraMap (MvPowerSeries σ K) KK ∘ ![q.val, -1, PowerSeries.subst q.val W.formalW])
  map_zero' := by
    refine Projective.Point.toAffine_of_Z_eq_zero ?_
    simp [PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalW]
  map_add' q₁ q₂ := by
    -- Additivity holds identically via `WeierstrassCurve.dblAddXYZ_formalW_eq_smul`.
    set ρ := algebraMap (MvPowerSeries σ K) KK
    have hq₁ := constantCoeff_point_eq_zero W q₁
    have hq₂ := constantCoeff_point_eq_zero W q₂
    have hpair : MvPowerSeries.HasSubst (pairSubstitution q₁.val q₂.val) :=
      hasSubst_pair hq₁ hq₂
    set s : MvPowerSeries (Unit ⊕ Unit) K →ₐ[K] MvPowerSeries σ K :=
      MvPowerSeries.substAlgHom hpair
    have hs_curve :
        (W.toProjective.map (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K))).map
            (s : MvPowerSeries (Unit ⊕ Unit) K →+* MvPowerSeries σ K) =
          W.toProjective.map (algebraMap K (MvPowerSeries σ K)) := by
      ext : 1 <;> exact s.commutes _
    have hs_vec (z : MvPowerSeries (Unit ⊕ Unit) K) (hz : constantCoeff z = 0) :
        (s : MvPowerSeries (Unit ⊕ Unit) K →+* MvPowerSeries σ K) ∘
            ![z, -1, PowerSeries.subst z W.formalW] =
          ![s z, -1, PowerSeries.subst (s z) W.formalW] := by
      funext k
      fin_cases k
      · rfl
      · simp
      · simp only [Function.comp_apply, AlgHom.coe_toRingHom, s, coe_substAlgHom]
        exact subst_powerSeriesSubst hpair (.of_constantCoeff_zero hz) W.formalW
    have hs₁ : s (X (Sum.inl ())) = q₁.val := by
      simp [s, subst_X hpair, pairSubstitution]
    have hs₂ : s (X (Sum.inr ())) = q₂.val := by
      simp [s, subst_X hpair, pairSubstitution]
    have hsF : s (formalAdd W) = (q₁ + q₂).val := by
      have hfin : MvPowerSeries.HasSubst ![q₁.val, q₂.val] :=
        hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i; exacts [hq₁, hq₂]
      have hcomp : (![q₁.val, q₂.val] : Fin 2 → MvPowerSeries σ K) ∘ unitSumUnitEquivFinTwo =
          pairSubstitution q₁.val q₂.val := by
        funext i
        rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [pairSubstitution]
      rw [FormalGroup.add_apply, formalGroup_toPowerSeries,
        MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _ hfin, hcomp, ← coe_substAlgHom hpair]
    have hv₁ := hs_vec (X (Sum.inl ())) (constantCoeff_X _)
    have hv₂ := hs_vec (X (Sum.inr ())) (constantCoeff_X _)
    have hvF := hs_vec (formalAdd W) (constantCoeff_formalAdd W)
    rw [hs₁] at hv₁
    rw [hs₂] at hv₂
    rw [hsF] at hvF
    -- Push `dblAddXYZ_formalW_eq_smul` and `isUnit_dblAddY_formalW` along `s` and then `ρ`.
    have keyS := congrArg (fun v ↦ (s : MvPowerSeries (Unit ⊕ Unit) K →+* MvPowerSeries σ K) ∘ v)
      W.dblAddXYZ_formalW_eq_smul
    rw [← Projective.map_dblAddXYZ, hs_curve, hv₁, hv₂] at keyS
    have hY_eq :
        (s : MvPowerSeries (Unit ⊕ Unit) K →+* MvPowerSeries σ K)
          ((W.toProjective.map (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K))).dblAddY
            ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
            ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW]) =
          (W.toProjective.map (algebraMap K (MvPowerSeries σ K))).dblAddY
            ![q₁.val, -1, PowerSeries.subst q₁.val W.formalW]
            ![q₂.val, -1, PowerSeries.subst q₂.val W.formalW] := by
      rw [← Projective.map_dblAddY, hs_curve, hv₁, hv₂]
    have hYS : IsUnit ((W.toProjective.map (algebraMap K (MvPowerSeries σ K))).dblAddY
        ![q₁.val, -1, PowerSeries.subst q₁.val W.formalW]
        ![q₂.val, -1, PowerSeries.subst q₂.val W.formalW]) := by
      rw [← hY_eq]
      exact W.isUnit_dblAddY_formalW.map (s : MvPowerSeries (Unit ⊕ Unit) K →+* MvPowerSeries σ K)
    set P₁ := ρ ∘ ![q₁.val, -1, PowerSeries.subst q₁.val W.formalW]
    set P₂ := ρ ∘ ![q₂.val, -1, PowerSeries.subst q₂.val W.formalW]
    set P₁₂ := ρ ∘ ![(q₁ + q₂).val, -1, PowerSeries.subst (q₁ + q₂).val W.formalW]
    set u : KK := ρ (-((W.toProjective.map (algebraMap K (MvPowerSeries σ K))).dblAddY
        ![q₁.val, -1, PowerSeries.subst q₁.val W.formalW]
        ![q₂.val, -1, PowerSeries.subst q₂.val W.formalW]))
    have hu : IsUnit u := (hYS.neg).map ρ
    have keyKK : (W.baseChange KK).toProjective.dblAddXYZ P₁ P₂ = u • P₁₂ := by
      rw [baseChange_toProjective_eq_map W σ KK, Projective.map_dblAddXYZ, keyS]
      funext k
      have hk := congrFun hvF k
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_neg, u, P₁₂] at hk ⊢
      rw [hY_eq, hk]
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
    exact Projective.Point.toAffine_of_equiv ⟨hu.unit, by simp [Units.smul_def]⟩

private theorem mvPowerSeriesPointHom_apply (q : (formalGroup W).Point σ) :
    mvPowerSeriesPointHom W σ KK q = Projective.Point.toAffine (W.baseChange KK).toProjective
      (algebraMap (MvPowerSeries σ K) KK ∘ ![q.val, -1, PowerSeries.subst q.val W.formalW]) :=
  rfl

variable [IsFractionRing (MvPowerSeries σ K) KK]

/-- Over a fraction field `KK` of `MvPowerSeries σ K`, `mvPowerSeriesPointHom` is injective. -/
private theorem mvPowerSeriesPointHom_injective :
    Function.Injective (mvPowerSeriesPointHom W σ KK) := by
  -- At any nonzero `q` the `Z`-coordinate `w(q)` is nonzero in `KK`, so `toAffine` is nonzero.
  refine (injective_iff_map_eq_zero _).mpr fun q hq0 ↦ ?_
  by_contra hq
  have hval : q.val ≠ 0 := fun h ↦ hq (Subtype.ext h)
  have hz : (algebraMap (MvPowerSeries σ K) KK ∘
      ![q.val, -1, PowerSeries.subst q.val W.formalW]) 2 ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero (constantCoeff_point_eq_zero W q) hval
  rw [mvPowerSeriesPointHom_apply,
    Projective.Point.toAffine_of_Z_ne_zero (nonsingular_formalPointVec W σ KK q) hz] at hq0
  exact Affine.Point.some_ne_zero _ hq0

/-- Any `K`-algebra homomorphism `A : K(W) →ₐ[K] KK` sending `-x / y` to `q` and `-1 / y` to `w(q)`
at a nonzero formal point `q` carries `W.toAffine.genericPoint` to `mvPowerSeriesPointHom q`. -/
private theorem map_genericPoint_eq_mvPowerSeriesPointHom
    (A : W.toAffine.FunctionField →ₐ[K] KK) {q : (formalGroup W).Point σ} (hq0 : q.val ≠ 0)
    (hparam : A (-W.toAffine.genericX / W.toAffine.genericY) =
      algebraMap (MvPowerSeries σ K) KK q.val)
    (hw : A (-W.toAffine.genericY⁻¹) =
      algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q.val W.formalW)) :
    Point.map A W.toAffine.genericPoint = mvPowerSeriesPointHom W σ KK q := by
  let ρ := algebraMap (MvPowerSeries σ K) KK
  let w := ρ (PowerSeries.subst q.val W.formalW)
  have hw0 : w ≠ 0 := W.algebraMap_subst_formalW_ne_zero (constantCoeff_point_eq_zero W q) hq0
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

end FractionField

end FormalPoints

/-! ### Formal series of morphisms in `Hom` -/

namespace Hom

section Defs

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

open scoped Classical in
/-- **The formal power series of a morphism `f : Hom W₁.toAffine W₂.toAffine`**: `0` for the zero
morphism, and `(toIsogeny hf).formalSeries` when `f ≠ 0`. -/
noncomputable def formalSeries (f : Hom W₁.toAffine W₂.toAffine) : K⟦X⟧ :=
  if hf : f = 0 then 0 else (toIsogeny hf).formalSeries

@[simp]
theorem formalSeries_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalSeries = 0 :=
  dite_eq_left_of_eq_true (eq_true rfl)

@[simp]
theorem formalSeries_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalSeries = φ.formalSeries := by
  rw [formalSeries, dite_eq_right_of_eq_false (eq_false (ofIsogeny_ne_zero φ)),
    toIsogeny_ofIsogeny]

@[simp]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

@[simp]
theorem formalSeries_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp [φ.formalSeries_ne_zero, ofIsogeny_ne_zero]

@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (Hom.id W.toAffine).formalSeries = PowerSeries.X := by
  rw [Hom.id_def, formalSeries_ofIsogeny, Isogeny.formalSeries_id]

@[simp]
theorem formalSeries_comp (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalSeries = PowerSeries.subst f.formalSeries g.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp [PowerSeries.subst_zero]
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp [PowerSeries.subst_zero_of_constantCoeff_zero ψ.constantCoeff_formalSeries]
  · rw [ofIsogeny_comp_ofIsogeny, formalSeries_ofIsogeny, formalSeries_ofIsogeny,
      formalSeries_ofIsogeny, Isogeny.formalSeries_comp]

end Defs

section Additivity

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- The formal point `(f.formalSeries, _)` in `(formalGroup W₂).Point Unit`. -/
private noncomputable def formalPointFun (f : Hom W₁.toAffine W₂.toAffine) :
    (formalGroup W₂).Point Unit :=
  ⟨f.formalSeries, PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_formalSeries⟩

/-- Laurent expansion of `K(W₁)` into `FractionRing (MvPowerSeries Unit K)`. -/
private noncomputable def unitLaurentEmb (W₁ : WeierstrassCurve K) :
    W₁.toAffine.FunctionField →ₐ[K] FractionRing (MvPowerSeries Unit K) :=
  (TauCeti.LaurentSeries.mvSubstAlgHom (FractionRing (MvPowerSeries Unit K)) (constantCoeff_X ())
    (nonZeroDivisors.ne_zero X_mem_nonZeroDivisors)).comp W₁.functionFieldLaurentExpansion

private theorem map_unitLaurentEmb_tautologicalPoint
    [DecidableEq (FractionRing (MvPowerSeries Unit K))] (f : Hom W₁.toAffine W₂.toAffine) :
    Point.map (unitLaurentEmb W₁) f.tautologicalPoint =
      mvPowerSeriesPointHom W₂ Unit (FractionRing (MvPowerSeries Unit K)) (formalPointFun f) := by
  have hX_eq : (X () : MvPowerSeries Unit K) = PowerSeries.X := rfl
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · have hz : formalPointFun (0 : Hom W₁.toAffine W₂.toAffine) = 0 := Subtype.ext formalSeries_zero
    rw [tautologicalPoint_zero, _root_.map_zero, hz, _root_.map_zero]
  · rw [tautologicalPoint_ofIsogeny, tautologicalPoint_eq_map_genericPoint, Point.map_map]
    refine map_genericPoint_eq_mvPowerSeriesPointHom W₂ Unit (FractionRing (MvPowerSeries Unit K))
      ((unitLaurentEmb W₁).comp φ.fieldPullback)
      (by simpa [formalPointFun] using φ.formalSeries_ne_zero) ?_ ?_
    · simp only [unitLaurentEmb, AlgHom.comp_apply, formalPointFun, formalSeries_ofIsogeny,
        ← φ.coe_formalSeries, TauCeti.LaurentSeries.mvSubstAlgHom_coe, hX_eq, PowerSeries.X_subst]
    · simp only [unitLaurentEmb, AlgHom.comp_apply, formalPointFun, formalSeries_ofIsogeny,
        ← φ.coe_subst_formalW_formalSeries, TauCeti.LaurentSeries.mvSubstAlgHom_coe, hX_eq,
        PowerSeries.X_subst]

/-- **Sending a morphism `f : Hom W₁ W₂` to its formal power series is an additive group
homomorphism** into the power-series points `(formalGroup W₂).Point Unit`. -/
noncomputable def formalPointAddHom :
    Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit where
  toFun := formalPointFun
  map_zero' := Subtype.ext formalSeries_zero
  map_add' f g := by
    classical
    apply mvPowerSeriesPointHom_injective W₂ Unit (FractionRing (MvPowerSeries Unit K))
    rw [_root_.map_add, ← map_unitLaurentEmb_tautologicalPoint,
      ← map_unitLaurentEmb_tautologicalPoint, ← map_unitLaurentEmb_tautologicalPoint,
      tautologicalPoint_add, _root_.map_add]

@[simp]
theorem formalPointAddHom_val (f : Hom W₁.toAffine W₂.toAffine) :
    (formalPointAddHom f).val = f.formalSeries :=
  (rfl)

/-- **A morphism into an elliptic curve is uniquely determined by its formal power series.** -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := fun f g h ↦ by
  have hself : formalPointAddHom f = formalPointAddHom g := Subtype.ext h
  have h0 : (f - g).formalSeries = 0 := by
    have hsub := _root_.map_sub formalPointAddHom f g
    rw [hself, sub_self] at hsub
    exact congrArg Subtype.val hsub
  exact sub_eq_zero.mp (formalSeries_eq_zero_iff.mp h0)

/-- **The formal series of a sum of morphisms is the formal-group sum of their formal series**
(Silverman IV.4.2(a)). -/
theorem formalSeries_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      MvPowerSeries.subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries := by
  simpa only [formalPointAddHom_val, FormalGroup.add_apply] using
    congrArg Subtype.val (_root_.map_add formalPointAddHom f g)

/-- **The formal series of `-f` is the formal-group inverse evaluated at `f.formalSeries`.** -/
theorem formalSeries_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries (formalGroup W₂).addInvX := by
  simpa only [formalPointAddHom_val, FormalGroup.neg_apply] using
    congrArg Subtype.val (_root_.map_neg formalPointAddHom f)

/-- **The formal series of `n • f` (`n : ℕ`) is `[n]_{formalGroup W₂}(f.formalSeries)`.** -/
theorem formalSeries_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) := by
  have h := congrArg Subtype.val (_root_.map_nsmul formalPointAddHom n f)
  rwa [formalPointAddHom_val, ← (formalGroup W₂).subst_nsmulSeries (formalPointAddHom f) n,
    formalPointAddHom_val] at h

/-- **The formal series of `n • f` (`n : ℤ`) is `[n]_{formalGroup W₂}(f.formalSeries)`.** -/
theorem formalSeries_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) := by
  have h := congrArg Subtype.val (_root_.map_zsmul formalPointAddHom n f)
  rwa [formalPointAddHom_val, ← (formalGroup W₂).subst_zsmulSeries (formalPointAddHom f) n,
    formalPointAddHom_val] at h

end Additivity

end Hom

section MulByInt

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The formal series of the negation isogeny `[-1]` is the formal-group inverse.** -/
@[simp]
theorem formalSeries_negIsogeny :
    (negIsogeny W.toAffine).formalSeries = (formalGroup W).addInvX := by
  have h : Hom.ofIsogeny (negIsogeny W.toAffine) = -Hom.id W.toAffine := by
    rw [Hom.id_def, Hom.neg_ofIsogeny, comp_id]
  have hs := congrArg Hom.formalSeries h
  rwa [Hom.formalSeries_ofIsogeny, Hom.formalSeries_neg, Hom.formalSeries_id,
    PowerSeries.X_subst] at hs

/-- **The formal series of the multiplication-by-`n` isogeny `[n]` is the formal-group
multiplication series `(formalGroup W).zsmulSeries n`.** -/
@[simp]
theorem formalSeries_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  have hs := congrArg Hom.formalSeries (ofIsogeny_mulByIntIsogeny W.toAffine hn)
  rwa [Hom.formalSeries_ofIsogeny, Hom.formalSeries_zsmul, Hom.formalSeries_id,
    PowerSeries.X_subst] at hs

/-- **The formal series of `[n]` (`n ≠ 0`) is `(formalGroup W).zsmulSeries n`.** -/
-- Not `@[simp]`: `mulByIntIsogenyOfNeZero` is an `abbrev` for `mulByIntIsogeny`.
theorem formalSeries_mulByIntIsogenyOfNeZero {n : ℤ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n :=
  formalSeries_mulByIntIsogeny W _

/-- **For a nonzero natural number `n`, the formal series of `[n]` is
`(formalGroup W).nsmulSeries n`.** -/
theorem formalSeries_mulByIntIsogenyOfNeZero_natCast {n : ℕ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine (n := n) (mod_cast hn)).formalSeries =
      (formalGroup W).nsmulSeries n := by
  rw [formalSeries_mulByIntIsogenyOfNeZero, FormalGroup.zsmulSeries_natCast]

end MulByInt

/-! ### The formal-group homomorphism of an isogeny -/

section FormalGroupHom

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

/-- For a nonzero formal point `q` of `formalGroup W₁`, evaluating `((ofIsogeny φ).map _).pointMap`
at `mvPowerSeriesPointHom W₁ q` produces `mvPowerSeriesPointHom W₂ (φ.formalSeries(q))`. -/
private theorem pointMap_ofIsogeny_mvPowerSeriesPointHom [W₁.IsElliptic] [W₂.IsElliptic]
    {σ : Type*} (KK : Type*) [Field KK] [DecidableEq KK] [Algebra K KK]
    [Algebra (MvPowerSeries σ K) KK] [IsScalarTower K (MvPowerSeries σ K) KK]
    [IsFractionRing (MvPowerSeries σ K) KK] (φ : Isogeny W₁.toAffine W₂.toAffine)
    {q : (formalGroup W₁).Point σ} (hq0 : q.val ≠ 0) :
    ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap (mvPowerSeriesPointHom W₁ σ KK q) =
      mvPowerSeriesPointHom W₂ σ KK
        ⟨PowerSeries.subst q.val φ.formalSeries,
          .of_constantCoeff_zero
            (PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_point_eq_zero W₁ q) _
              φ.constantCoeff_formalSeries)⟩ := by
  have hq : constantCoeff q.val = 0 := constantCoeff_point_eq_zero W₁ q
  let ev : W₁.toAffine.FunctionField →ₐ[K] KK :=
    (TauCeti.LaurentSeries.mvSubstAlgHom KK hq hq0).comp W₁.functionFieldLaurentExpansion
  have hsrc : Point.map ev W₁.toAffine.genericPoint = mvPowerSeriesPointHom W₁ σ KK q := by
    refine map_genericPoint_eq_mvPowerSeriesPointHom W₁ σ KK ev hq0 ?_ ?_
    · simp only [ev, AlgHom.comp_apply, W₁.functionFieldLaurentExpansion_neg_genericX_div_genericY,
        TauCeti.LaurentSeries.mvSubstAlgHom_coe, PowerSeries.subst_X q.prop]
    · simp only [ev, AlgHom.comp_apply, W₁.functionFieldLaurentExpansion_neg_inv_genericY,
        TauCeti.LaurentSeries.mvSubstAlgHom_coe]
  have hφq0 : PowerSeries.subst q.val φ.formalSeries ≠ 0 :=
    (PowerSeries.mvPowerSeries_subst_eq_zero_iff hq hq0).not.mpr φ.formalSeries_ne_zero
  have htgt : Point.map ev (Hom.ofIsogeny φ).tautologicalPoint =
      mvPowerSeriesPointHom W₂ σ KK
        ⟨PowerSeries.subst q.val φ.formalSeries,
          .of_constantCoeff_zero
            (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)⟩ := by
    rw [Hom.tautologicalPoint_ofIsogeny, tautologicalPoint_eq_map_genericPoint, Point.map_map]
    refine map_genericPoint_eq_mvPowerSeriesPointHom W₂ σ KK (ev.comp φ.fieldPullback) hφq0 ?_ ?_
    · simp only [ev, AlgHom.comp_apply, ← φ.coe_formalSeries,
        TauCeti.LaurentSeries.mvSubstAlgHom_coe]
    · simp only [ev, AlgHom.comp_apply, ← φ.coe_subst_formalW_formalSeries,
        TauCeti.LaurentSeries.mvSubstAlgHom_coe,
        PowerSeries.subst_comp_subst_apply
          (.of_constantCoeff_zero' φ.constantCoeff_formalSeries) q.prop]
  rw [← hsrc, Hom.pointMap_map_algebraMap_map_genericPoint, htgt]

/-- **The formal-group homomorphism attached to an isogeny** `φ : W₁ → W₂` to an elliptic curve:
`φ.formalSeries` satisfies `φ.formalSeries((formalGroup W₁)(X, Y)) =
(formalGroup W₂)(φ.formalSeries(X), φ.formalSeries(Y))` (Silverman IV.4.2). -/
noncomputable def formalGroupHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := φ.formalSeries
  zero_constantCoeff := φ.constantCoeff_formalSeries
  hom := by
    classical
    have : W₁.IsElliptic := φ.isElliptic
    let KK := FractionRing (MvPowerSeries (Fin 2) K)
    let q₀ : (formalGroup W₁).Point (Fin 2) := ⟨X 0, PowerSeries.HasSubst.X 0⟩
    let q₁ : (formalGroup W₁).Point (Fin 2) := ⟨X 1, PowerSeries.HasSubst.X 1⟩
    have hq₀ : q₀.val ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
    have hq₁ : q₁.val ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
    have hsum_val : (q₀ + q₁).val = (formalGroup W₁).toPowerSeries := by
      rw [FormalGroup.add_apply]
      have hX : (![q₀.val, q₁.val] : Fin 2 → MvPowerSeries (Fin 2) K) = X := by
        funext i
        fin_cases i <;> rfl
      rw [hX, subst_self, id_eq]
    have hsum0 : (q₀ + q₁).val ≠ 0 := by
      rw [hsum_val]
      intro h0
      have hc := congrArg (coeff (Finsupp.single 0 1)) h0
      rw [(formalGroup W₁).lin_coeff_X, map_zero] at hc
      exact one_ne_zero hc
    -- Apply `Hom.pointMap_add` on `(W₁.baseChange KK).toAffine.Point` to `q₀` and `q₁`.
    let r₀ : (formalGroup W₂).Point (Fin 2) :=
      ⟨PowerSeries.subst q₀.val φ.formalSeries,
        .of_constantCoeff_zero (PowerSeries.constantCoeff_subst_eq_zero
          (constantCoeff_point_eq_zero W₁ q₀) _ φ.constantCoeff_formalSeries)⟩
    let r₁ : (formalGroup W₂).Point (Fin 2) :=
      ⟨PowerSeries.subst q₁.val φ.formalSeries,
        .of_constantCoeff_zero (PowerSeries.constantCoeff_subst_eq_zero
          (constantCoeff_point_eq_zero W₁ q₁) _ φ.constantCoeff_formalSeries)⟩
    have h₁ : mvPowerSeriesPointHom W₂ (Fin 2) KK
        ⟨PowerSeries.subst (q₀ + q₁).val φ.formalSeries,
          .of_constantCoeff_zero (PowerSeries.constantCoeff_subst_eq_zero
            (constantCoeff_point_eq_zero W₁ (q₀ + q₁)) _ φ.constantCoeff_formalSeries)⟩ =
        mvPowerSeriesPointHom W₂ (Fin 2) KK (r₀ + r₁) := by
      refine (pointMap_ofIsogeny_mvPowerSeriesPointHom KK φ hsum0).symm.trans ?_
      refine (congrArg ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap
        ((mvPowerSeriesPointHom W₁ (Fin 2) KK).map_add q₀ q₁)).trans ?_
      refine (Hom.pointMap_add ((Hom.ofIsogeny φ).map (algebraMap K KK)) _ _).trans ?_
      refine (congrArg₂ (· + ·) (pointMap_ofIsogeny_mvPowerSeriesPointHom KK φ hq₀)
        (pointMap_ofIsogeny_mvPowerSeriesPointHom KK φ hq₁)).trans ?_
      exact ((mvPowerSeriesPointHom W₂ (Fin 2) KK).map_add r₀ r₁).symm
    have heq : PowerSeries.subst (q₀ + q₁).val φ.formalSeries = (r₀ + r₁).val :=
      congrArg Subtype.val (mvPowerSeriesPointHom_injective W₂ (Fin 2) KK h₁)
    rw [hsum_val, FormalGroup.add_apply] at heq
    rw [heq]
    congr 1
    funext i
    fin_cases i <;> simp [r₀, r₁, q₀, q₁, PowerSeries.toMvPowerSeries_eq_subst]

@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries :=
  (rfl)

@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Isogeny.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext : 1
  simp

@[simp]
theorem formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (ψ : Isogeny W₂.toAffine W₃.toAffine) (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).formalGroupHom = ψ.formalGroupHom.comp φ.formalGroupHom := by
  ext : 1
  simp

/-- **A separable isogeny to an elliptic curve induces an isomorphism of formal group laws.** -/
noncomputable def formalGroupIso [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    FormalGroupIso (formalGroup W₁) (formalGroup W₂) :=
  φ.formalGroupHom.toIso (φ.isUnit_coeff_one_formalSeries_iff_isSeparable.mpr inferInstance)

@[simp]
theorem formalGroupIso_toHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalGroupIso.toHom = φ.formalGroupHom :=
  FormalGroupHom.toIso_toHom _ _

end FormalGroupHom

end TauCeti.Isogeny

end
