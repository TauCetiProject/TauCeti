/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.MvPowerSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Neg
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Order
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
public import TauCeti.RingTheory.FormalGroup.Hom.Basic
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Formal power series of morphisms and formal-group homomorphisms

Let `W₁` and `W₂` be elliptic curves over a field `K`. Expanding the pulled-back parameter
`-x₂ / y₂` at the point at infinity in `-x₁ / y₁` attaches a formal power series
`φ.formalSeries : K⟦X⟧` to every isogeny `φ : W₁ → W₂`; extending by `0` on the zero morphism gives
`Hom.formalSeries : Hom W₁ W₂ → K⟦X⟧`. This file proves the two compatibility laws between this
local expansion and the formal group laws `formalGroup W₁` and `formalGroup W₂` (Silverman IV.4):

1. **Additivity in the morphism (`Hom.formalPointAddHom`, `Hom.formalSeries_add`).** Sending a
   morphism `f : Hom W₁ W₂` to `f.formalSeries` is an injective group homomorphism into the group
   `(formalGroup W₂).Point Unit` of power-series points of `formalGroup W₂`
   (`Hom.formalPointAddHom_injective`). Consequently, the formal series of `f + g` is
   `(formalGroup W₂)(f.formalSeries, g.formalSeries)`, the formal series of `-f` is
   `(formalGroup W₂).addInvX(f.formalSeries)`, and the formal series of the multiplication-by-`n`
   isogeny `[n]` on `W` is `(formalGroup W).zsmulSeries n` (in particular
   `(formalGroup W).nsmulSeries n` for natural `n ≠ 0`).
2. **The formal-group homomorphism of an isogeny (`Isogeny.formalGroupHom`).** Every isogeny
   `φ : W₁ → W₂` satisfies `φ.formalSeries((formalGroup W₁)(X, Y)) =
   (formalGroup W₂)(φ.formalSeries(X), φ.formalSeries(Y))`, packaged as a bundled
   `FormalGroupHom (formalGroup W₁) (formalGroup W₂)` functorial in `φ` and compatible with
   `WeierstrassCurve.mvPowerSeriesPointHom` (`Isogeny.pointMap_ofIsogeny_mvPowerSeriesPointHom`).
   When `φ` is separable its linear coefficient is a unit
   (`Isogeny.isUnit_coeff_one_formalSeries_iff_isSeparable`), yielding a `FormalGroupIso`
   (`Isogeny.formalGroupIso`).

Both statements are read off `WeierstrassCurve.mvPowerSeriesPointHom`: over
`FractionRing (MvPowerSeries Unit K)` (`σ = Unit`), evaluating `f.tautologicalPoint` along the
Laurent expansion of `W₁` identifies it with the formal point `f.formalSeries`, proving (1). Over
`FractionRing (MvPowerSeries (Fin 2) K)` (`σ = Fin 2`), evaluating `Hom.pointMap` on the two formal
coordinate points `X 0`, `X 1` and their sum `(formalGroup W₁)(X 0, X 1)` via `Hom.pointMap_add` and
`Hom.pointMap_map_algebraMap_map_genericPoint` proves (2).

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries`: the formal power series of a morphism in `Hom W₁ W₂`, `0` on
  the zero morphism and `Isogeny.formalSeries` on an isogeny.
* `TauCeti.Isogeny.Hom.formalPointAddHom`: `Hom W₁ W₂ →+ (formalGroup W₂).Point Unit`.
* `TauCeti.Isogeny.formalGroupHom`: the `FormalGroupHom (formalGroup W₁) (formalGroup W₂)` induced
  by an isogeny `φ : W₁ → W₂`.
* `TauCeti.Isogeny.Hom.formalGroupHom`: the `FormalGroupHom (formalGroup W₁) (formalGroup W₂)`
  induced by a morphism `f : Hom W₁ W₂`, the zero homomorphism for `f = 0`.
* `TauCeti.Isogeny.formalGroupIso`: the `FormalGroupIso (formalGroup W₁) (formalGroup W₂)` induced
  by a separable isogeny `φ : W₁ → W₂`.

## Main results

* `TauCeti.Isogeny.Hom.formalPointAddHom_injective`, `TauCeti.Isogeny.Hom.formalSeries_inj`, and
  `TauCeti.Isogeny.formalGroupHom_inj`: morphisms and isogenies are uniquely determined by their
  formal power series and formal-group homomorphisms.
* `TauCeti.Isogeny.formalSeries_map` and `TauCeti.Isogeny.Hom.formalSeries_map`: `formalSeries`
  commutes with base change of the coefficient field.
* `TauCeti.Isogeny.Hom.formalSeries_add`, `TauCeti.Isogeny.Hom.formalSeries_neg`,
  `TauCeti.Isogeny.Hom.formalSeries_sub`, `TauCeti.Isogeny.Hom.formalSeries_nsmul`,
  `TauCeti.Isogeny.Hom.formalSeries_zsmul`: formal-group addition, inversion, subtraction and scalar
  multiplication of formal series of morphisms.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny` and
  `TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero_natCast`: the formal series of `[n]` is
  `(formalGroup W).zsmulSeries n` (and `(formalGroup W).nsmulSeries n` for `n : ℕ`).
* `TauCeti.Isogeny.pointMap_ofIsogeny_mvPowerSeriesPointHom` and
  `TauCeti.Isogeny.Hom.formalPointAddHom_ofIsogeny_comp`: equivariance of
  `WeierstrassCurve.mvPowerSeriesPointHom` and `Hom.formalPointAddHom` under `φ.formalGroupHom`.
* `TauCeti.Isogeny.formalGroupHom_id`, `TauCeti.Isogeny.formalGroupHom_comp`,
  `TauCeti.Isogeny.formalGroupHom_negIsogeny`, and `TauCeti.Isogeny.formalGroupHom_mulByIntIsogeny`:
  functoriality of `Isogeny.formalGroupHom` and its values on `[-1]` and `[n]`.
* `TauCeti.Isogeny.Hom.formalGroupHom_injective`, `TauCeti.Isogeny.Hom.formalGroupHom_comp`,
  `TauCeti.Isogeny.Hom.formalGroupHom_zsmul`,
  `TauCeti.Isogeny.Hom.formalGroupHom_add_applyPoint`,
  `TauCeti.Isogeny.Hom.formalGroupHom_nsmul_applyPoint`, and
  `TauCeti.Isogeny.Hom.formalGroupHom_zsmul_applyPoint`: `Hom.formalGroupHom` is injective and
  functorial, and sums and scalar multiples of morphisms act on formal points through the group law
  of `formalGroup W₂`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4, IV.2 and IV.4.
-/

public section

open MvPowerSeries WeierstrassCurve WeierstrassCurve.Affine
open scoped LaurentSeries PowerSeries nonZeroDivisors

namespace TauCeti.Isogeny

/-! ### Base change of the formal series of an isogeny -/

/-- Base change of an isogeny along a field homomorphism `σ` maps the coefficients of its formal
series by `σ`. -/
@[simp]
theorem formalSeries_map {K L : Type*} [Field K] [Field L] {W₁ W₂ : WeierstrassCurve K}
    (φ : Isogeny W₁.toAffine W₂.toAffine) (σ : K →+* L) :
    (φ.map σ).formalSeries = PowerSeries.map σ φ.formalSeries := by
  apply (formalSeries_eq_iff (W₁ := W₁.map σ) (W₂ := W₂.map σ) (φ.map σ) _).mpr
  rw [← HahnSeries.map_ofPowerSeries, ← HahnSeries.mapRingHom_apply, coe_formalSeries,
    ← W₁.functionFieldLaurentExpansion_map, ← map_fieldPullback_map]
  simp [FunctionField.map_genericX, FunctionField.map_genericY]

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

-- Handle composites before `formalSeries_comp` rewrites them to substitutions.
@[simp↓]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

-- Handle composites before `formalSeries_comp` rewrites them to substitutions.
@[simp↓]
theorem formalSeries_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp [φ.formalSeries_ne_zero, ofIsogeny_ne_zero]

/-- **A morphism is uniquely determined by its formal power series.** -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro f g h
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [formalSeries_zero] at h
    exact (formalSeries_eq_zero_iff.mp h.symm).symm
  · rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
    · rw [formalSeries_zero] at h
      exact (ofIsogeny_ne_zero φ (formalSeries_eq_zero_iff.mp h)).elim
    · rw [formalSeries_ofIsogeny, formalSeries_ofIsogeny] at h
      exact congrArg ofIsogeny (Isogeny.formalSeries_injective h)

-- Handle composites before `formalSeries_comp` rewrites them to substitutions.
@[simp↓]
theorem formalSeries_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = g.formalSeries ↔ f = g :=
  formalSeries_injective.eq_iff

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

/-- Base change of a morphism maps the coefficients of its formal series. -/
@[simp]
theorem formalSeries_map {L : Type*} [Field L] (f : Hom W₁.toAffine W₂.toAffine) (σ : K →+* L) :
    (f.map σ).formalSeries = PowerSeries.map σ f.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [zero_map, formalSeries_zero, formalSeries_zero, map_zero]
  · rw [ofIsogeny_map, formalSeries_ofIsogeny, formalSeries_ofIsogeny, Isogeny.formalSeries_map]

private noncomputable def evalFormalPoint (f : Hom W₁.toAffine W₂.toAffine) {σ : Type*}
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) : (formalGroup W₂).Point σ :=
  ⟨PowerSeries.subst q f.formalSeries,
    .of_constantCoeff_zero
      (PowerSeries.constantCoeff_subst_eq_zero hq _ f.constantCoeff_formalSeries)⟩

/-- Evaluating `f.tautologicalPoint` along
`(mvSubstAlgHom KK hq hq0).comp W₁.functionFieldLaurentExpansion` for a nonzero parameter `q` with
zero constant coefficient gives the formal point `f.formalSeries(q)`. -/
private theorem map_mvSubstAlgHom_tautologicalPoint [W₂.IsElliptic] {σ : Type*} (KK : Type*)
    [Field KK] [DecidableEq KK] [Algebra K KK] [Algebra (MvPowerSeries σ K) KK]
    [IsScalarTower K (MvPowerSeries σ K) KK] [FaithfulSMul (MvPowerSeries σ K) KK]
    (f : Hom W₁.toAffine W₂.toAffine) {q : MvPowerSeries σ K} (hq : constantCoeff q = 0)
    (hq0 : q ≠ 0) :
    Point.map ((TauCeti.LaurentSeries.mvSubstAlgHom KK hq hq0).comp
        W₁.functionFieldLaurentExpansion) f.tautologicalPoint =
      W₂.mvPowerSeriesPointHom σ KK (evalFormalPoint f hq) := by
  let ev : W₁.toAffine.FunctionField →ₐ[K] KK :=
    (TauCeti.LaurentSeries.mvSubstAlgHom KK hq hq0).comp W₁.functionFieldLaurentExpansion
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · have hz : evalFormalPoint (0 : Hom W₁.toAffine W₂.toAffine) hq = 0 :=
      Subtype.ext (by simp [evalFormalPoint, PowerSeries.subst_zero])
    rw [tautologicalPoint_zero, _root_.map_zero, hz, _root_.map_zero]
  · rw [tautologicalPoint_ofIsogeny, tautologicalPoint_eq_map_genericPoint, Point.map_map]
    refine W₂.map_genericPoint_eq_mvPowerSeriesPointHom σ KK (ev.comp φ.fieldPullback) ?_ ?_
    · simp only [ev, evalFormalPoint, AlgHom.comp_apply, formalSeries_ofIsogeny,
        ← φ.coe_formalSeries, TauCeti.LaurentSeries.mvSubstAlgHom_coe]
    · simp only [ev, evalFormalPoint, AlgHom.comp_apply, formalSeries_ofIsogeny,
        ← φ.coe_subst_formalW_formalSeries, TauCeti.LaurentSeries.mvSubstAlgHom_coe,
        PowerSeries.subst_comp_subst_apply
          (.of_constantCoeff_zero' φ.constantCoeff_formalSeries) (.of_constantCoeff_zero hq)]

end Defs

section Additivity

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- The formal point `(f.formalSeries, _)` in `(formalGroup W₂).Point Unit`. -/
private noncomputable def formalPointFun (f : Hom W₁.toAffine W₂.toAffine) :
    (formalGroup W₂).Point Unit :=
  ⟨f.formalSeries, PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_formalSeries⟩

private theorem map_unitLaurent_tautologicalPoint
    [DecidableEq (FractionRing (MvPowerSeries Unit K))] (f : Hom W₁.toAffine W₂.toAffine) :
    Point.map
        ((TauCeti.LaurentSeries.mvSubstAlgHom (FractionRing (MvPowerSeries Unit K))
            (constantCoeff_X ()) (nonZeroDivisors.ne_zero X_mem_nonZeroDivisors)).comp
          W₁.functionFieldLaurentExpansion)
        f.tautologicalPoint =
      W₂.mvPowerSeriesPointHom Unit (FractionRing (MvPowerSeries Unit K)) (formalPointFun f) := by
  refine (map_mvSubstAlgHom_tautologicalPoint (FractionRing (MvPowerSeries Unit K)) f
    (constantCoeff_X ()) (nonZeroDivisors.ne_zero X_mem_nonZeroDivisors)).trans ?_
  congr 1
  exact Subtype.ext
    (by simp only [evalFormalPoint, formalPointFun, ← PowerSeries.X_apply, PowerSeries.X_subst])

/-- **Sending a morphism `f : Hom W₁ W₂` into an elliptic curve `W₂` to its formal power series is
an additive group homomorphism** into `(formalGroup W₂).Point Unit`. -/
noncomputable def formalPointAddHom :
    Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit where
  toFun := formalPointFun
  map_zero' := Subtype.ext formalSeries_zero
  map_add' f g := by
    classical
    apply W₂.mvPowerSeriesPointHom_injective Unit (FractionRing (MvPowerSeries Unit K))
    rw [_root_.map_add, ← map_unitLaurent_tautologicalPoint, ← map_unitLaurent_tautologicalPoint,
      ← map_unitLaurent_tautologicalPoint, tautologicalPoint_add, _root_.map_add]

@[simp]
theorem val_formalPointAddHom (f : Hom W₁.toAffine W₂.toAffine) :
    (formalPointAddHom f).val = f.formalSeries :=
  (rfl)

@[simp]
theorem formalPointAddHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    formalPointAddHom (Hom.id W.toAffine) = (formalGroup W).tautologicalPoint :=
  Subtype.ext ((formalSeries_id W).trans (formalGroup W).val_tautologicalPoint.symm)

/-- **`formalPointAddHom` is injective** for morphisms into an elliptic curve `W₂`. -/
theorem formalPointAddHom_injective :
    Function.Injective (formalPointAddHom (W₁ := W₁) (W₂ := W₂)) :=
  (injective_iff_map_eq_zero _).mpr fun _ hf ↦
    formalSeries_eq_zero_iff.mp (congrArg Subtype.val hf)

/-- **The formal series of a sum of morphisms into an elliptic curve is the formal-group sum of
their formal series** (Silverman IV.4). -/
theorem formalSeries_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      MvPowerSeries.subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries := by
  simpa only [val_formalPointAddHom, FormalGroup.add_apply] using
    congrArg Subtype.val (_root_.map_add formalPointAddHom f g)

/-- **The formal series of `-f` for a morphism into an elliptic curve is the formal-group inverse
evaluated at `f.formalSeries`.** -/
theorem formalSeries_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries (formalGroup W₂).addInvX := by
  simpa only [val_formalPointAddHom, FormalGroup.neg_apply] using
    congrArg Subtype.val (_root_.map_neg formalPointAddHom f)

/-- **The formal series of `f - g` for morphisms into an elliptic curve is the formal-group sum of
`f.formalSeries` and `(formalGroup W₂).addInvX(g.formalSeries)`.** -/
theorem formalSeries_sub (f g : Hom W₁.toAffine W₂.toAffine) :
    (f - g).formalSeries =
      MvPowerSeries.subst ![f.formalSeries,
          PowerSeries.subst g.formalSeries (formalGroup W₂).addInvX]
        (formalGroup W₂).toPowerSeries := by
  rw [sub_eq_add_neg, formalSeries_add, formalSeries_neg]

/-- **The formal series of `n • f` (`n : ℕ`) for a morphism into an elliptic curve is
`[n]_{formalGroup W₂}(f.formalSeries)`.** -/
theorem formalSeries_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) := by
  have h := congrArg Subtype.val (_root_.map_nsmul formalPointAddHom n f)
  rwa [val_formalPointAddHom, ← (formalGroup W₂).subst_nsmulSeries (formalPointAddHom f) n,
    val_formalPointAddHom] at h

/-- **The formal series of `n • f` (`n : ℤ`) for a morphism into an elliptic curve is
`[n]_{formalGroup W₂}(f.formalSeries)`.** -/
theorem formalSeries_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) := by
  have h := congrArg Subtype.val (_root_.map_zsmul formalPointAddHom n f)
  rwa [val_formalPointAddHom, ← (formalGroup W₂).subst_zsmulSeries (formalPointAddHom f) n,
    val_formalPointAddHom] at h

end Additivity

end Hom

section MulByInt

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **For an elliptic curve `W`, the formal series of the multiplication-by-`n` isogeny `[n]` is
the formal-group multiplication series `(formalGroup W).zsmulSeries n`.** -/
@[simp]
theorem formalSeries_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  have hs := congrArg Hom.formalSeries (ofIsogeny_mulByIntIsogeny W.toAffine hn)
  rwa [Hom.formalSeries_ofIsogeny, Hom.formalSeries_zsmul, Hom.formalSeries_id,
    PowerSeries.X_subst] at hs

/-- **For an elliptic curve `W` and a nonzero natural number `n`, the formal series of `[n]` is
`(formalGroup W).nsmulSeries n`.** -/
theorem formalSeries_mulByIntIsogenyOfNeZero_natCast {n : ℕ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine (n := n) (mod_cast hn)).formalSeries =
      (formalGroup W).nsmulSeries n := by
  rw [formalSeries_mulByIntIsogeny, FormalGroup.zsmulSeries_natCast]

end MulByInt

/-! ### The formal-group homomorphism of an isogeny -/

section FormalGroupHom

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

private theorem pointMap_ofIsogeny_mvPowerSeriesPointHom_of_ne_zero [W₁.IsElliptic] [W₂.IsElliptic]
    {σ : Type*} (KK : Type*) [Field KK] [DecidableEq KK] [Algebra K KK]
    [Algebra (MvPowerSeries σ K) KK] [IsScalarTower K (MvPowerSeries σ K) KK]
    [FaithfulSMul (MvPowerSeries σ K) KK] (φ : Isogeny W₁.toAffine W₂.toAffine)
    {q : (formalGroup W₁).Point σ} (hq0 : q.val ≠ 0) :
    ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap (W₁.mvPowerSeriesPointHom σ KK q) =
      W₂.mvPowerSeriesPointHom σ KK (Hom.evalFormalPoint (Hom.ofIsogeny φ) q.prop.eq_zero) := by
  have hq : constantCoeff q.val = 0 := q.prop.eq_zero
  let ev : W₁.toAffine.FunctionField →ₐ[K] KK :=
    (TauCeti.LaurentSeries.mvSubstAlgHom KK hq hq0).comp W₁.functionFieldLaurentExpansion
  have hsrc : Point.map ev W₁.toAffine.genericPoint = W₁.mvPowerSeriesPointHom σ KK q := by
    refine W₁.map_genericPoint_eq_mvPowerSeriesPointHom σ KK ev ?_ ?_
    · simp only [ev, AlgHom.comp_apply, W₁.functionFieldLaurentExpansion_neg_genericX_div_genericY,
        TauCeti.LaurentSeries.mvSubstAlgHom_coe, PowerSeries.subst_X q.prop]
    · simp only [ev, AlgHom.comp_apply, W₁.functionFieldLaurentExpansion_neg_inv_genericY,
        TauCeti.LaurentSeries.mvSubstAlgHom_coe]
  refine (congrArg ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap hsrc.symm).trans ?_
  exact (Hom.pointMap_map_algebraMap_map_genericPoint (Hom.ofIsogeny φ) ev).trans
    (Hom.map_mvSubstAlgHom_tautologicalPoint KK (Hom.ofIsogeny φ) hq hq0)

/-- **The formal-group homomorphism attached to an isogeny** `φ : W₁ → W₂` to an elliptic curve:
`φ.formalSeries` satisfies `φ.formalSeries((formalGroup W₁)(X, Y)) =
(formalGroup W₂)(φ.formalSeries(X), φ.formalSeries(Y))` (Silverman IV.2, IV.4). -/
noncomputable def formalGroupHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) :=
  FormalGroupHom.ofHomDefectEqZero φ.constantCoeff_formalSeries <| by
    classical
    have : W₁.IsElliptic := φ.isElliptic
    rw [FormalGroup.homDefect_eq_sub_subst_pair, sub_eq_zero]
    let KK := FractionRing (MvPowerSeries (Fin 2) K)
    let q₀ : (formalGroup W₁).Point (Fin 2) := ⟨X 0, PowerSeries.HasSubst.X 0⟩
    let q₁ : (formalGroup W₁).Point (Fin 2) := ⟨X 1, PowerSeries.HasSubst.X 1⟩
    have hq₀ : q₀.val ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
    have hq₁ : q₁.val ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
    have hsum_val : (q₀ + q₁).val = (formalGroup W₁).toPowerSeries := by
      rw [FormalGroup.add_apply]
      simp only [q₀, q₁, finTwo_X_eq_X, subst_self, id_eq]
    have hsum0 : (q₀ + q₁).val ≠ 0 := by
      rw [hsum_val]
      intro h0
      have hc := congrArg (coeff (Finsupp.single 0 1)) h0
      rw [(formalGroup W₁).lin_coeff_X, map_zero] at hc
      exact one_ne_zero hc
    -- Apply `Hom.pointMap_add` on `(W₁.baseChange KK).toAffine.Point` to `q₀` and `q₁`.
    let r₀ := Hom.evalFormalPoint (Hom.ofIsogeny φ) q₀.prop.eq_zero
    let r₁ := Hom.evalFormalPoint (Hom.ofIsogeny φ) q₁.prop.eq_zero
    have h₁ : W₂.mvPowerSeriesPointHom (Fin 2) KK
        (Hom.evalFormalPoint (Hom.ofIsogeny φ) (q₀ + q₁).prop.eq_zero) =
        W₂.mvPowerSeriesPointHom (Fin 2) KK (r₀ + r₁) := by
      refine (pointMap_ofIsogeny_mvPowerSeriesPointHom_of_ne_zero KK φ hsum0).symm.trans ?_
      refine (congrArg ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap
        ((W₁.mvPowerSeriesPointHom (Fin 2) KK).map_add q₀ q₁)).trans ?_
      refine (Hom.pointMap_add ((Hom.ofIsogeny φ).map (algebraMap K KK)) _ _).trans ?_
      refine (congrArg₂ (· + ·) (pointMap_ofIsogeny_mvPowerSeriesPointHom_of_ne_zero KK φ hq₀)
        (pointMap_ofIsogeny_mvPowerSeriesPointHom_of_ne_zero KK φ hq₁)).trans ?_
      exact ((W₂.mvPowerSeriesPointHom (Fin 2) KK).map_add r₀ r₁).symm
    have heq : PowerSeries.subst (q₀ + q₁).val (Hom.ofIsogeny φ).formalSeries = (r₀ + r₁).val :=
      congrArg Subtype.val (W₂.mvPowerSeriesPointHom_injective (Fin 2) KK h₁)
    rw [hsum_val, FormalGroup.add_apply] at heq
    simpa only [r₀, r₁, q₀, q₁, Hom.evalFormalPoint, Hom.formalSeries_ofIsogeny] using heq

@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries :=
  FormalGroupHom.ofHomDefectEqZero_toPowerSeries _ _

/-- **An isogeny to an elliptic curve is uniquely determined by its formal-group homomorphism.** -/
theorem formalGroupHom_injective [W₂.IsElliptic] :
    Function.Injective (formalGroupHom (W₁ := W₁) (W₂ := W₂)) := fun _ _ h ↦
  formalSeries_injective <| by
    simpa only [formalGroupHom_toPowerSeries] using congrArg FormalGroupHom.toPowerSeries h

-- Handle composites before `formalGroupHom_comp` rewrites them.
@[simp↓]
theorem formalGroupHom_inj [W₂.IsElliptic] {φ ψ : Isogeny W₁.toAffine W₂.toAffine} :
    φ.formalGroupHom = ψ.formalGroupHom ↔ φ = ψ :=
  formalGroupHom_injective.eq_iff

/-- **Evaluating a base-changed isogeny on a power-series formal point pushes the formal point
forward along `φ.formalGroupHom`.** -/
theorem pointMap_ofIsogeny_mvPowerSeriesPointHom [W₁.IsElliptic] [W₂.IsElliptic] {σ : Type*}
    (KK : Type*) [Field KK] [DecidableEq KK] [Algebra K KK] [Algebra (MvPowerSeries σ K) KK]
    [IsScalarTower K (MvPowerSeries σ K) KK] [FaithfulSMul (MvPowerSeries σ K) KK]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (q : (formalGroup W₁).Point σ) :
    ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap (W₁.mvPowerSeriesPointHom σ KK q) =
      W₂.mvPowerSeriesPointHom σ KK (φ.formalGroupHom.applyPoint q) := by
  rcases eq_or_ne q 0 with rfl | hq
  · refine (congrArg ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap
      (W₁.mvPowerSeriesPointHom σ KK).map_zero).trans ?_
    refine (Hom.pointMap_zero ((Hom.ofIsogeny φ).map (algebraMap K KK))).trans ?_
    exact ((congrArg (W₂.mvPowerSeriesPointHom σ KK) φ.formalGroupHom.applyPoint_zero).trans
      (W₂.mvPowerSeriesPointHom σ KK).map_zero).symm
  · have hq0 : q.val ≠ 0 := fun h ↦ hq (Subtype.ext h)
    refine (pointMap_ofIsogeny_mvPowerSeriesPointHom_of_ne_zero KK φ hq0).trans ?_
    congr 1
    exact Subtype.ext (by simp [FormalGroupHom.applyPoint_val, Hom.evalFormalPoint])

/-- **Postcomposing `f : Hom W₁ W₂` with an isogeny `ψ : W₂ → W₃` between elliptic curves acts on
`Hom.formalPointAddHom` via `ψ.formalGroupHom.applyPoint`.** -/
@[simp]
theorem Hom.formalPointAddHom_ofIsogeny_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (ψ : Isogeny W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    Hom.formalPointAddHom ((Hom.ofIsogeny ψ).comp f) =
      ψ.formalGroupHom.applyPoint (Hom.formalPointAddHom f) :=
  Subtype.ext (by simp [FormalGroupHom.applyPoint_val])

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

/-- **For an elliptic curve `W`, the formal-group homomorphism of `[-1]` is
`(formalGroup W).zsmulHom (-1)`.** -/
@[simp]
theorem formalGroupHom_negIsogeny (W : WeierstrassCurve K) [W.IsElliptic] :
    (negIsogeny W.toAffine).formalGroupHom = (formalGroup W).zsmulHom (-1) := by
  ext : 1
  simp

/-- **For an elliptic curve `W`, the formal-group homomorphism of `[n]` is
`(formalGroup W).zsmulHom n`.** -/
-- Covers `mulByIntIsogenyOfNeZero` as well, since it is an `abbrev` for `mulByIntIsogeny`.
@[simp]
theorem formalGroupHom_mulByIntIsogeny (W : WeierstrassCurve K) [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalGroupHom = (formalGroup W).zsmulHom n := by
  ext : 1
  simp

/-- **For an elliptic curve `W` and a nonzero natural number `n`, the formal-group homomorphism
of `[n]` is `(formalGroup W).nsmulHom n`.** -/
theorem formalGroupHom_mulByIntIsogenyOfNeZero_natCast (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine (n := n) (mod_cast hn)).formalGroupHom =
      (formalGroup W).nsmulHom n := by
  ext : 1
  simp

namespace Hom

variable [W₂.IsElliptic]

/-- **Every morphism `f : W₁ → W₂` to an elliptic curve induces a homomorphism of formal group
laws**, the zero homomorphism for the zero morphism and `Isogeny.formalGroupHom` on an isogeny
(Silverman IV.4). -/
noncomputable def formalGroupHom (f : Hom W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) :=
  FormalGroupHom.ofHomDefectEqZero f.constantCoeff_formalSeries <| by
    rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
    · rw [formalSeries_zero, FormalGroup.homDefect_zero]
    · rw [formalSeries_ofIsogeny, ← φ.formalGroupHom_toPowerSeries]
      exact φ.formalGroupHom.homDefect_toPowerSeries

@[simp]
theorem formalGroupHom_toPowerSeries (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalGroupHom.toPowerSeries = f.formalSeries :=
  FormalGroupHom.ofHomDefectEqZero_toPowerSeries _ _

/-- **A morphism to an elliptic curve is uniquely determined by its formal-group
homomorphism.** -/
theorem formalGroupHom_injective :
    Function.Injective (formalGroupHom (W₁ := W₁) (W₂ := W₂)) := fun _ _ h ↦
  formalSeries_injective <| by
    simpa only [formalGroupHom_toPowerSeries] using congrArg FormalGroupHom.toPowerSeries h

-- Handle composites before `formalGroupHom_comp` rewrites them.
@[simp↓]
theorem formalGroupHom_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalGroupHom = g.formalGroupHom ↔ f = g :=
  formalGroupHom_injective.eq_iff

@[simp]
theorem formalGroupHom_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalGroupHom = φ.formalGroupHom := by
  ext : 1
  simp

omit [W₂.IsElliptic] in
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Hom.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext : 1
  simp

@[simp]
theorem formalGroupHom_comp [W₃.IsElliptic] (g : Hom W₂.toAffine W₃.toAffine)
    (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalGroupHom = g.formalGroupHom.comp f.formalGroupHom := by
  ext : 1
  simp

/-- **Negating a morphism composes its formal-group homomorphism with `[-1]` on the target.** -/
@[simp]
theorem formalGroupHom_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalGroupHom = ((formalGroup W₂).zsmulHom (-1)).comp f.formalGroupHom := by
  ext : 1
  simp [formalSeries_neg]

/-- **Natural scalar multiplication of a morphism composes its formal-group homomorphism with
`[n]` on the target.** -/
@[simp]
theorem formalGroupHom_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalGroupHom = ((formalGroup W₂).nsmulHom n).comp f.formalGroupHom := by
  ext : 1
  simp [formalSeries_nsmul]

/-- **Integer scalar multiplication of a morphism composes its formal-group homomorphism with
`[n]` on the target.** -/
@[simp]
theorem formalGroupHom_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalGroupHom = ((formalGroup W₂).zsmulHom n).comp f.formalGroupHom := by
  ext : 1
  simp [formalSeries_zsmul]

/-- The zero morphism acts as zero on every formal power-series point. -/
@[simp]
theorem formalGroupHom_zero_applyPoint {σ : Type*} (x : (formalGroup W₁).Point σ) :
    (0 : Hom W₁.toAffine W₂.toAffine).formalGroupHom.applyPoint x = 0 := by
  apply Subtype.ext
  simp [FormalGroup.zero_apply]

/-- **A sum of morphisms acts on formal power-series points by addition in
`formalGroup W₂`.** -/
@[simp]
theorem formalGroupHom_add_applyPoint (f g : Hom W₁.toAffine W₂.toAffine) {σ : Type*}
    (x : (formalGroup W₁).Point σ) :
    (f + g).formalGroupHom.applyPoint x =
      f.formalGroupHom.applyPoint x + g.formalGroupHom.applyPoint x := by
  apply Subtype.ext
  rw [FormalGroupHom.applyPoint_val, formalGroupHom_toPowerSeries, formalSeries_add,
    FormalGroup.add_apply, FormalGroupHom.applyPoint_val, FormalGroupHom.applyPoint_val,
    formalGroupHom_toPowerSeries, formalGroupHom_toPowerSeries, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply
      (PowerSeries.hasSubst_pair f.constantCoeff_formalSeries g.constantCoeff_formalSeries)
      x.prop.const]
  congr 1
  funext i
  fin_cases i <;> simp [PowerSeries.subst_def]

-- Not `@[simp]`: `simp` already reduces the left-hand side via `formalGroupHom_neg`.
/-- Negation of a morphism acts by negation on formal power-series points. -/
theorem formalGroupHom_neg_applyPoint (f : Hom W₁.toAffine W₂.toAffine) {σ : Type*}
    (x : (formalGroup W₁).Point σ) :
    (-f).formalGroupHom.applyPoint x = -f.formalGroupHom.applyPoint x := by
  simp

/-- Subtraction of morphisms acts by subtraction on formal power-series points. -/
@[simp]
theorem formalGroupHom_sub_applyPoint (f g : Hom W₁.toAffine W₂.toAffine) {σ : Type*}
    (x : (formalGroup W₁).Point σ) :
    (f - g).formalGroupHom.applyPoint x =
      f.formalGroupHom.applyPoint x - g.formalGroupHom.applyPoint x := by
  rw [sub_eq_add_neg, formalGroupHom_add_applyPoint, formalGroupHom_neg_applyPoint,
    ← sub_eq_add_neg]

-- Not `@[simp]`: `simp` already reduces the left-hand side via `formalGroupHom_nsmul`.
/-- Natural scalar multiplication of a morphism acts by scalar multiplication on formal
power-series points. -/
theorem formalGroupHom_nsmul_applyPoint (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) {σ : Type*}
    (x : (formalGroup W₁).Point σ) :
    (n • f).formalGroupHom.applyPoint x = n • f.formalGroupHom.applyPoint x := by
  simp

-- Not `@[simp]`: `simp` already reduces the left-hand side via `formalGroupHom_zsmul`.
/-- Integer scalar multiplication of a morphism acts by scalar multiplication on formal
power-series points. -/
theorem formalGroupHom_zsmul_applyPoint (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) {σ : Type*}
    (x : (formalGroup W₁).Point σ) :
    (n • f).formalGroupHom.applyPoint x = n • f.formalGroupHom.applyPoint x := by
  simp

end Hom

/-- **A separable isogeny to an elliptic curve induces an isomorphism of formal group laws.** -/
noncomputable def formalGroupIso [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    FormalGroupIso (formalGroup W₁) (formalGroup W₂) :=
  φ.formalGroupHom.toIso <| by
    rw [formalGroupHom_toPowerSeries]
    exact φ.isUnit_coeff_one_formalSeries_iff_isSeparable.mpr inferInstance

@[simp]
theorem formalGroupIso_toHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalGroupIso.toHom = φ.formalGroupHom :=
  FormalGroupHom.toIso_toHom _ _

@[simp]
theorem formalGroupIso_invHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalGroupIso.invHom.toPowerSeries =
      φ.formalSeries.substInvOfIsUnit
        (φ.isUnit_coeff_one_formalSeries_iff_isSeparable.mpr inferInstance) := by
  rw [formalGroupIso, FormalGroupHom.toIso_invHom_toPowerSeries]
  congr! 1
  exact φ.formalGroupHom_toPowerSeries

end FormalGroupHom

end TauCeti.Isogeny

end
