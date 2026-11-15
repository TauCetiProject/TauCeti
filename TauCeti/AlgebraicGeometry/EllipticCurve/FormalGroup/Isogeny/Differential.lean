/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Expansion

/-!
# The invariant differential and separability on formal series of isogenies

Expanding rational functions at infinity in the local parameter `z = -x/y` sends the invariant
differential `ω = dx / (2y + a₁x + a₃)` of a Weierstrass curve `W`, when `2y + a₁x + a₃ ≠ 0` (in
particular, for any elliptic curve `W`), to the normalised invariant differential `P(X) dX` of its
formal group law `Ê`:
`(e(2y + a₁x + a₃))⁻¹ · d/dX (e x) = P(X)` in `K⸨X⸩`.

Along an isogeny `φ : W₁ → W₂` of elliptic curves, combining this expansion with the constancy of
the Kähler pullback `φ^*ω₂ = c ω₁` and the chain rule for Laurent substitution yields the formal
differential identity `P₂(φ(X)) · φ'(X) = c · P₁(X)` in `K⟦X⟧`. Evaluating constant coefficients
identifies the pullback scalar `c` with the linear coefficient `(φ.formalSeries).coeff 1`, so `φ`
is separable if and only if `(φ.formalSeries).coeff 1 ≠ 0` (equivalently,
`φ.formalSeries.order = 1`).

For relative Frobenius `F^n : W → W⁽ᵖⁿ⁾`, the formal series is `X ^ (p ^ n)`. Factoring any isogeny
into an iterated relative Frobenius followed by a separable isogeny shows that the order of
vanishing of `φ.formalSeries` is the inseparable degree of `φ` (Silverman IV.7.4).

## Main results

* `WeierstrassCurve.inv_functionFieldLaurentExpansion_invariantDifferentialDenom_mul_derivative`:
  the Laurent expansion of `dx / (2y + a₁x + a₃)` at infinity is
  `(formalGroup W).invariantDifferential` (with an `of_ne_zero` version avoiding ellipticity).
* `TauCeti.Isogeny.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul`:
  `φ^*ω₂ = (coeff 1 φ.formalSeries) • ω₁`.
* `TauCeti.Isogeny.subst_formalSeries_invariantDifferential_mul_derivative`:
  `P₂(φ(X)) · φ'(X) = (coeff 1 φ.formalSeries) • P₁(X)`.
* `TauCeti.Isogeny.isSeparable_iff_coeff_one_formalSeries_ne_zero` and
  `TauCeti.Isogeny.isSeparable_iff_order_formalSeries_eq_one`: formal separability criteria.
* `TauCeti.Isogeny.formalSeries_relativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`: relative Frobenius has formal
  series `X ^ p` and `X ^ (p ^ n)`.
* `TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree`: `φ.formalSeries.order` equals the
  inseparable degree of `φ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5, IV.4, and IV.7.4.
-/

public section

open HahnSeries WeierstrassCurve
open scoped LaurentSeries PowerSeries

namespace WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- The formal denominator `1 - a₁X - a₂X² - 2a₃w - 2a₄Xw - 3a₆w²` coerced to `K⸨X⸩`. -/
private theorem coe_formalInvariantDifferentialDenom :
    (W.formalInvariantDifferentialDenom : K⸨X⸩) =
      1 - algebraMap K K⸨X⸩ W.a₁ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) -
        algebraMap K K⸨X⸩ W.a₂ * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) ^ 2 -
        2 * algebraMap K K⸨X⸩ W.a₃ * (formalW W : K⸨X⸩) -
        2 * algebraMap K K⸨X⸩ W.a₄ * (((PowerSeries.X : K⟦X⟧) : K⸨X⸩) * (formalW W : K⸨X⸩)) -
        3 * algebraMap K K⸨X⸩ W.a₆ * (formalW W : K⸨X⸩) ^ 2 := by
  rw [formalInvariantDifferentialDenom_def]
  simp only [PowerSeries.smul_eq_C_mul, ← PowerSeries.algebraMap_eq, ← LaurentSeries.coe_algebraMap,
    map_sub, map_one, map_mul, map_pow, map_ofNat, ← IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩]

/-- **The Laurent expansion of `ω = dx / (2y + a₁x + a₃)` at infinity is the invariant differential
of the formal group law**, for any Weierstrass curve whose denominator `2y + a₁x + a₃` is nonzero in
the function field (Silverman IV.4). -/
theorem inv_functionFieldLaurentExpansion_invariantDifferentialDenom_mul_derivative_of_ne_zero
    (hW : W.toAffine.invariantDifferentialDenom ≠ 0) :
    (W.functionFieldLaurentExpansion W.toAffine.invariantDifferentialDenom)⁻¹ *
        _root_.LaurentSeries.derivative K
          (W.functionFieldLaurentExpansion W.toAffine.genericX) =
      ((formalGroup W).invariantDifferential : K⸨X⸩) := by
  set q : K⸨X⸩ := ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)
  set w : K⸨X⸩ := (formalW W : K⸨X⸩)
  -- Lift the Weierstrass equation for `w` and the inverse of the formal denominator to `K⸨X⸩`.
  have heq : w = wEquationRHS W q w := by
    simpa only [q, w, ← LaurentSeries.coe_algebraMap, algebraMap_wEquationRHS] using
      congrArg (ofPowerSeries ℤ K) (formalW_wEquation W)
  have hinv : ((formalGroup W).invariantDifferential : K⸨X⸩) *
      (W.formalInvariantDifferentialDenom : K⸨X⸩) = 1 := by
    simpa only [PowerSeries.coe_mul, PowerSeries.coe_one] using
      congrArg (ofPowerSeries ℤ K)
        W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  have hG0 : (W.formalInvariantDifferentialDenom : K⸨X⸩) ≠ 0 := right_ne_zero_of_mul_eq_one hinv
  have hGinv : (W.formalInvariantDifferentialDenom : K⸨X⸩)⁻¹ =
      ((formalGroup W).invariantDifferential : K⸨X⸩) :=
    inv_eq_of_mul_eq_one_left hinv
  -- Express `e(2y + a₁x + a₃)` as `polynomialY` evaluated at `(q / w, -1 / w)`.
  have hdenom_eq : W.functionFieldLaurentExpansion W.toAffine.invariantDifferentialDenom =
      (W⁄K⸨X⸩).toAffine.polynomialY.evalEval (q / w) (-1 / w) := by
    rw [Affine.invariantDifferentialDenom_def, Affine.evalEval_polynomialY]
    simp only [map_add, map_mul, map_ofNat, AlgHom.commutes, WeierstrassCurve.baseChange,
      map_a₁, map_a₃, W.functionFieldLaurentExpansion_genericX_eq_div,
      W.functionFieldLaurentExpansion_genericY_eq_div, q, w]
  have hdenom_ne : W.functionFieldLaurentExpansion W.toAffine.invariantDifferentialDenom ≠ 0 :=
    (map_ne_zero_iff _ W.functionFieldLaurentExpansion.injective).mpr hW
  have hu : -2 + algebraMap K K⸨X⸩ W.a₁ * q + algebraMap K K⸨X⸩ W.a₃ * w ≠ 0 := by
    intro hu0
    apply hdenom_ne
    rw [hdenom_eq, Affine.evalEval_polynomialY]
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃]
    have hdiv : 2 * (-1 / w) + algebraMap K K⸨X⸩ W.a₁ * (q / w) +
        algebraMap K K⸨X⸩ W.a₃ =
        (-2 + algebraMap K K⸨X⸩ W.a₁ * q + algebraMap K K⸨X⸩ W.a₃ * w) / w := by
      have hw0 : w ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).mpr W.formalW_ne_zero
      field_simp
    rw [hdiv, hu0, zero_div]
  -- Apply implicit differentiation for `q / w` along `laurentSeriesDerivation`.
  rw [W.coe_formalInvariantDifferentialDenom] at hG0 hGinv
  have hmain := W.inv_evalEval_polynomialY_smul_derivation_div (TauCeti.laurentSeriesDerivation K)
    heq hG0 hu
  have hDq : TauCeti.laurentSeriesDerivation K q = 1 := by
    rw [TauCeti.laurentSeriesDerivation_apply, ← PowerSeries.coe_derivative,
      PowerSeries.derivative_X, PowerSeries.coe_one]
  rw [← hdenom_eq, TauCeti.laurentSeriesDerivation_apply,
    ← W.functionFieldLaurentExpansion_genericX_eq_div, hDq, smul_eq_mul, smul_eq_mul, mul_one,
    hGinv] at hmain
  exact hmain

/-- **The Laurent expansion of `ω = dx / (2y + a₁x + a₃)` at infinity is the invariant
differential of the formal group law** of an elliptic curve (Silverman IV.4). -/
theorem inv_functionFieldLaurentExpansion_invariantDifferentialDenom_mul_derivative
    [W.IsElliptic] :
    (W.functionFieldLaurentExpansion W.toAffine.invariantDifferentialDenom)⁻¹ *
        _root_.LaurentSeries.derivative K
          (W.functionFieldLaurentExpansion W.toAffine.genericX) =
      ((formalGroup W).invariantDifferential : K⸨X⸩) :=
  W.inv_functionFieldLaurentExpansion_invariantDifferentialDenom_mul_derivative_of_ne_zero
    W.toAffine.invariantDifferentialDenom_ne_zero

end WeierstrassCurve

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}

/-- **A scalar relation `φ^*ω₂ = c ω₁` on Kähler invariant differentials expands to
`P₂(φ(X)) · φ'(X) = c · P₁(X)` on formal invariant differentials**, whenever both curves
have nonzero invariant-differential denominators. -/
theorem subst_formalSeries_invariantDifferential_mul_derivative_of_pullbackDifferential_eq_smul
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    (hW₁ : W₁.toAffine.invariantDifferentialDenom ≠ 0)
    (hW₂ : W₂.toAffine.invariantDifferentialDenom ≠ 0) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine) :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
        d⁄dX φ.formalSeries =
      c • (formalGroup W₁).invariantDifferential := by
  set d₂ := φ.fieldPullback W₂.toAffine.invariantDifferentialDenom
  have hd₂ : d₂ ≠ 0 := (map_ne_zero_iff _ φ.fieldPullback.injective).mpr hW₂
  have hD : KaehlerDifferential.D K W₁.toAffine.FunctionField
      (φ.fieldPullback W₂.toAffine.genericX) =
      (d₂ * algebraMap K W₁.toAffine.FunctionField c *
        (W₁.toAffine.invariantDifferentialDenom)⁻¹) •
        KaehlerDifferential.D K W₁.toAffine.FunctionField W₁.toAffine.genericX := by
    have hc' := congrArg (d₂ • ·) hc
    rw [Affine.invariantDifferential_def, Affine.invariantDifferential_def,
      pullbackDifferential_smul, pullbackDifferential_D, map_inv₀, smul_smul,
      mul_inv_cancel₀ hd₂, one_smul, ← algebraMap_smul W₁.toAffine.FunctionField c,
      smul_smul, smul_smul] at hc'
    exact hc'
  have hexp := TauCeti.derivative_algHom_eq_mul_of_D_eq_smul
    (e := W₁.functionFieldLaurentExpansion) hD
  have hed₂ : W₁.functionFieldLaurentExpansion d₂ ≠ 0 :=
    (map_ne_zero_iff _ W₁.functionFieldLaurentExpansion.injective).mpr hd₂
  have hexp' : (W₁.functionFieldLaurentExpansion d₂)⁻¹ *
      _root_.LaurentSeries.derivative K
        (W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericX)) =
      algebraMap K K⸨X⸩ c *
        ((W₁.functionFieldLaurentExpansion W₁.toAffine.invariantDifferentialDenom)⁻¹ *
          _root_.LaurentSeries.derivative K
            (W₁.functionFieldLaurentExpansion W₁.toAffine.genericX)) := by
    rw [hexp]
    simp only [map_mul, map_inv₀, AlgHom.commutes]
    field_simp [hed₂]
  have hed₂_eq : W₁.functionFieldLaurentExpansion d₂ =
      TauCeti.LaurentSeries.substAlgHom φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
        (W₂.functionFieldLaurentExpansion W₂.toAffine.invariantDifferentialDenom) :=
    φ.functionFieldLaurentExpansion_fieldPullback _
  have hω₁ :=
    W₁.inv_functionFieldLaurentExpansion_invariantDifferentialDenom_mul_derivative_of_ne_zero hW₁
  have hω₂ :=
    W₂.inv_functionFieldLaurentExpansion_invariantDifferentialDenom_mul_derivative_of_ne_zero hW₂
  rw [hω₁, φ.functionFieldLaurentExpansion_fieldPullback W₂.toAffine.genericX,
    TauCeti.LaurentSeries.derivative_substAlgHom, hed₂_eq, ← map_inv₀, ← mul_assoc, ← map_mul,
    hω₂, TauCeti.LaurentSeries.substAlgHom_coe, ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul,
    laurentSeries_algebraMap_mul_eq_smul, ← PowerSeries.coe_smul] at hexp'
  exact ofPowerSeries_injective hexp'

/-- **The pullback scalar in `φ^*ω₂ = c ω₁` is the linear coefficient of `φ.formalSeries`**,
whenever both curves have nonzero invariant-differential denominators. -/
theorem coeff_one_formalSeries_eq_of_pullbackDifferential_eq_smul
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    (hW₁ : W₁.toAffine.invariantDifferentialDenom ≠ 0)
    (hW₂ : W₂.toAffine.invariantDifferentialDenom ≠ 0) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine) :
    PowerSeries.coeff 1 φ.formalSeries = c := by
  have h := congrArg PowerSeries.constantCoeff
    (φ.subst_formalSeries_invariantDifferential_mul_derivative_of_pullbackDifferential_eq_smul
      hW₁ hW₂ hc)
  have hsubst : PowerSeries.constantCoeff
      (PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential) = 1 := by
    have h0 := PowerSeries.constantCoeff_subst_of_constantCoeff_zero
      φ.constantCoeff_formalSeries (formalGroup W₂).invariantDifferential
    rw [FormalGroup.constantCoeff_invariantDifferential, Algebra.algebraMap_self_apply] at h0
    exact h0
  have hderiv : PowerSeries.constantCoeff (d⁄dX φ.formalSeries) =
      PowerSeries.coeff 1 φ.formalSeries := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simpa only [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.constantCoeff_C, hsubst, hderiv,
    FormalGroup.constantCoeff_invariantDifferential, one_mul, mul_one] using h

section IsElliptic

variable [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **An isogeny pulls the invariant differential back by the linear coefficient of its formal
series** (Silverman III.5, IV.4): `φ^*ω₂ = ((φ.formalSeries).coeff 1) • ω₁`. -/
theorem pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul :
    φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      PowerSeries.coeff 1 φ.formalSeries • Affine.invariantDifferential W₁.toAffine := by
  have : W₁.IsElliptic := φ.isElliptic
  obtain ⟨c, hc, -⟩ := existsUnique_pullbackDifferential_invariantDifferential_eq_smul φ
  rwa [φ.coeff_one_formalSeries_eq_of_pullbackDifferential_eq_smul
    W₁.toAffine.invariantDifferentialDenom_ne_zero
    W₂.toAffine.invariantDifferentialDenom_ne_zero hc]

/-- **Pullback of the formal invariant differential along an isogeny** (Silverman IV.4):
`P₂(φ(X)) · φ'(X) = ((φ.formalSeries).coeff 1) • P₁(X)`. -/
theorem subst_formalSeries_invariantDifferential_mul_derivative :
    PowerSeries.subst φ.formalSeries (formalGroup W₂).invariantDifferential *
        d⁄dX φ.formalSeries =
      PowerSeries.coeff 1 φ.formalSeries • (formalGroup W₁).invariantDifferential := by
  have : W₁.IsElliptic := φ.isElliptic
  exact φ.subst_formalSeries_invariantDifferential_mul_derivative_of_pullbackDifferential_eq_smul
    W₁.toAffine.invariantDifferentialDenom_ne_zero
    W₂.toAffine.invariantDifferentialDenom_ne_zero
    φ.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul

/-- **An isogeny is separable if and only if its formal series has nonzero linear coefficient.** -/
theorem isSeparable_iff_coeff_one_formalSeries_ne_zero :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      PowerSeries.coeff 1 φ.formalSeries ≠ 0 :=
  isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul φ
    φ.pullbackDifferential_invariantDifferential_eq_coeff_one_formalSeries_smul

/-- **An isogeny is separable if and only if its formal series has order `1`.** -/
theorem isSeparable_iff_order_formalSeries_eq_one :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      φ.formalSeries.order = 1 := by
  rw [φ.isSeparable_iff_coeff_one_formalSeries_ne_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (PowerSeries.order_eq_nat (n := 1)).mpr ⟨h, fun i hi ↦ by
      obtain rfl : i = 0 := by omega
      simp⟩
  · exact ((PowerSeries.order_eq_nat (n := 1)).mp h).1

end IsElliptic

section RelativeFrobenius

variable (p : ℕ) [ExpChar K p]

/-- **The formal series of the `n`-fold relative Frobenius isogeny is `X ^ (p ^ n)`.** No
ellipticity assumption is needed. -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (W : WeierstrassCurve K) (n : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine n).formalSeries = PowerSeries.X ^ p ^ n := by
  let _ := expChar_of_injective_algebraMap (algebraMap K W.toAffine.FunctionField).injective p
  apply (formalSeries_eq_iff _ _).mpr
  rw [map_div₀, map_neg, fieldPullback_iterateRelativeFrobeniusIsogeny_genericX,
    fieldPullback_iterateRelativeFrobeniusIsogeny_genericY, neg_div, ← div_pow]
  have hneg : -(W.toAffine.genericX / W.toAffine.genericY) ^ p ^ n =
      (-W.toAffine.genericX / W.toAffine.genericY) ^ p ^ n := by
    rw [neg_div, ← iterateFrobenius_def (R := W.toAffine.FunctionField) p n,
      ← iterateFrobenius_def (R := W.toAffine.FunctionField) p n, map_neg]
  rw [hneg, PowerSeries.coe_pow, map_pow, W.functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- **The formal series of the relative Frobenius isogeny is `X ^ p`.** No ellipticity assumption
is needed. -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny (W : WeierstrassCurve K) :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  have hcast {σ τ : K →+* K} (h : σ = τ) (φ : Isogeny W.toAffine (W.toAffine.map σ)) :
      formalSeries (W₂ := W.map τ) (congrArg W.toAffine.map h ▸ φ) =
        formalSeries (W₂ := W.map σ) φ := by
    subst h; rfl
  have h1 := formalSeries_iterateRelativeFrobeniusIsogeny p W 1
  rw [iterateRelativeFrobeniusIsogeny_one, pow_one] at h1
  exact (hcast (iterateFrobenius_one (R := K) p).symm
    (relativeFrobeniusIsogeny p W.toAffine)).symm.trans h1

end RelativeFrobenius

/-- **The order of the formal series of an isogeny equals its inseparable degree**
(Silverman IV.7.4). -/
@[simp]
theorem order_formalSeries_eq_inseparableDegree [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalSeries.order = φ.inseparableDegree := by
  obtain ⟨p, _⟩ := ExpChar.exists K
  obtain ⟨r, χ, hsep, hχ⟩ := exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  have : Algebra.IsSeparable χ.fieldPullback.fieldRange
      (W₁.toAffine.map (iterateFrobenius K p r)).FunctionField := hsep
  have hr : φ.inseparableDegree = p ^ r :=
    inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ
  have hord :
      (χ : Isogeny (W₁.map (iterateFrobenius K p r)).toAffine
        W₂.toAffine).formalSeries.order = 1 :=
    (isSeparable_iff_order_formalSeries_eq_one χ).mp hsep
  have hc₀ := (iterateRelativeFrobeniusIsogeny p W₁.toAffine r).constantCoeff_formalSeries
  rw [hr, ← hχ, formalSeries_comp, PowerSeries.order_subst hc₀,
    formalSeries_iterateRelativeFrobeniusIsogeny, PowerSeries.order_X_pow, hord, mul_one,
    Nat.cast_pow]

/-- The natural-number order of `φ.formalSeries` is `φ.inseparableDegree`. -/
theorem toNat_order_formalSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalSeries.order.toNat = φ.inseparableDegree := by
  rw [φ.order_formalSeries_eq_inseparableDegree, ENat.toNat_natCast]

end TauCeti.Isogeny
