/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Tamagawa
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MinimalRealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DefectIdeal
public import TauCeti.RingTheory.FractionalIdeal.Norm
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
-- Proof-only: existence of a reduced global minimal equation over `ℚ` in every variable-change
-- orbit, and the finite-place product formula for normalized absolute values.
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ProductFormula

/-!
# The global product formula for local Kummer ratios

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over `ℚ`. At each place of `ℚ`, the local Kummer
ratio `[E₂(ℚ_v) : φ E₁(ℚ_v)] / #E₁(ℚ_v)[φ]` compares the local invariant of `E₂` with that of `E₁`
up to the pullback scalar of the invariant differential:

* At the archimedean place (`TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_realKummerRatio`), if
  `φ^*ω₂ = c ω₁` and changes of variables `C₁`, `C₂` with scaling factors `u₁`, `u₂` carry `E₁`,
  `E₂` to globally minimal equations over `ℤ`, then
  `|c u₂ / u₁| · Ω(E₁) · φ.realKummerRatio = Ω(E₂)`, where `Ω(E)` is
  `WeierstrassCurve.minimalRealPeriod`.
* At each finite prime `v` (`TauCeti.Isogeny.finiteKummerRatio_eq_of_isGlobalMinimal_smul`),
  `|c u₂ / u₁|_v · c_v(E₁) · φ.finiteKummerRatio v = c_v(E₂)`, including at `v = (2)` and at
  primes dividing `deg φ`.

Taking the product over all finite primes of a Dedekind domain `R` with finite quotients and
characteristic-zero fraction field `K` yields a general finite-place relation between
`WeierstrassCurve.tamagawaProduct` and `∏ᶠ v, φ.finiteKummerRatio v`. Without assuming global
minimal equations, and with only `2 ≠ 0` in `K` and `deg φ ≠ 0` in `R`, the choice-free local
formula `TauCeti.Isogeny.finiteKummerRatio_eq_zpow_obstructionExponentAt_mul_tamagawaNumberAt_div`
gives the same relation with the valuation factor `∏ᶠ v, (#(R ⧸ v)) ^ (ord_v c + f_v(E₂) - f_v(E₁))`
in terms of the local obstruction exponents. When `R` is finite and free over `ℤ` and `K` is finite
over `ℚ`, this factor is evaluated through `FractionalIdeal.absNorm`: for integral models
`C₁ • E₁` and `C₂ • E₂` over `R` it is `|Norm_{K/ℚ}(c u₂ / u₁)| · Norm(𝔍₂) / Norm(𝔍₁)`, where `𝔍ᵢ`
is the Weierstrass defect ideal of `Cᵢ • Eᵢ`, and this simplifies to `|Norm_{K/ℚ}(c u₂ / u₁)|` on
globally minimal equations. Over `ℚ` (`R = ℤ`), the
product formula `∏ᶠ v, |d|_v = |d|⁻¹` (`TauCeti.finprod_normalizedAbsoluteValue_rat`) cancels the
real factor `|c u₂ / u₁|` against the finite product of `|c u₂ / u₁|_v`, and
`WeierstrassCurve.exists_smul_eq_reducedMinimalModel` supplies global minimal equations for
arbitrary elliptic curves over `ℚ`. Consequently, for **every** pair of elliptic curves `E₁`, `E₂`
over `ℚ` and **every** isogeny `φ : E₁ → E₂`,

`Ω(E₁) · ∏_v c_v(E₁) · φ.kummerRatioProduct = Ω(E₂) · ∏_v c_v(E₂)`,

independently of any choice of Weierstrass equations or differentials. In particular, every
endomorphism isogeny `φ : E → E` over `ℚ` satisfies `φ.kummerRatioProduct = 1`, and isogenies in
opposite directions have inverse Kummer-ratio products.

No equality between `φ.kummerRatioProduct` and ratios of global Selmer or Shafarevich–Tate groups is
asserted in this file; this file establishes the local-product side of Cassels' isogeny-invariance
calculation.

## Main results

* `TauCeti.Isogeny.abs_mul_realPeriod_mul_kummerRatio` and `TauCeti.Isogeny.kummerRatio_real_eq`:
  over `ℝ`, `|c| · Ω(W₁) · φ.kummerRatio = Ω(W₂)`.
* `TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_realKummerRatio` and
  `TauCeti.Isogeny.realKummerRatio_eq_of_isGlobalMinimal_smul`: over `ℚ`, the archimedean Kummer
  ratio in terms of `minimalRealPeriod`.
* `TauCeti.Isogeny.finprod_normalizedAbsoluteValue_mul_tamagawaProduct_mul_finprod`: over a
  Dedekind domain with finite quotients and characteristic-zero fraction field, the product of
  finite local Kummer ratios against `tamagawaProduct`.
* `finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_obstructionExponentAt_mul` (in
  namespace `TauCeti.Isogeny`): the choice-free finite-place product over a Dedekind domain with
  finite quotients, assuming only `2 ≠ 0` in `K` and `deg φ ≠ 0` in `R`; on globally minimal
  equations it is `finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_mul`.
* `finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul_absNorm_div_mul_of_isIntegral_smul`
  and `TauCeti.Isogeny.finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul`: over a
  number field, the valuation factor via norms and Weierstrass defect ideals of integral models.
* `TauCeti.Isogeny.finprod_finiteKummerRatio_eq_of_isGlobalMinimal_smul` and
  `TauCeti.Isogeny.finprod_finiteKummerRatio_eq_of_isGlobalMinimal`: over `ℚ`,
  `∏ᶠ v, φ.finiteKummerRatio v = |c u₂ / u₁| · c(E₂) / c(E₁)`.
* `TauCeti.Isogeny.minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct` and
  `TauCeti.Isogeny.kummerRatioProduct_eq_div`: **the global product formula for local Kummer ratios
  over `ℚ`**, `Ω(E₁) · c(E₁) · φ.kummerRatioProduct = Ω(E₂) · c(E₂)`.
* `TauCeti.Isogeny.kummerRatioProduct_self` and
  `TauCeti.Isogeny.kummerRatioProduct_mul_kummerRatioProduct`: every self-isogeny over `ℚ` has
  `kummerRatioProduct = 1`, and opposite isogenies have inverse `kummerRatioProduct`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199, §4, equation (4.2).
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), 79–114, §3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5, VIII.8 and X.4.
-/

public section

open IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

private theorem isGlobalMinimal_of_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]
    (h : W = W') (hW' : IsGlobalMinimal R W') : IsGlobalMinimal R W := by
  subst h
  exact hW'

section Real

variable {W₁ W₂ : WeierstrassCurve.Affine ℝ} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The real Kummer ratio and the real period**: if `φ : W₁ → W₂` is an isogeny over `ℝ` with
`φ^*ω₂ = c ω₁`, then `|c| · Ω(W₁) · φ.kummerRatio = Ω(W₂)`. -/
theorem abs_mul_realPeriod_mul_kummerRatio (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    |c| * W₁.realPeriod * (φ.kummerRatio : ℝ) = W₂.realPeriod := by
  have h := abs_mul_realPeriod_mul_index_eq_card_ker_mul φ hc
  have := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  have hker : (Nat.card (Hom.ofIsogeny φ).pointMapHom.ker : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [kummerRatio_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, ← mul_div_assoc,
    div_eq_iff hker, h, mul_comm]

/-- **Explicit formula for the real Kummer ratio**: for `φ : W₁ → W₂` over `ℝ` with
`φ^*ω₂ = c ω₁`, `(φ.kummerRatio : ℝ) = |c|⁻¹ * Ω(W₂) / Ω(W₁)`. -/
theorem kummerRatio_real_eq (φ : Isogeny W₁ W₂) {c : ℝ}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    (φ.kummerRatio : ℝ) = |c|⁻¹ * W₂.realPeriod / W₁.realPeriod := by
  have hc0 : |c| ≠ 0 := abs_ne_zero.mpr (ne_zero_of_pullbackDifferential_eq_smul φ hc)
  have hΩ₁ : W₁.realPeriod ≠ 0 := W₁.realPeriod_pos.ne'
  rw [← abs_mul_realPeriod_mul_kummerRatio φ hc]
  field_simp

end Real

section RationalReal

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **The real Kummer ratio of an isogeny over `ℚ` via global minimal equations**: if `φ^*ω₂ = c ω₁`
and `C₁`, `C₂` carry `E₁`, `E₂` to globally minimal equations over `ℤ`, then
`|c u₂ / u₁| · Ω(E₁) · φ.realKummerRatio = Ω(E₂)`. -/
theorem abs_mul_minimalRealPeriod_mul_realKummerRatio (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ) =
      E₂.minimalRealPeriod := by
  have h := abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul φ hc hC₁ hC₂
  have := (Hom.ofIsogeny (φ.baseChange ℝ)).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have hker : (Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [realKummerRatio_def, ← kummerRatio_baseChange, kummerRatio_def]
  push_cast at h ⊢
  rw [← mul_div_assoc, div_eq_iff hker, h, mul_comm]

/-- **Explicit formula for `realKummerRatio` via global minimal equations**:
`(φ.realKummerRatio : ℝ) = |c u₂ / u₁|⁻¹ * Ω(E₂) / Ω(E₁)`. -/
theorem realKummerRatio_eq_of_isGlobalMinimal_smul (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    (φ.realKummerRatio : ℝ) =
      |((c * C₂.u / C₁.u : ℚ) : ℝ)|⁻¹ * E₂.minimalRealPeriod / E₁.minimalRealPeriod := by
  have hd : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero (ne_zero_of_pullbackDifferential_eq_smul φ hc) C₂.u.ne_zero)
      C₁.u.ne_zero
  have habs : |((c * C₂.u / C₁.u : ℚ) : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hd)
  have hΩ₁ : E₁.minimalRealPeriod ≠ 0 := E₁.minimalRealPeriod_pos.ne'
  rw [← abs_mul_minimalRealPeriod_mul_realKummerRatio φ hc hC₁ hC₂]
  field_simp

/-- **The real Kummer ratio between globally minimal equations over `ℤ`**:
`|c| · Ω(E₁) · φ.realKummerRatio = Ω(E₂)`. -/
theorem abs_mul_minimalRealPeriod_mul_realKummerRatio_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    |(c : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ) = E₂.minimalRealPeriod := by
  simpa using abs_mul_minimalRealPeriod_mul_realKummerRatio φ hc
    (isGlobalMinimal_of_eq (one_smul (VariableChange ℚ) E₁) h₁)
    (isGlobalMinimal_of_eq (one_smul (VariableChange ℚ) E₂) h₂)

/-- **Explicit formula for `realKummerRatio` between globally minimal equations over `ℤ`**:
`(φ.realKummerRatio : ℝ) = |c|⁻¹ * Ω(E₂) / Ω(E₁)`. -/
theorem realKummerRatio_eq_of_isGlobalMinimal (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    (φ.realKummerRatio : ℝ) = |(c : ℝ)|⁻¹ * E₂.minimalRealPeriod / E₁.minimalRealPeriod := by
  simpa using realKummerRatio_eq_of_isGlobalMinimal_smul φ hc
    (isGlobalMinimal_of_eq (one_smul (VariableChange ℚ) E₁) h₁)
    (isGlobalMinimal_of_eq (one_smul (VariableChange ℚ) E₂) h₂)

end RationalReal

section FiniteProduct

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  {K : Type*} [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]

omit [CharZero K] in
private theorem finprod_cast_tamagawaNumberAt (E : WeierstrassCurve K) [E.IsElliptic] :
    (∏ᶠ v : HeightOneSpectrum R, (E.tamagawaNumberAt v : ℚ)) = E.tamagawaProduct (R := R) := by
  rw [E.tamagawaProduct_def]
  exact ((Nat.castRingHom ℚ).toMonoidHom.map_finprod_of_preimage_one
    (fun _ h ↦ Nat.cast_eq_one.mp h) _).symm

/-- **Product of finite local Kummer ratios over a Dedekind domain**: if `C₁ • E₁` and `C₂ • E₂`
are globally minimal over `R` and `φ^*ω₂ = c ω₁`, then multiplying `∏ᶠ v, φ.finiteKummerRatio v` by
`E₁.tamagawaProduct` and `∏ᶠ v, |c u₂ / u₁|_v` gives `E₂.tamagawaProduct`. -/
theorem finprod_normalizedAbsoluteValue_mul_tamagawaProduct_mul_finprod
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange K} (h₁ : IsGlobalMinimal R (C₁ • E₁))
    (h₂ : IsGlobalMinimal R (C₂ • E₂)) :
    (∏ᶠ v : HeightOneSpectrum R,
        (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
          (algebraMap K (v.adicCompletion K) (c * C₂.u / C₁.u)) : ℚ)) *
      E₁.tamagawaProduct (R := R) *
      (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) =
    E₂.tamagawaProduct (R := R) := by
  have hd : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero (ne_zero_of_pullbackDifferential_eq_smul φ hc) C₂.u.ne_zero)
      C₁.u.ne_zero
  have hf₁ : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦
      (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
        (algebraMap K (v.adicCompletion K) (c * C₂.u / C₁.u)) : ℚ)) :=
    (TauCeti.hasFiniteMulSupport_normalizedAbsoluteValue_algebraMap R hd).fun_comp NNRat.cast_one
  have hf₂ : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum R ↦ (E₁.tamagawaNumberAt v : ℚ)) :=
    (E₁.hasFiniteMulSupport_tamagawaNumberAt (R := R)).fun_comp Nat.cast_one
  have hf₃ := φ.hasFiniteMulSupport_finiteKummerRatio (R := R)
    (Nat.cast_ne_zero.mpr φ.degree_ne_zero)
  rw [← finprod_cast_tamagawaNumberAt (R := R) E₁, ← finprod_cast_tamagawaNumberAt (R := R) E₂,
    ← finprod_mul_distrib hf₁ hf₂, ← finprod_mul_distrib (hf₁.fun_mul hf₂) hf₃]
  refine finprod_congr fun v ↦ ?_
  rw [finiteKummerRatio_eq_of_isGlobalMinimal_smul φ hc h₁ h₂ v]
  have hv0 : (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
      (algebraMap K (v.adicCompletion K) (c * C₂.u / C₁.u)) : ℚ) ≠ 0 :=
    NNRat.cast_ne_zero.mpr ((TauCeti.normalizedAbsoluteValue (v.adicCompletion K)).ne_zero_iff.mpr
      ((map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).mpr hd))
  have ht₁ : (E₁.tamagawaNumberAt v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (E₁.tamagawaNumberAt_pos v).ne'
  field_simp

/-- **Product of finite local Kummer ratios on globally minimal equations over `R`.** -/
theorem finprod_normalizedAbsoluteValue_mul_tamagawaProduct_mul_finprod_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal R E₁) (h₂ : IsGlobalMinimal R E₂) :
    (∏ᶠ v : HeightOneSpectrum R,
        (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
          (algebraMap K (v.adicCompletion K) c) : ℚ)) *
      E₁.tamagawaProduct (R := R) *
      (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) =
    E₂.tamagawaProduct (R := R) := by
  simpa using finprod_normalizedAbsoluteValue_mul_tamagawaProduct_mul_finprod φ hc
    (isGlobalMinimal_of_eq (one_smul (VariableChange K) E₁) h₁)
    (isGlobalMinimal_of_eq (one_smul (VariableChange K) E₂) h₂)

end FiniteProduct

section ObstructionProduct

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- For nonzero `c : K` and integral models `D₁ • E₁` and `D₂ • E₂` over `R`, the invertible
fractional ideal `(c · D₂.u / D₁.u) · 𝔍_{D₂ • E₂} · 𝔍_{D₁ • E₁}⁻¹`, whose multiplicity at every
height-one prime `v` is `(v.valuation K).ord c + f_v(E₂) - f_v(E₁)`. -/
private noncomputable def obstructionScalingUnit (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K]
    (E₁ E₂ : WeierstrassCurve K) [E₁.IsElliptic] [E₂.IsElliptic]
    {c : K} (hc0 : c ≠ 0) (D₁ D₂ : VariableChange K)
    [IsIntegral R (D₁ • E₁)] [IsIntegral R (D₂ • E₂)] : (FractionalIdeal R⁰ K)ˣ :=
  toPrincipalIdeal R K
      (Units.mk0 (c * D₂.u / D₁.u) (div_ne_zero (mul_ne_zero hc0 D₂.u.ne_zero) D₁.u.ne_zero)) *
    Units.mk0 (weierstrassDefectIdeal R (D₂ • E₂) : FractionalIdeal R⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr (weierstrassDefectIdeal_ne_bot R (D₂ • E₂))) *
    (Units.mk0 (weierstrassDefectIdeal R (D₁ • E₁) : FractionalIdeal R⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr (weierstrassDefectIdeal_ne_bot R (D₁ • E₁))))⁻¹

private theorem count_obstructionScalingUnit
    (E₁ E₂ : WeierstrassCurve K) [E₁.IsElliptic] [E₂.IsElliptic]
    {c : K} (hc0 : c ≠ 0) (D₁ D₂ : VariableChange K)
    [IsIntegral R (D₁ • E₁)] [IsIntegral R (D₂ • E₂)] (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v
        (obstructionScalingUnit R E₁ E₂ hc0 D₁ D₂ : FractionalIdeal R⁰ K) =
      (v.valuation K).ord c + obstructionExponentAt R v E₂ - obstructionExponentAt R v E₁ := by
  have h₁ : weierstrassDefectIdeal R (D₁ • E₁) ≠ ⊥ := by
    simpa using weierstrassDefectIdeal_ne_bot R (D₁ • E₁)
  have h₂ : weierstrassDefectIdeal R (D₂ • E₂) ≠ ⊥ := by
    simpa using weierstrassDefectIdeal_ne_bot R (D₂ • E₂)
  have hcount (W : WeierstrassCurve K) [W.IsElliptic] [IsIntegral R W] :
      FractionalIdeal.count K v (weierstrassDefectIdeal R W : FractionalIdeal R⁰ K) =
        obstructionExponentAt R v W := by
    rw [FractionalIdeal.count_coeIdeal K v (weierstrassDefectIdeal_ne_bot R W),
      count_weierstrassDefectIdeal_eq_obstructionExponentAt]
  simp [obstructionScalingUnit, FractionalIdeal.count_mul, FractionalIdeal.count_inv,
    FractionalIdeal.count_spanSingleton_eq_neg_log_valuation, hc0, h₁, h₂, hcount,
    ← Valuation.ord_def]
  ring

section HasFiniteQuotients

variable [Ring.HasFiniteQuotients R]
  {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]

/-- If every finite local Kummer ratio is `f v · c_v(E₂) / c_v(E₁)` for a finitely supported `f`,
then `(∏ᶠ v, φ.finiteKummerRatio v) · c(E₁) = (∏ᶠ v, f v) · c(E₂)`. -/
private theorem finprod_finiteKummerRatio_mul_tamagawaProduct_of_forall_eq
    (φ : Isogeny E₁.toAffine E₂.toAffine) (hφK : (φ.degree : K) ≠ 0)
    (f : HeightOneSpectrum R → ℚ) (hf : Function.HasFiniteMulSupport f)
    (h : ∀ v, φ.finiteKummerRatio v = f v * E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v) :
    (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := R) =
      (∏ᶠ v : HeightOneSpectrum R, f v) * E₂.tamagawaProduct (R := R) := by
  have hcast_tam (E : WeierstrassCurve K) [E.IsElliptic] :
      (E.tamagawaProduct (R := R) : ℚ) =
        ∏ᶠ v : HeightOneSpectrum R, (E.tamagawaNumberAt v : ℚ) := by
    rw [E.tamagawaProduct_def]
    exact MonoidHom.map_finprod (Nat.castRingHom ℚ).toMonoidHom
      E.hasFiniteMulSupport_tamagawaNumberAt
  rw [hcast_tam E₁, hcast_tam E₂,
    ← finprod_mul_distrib (φ.hasFiniteMulSupport_finiteKummerRatio hφK)
      (E₁.hasFiniteMulSupport_tamagawaNumberAt.fun_comp Nat.cast_one),
    ← finprod_mul_distrib hf (E₂.hasFiniteMulSupport_tamagawaNumberAt.fun_comp Nat.cast_one)]
  refine finprod_congr fun v ↦ ?_
  rw [h v, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (E₁.tamagawaNumberAt_pos v).ne')]

/-- **Choice-free global finite-place product of Kummer ratios and Tamagawa numbers.** Assume
`Ring.HasFiniteQuotients R`. For any elliptic curves `E₁` and `E₂` over `K` and any isogeny
`φ : E₁ → E₂` with `φ^*ω₂ = c ω₁`, `2 ≠ 0` in `K`, and `deg φ ≠ 0` in `R`, multiplying all finite
local Kummer ratios by `E₁.tamagawaProduct` yields `E₂.tamagawaProduct` times the product over `v`
of `(#(R ⧸ v)) ^ (ord_v c + f_v(E₂) - f_v(E₁))`. No global minimal equation is assumed. -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_obstructionExponentAt_mul
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := R) =
      (∏ᶠ v : HeightOneSpectrum R,
        (Nat.card (R ⧸ v.asIdeal) : ℚ) ^
          ((v.valuation K).ord c + obstructionExponentAt R v E₂ - obstructionExponentAt R v E₁)) *
        E₂.tamagawaProduct (R := R) := by
  have hφK : (φ.degree : K) ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hφ
  have hc0 : c ≠ 0 := φ.ne_zero_of_pullbackDifferential_eq_smul_of_degree_ne_zero hc hφK
  obtain ⟨D₁, hD₁⟩ := exists_smul_isIntegral R E₁
  obtain ⟨D₂, hD₂⟩ := exists_smul_isIntegral R E₂
  refine finprod_finiteKummerRatio_mul_tamagawaProduct_of_forall_eq φ hφK _ ?_
    fun v ↦ finiteKummerRatio_eq_zpow_obstructionExponentAt_mul_tamagawaNumberAt_div φ v hc h2 hφ
  simp_rw [← count_obstructionScalingUnit E₁ E₂ hc0 D₁ D₂]
  exact FractionalIdeal.hasFiniteMulSupport_zpow_count _ _

/-- **Global finite-place product of Kummer ratios and Tamagawa numbers via global minimal
equations.** Assume `Ring.HasFiniteQuotients R`, `2 ≠ 0` in `K`, and `deg φ ≠ 0` in `R` (so `K` may
have positive characteristic). When `φ^*ω₂ = c ω₁` and `C₁ • E₁` and `C₂ • E₂` are globally minimal
over `R`, multiplying all finite local Kummer ratios by the Tamagawa product of `E₁` yields the
Tamagawa product of `E₂` times the product of the prime-norm powers of `c · C₂.u / C₁.u`. -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_mul
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange K} (hC₁ : IsGlobalMinimal R (C₁ • E₁))
    (hC₂ : IsGlobalMinimal R (C₂ • E₂))
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := R) =
      (∏ᶠ v : HeightOneSpectrum R,
        (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation K (c * C₂.u / C₁.u)))) *
        E₂.tamagawaProduct (R := R) := by
  have hφK : (φ.degree : K) ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hφ
  refine finprod_finiteKummerRatio_mul_tamagawaProduct_of_forall_eq φ hφK _
    (HeightOneSpectrum.hasFiniteMulSupport_zpow_neg_log_valuation _ _) fun v ↦ ?_
  have _ := hC₁.isMinimal v
  have _ := hC₂.isMinimal v
  exact finiteKummerRatio_eq_zpow_mul_tamagawaNumberAt_div φ v hc C₁ C₂ h2 hφ

/-- **Global finite-place product of Kummer ratios and Tamagawa numbers between global minimal
equations.** Assume `Ring.HasFiniteQuotients R`, `2 ≠ 0` in `K`, and `deg φ ≠ 0` in `R`, with
`φ^*ω₂ = c ω₁` and `E₁`, `E₂` globally minimal over `R`. -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_mul_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal R E₁) (h₂ : IsGlobalMinimal R E₂)
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := R) =
      (∏ᶠ v : HeightOneSpectrum R,
        (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation K c))) *
        E₂.tamagawaProduct (R := R) := by
  simpa [VariableChange.one_def] using
    finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_mul φ hc
      (isGlobalMinimal_of_eq (one_smul (VariableChange K) E₁) h₁)
      (isGlobalMinimal_of_eq (one_smul (VariableChange K) E₂) h₂) h2 hφ

end HasFiniteQuotients

section NumberFieldNorm

variable [Module.Free ℤ R] [Module.Finite ℤ R] [Algebra ℚ K] [Module.Finite ℚ K]
  {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]

local instance : Ring.HasFiniteQuotients R := .of_module_finite ℤ R

/-- **The finite-place Kummer/Tamagawa identity on integral models over a number field.** Let `R` be
a Dedekind domain finite and free over `ℤ` with fraction field `K` finite over `ℚ`. If `C₁ • E₁` and
`C₂ • E₂` are integral over `R` and `φ^*ω₂ = c ω₁`, then
`(∏_v φ.finiteKummerRatio v) · E₁.tamagawaProduct =
  (|Norm_{K/ℚ}(c · C₂.u / C₁.u)| · Norm(𝔍_{C₂ • E₂}) / Norm(𝔍_{C₁ • E₁})) · E₂.tamagawaProduct`. -/
theorem
    finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul_absNorm_div_mul_of_isIntegral_smul
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (C₁ C₂ : VariableChange K) [IsIntegral R (C₁ • E₁)] [IsIntegral R (C₂ • E₂)] :
    (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := R) =
      (|Algebra.norm ℚ (c * C₂.u / C₁.u)| *
        (Ideal.absNorm (weierstrassDefectIdeal R (C₂ • E₂)) : ℚ) /
        Ideal.absNorm (weierstrassDefectIdeal R (C₁ • E₁))) *
        E₂.tamagawaProduct (R := R) := by
  have _ : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hφK : (φ.degree : K) ≠ 0 := Nat.cast_ne_zero.mpr φ.degree_pos.ne'
  have hφ : (φ.degree : R) ≠ 0 := by
    intro h0
    exact hφK (by rw [← map_natCast (algebraMap R K), h0, map_zero])
  have hc0 : c ≠ 0 := φ.ne_zero_of_pullbackDifferential_eq_smul hc
  rw [finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_obstructionExponentAt_mul
    φ hc h2 hφ]
  congr 1
  simp_rw [← count_obstructionScalingUnit E₁ E₂ hc0 C₁ C₂]
  rw [FractionalIdeal.finprod_zpow_count_units_eq_absNorm
    (obstructionScalingUnit R E₁ E₂ hc0 C₁ C₂)]
  simp [obstructionScalingUnit, FractionalIdeal.coeIdeal_absNorm, div_eq_mul_inv, Algebra.norm_inv]

/-- **The finite-place Kummer/Tamagawa identity between equations integral over `R`.** Here `R` is a
Dedekind domain finite and free over `ℤ`, `K` is finite over `ℚ`, `E₁` and `E₂` are integral over
`R`, and `φ^*ω₂ = c ω₁`. -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul_absNorm_div_mul_of_isIntegral
    (φ : Isogeny E₁.toAffine E₂.toAffine) [IsIntegral R E₁] [IsIntegral R E₂] {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine) :
    (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := R) =
      (|Algebra.norm ℚ c| * (Ideal.absNorm (weierstrassDefectIdeal R E₂) : ℚ) /
        Ideal.absNorm (weierstrassDefectIdeal R E₁)) *
        E₂.tamagawaProduct (R := R) := by
  have _ : IsIntegral R ((1 : VariableChange K) • E₁) := by
    simpa only [one_smul] using (inferInstance : IsIntegral R E₁)
  have _ : IsIntegral R ((1 : VariableChange K) • E₂) := by
    simpa only [one_smul] using (inferInstance : IsIntegral R E₂)
  have h :=
    finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul_absNorm_div_mul_of_isIntegral_smul
      (R := R) φ hc 1 1
  have h₁ : weierstrassDefectIdeal R ((1 : VariableChange K) • E₁) = weierstrassDefectIdeal R E₁ :=
    by congr! 1; exact one_smul _ _
  have h₂ : weierstrassDefectIdeal R ((1 : VariableChange K) • E₂) = weierstrassDefectIdeal R E₂ :=
    by congr! 1; exact one_smul _ _
  rw [h₁, h₂] at h
  simpa [VariableChange.one_def] using h

/-- **The finite-place Kummer/Tamagawa identity evaluated via the norm to `ℚ`.** Let `R` be a
Dedekind domain finite and free over `ℤ` with fraction field `K` finite over `ℚ`. If `C₁ • E₁` and
`C₂ • E₂` are globally minimal over `R` and `φ^*ω₂ = c ω₁`, then
`(∏_v φ.finiteKummerRatio v) · E₁.tamagawaProduct = |Norm_{K/ℚ}(c · C₂.u / C₁.u)| ·
  E₂.tamagawaProduct`. -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange K} (hC₁ : IsGlobalMinimal R (C₁ • E₁))
    (hC₂ : IsGlobalMinimal R (C₂ • E₂)) :
    (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := R) =
      |Algebra.norm ℚ (c * C₂.u / C₁.u)| * E₂.tamagawaProduct (R := R) := by
  have _ := hC₁.isIntegral
  have _ := hC₂.isIntegral
  rw [
    finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul_absNorm_div_mul_of_isIntegral_smul
      φ hc C₁ C₂,
    (weierstrassDefectIdeal_eq_top_iff_isGlobalMinimal (C₁ • E₁)).mpr hC₁,
    (weierstrassDefectIdeal_eq_top_iff_isGlobalMinimal (C₂ • E₂)).mpr hC₂,
    Ideal.absNorm_top]
  simp

/-- **The finite-place Kummer/Tamagawa identity between global minimal equations.** Let `R` be a
Dedekind domain finite and free over `ℤ` with fraction field `K` finite over `ℚ`. If `E₁` and `E₂`
are globally minimal over `R` and `φ^*ω₂ = c ω₁`, then
`(∏_v φ.finiteKummerRatio v) · E₁.tamagawaProduct = |Norm_{K/ℚ}(c)| · E₂.tamagawaProduct`. -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal R E₁) (h₂ : IsGlobalMinimal R E₂) :
    (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := R) =
      |Algebra.norm ℚ c| * E₂.tamagawaProduct (R := R) := by
  simpa [VariableChange.one_def] using
    finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul φ hc
      (isGlobalMinimal_of_eq (one_smul (VariableChange K) E₁) h₁)
      (isGlobalMinimal_of_eq (one_smul (VariableChange K) E₂) h₂)

end NumberFieldNorm

end ObstructionProduct

section GlobalProduct

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **Product of finite local Kummer ratios over `ℚ` via global minimal equations**: if
`φ^*ω₂ = c ω₁` and `C₁ • E₁`, `C₂ • E₂` are globally minimal over `ℤ`, then
`∏ᶠ v, φ.finiteKummerRatio v = |c u₂ / u₁| · c(E₂) / c(E₁)`. -/
theorem finprod_finiteKummerRatio_eq_of_isGlobalMinimal_smul
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) =
      |c * C₂.u / C₁.u| * E₂.tamagawaProduct (R := ℤ) / E₁.tamagawaProduct (R := ℤ) := by
  have hd : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero (ne_zero_of_pullbackDifferential_eq_smul φ hc) C₂.u.ne_zero)
      C₁.u.ne_zero
  have hprod := finprod_normalizedAbsoluteValue_mul_tamagawaProduct_mul_finprod φ hc hC₁ hC₂
  have hrat := TauCeti.finprod_normalizedAbsoluteValue_rat hd
  simp only [eq_ratCast] at hprod hrat
  rw [hrat] at hprod
  have habs : |c * C₂.u / C₁.u| ≠ 0 := abs_ne_zero.mpr hd
  have ht₁ : (E₁.tamagawaProduct (R := ℤ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (E₁.tamagawaProduct_pos (R := ℤ)).ne'
  rw [← hprod]
  field_simp

/-- **Product of finite local Kummer ratios over `ℚ` between globally minimal equations**:
`∏ᶠ v, φ.finiteKummerRatio v = |c| · c(E₂) / c(E₁)`. -/
theorem finprod_finiteKummerRatio_eq_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) =
      |c| * E₂.tamagawaProduct (R := ℤ) / E₁.tamagawaProduct (R := ℤ) := by
  simpa using finprod_finiteKummerRatio_eq_of_isGlobalMinimal_smul φ hc
    (isGlobalMinimal_of_eq (one_smul (VariableChange ℚ) E₁) h₁)
    (isGlobalMinimal_of_eq (one_smul (VariableChange ℚ) E₂) h₂)

/-- **The global product formula for local Kummer ratios over `ℚ`** (Cassels, 1965): for arbitrary
elliptic curves `E₁`, `E₂` over `ℚ` and every isogeny `φ : E₁ → E₂`,
`Ω(E₁) · c(E₁) · φ.kummerRatioProduct = Ω(E₂) · c(E₂)`, where `Ω(E)` is the minimal real period and
`c(E) = ∏_v c_v(E)` is the global Tamagawa product. -/
theorem minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct
    (φ : Isogeny E₁.toAffine E₂.toAffine) :
    E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) * φ.kummerRatioProduct =
      E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  obtain ⟨C₁, hC₁⟩ := exists_smul_eq_reducedMinimalModel E₁
  obtain ⟨C₂, hC₂⟩ := exists_smul_eq_reducedMinimalModel E₂
  have hmin₁ := isGlobalMinimal_of_eq hC₁ (isReducedMinimal_reducedMinimalModel E₁).isGlobalMinimal
  have hmin₂ := isGlobalMinimal_of_eq hC₂ (isReducedMinimal_reducedMinimalModel E₂).isGlobalMinimal
  have hd : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero (ne_zero_of_pullbackDifferential_eq_smul φ hc) C₂.u.ne_zero)
      C₁.u.ne_zero
  have habs : |((c * C₂.u / C₁.u : ℚ) : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hd)
  have hΩ₁ : E₁.minimalRealPeriod ≠ 0 := E₁.minimalRealPeriod_pos.ne'
  have ht₁ : (E₁.tamagawaProduct (R := ℤ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (E₁.tamagawaProduct_pos (R := ℤ)).ne'
  rw [kummerRatioProduct_def, Rat.cast_mul,
    realKummerRatio_eq_of_isGlobalMinimal_smul φ hc hmin₁ hmin₂,
    finprod_finiteKummerRatio_eq_of_isGlobalMinimal_smul φ hc hmin₁ hmin₂]
  push_cast at habs ⊢
  field_simp

/-- **Explicit ratio form of the global product formula for local Kummer ratios over `ℚ`**:
`(φ.kummerRatioProduct : ℝ) = (Ω(E₂) · c(E₂)) / (Ω(E₁) · c(E₁))`. -/
theorem kummerRatioProduct_eq_div (φ : Isogeny E₁.toAffine E₂.toAffine) :
    (φ.kummerRatioProduct : ℝ) =
      E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) /
        (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ)) := by
  have hΩ₁ : E₁.minimalRealPeriod ≠ 0 := E₁.minimalRealPeriod_pos.ne'
  have ht₁ : (E₁.tamagawaProduct (R := ℤ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (E₁.tamagawaProduct_pos (R := ℤ)).ne'
  rw [← minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct φ]
  field_simp

/-- **Every endomorphism isogeny of an elliptic curve over `ℚ` has Kummer-ratio product equal to
one**: in particular, multiplication-by-`n` satisfies `([n]).kummerRatioProduct = 1`. -/
theorem kummerRatioProduct_self {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (φ : Isogeny E.toAffine E.toAffine) :
    φ.kummerRatioProduct = 1 := by
  have hpos : E.minimalRealPeriod * E.tamagawaProduct (R := ℤ) ≠ 0 :=
    mul_ne_zero E.minimalRealPeriod_pos.ne'
      (Nat.cast_ne_zero.mpr (E.tamagawaProduct_pos (R := ℤ)).ne')
  have h : (φ.kummerRatioProduct : ℝ) = 1 :=
    mul_left_cancel₀ hpos
      ((minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct φ).trans (mul_one _).symm)
  exact_mod_cast h

/-- **Opposite isogenies over `ℚ` have inverse Kummer-ratio products**: for any `φ : E₁ → E₂` and
`ψ : E₂ → E₁` (for instance, `ψ = φ.dual`), `ψ.kummerRatioProduct * φ.kummerRatioProduct = 1`. -/
theorem kummerRatioProduct_mul_kummerRatioProduct (ψ : Isogeny E₂.toAffine E₁.toAffine)
    (φ : Isogeny E₁.toAffine E₂.toAffine) :
    ψ.kummerRatioProduct * φ.kummerRatioProduct = 1 := by
  rw [← kummerRatioProduct_comp, kummerRatioProduct_self]

end GlobalProduct

end TauCeti.Isogeny

end
