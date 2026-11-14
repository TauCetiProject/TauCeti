/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Tamagawa
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MinimalRealPeriod
-- Proof-only: existence of a reduced global minimal equation over `ℚ` in every variable-change
-- orbit.
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced

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
`WeierstrassCurve.tamagawaProduct` and `∏ᶠ v, φ.finiteKummerRatio v`. Over `ℚ` (`R = ℤ`), the
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
  have hmap : (φ.map (algebraMap ℚ ℝ)).kummerRatio = (φ.baseChange ℝ).kummerRatio :=
    congrArg (fun f : ℚ →+* ℝ ↦ (φ.map f).kummerRatio) (Subsingleton.elim _ _)
  rw [realKummerRatio_def, hmap, kummerRatio_def]
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

omit [CharZero K] in
private theorem hasFiniteMulSupport_cast_tamagawaNumberAt (E : WeierstrassCurve K) [E.IsElliptic] :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦ (E.tamagawaNumberAt v : ℚ)) :=
  (E.hasFiniteMulSupport_tamagawaNumberAt (R := R)).subset fun v hv ↦ by
    rw [Function.mem_mulSupport] at hv ⊢
    exact_mod_cast hv

omit [CharZero K] [E₁.IsElliptic] [E₂.IsElliptic] in
private theorem hasFiniteMulSupport_cast_normalizedAbsoluteValue {x : K} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦
      (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
        (algebraMap K (v.adicCompletion K) x) : ℚ)) :=
  (TauCeti.hasFiniteMulSupport_normalizedAbsoluteValue_algebraMap R hx).subset fun v hv ↦ by
    rw [Function.mem_mulSupport] at hv ⊢
    exact_mod_cast hv

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
  have hf₁ := hasFiniteMulSupport_cast_normalizedAbsoluteValue (R := R) hd
  have hf₂ := hasFiniteMulSupport_cast_tamagawaNumberAt (R := R) E₁
  have hf₃ := φ.hasFiniteMulSupport_finiteKummerRatio (R := R)
    (Nat.cast_ne_zero.mpr φ.degree_ne_zero)
  have hf₁₂ : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦
      (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
        (algebraMap K (v.adicCompletion K) (c * C₂.u / C₁.u)) : ℚ) * E₁.tamagawaNumberAt v) :=
    (hf₁.union hf₂).subset fun v hv ↦ by
      rw [Function.mem_mulSupport] at hv
      by_contra h
      rw [Set.mem_union, Function.mem_mulSupport, Function.mem_mulSupport, not_or, not_not,
        not_not] at h
      exact hv (by rw [h.1, h.2, mul_one])
  rw [← finprod_cast_tamagawaNumberAt (R := R) E₁, ← finprod_cast_tamagawaNumberAt (R := R) E₂,
    ← finprod_mul_distrib hf₁ hf₂, ← finprod_mul_distrib hf₁₂ hf₃]
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
