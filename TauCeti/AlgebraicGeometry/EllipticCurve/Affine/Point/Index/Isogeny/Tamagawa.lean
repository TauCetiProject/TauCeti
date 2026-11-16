/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Ratio
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DefectIdeal
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.RealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Index
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MinimalRealPeriod
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AdicCompletion
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GlobalExistence
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny
import TauCeti.RingTheory.FractionalIdeal.Norm

/-!
# Local Kummer ratios, Tamagawa numbers, and the real period under an isogeny

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over the fraction field `K` of a Dedekind
domain `R`, pulling the invariant differential back as `φ^*ω₂ = c ω₁`. At a height-one prime `v` of
`R` with finite residue field `κ(v) = R ⧸ v`, if `2 ≠ 0` in `K_v` and `deg φ ≠ 0` in `R`, comparing
`φ` on deep formal-group subgroups with the filtration index formula on minimal equations expresses
the completed local Kummer ratio `[E₂(K_v) : φ E₁(K_v)] / #E₁(K_v)[φ]` in terms of the differential
scaling factor on `v`-minimal models (or the local obstruction exponents `f_v(Eᵢ)`) and the local
Tamagawa numbers:

`z_v(φ) = (#κ(v)) ^ ord_v(c · u₂ / u₁) · c_v(E₂) / c_v(E₁)`
`       = (#κ(v)) ^ (ord_v(c) + f_v(E₂) - f_v(E₁)) · c_v(E₂) / c_v(E₁)`.

The common nonsingular reduced point count `#E_ns(κ(v))` cancels between the two minimal models
(`TauCeti.Isogeny.natCard_point_reduction_eq`), including at bad reduction and at places dividing
`deg φ`.

When `R` is finite and free over `ℤ` with fraction field `K` finite over `ℚ`, taking the product
over all finite places for integral models `C₁ • E₁` and `C₂ • E₂` over `R` evaluates the valuation
factor via `FractionalIdeal.absNorm` to
`|Norm_{K/ℚ}(c · u₂ / u₁)| · Norm(𝔍_{C₂ • E₂}) / Norm(𝔍_{C₁ • E₁})`, simplifying to
`|Norm_{K/ℚ}(c · u₂ / u₁)|` when `C₁ • E₁` and `C₂ • E₂` are globally minimal over `R`.

Over `ℚ`, every elliptic curve admits a globally minimal equation over `ℤ`, and combining the
finite-place product with the transformation of `realPeriod` over `ℝ`
(`TauCeti.Isogeny.kummerRatio_mul_abs_mul_realPeriod_eq`) and `minimalRealPeriod` over `ℚ` cancels
`|c · u₂ / u₁|` between the archimedean and nonarchimedean places to yield the choice-free identity

`φ.kummerRatioProduct * E₁.minimalRealPeriod * E₁.tamagawaProduct =
  E₂.minimalRealPeriod * E₂.tamagawaProduct`.

## Main results

* `TauCeti.Isogeny.kummerRatio_eq_zpow_mul_tamagawaNumber_div_of_isMinimal` and
  `TauCeti.Isogeny.kummerRatio_eq_zpow_mul_tamagawaNumber_div`: the local Kummer ratio over an adic
  completion `F_u` in terms of `Valued.v` and local Tamagawa numbers.
* `TauCeti.Isogeny.finiteKummerRatio_eq_zpow_mul_tamagawaNumberAt_div` and
  `TauCeti.Isogeny.finiteKummerRatio_eq_zpow_obstructionExponentAt_mul_tamagawaNumberAt_div`: the
  finite-place formula at `v : HeightOneSpectrum R` in terms of `v`-minimal models or
  `obstructionExponentAt`.
* The Dedekind-domain finite-place product formulas (in `namespace TauCeti.Isogeny`)
  `finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_obstructionExponentAt_mul` and
  `finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_mul`.
* Evaluation of the finite-place product via norms and defect ideals over a number field:
  `finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul_absNorm_div_mul_of_isIntegral_smul`
  and `finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul_absNorm_div_mul_of_isIntegral`,
  specialising to `TauCeti.Isogeny.finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul`.
* `TauCeti.Isogeny.realKummerRatio_mul_abs_mul_minimalRealPeriod_eq`: the archimedean Kummer-ratio
  period identity for `minimalRealPeriod` over `ℚ`.
* `TauCeti.Isogeny.kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct`: over `ℚ`, the
  product of local Kummer ratios across all places equals the ratio of `minimalRealPeriod *
  tamagawaProduct`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199, Lemma 3.1 and §4.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), §3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5, VII.6, and X.4.
-/

public section

open Filter IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ValuativeRel
open WeierstrassCurve WeierstrassCurve.Affine
open scoped nonZeroDivisors WithZero

namespace TauCeti.Isogeny

private theorem natCast_ne_zero_of_injective {S T : Type*} [NonAssocSemiring S]
    [NonAssocSemiring T] {f : S →+* T} (hf : Function.Injective f) {n : ℕ} (hn : (n : S) ≠ 0) :
    (n : T) ≠ 0 := by
  simpa using hf.ne hn

private theorem div_eq_zpow_sub_mul_div_of_mul_eq {a b q m c₁ c₂ k j : ℕ}
    (hb : b ≠ 0) (hq : q ≠ 0) (hm : m ≠ 0) (hc₁ : c₁ ≠ 0)
    (h : a * (q ^ k * m * c₁) = (q ^ j * m * c₂) * b) :
    (a : ℚ) / b = (q : ℚ) ^ ((j : ℤ) - k) * c₂ / c₁ := by
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hc₁' : (c₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc₁
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have hrat : (a : ℚ) * ((q : ℚ) ^ k * m * c₁) = ((q : ℚ) ^ j * m * c₂) * b := by
    exact_mod_cast h
  rw [zpow_sub₀ hq', zpow_natCast, zpow_natCast]
  field_simp
  apply mul_right_cancel₀ hm'
  linear_combination hrat

/-! ### Completed local formula -/

section Local

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "R_u" =>
  Valuation.valuationSubring
    (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))

-- `O_u = u.adicCompletionIntegers F` is definitionally `R_u = Valued.v.valuationSubring`.
private local instance : HenselianLocalRing R_u :=
  inferInstanceAs (HenselianLocalRing O_u)

private local instance : Finite (IsLocalRing.ResidueField R_u) :=
  Finite.of_equiv _ (u.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv

/-- **The local Kummer ratio on minimal equations over an adic completion.** Assume
`Finite (A ⧸ u.asIdeal)`. Let `W₁` and `W₂` be elliptic equations over `F_u` minimal over `O_u`,
and let `φ : W₁ → W₂` pull back the invariant differential as `φ^*ω₂ = c ω₁`, with `2 ≠ 0` in `F_u`
and `deg φ ≠ 0` in `A`. Then
`φ.kummerRatio = (#(A ⧸ u)) ^ (-log (v c)) · c_u(W₂) / c_u(W₁)`. -/
theorem kummerRatio_eq_zpow_mul_tamagawaNumber_div_of_isMinimal
    {W₁ W₂ : WeierstrassCurve F_u} [W₁.IsElliptic] [W₂.IsElliptic]
    [IsMinimal O_u W₁] [IsMinimal O_u W₂]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    φ.kummerRatio =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ (-WithZero.log (Valued.v c)) *
        W₂.tamagawaNumber (Valued.v : Valuation F_u ℤᵐ⁰) /
        W₁.tamagawaNumber (Valued.v : Valuation F_u ℤᵐ⁰) := by
  classical
  obtain ⟨C₁, rfl⟩ := (inferInstance : IsIntegral O_u W₁).integral
  obtain ⟨C₂, rfl⟩ := (inferInstance : IsIntegral O_u W₂).integral
  have hdeg_ne : (φ.degree : F_u) ≠ 0 :=
    natCast_ne_zero_of_injective (RingHom.injective (algebraMap F F_u))
      (natCast_ne_zero_of_injective (IsFractionRing.injective A F) hn)
  have hc0 : c ≠ 0 := φ.ne_zero_of_pullbackDifferential_eq_smul_of_degree_ne_zero hdeg_ne hc
  have hvc : Valued.v c ≠ 0 := (Valued.v : Valuation F_u ℤᵐ⁰).ne_zero_iff.mpr hc0
  -- Choose a deep formal level `k₀ + 1` with `j₀ = k₀ - log (v c) ≥ 0`.
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_index_range_pointMapHom_mul_index_formalPointFiltration u hc h2 hn)
  let k₀ : ℕ := N + (WithZero.log (Valued.v c)).natAbs
  let j₀ : ℕ := ((k₀ : ℤ) - WithZero.log (Valued.v c)).toNat
  have hj₀_int : (j₀ : ℤ) = (k₀ : ℤ) - WithZero.log (Valued.v c) := by
    dsimp [j₀, k₀]
    omega
  have hjk : Valued.v c * WithZero.exp ((j₀ + 1 : ℕ) : ℤ) =
      WithZero.exp ((k₀ + 1 : ℕ) : ℤ) := by
    rw [← WithZero.exp_log hvc, ← WithZero.exp_add, WithZero.exp_inj]
    push_cast
    omega
  have hdeep := hN (k₀ + 1) (by dsimp [k₀]; omega) (j₀ + 1) hjk
  rw [C₁.index_formalPointFiltration_eq_mul_tamagawaNumber u k₀,
    C₂.index_formalPointFiltration_eq_mul_tamagawaNumber u j₀] at hdeep
  -- Identify the residue cardinality and the reduced point counts on the two minimal models.
  have hq : Nat.card (IsLocalRing.ResidueField O_u) = Nat.card (A ⧸ u.asIdeal) :=
    Nat.card_congr (u.residueFieldEquivAdicCompletionIntegers (K := F)).symm.toEquiv
  have _ : IsMinimal 𝒪[F_u] (C₁.baseChange F_u) :=
    (isMinimal_integer_adicCompletion_iff u (C₁.baseChange F_u)).mpr inferInstance
  have _ : IsMinimal 𝒪[F_u] (C₂.baseChange F_u) :=
    (isMinimal_integer_adicCompletion_iff u (C₂.baseChange F_u)).mpr inferInstance
  have hred_eq :
      Nat.card ((integralModel R_u (C₁.baseChange F_u)).map
          (IsLocalRing.residue R_u)).toAffine.Point =
        Nat.card ((integralModel R_u (C₂.baseChange F_u)).map
          (IsLocalRing.residue R_u)).toAffine.Point :=
    (C₁.natCard_point_reduction_baseChange_adicCompletion).symm.trans
      (φ.natCard_point_reduction_eq.trans
        C₂.natCard_point_reduction_baseChange_adicCompletion)
  rw [hq, hred_eq] at hdeep
  have _ := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  have hsub : (j₀ : ℤ) - k₀ = -WithZero.log (Valued.v c) := by omega
  rw [kummerRatio_def,
    div_eq_zpow_sub_mul_div_of_mul_eq Nat.card_pos.ne' Nat.card_pos.ne' Nat.card_pos.ne'
      (tamagawaNumber_pos _ _).ne' hdeep,
    hsub]

/-- **The local Kummer ratio on arbitrary equations over an adic completion.** Assume
`Finite (A ⧸ u.asIdeal)`, `2 ≠ 0` in `F_u`, and `deg φ ≠ 0` in `A`. If `C₁` and `C₂` carry `E₁` and
`E₂` to equations minimal over `O_u`, and `φ^*ω₂ = c ω₁`, then
`φ.kummerRatio = (#(A ⧸ u)) ^ (-log (v (c · C₂.u / C₁.u))) · c_u(E₂) / c_u(E₁)`. -/
theorem kummerRatio_eq_zpow_mul_tamagawaNumber_div
    {E₁ E₂ : WeierstrassCurve F_u} [E₁.IsElliptic] [E₂.IsElliptic]
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (C₁ C₂ : VariableChange F_u) [IsMinimal O_u (C₁ • E₁)] [IsMinimal O_u (C₂ • E₂)]
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    φ.kummerRatio =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ (-WithZero.log (Valued.v (c * C₂.u / C₁.u))) *
        E₂.tamagawaNumber (Valued.v : Valuation F_u ℤᵐ⁰) /
        E₁.tamagawaNumber (Valued.v : Valuation F_u ℤᵐ⁰) := by
  rw [← φ.kummerRatio_conjByVariableChange C₁ C₂,
    kummerRatio_eq_zpow_mul_tamagawaNumber_div_of_isMinimal u (φ.conjByVariableChange C₁ C₂)
      (φ.pullbackDifferential_conjByVariableChange_invariantDifferential hc C₁ C₂) h2
      (by rwa [degree_conjByVariableChange]),
    tamagawaNumber_smul, tamagawaNumber_smul]

end Local

/-! ### Finite places of a global Dedekind domain -/

section FinitePlaces

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

private theorem neg_log_valuation_mul_div (v : HeightOneSpectrum R) {c : K} (hc0 : c ≠ 0)
    (C₁ C₂ : VariableChange K) :
    -WithZero.log (v.valuation K (c * C₂.u / C₁.u)) =
      (v.valuation K).ord c + (v.valuation K).ord (C₂.u : K) -
        (v.valuation K).ord (C₁.u : K) := by
  rw [← Valuation.ord_def, Valuation.ord_div _ (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero,
    Valuation.ord_mul _ ((v.valuation K).ne_zero_iff.mpr hc0)
      ((v.valuation K).ne_zero_iff.mpr C₂.u.ne_zero)]

private theorem neg_log_valuation_mul_div_eq_ord_add_obstructionExponentAt
    (E₁ E₂ : WeierstrassCurve K) [E₁.IsElliptic] [E₂.IsElliptic]
    (v : HeightOneSpectrum R) {c : K} (hc0 : c ≠ 0) (C₁ C₂ : VariableChange K)
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • E₁)]
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • E₂)] :
    -WithZero.log (v.valuation K (c * C₂.u / C₁.u)) =
      (v.valuation K).ord c + obstructionExponentAt R v E₂ - obstructionExponentAt R v E₁ := by
  have hf₁ : obstructionExponentAt R v (C₁ • E₁) = 0 :=
    (obstructionExponentAt_eq_zero_iff_isMinimal R v (C₁ • E₁)).mpr inferInstance
  have hf₂ : obstructionExponentAt R v (C₂ • E₂) = 0 :=
    (obstructionExponentAt_eq_zero_iff_isMinimal R v (C₂ • E₂)).mpr inferInstance
  rw [obstructionExponentAt_smul] at hf₁ hf₂
  rw [neg_log_valuation_mul_div v hc0 C₁ C₂]
  omega

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

/-- **The finite local Kummer ratio in terms of local Tamagawa numbers.** Assume
`Ring.HasFiniteQuotients R`. Let `φ : E₁ → E₂` pull back the invariant differential as
`φ^*ω₂ = c ω₁`, with `2 ≠ 0` in `K` and `deg φ ≠ 0` in `R`. If `C₁` and `C₂` carry `E₁` and `E₂` to
equations minimal at `v`, then
`φ.finiteKummerRatio v = (#(R ⧸ v)) ^ (-log (v (c · C₂.u / C₁.u))) · c_v(E₂) / c_v(E₁)`. -/
theorem finiteKummerRatio_eq_zpow_mul_tamagawaNumberAt_div
    (φ : Isogeny E₁.toAffine E₂.toAffine) (v : HeightOneSpectrum R) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (C₁ C₂ : VariableChange K)
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • E₁)]
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • E₂)]
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    φ.finiteKummerRatio v =
      (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation K (c * C₂.u / C₁.u))) *
        E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v := by
  have : Finite (R ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have _ : IsMinimal (v.adicCompletionIntegers K)
      (C₁.baseChange (v.adicCompletion K) • E₁.baseChange (v.adicCompletion K)) := by
    rw [baseChange_smul_baseChange]
    exact (isMinimal_baseChange_adicCompletionIntegers_iff v (C₁ • E₁)).mpr inferInstance
  have _ : IsMinimal (v.adicCompletionIntegers K)
      (C₂.baseChange (v.adicCompletion K) • E₂.baseChange (v.adicCompletion K)) := by
    rw [baseChange_smul_baseChange]
    exact (isMinimal_baseChange_adicCompletionIntegers_iff v (C₂ • E₂)).mpr inferInstance
  have h2_comp : (2 : v.adicCompletion K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]
    exact (RingHom.injective _).ne h2
  have hφ_deg : ((φ.baseChange (v.adicCompletion K)).degree : R) ≠ 0 := by
    have hdeg_eq : (φ.baseChange (v.adicCompletion K)).degree = φ.degree :=
      degree_map φ (algebraMap K (v.adicCompletion K))
    rwa [hdeg_eq]
  have hφ_diff : (φ.baseChange (v.adicCompletion K)).pullbackDifferential
      (invariantDifferential (E₂.baseChange (v.adicCompletion K)).toAffine) =
      algebraMap K (v.adicCompletion K) c •
        invariantDifferential (E₁.baseChange (v.adicCompletion K)).toAffine :=
    map_pullbackDifferential_invariantDifferential_eq_smul φ (algebraMap K (v.adicCompletion K)) hc
  have hval : Valued.v (algebraMap K (v.adicCompletion K) c *
      (C₂.baseChange (v.adicCompletion K)).u / (C₁.baseChange (v.adicCompletion K)).u) =
      v.valuation K (c * C₂.u / C₁.u) := by
    simp [VariableChange.baseChange, algebraMap_adicCompletion]
  -- `Valuation.valuationSubring` coerces definitionally to `Valuation.integer`, i.e. `𝒪[K_v]`.
  have _ : IsDiscreteValuationRing (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring :=
    inferInstanceAs (IsDiscreteValuationRing 𝒪[v.adicCompletion K])
  have hequiv : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsEquiv
      (ValuativeRel.valuation (v.adicCompletion K)) :=
    (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).symm
  have hdef : φ.finiteKummerRatio v = (φ.baseChange (v.adicCompletion K)).kummerRatio :=
    finiteKummerRatio_def φ v
  rw [hdef,
    kummerRatio_eq_zpow_mul_tamagawaNumber_div v (φ.baseChange (v.adicCompletion K)) hφ_diff
      (C₁.baseChange (v.adicCompletion K)) (C₂.baseChange (v.adicCompletion K)) h2_comp hφ_deg,
    hval, tamagawaNumber_congr _ hequiv, tamagawaNumber_congr _ hequiv,
    ← tamagawaNumberAt_def, ← tamagawaNumberAt_def]

/-- **The finite local Kummer ratio on `v`-minimal equations.** Assume `Ring.HasFiniteQuotients R`.
If `E₁` and `E₂` are minimal at `v`, `φ^*ω₂ = c ω₁`, `2 ≠ 0` in `K`, and `deg φ ≠ 0` in `R`, then
`φ.finiteKummerRatio v = (#(R ⧸ v)) ^ (-log (v c)) · c_v(E₂) / c_v(E₁)`. -/
theorem finiteKummerRatio_eq_zpow_mul_tamagawaNumberAt_div_of_isMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) (v : HeightOneSpectrum R)
    [IsMinimal (Localization.AtPrime v.asIdeal) E₁]
    [IsMinimal (Localization.AtPrime v.asIdeal) E₂]
    {c : K} (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    φ.finiteKummerRatio v =
      (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation K c)) *
        E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v := by
  have _ : IsMinimal (Localization.AtPrime v.asIdeal) ((1 : VariableChange K) • E₁) := by
    simpa only [one_smul] using (inferInstance : IsMinimal (Localization.AtPrime v.asIdeal) E₁)
  have _ : IsMinimal (Localization.AtPrime v.asIdeal) ((1 : VariableChange K) • E₂) := by
    simpa only [one_smul] using (inferInstance : IsMinimal (Localization.AtPrime v.asIdeal) E₂)
  simpa [VariableChange.one_def] using
    finiteKummerRatio_eq_zpow_mul_tamagawaNumberAt_div φ v hc 1 1 h2 hφ

/-- **Choice-free local Kummer/Tamagawa formula at a finite place.** Assume
`Ring.HasFiniteQuotients R`. If `φ : E₁ → E₂` pulls back the invariant differential as
`φ^*ω₂ = c ω₁`, with `2 ≠ 0` in `K` and `deg φ ≠ 0` in `R`, then
`φ.finiteKummerRatio v = (#(R ⧸ v)) ^ (ord_v c + f_v(E₂) - f_v(E₁)) · c_v(E₂) / c_v(E₁)`,
where `f_v(Eᵢ) = obstructionExponentAt R v Eᵢ`. -/
theorem finiteKummerRatio_eq_zpow_obstructionExponentAt_mul_tamagawaNumberAt_div
    (φ : Isogeny E₁.toAffine E₂.toAffine) (v : HeightOneSpectrum R) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    φ.finiteKummerRatio v =
      (Nat.card (R ⧸ v.asIdeal) : ℚ) ^
        ((v.valuation K).ord c + obstructionExponentAt R v E₂ - obstructionExponentAt R v E₁) *
        E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v := by
  have hφK : (φ.degree : K) ≠ 0 := natCast_ne_zero_of_injective (IsFractionRing.injective R K) hφ
  have hc0 : c ≠ 0 := φ.ne_zero_of_pullbackDifferential_eq_smul_of_degree_ne_zero hφK hc
  obtain ⟨C₁, hC₁⟩ := exists_isMinimal (Localization.AtPrime v.asIdeal) E₁
  obtain ⟨C₂, hC₂⟩ := exists_isMinimal (Localization.AtPrime v.asIdeal) E₂
  rw [finiteKummerRatio_eq_zpow_mul_tamagawaNumberAt_div φ v hc C₁ C₂ h2 hφ,
    neg_log_valuation_mul_div_eq_ord_add_obstructionExponentAt E₁ E₂ v hc0 C₁ C₂]

/-- **Choice-free global finite-place product of Kummer ratios and Tamagawa numbers.** Assume
`Ring.HasFiniteQuotients R`. For any elliptic curves `E₁` and `E₂` over `K` and any isogeny
`φ : E₁ → E₂` with `φ^*ω₂ = c ω₁`, `2 ≠ 0` in `K`, and `deg φ ≠ 0` in `R`, multiplying all finite
local Kummer ratios by `E₁.tamagawaProduct` yields `E₂.tamagawaProduct` times the product over `v`
of `(#(R ⧸ v)) ^ (ord_v c + f_v(E₂) - f_v(E₁))`. -/
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
  have hφK : (φ.degree : K) ≠ 0 := natCast_ne_zero_of_injective (IsFractionRing.injective R K) hφ
  have hc0 : c ≠ 0 := φ.ne_zero_of_pullbackDifferential_eq_smul_of_degree_ne_zero hφK hc
  obtain ⟨D₁, hD₁⟩ := exists_smul_isIntegral R E₁
  obtain ⟨D₂, hD₂⟩ := exists_smul_isIntegral R E₂
  have hsupp_exp : Function.HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
      (Nat.card (R ⧸ v.asIdeal) : ℚ) ^
        ((v.valuation K).ord c + obstructionExponentAt R v E₂ - obstructionExponentAt R v E₁) := by
    simp_rw [← count_obstructionScalingUnit E₁ E₂ hc0 D₁ D₂]
    exact FractionalIdeal.hasFiniteMulSupport_zpow_count _ _
  have hsupp_tam₁ : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum R ↦ (E₁.tamagawaNumberAt v : ℚ)) :=
    E₁.hasFiniteMulSupport_tamagawaNumberAt.fun_comp Nat.cast_one
  have hsupp_tam₂ : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum R ↦ (E₂.tamagawaNumberAt v : ℚ)) :=
    E₂.hasFiniteMulSupport_tamagawaNumberAt.fun_comp Nat.cast_one
  have hcast_tam (E : WeierstrassCurve K) [E.IsElliptic] :
      (E.tamagawaProduct (R := R) : ℚ) =
        ∏ᶠ v : HeightOneSpectrum R, (E.tamagawaNumberAt v : ℚ) := by
    rw [E.tamagawaProduct_def]
    exact MonoidHom.map_finprod (Nat.castRingHom ℚ).toMonoidHom
      E.hasFiniteMulSupport_tamagawaNumberAt
  rw [hcast_tam E₁, hcast_tam E₂,
    ← finprod_mul_distrib (φ.hasFiniteMulSupport_finiteKummerRatio hφK) hsupp_tam₁,
    ← finprod_mul_distrib hsupp_exp hsupp_tam₂]
  refine finprod_congr fun v ↦ ?_
  have hc₁0 : (E₁.tamagawaNumberAt v : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (E₁.tamagawaNumberAt_pos v).ne'
  rw [finiteKummerRatio_eq_zpow_obstructionExponentAt_mul_tamagawaNumberAt_div φ v hc h2 hφ,
    div_mul_cancel₀ _ hc₁0]

/-- **Global finite-place product of Kummer ratios and Tamagawa numbers.** Assume
`Ring.HasFiniteQuotients R`, `2 ≠ 0` in `K`, and `deg φ ≠ 0` in `R`. When `φ^*ω₂ = c ω₁` and
`C₁ • E₁` and `C₂ • E₂` are globally minimal over `R`, multiplying all finite local Kummer ratios by
the Tamagawa product of `E₁` yields the Tamagawa product of `E₂` times the product of the
prime-norm powers of `c · C₂.u / C₁.u`. -/
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
  have hφK : (φ.degree : K) ≠ 0 := natCast_ne_zero_of_injective (IsFractionRing.injective R K) hφ
  have hc0 : c ≠ 0 := φ.ne_zero_of_pullbackDifferential_eq_smul_of_degree_ne_zero hφK hc
  rw [finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_obstructionExponentAt_mul
    φ hc h2 hφ]
  congr 1
  refine finprod_congr fun v ↦ ?_
  have _ := hC₁.isMinimal v
  have _ := hC₂.isMinimal v
  congr 1
  exact (neg_log_valuation_mul_div_eq_ord_add_obstructionExponentAt E₁ E₂ v hc0 C₁ C₂).symm

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
  have hC₁ : IsGlobalMinimal R ((1 : VariableChange K) • E₁) := by simpa only [one_smul] using h₁
  have hC₂ : IsGlobalMinimal R ((1 : VariableChange K) • E₂) := by simpa only [one_smul] using h₂
  simpa [VariableChange.one_def] using
    finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_mul φ hc hC₁ hC₂ h2 hφ

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
  have hC₁ : IsGlobalMinimal R ((1 : VariableChange K) • E₁) := by simpa only [one_smul] using h₁
  have hC₂ : IsGlobalMinimal R ((1 : VariableChange K) • E₂) := by simpa only [one_smul] using h₂
  simpa [VariableChange.one_def] using
    finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul φ hc hC₁ hC₂

end NumberFieldNorm

end FinitePlaces

/-! ### Archimedean place and global period–Tamagawa transformation over `ℚ` -/

section Rational

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- Over `ℚ`, if `φ^*ω₂ = c ω₁` and `C₁`, `C₂` carry `E₁`, `E₂` to globally minimal equations over
`ℤ`, the product of all finite local Kummer ratios times `E₁.tamagawaProduct` equals
`|c · C₂.u / C₁.u| · E₂.tamagawaProduct`. -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_rat
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := ℤ) =
      |c * C₂.u / C₁.u| * E₂.tamagawaProduct (R := ℤ) := by
  simpa [Algebra.norm_self] using
    finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul (R := ℤ) φ hc hC₁ hC₂

/-- Over `ℚ`, if `E₁` and `E₂` are themselves globally minimal over `ℤ` and `φ^*ω₂ = c ω₁`, then
`(∏_p φ.finiteKummerRatio p) · E₁.tamagawaProduct = |c| · E₂.tamagawaProduct`. -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_rat_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := ℤ) =
      |c| * E₂.tamagawaProduct (R := ℤ) := by
  simpa [Algebra.norm_self] using
    finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul_of_isGlobalMinimal (R := ℤ)
      φ hc h₁ h₂

/-- At the real place over `ℚ`, if `φ^*ω₂ = c ω₁` and `C₁`, `C₂` carry `E₁`, `E₂` to globally
minimal equations over `ℤ`, then `φ.realKummerRatio * |c · C₂.u / C₁.u| * Ω(E₁) = Ω(E₂)`. -/
theorem realKummerRatio_mul_abs_mul_minimalRealPeriod_eq
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    (φ.realKummerRatio : ℝ) * |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod =
      E₂.minimalRealPeriod := by
  classical
  rw [realKummerRatio_def, mul_assoc]
  exact ratCast_kummerRatio_mul_eq_of_mul_index_eq_card_ker_mul (φ.baseChange ℝ)
    (abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul φ hc hC₁ hC₂)

/-- Between globally minimal equations over `ℤ`, if `φ^*ω₂ = c ω₁`, then
`φ.realKummerRatio * |c| * Ω(E₁) = Ω(E₂)`. -/
theorem realKummerRatio_mul_abs_mul_minimalRealPeriod_eq_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    (φ.realKummerRatio : ℝ) * |(c : ℝ)| * E₁.minimalRealPeriod = E₂.minimalRealPeriod := by
  have hC₁ : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E₁) := by simpa only [one_smul] using h₁
  have hC₂ : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E₂) := by simpa only [one_smul] using h₂
  simpa [VariableChange.one_def] using
    realKummerRatio_mul_abs_mul_minimalRealPeriod_eq φ hc hC₁ hC₂

/-- **Transformation of `minimalRealPeriod * tamagawaProduct` under an isogeny over `ℚ`.** For any
isogeny `φ : E₁ → E₂` of elliptic curves over `ℚ`, the product of local Kummer ratios across the
real place and all finite primes relates the global period–Tamagawa products without choices of
minimal equations or differentials:
`(φ.kummerRatioProduct : ℝ) * E₁.minimalRealPeriod * E₁.tamagawaProduct =
  E₂.minimalRealPeriod * E₂.tamagawaProduct`. -/
theorem kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct
    (φ : Isogeny E₁.toAffine E₂.toAffine) :
    (φ.kummerRatioProduct : ℝ) * E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) =
      E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  obtain ⟨C₁, hC₁⟩ := exists_isGlobalMinimal_smul ℤ E₁
  obtain ⟨C₂, hC₂⟩ := exists_isGlobalMinimal_smul ℤ E₂
  have hfin : ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ) *
      (E₁.tamagawaProduct (R := ℤ) : ℝ) =
      |((c * C₂.u / C₁.u : ℚ) : ℝ)| * (E₂.tamagawaProduct (R := ℤ) : ℝ) := by
    have h := congrArg ((↑) : ℚ → ℝ)
      (finprod_finiteKummerRatio_mul_tamagawaProduct_rat φ hc hC₁ hC₂)
    simpa only [Rat.cast_mul, Rat.cast_abs, Rat.cast_natCast] using h
  have hreal := realKummerRatio_mul_abs_mul_minimalRealPeriod_eq φ hc hC₁ hC₂
  rw [kummerRatioProduct_def, Rat.cast_mul]
  calc
    (φ.realKummerRatio : ℝ) * (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) *
        E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ)
      = (φ.realKummerRatio : ℝ) * E₁.minimalRealPeriod *
          (((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ) *
            E₁.tamagawaProduct (R := ℤ)) := by ring
    _ = ((φ.realKummerRatio : ℝ) * |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod) *
          E₂.tamagawaProduct (R := ℤ) := by
        rw [hfin]
        ring
    _ = E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
        rw [hreal]

/-- **Quotient form of the period–Tamagawa transformation over `ℚ`.** -/
theorem minimalRealPeriod_mul_tamagawaProduct_div_eq_kummerRatioProduct
    (φ : Isogeny E₁.toAffine E₂.toAffine) :
    E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) /
        (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ)) =
      φ.kummerRatioProduct := by
  have hΩ : E₁.minimalRealPeriod ≠ 0 := E₁.minimalRealPeriod_pos.ne'
  have hT : (E₁.tamagawaProduct (R := ℤ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (E₁.tamagawaProduct_pos (R := ℤ)).ne'
  rw [div_eq_iff (mul_ne_zero hΩ hT),
    ← kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct φ, mul_assoc]

end Rational

end TauCeti.Isogeny

end
