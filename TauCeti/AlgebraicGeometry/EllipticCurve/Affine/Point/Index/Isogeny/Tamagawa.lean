/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Ratio
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MinimalRealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Index
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AdicCompletion
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport

/-!
# Local Kummer ratios, Tamagawa numbers, and the real period under an isogeny

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over a global or completed local field, pulling
the invariant differential back as `φ^*ω₂ = c ω₁`. At each place `v`, the local Kummer ratio
`z_v(φ) = [E₂(K_v) : φ E₁(K_v)] / #E₁(K_v)[φ]` compares the local image and kernel of `φ`.

At a finite place `v` of a Dedekind domain `R` with finite residue field `κ(v)` of cardinality
`q_v = N(v)`, let `C₁` and `C₂` carry `E₁` and `E₂` to minimal equations at `v`, with scaling
factors `u₁` and `u₂`, so that `c u₂ / u₁` is the differential constant read between minimal
equations. On deep levels of the formal group `φ` shifts the filtration by the `v`-adic order of
`c u₂ / u₁` (`TauCeti.Isogeny.eventually_index_range_pointMapHom_mul_index_formalPointFiltration`),
while each formal level index factors into a power of `q_v`, the nonsingular reduction count
`#E_ns(κ(v))`, and the local Tamagawa number `c_v(E)`
(`WeierstrassCurve.index_formalPointFiltration_eq_mul_tamagawaNumber`). Because isogenous minimal
equations over the local field `K_v` have equally many nonsingular reduced points at good and bad
reduction alike (`TauCeti.Isogeny.natCard_point_reduction_eq`), the reduced point counts cancel,
leaving the local identity

`|c u₂ / u₁|_v · z_v(φ) · c_v(E₁) = c_v(E₂)`.

Over `ℚ` at the archimedean place, dividing
`TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul` by `#E₁(ℝ)[φ]` gives the
parallel identity for the minimal real period `Ω(E)`:

`|c u₂ / u₁|_∞ · z_∞(φ) · Ω(E₁) = Ω(E₂)`.

When `C₁` and `C₂` carry `E₁` and `E₂` to globally minimal equations over `ℤ`, the same nonzero
rational constant `q = c u₂ / u₁` governs every place simultaneously. Multiplying the archimedean
and finite-place identities over all places of `ℚ` and cancelling `|q|_∞ · ∏_p |q|_p = 1` by the
product formula yields Cassels' global identity

`z(φ) · (Ω(E₁) · ∏_p c_p(E₁)) = Ω(E₂) · ∏_p c_p(E₂)`,

which expresses the product `z(φ)` of all local Kummer ratios of `φ` as the ratio of the
period–Tamagawa products of `E₂` and `E₁`.

## Main results

* `TauCeti.Isogeny.zpow_natCard_mul_kummerRatio_mul_tamagawaNumber_of_isMinimal` and
  `TauCeti.Isogeny.zpow_natCard_mul_kummerRatio_mul_tamagawaNumber`: the local identity over an
  adic completion `K_v` with `2 ≠ 0` and `(deg φ : R) ≠ 0`.
* `TauCeti.Isogeny.adicAbv_mul_finiteKummerRatio_mul_tamagawaNumberAt` and
  `TauCeti.Isogeny.adicAbv_mul_finiteKummerRatio_mul_tamagawaNumberAt_of_isGlobalMinimal`: the
  finite-place identity in terms of `NumberField.HeightOneSpectrum.adicAbv`, `finiteKummerRatio`,
  and `WeierstrassCurve.tamagawaNumberAt`.
* `TauCeti.Isogeny.abs_mul_realKummerRatio_mul_minimalRealPeriod` and
  `TauCeti.Isogeny.abs_mul_realKummerRatio_mul_minimalRealPeriod_of_isGlobalMinimal`: the real-place
  identity over `ℚ`.
* `TauCeti.Isogeny.kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct`: Cassels' global
  identity `z(φ) · (Ω(E₁) · ∏_p c_p(E₁)) = Ω(E₂) · ∏_p c_p(E₂)` for any isogeny over `ℚ`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199, §6.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, III.5, VII.5–6, VIII.8.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ValuativeRel WeierstrassCurve
open scoped WithZero

namespace TauCeti.Isogeny

/-! ### Differential constant under variable changes -/

/-- Conjugating an isogeny `φ : W₁ → W₂` with `φ^*ω₂ = c ω₁` by changes of variables `C₁` and `C₂`
multiplies the differential pullback constant by `C₂.u / C₁.u`. -/
private theorem pullbackDifferential_variableChangeIsogeny_comp_comp
    {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F}
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (C₁ C₂ : VariableChange F) :
    ((variableChangeIsogeny C₂ (rfl : C₂ • W₂.toAffine = (C₂ • W₂).toAffine)).comp
        (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ W₁.toAffine)))).pullbackDifferential
        (Affine.invariantDifferential (C₂ • W₂).toAffine) =
      (c * C₂.u / C₁.u) • Affine.invariantDifferential (C₁ • W₁).toAffine := by
  rw [pullbackDifferential_comp, LinearMap.comp_apply,
    pullbackDifferential_variableChangeIsogeny_invariantDifferential, LinearMap.map_smul,
    pullbackDifferential_comp, LinearMap.comp_apply, hc, LinearMap.map_smul,
    pullbackDifferential_variableChangeIsogeny_invariantDifferential, smul_smul, smul_smul]
  congr 1
  simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  ring

/-! ### Local identity at a finite place -/

section AdicCompletion

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open scoped Classical in
/-- On a minimal equation over `v.adicCompletionIntegers K`, the index of the `(k + 1)`-st formal
level factors into `(#𝓀[K_v]) ^ k`, the nonsingular reduction count at `𝒪[K_v]`, and the Tamagawa
number with respect to `ValuativeRel.valuation K_v`. -/
private theorem index_formalPointFiltration_eq_mul_reduction_mul_tamagawaNumber
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    (M : WeierstrassCurve (v.adicCompletionIntegers K))
    [(M.baseChange (v.adicCompletion K)).IsElliptic]
    [IsMinimal 𝒪[v.adicCompletion K] (M.baseChange (v.adicCompletion K))] (k : ℕ) :
    (M.formalPointFiltration v (k + 1)).index =
      Nat.card 𝓀[v.adicCompletion K] ^ k *
        Nat.card
          ((M.baseChange (v.adicCompletion K)).reduction 𝒪[v.adicCompletion K]).toAffine.Point *
        (M.baseChange (v.adicCompletion K)).tamagawaNumber (valuation (v.adicCompletion K)) := by
  have : IsMinimal (v.adicCompletionIntegers K) (M.baseChange (v.adicCompletion K)) :=
    (isMinimal_adicCompletion_iff v _).mp inferInstance
  have hq : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Nat.card 𝓀[v.adicCompletion K] :=
    Nat.card_congr <| (IsLocalRing.ResidueField.mapEquiv
      (v.integerEquivAdicCompletionIntegers (K := K)).symm).toEquiv
  have hequiv := ValuativeRel.isEquiv (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    (valuation (v.adicCompletion K))
  rw [M.index_formalPointFiltration_eq_mul_tamagawaNumber v, hq,
    ← M.natCard_point_reduction_baseChange_adicCompletion, tamagawaNumber_congr _ hequiv]

/-- When `deg φ` is nonzero in `R`, the differential pullback constant of `φ` over `K_v` has
nonzero valuation. -/
private theorem valued_ne_zero_of_pullbackDifferential_eq_smul (v : HeightOneSpectrum R)
    {W₁ W₂ : WeierstrassCurve (v.adicCompletion K)} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : v.adicCompletion K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (hφ : (φ.degree : R) ≠ 0) : Valued.v c ≠ 0 := by
  obtain ⟨e, hne⟩ := v.exists_span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow (K := K) hφ
  rw [map_natCast] at hne
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hcc' : Valued.v c * Valued.v c' = WithZero.exp (-(e : ℤ)) := by
    rw [← map_mul, φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc',
      ← v.valued_eq_exp_neg_of_span_eq_maximalIdeal_pow hne]
    simp
  exact left_ne_zero_of_mul (hcc' ▸ WithZero.exp_ne_zero)

/-- Auxiliary form of `zpow_natCard_mul_kummerRatio_mul_tamagawaNumber_of_isMinimal` for curves
already presented as base changes from `v.adicCompletionIntegers K`. -/
private theorem zpow_natCard_mul_kummerRatio_mul_tamagawaNumber_baseChange
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    {M₁ M₂ : WeierstrassCurve (v.adicCompletionIntegers K)}
    [(M₁.baseChange (v.adicCompletion K)).IsElliptic]
    [(M₂.baseChange (v.adicCompletion K)).IsElliptic]
    [IsMinimal 𝒪[v.adicCompletion K] (M₁.baseChange (v.adicCompletion K))]
    [IsMinimal 𝒪[v.adicCompletion K] (M₂.baseChange (v.adicCompletion K))]
    (φ : Isogeny (M₁.baseChange (v.adicCompletion K)).toAffine
      (M₂.baseChange (v.adicCompletion K)).toAffine)
    {c : v.adicCompletion K}
    (hc : φ.pullbackDifferential
        (Affine.invariantDifferential (M₂.baseChange (v.adicCompletion K)).toAffine) =
      c • Affine.invariantDifferential (M₁.baseChange (v.adicCompletion K)).toAffine)
    (h2 : (2 : v.adicCompletion K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    ((Nat.card 𝓀[v.adicCompletion K] : ℚ) ^ WithZero.log (Valued.v c)) * φ.kummerRatio *
        ((M₁.baseChange (v.adicCompletion K)).tamagawaNumber
          (valuation (v.adicCompletion K)) : ℚ) =
      (M₂.baseChange (v.adicCompletion K)).tamagawaNumber (valuation (v.adicCompletion K)) := by
  classical
  have hvc : Valued.v c ≠ 0 := valued_ne_zero_of_pullbackDifferential_eq_smul v φ hc hφ
  set d : ℤ := WithZero.log (Valued.v c)
  obtain ⟨k₀, hlev, hk₀⟩ :=
    ((eventually_index_range_pointMapHom_mul_index_formalPointFiltration v hc h2 hφ).and
      (Filter.eventually_ge_atTop (d.natAbs + 1))).exists
  set k : ℕ := k₀ - 1
  set j : ℕ := ((k : ℤ) - d).toNat
  have hk : k₀ = k + 1 := by omega
  rw [hk] at hlev
  have hjk : Valued.v c * WithZero.exp ((j + 1 : ℕ) : ℤ) = WithZero.exp ((k + 1 : ℕ) : ℤ) := by
    rw [← WithZero.exp_log hvc, ← WithZero.exp_add, WithZero.exp_inj]
    push_cast
    omega
  have hind := hlev (j + 1) hjk
  rw [index_formalPointFiltration_eq_mul_reduction_mul_tamagawaNumber v M₁,
    index_formalPointFiltration_eq_mul_reduction_mul_tamagawaNumber v M₂,
    ← φ.natCard_point_reduction_eq] at hind
  let q : ℚ := Nat.card 𝓀[v.adicCompletion K]
  let N : ℚ := Nat.card
    ((M₁.baseChange (v.adicCompletion K)).reduction 𝒪[v.adicCompletion K]).toAffine.Point
  let idx : ℚ := (Hom.ofIsogeny φ).pointMapHom.range.index
  let ker : ℚ := Nat.card (Hom.ofIsogeny φ).pointMapHom.ker
  let t₁ : ℚ :=
    (M₁.baseChange (v.adicCompletion K)).tamagawaNumber (valuation (v.adicCompletion K))
  let t₂ : ℚ :=
    (M₂.baseChange (v.adicCompletion K)).tamagawaNumber (valuation (v.adicCompletion K))
  have hcast : idx * (q ^ k * N * t₁) = (q ^ j * N * t₂) * ker := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using congrArg (Nat.cast (R := ℚ)) hind
  have hkr : φ.kummerRatio = idx / ker := kummerRatio_def φ
  have := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hker0 : ker ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hqd : q ^ d * q ^ j = q ^ k := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0]
    congr 1
    omega
  calc q ^ d * φ.kummerRatio * t₁
      = (idx * (q ^ k * N * t₁)) / (q ^ j * N * ker) := by
        rw [hkr, ← hqd]
        field_simp [hq0, hN0, hker0]
    _ = t₂ := by
        rw [hcast]
        field_simp [hq0, hN0, hker0]

/-- **The local Kummer ratio and Tamagawa numbers between minimal equations over `K_v`.** Let
`φ : W₁ → W₂` be an isogeny between minimal elliptic curves over the adic completion `K_v` at a
height-one prime `v` with finite residue field, pulling the invariant differential back as
`φ^*ω₂ = c ω₁`. If `2 ≠ 0` in `K_v` and `deg φ` is nonzero in `R`, then
`(#κ(v)) ^ log (v c) · z(φ) · c_v(W₁) = c_v(W₂)`. -/
theorem zpow_natCard_mul_kummerRatio_mul_tamagawaNumber_of_isMinimal
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    {W₁ W₂ : WeierstrassCurve (v.adicCompletion K)} [W₁.IsElliptic] [W₂.IsElliptic]
    [IsMinimal 𝒪[v.adicCompletion K] W₁] [IsMinimal 𝒪[v.adicCompletion K] W₂]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : v.adicCompletion K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (h2 : (2 : v.adicCompletion K) ≠ 0) (hφ : (φ.degree : R) ≠ 0) :
    ((Nat.card 𝓀[v.adicCompletion K] : ℚ) ^ WithZero.log (Valued.v c)) * φ.kummerRatio *
        (W₁.tamagawaNumber (valuation (v.adicCompletion K)) : ℚ) =
      W₂.tamagawaNumber (valuation (v.adicCompletion K)) := by
  have : IsMinimal (v.adicCompletionIntegers K) W₁ :=
    (isMinimal_adicCompletion_iff v W₁).mp inferInstance
  have : IsMinimal (v.adicCompletionIntegers K) W₂ :=
    (isMinimal_adicCompletion_iff v W₂).mp inferInstance
  have hM₁ : ∃ M₁ : WeierstrassCurve (v.adicCompletionIntegers K),
      M₁.baseChange (v.adicCompletion K) = W₁ :=
    ⟨integralModel (v.adicCompletionIntegers K) W₁, baseChange_integralModel_eq _ _⟩
  have hM₂ : ∃ M₂ : WeierstrassCurve (v.adicCompletionIntegers K),
      M₂.baseChange (v.adicCompletion K) = W₂ :=
    ⟨integralModel (v.adicCompletionIntegers K) W₂, baseChange_integralModel_eq _ _⟩
  revert φ hc hφ
  rcases hM₁ with ⟨M₁, rfl⟩
  rcases hM₂ with ⟨M₂, rfl⟩
  intro φ hc hφ
  exact zpow_natCard_mul_kummerRatio_mul_tamagawaNumber_baseChange v φ hc h2 hφ

/-- **The local Kummer ratio and Tamagawa numbers over `K_v`.** Let `φ : W₁ → W₂` be an isogeny of
elliptic curves over `K_v` with `φ^*ω₂ = c ω₁`, and let `C₁`, `C₂` carry `W₁`, `W₂` to minimal
equations over `𝒪[K_v]`. If `2 ≠ 0` in `K_v` and `deg φ` is nonzero in `R`, then
`(#κ(v)) ^ log (v (c u₂ / u₁)) · z(φ) · c_v(W₁) = c_v(W₂)`. -/
theorem zpow_natCard_mul_kummerRatio_mul_tamagawaNumber
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    {W₁ W₂ : WeierstrassCurve (v.adicCompletion K)} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : v.adicCompletion K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (h2 : (2 : v.adicCompletion K) ≠ 0) (hφ : (φ.degree : R) ≠ 0)
    (C₁ C₂ : VariableChange (v.adicCompletion K))
    [IsMinimal 𝒪[v.adicCompletion K] (C₁ • W₁)] [IsMinimal 𝒪[v.adicCompletion K] (C₂ • W₂)] :
    ((Nat.card 𝓀[v.adicCompletion K] : ℚ) ^ WithZero.log (Valued.v (c * C₂.u / C₁.u))) *
        φ.kummerRatio *
        (W₁.tamagawaNumber (valuation (v.adicCompletion K)) : ℚ) =
      W₂.tamagawaNumber (valuation (v.adicCompletion K)) := by
  let ψ : Isogeny (C₁ • W₁).toAffine (C₂ • W₂).toAffine :=
    (variableChangeIsogeny C₂ (rfl : C₂ • W₂.toAffine = (C₂ • W₂).toAffine)).comp
      (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ W₁.toAffine)))
  have hψ := zpow_natCard_mul_kummerRatio_mul_tamagawaNumber_of_isMinimal v ψ
    (pullbackDifferential_variableChangeIsogeny_comp_comp φ hc C₁ C₂) h2
    (by simpa [ψ] using hφ)
  simpa only [ψ, kummerRatio_comp, kummerRatio_variableChangeIsogeny, one_mul, mul_one,
    tamagawaNumber_smul] using hψ

end AdicCompletion

/-! ### Finite places of a Dedekind domain with finite quotients -/

section FinitePlace

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- At a height-one prime `v` of `R`, the residue-cardinality power `(#κ(v)) ^ log (v x)` of a
nonzero element `x ∈ K` equals its normalised `v`-adic absolute value `adicAbv K v x`. -/
private theorem zpow_natCard_residueField_eq_adicAbv (v : HeightOneSpectrum R) {x : K}
    (hx : x ≠ 0) :
    (Nat.card 𝓀[v.adicCompletion K] : ℝ) ^
        WithZero.log (Valued.v (algebraMap K (v.adicCompletion K) x)) =
      NumberField.HeightOneSpectrum.adicAbv K v x := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ ((v.valuation K).ne_zero_iff.mpr hx),
    v.natCard_residueField_adicCompletion_eq_absNorm, algebraMap_adicCompletion,
    Function.comp_apply, valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]
  push_cast
  rfl

/-- **The finite-place Kummer ratio and Tamagawa number under an isogeny.** Let `φ : E₁ → E₂` be an
isogeny over `K` with `φ^*ω₂ = c ω₁`, and let `C₁`, `C₂` carry `E₁`, `E₂` to minimal equations at
`v`. If `2 ≠ 0` in `K` and `deg φ` is nonzero in `R`, then
`|c u₂ / u₁|_v · z_v(φ) · c_v(E₁) = c_v(E₂)`. -/
theorem adicAbv_mul_finiteKummerRatio_mul_tamagawaNumberAt
    {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0)
    (C₁ C₂ : VariableChange K) (v : HeightOneSpectrum R)
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • E₁)]
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • E₂)] :
    NumberField.HeightOneSpectrum.adicAbv K v (c * C₂.u / C₁.u) *
        (φ.finiteKummerRatio v : ℝ) * E₁.tamagawaNumberAt v =
      E₂.tamagawaNumberAt v := by
  have : Finite (R ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have hM₁ : IsMinimal 𝒪[v.adicCompletion K]
      (C₁.baseChange (v.adicCompletion K) • E₁.baseChange (v.adicCompletion K)) := by
    rw [baseChange_smul_baseChange]
    exact (isMinimal_localizationAtPrime_iff_adicCompletion v (C₁ • E₁)).mp inferInstance
  have hM₂ : IsMinimal 𝒪[v.adicCompletion K]
      (C₂.baseChange (v.adicCompletion K) • E₂.baseChange (v.adicCompletion K)) := by
    rw [baseChange_smul_baseChange]
    exact (isMinimal_localizationAtPrime_iff_adicCompletion v (C₂ • E₂)).mp inferInstance
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hdegK : (φ.degree : K) ≠ 0 := by
    rw [← map_natCast (algebraMap R K)]
    exact (FaithfulSMul.algebraMap_eq_zero_iff R K).not.mpr hφ
  have hc0 : c ≠ 0 := left_ne_zero_of_mul <| by
    rwa [φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc']
  have hq0 : c * C₂.u / C₁.u ≠ 0 := div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have h2v : (2 : v.adicCompletion K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]
    exact (algebraMap K (v.adicCompletion K)).injective.ne h2
  have hdegv : (φ.baseChange (v.adicCompletion K)).degree = φ.degree :=
    degree_map φ (algebraMap K (v.adicCompletion K))
  have hkr : (φ.baseChange (v.adicCompletion K)).kummerRatio = φ.finiteKummerRatio v :=
    (φ.finiteKummerRatio_def v).symm
  have hloc := zpow_natCard_mul_kummerRatio_mul_tamagawaNumber v
    (φ.baseChange (v.adicCompletion K))
    (map_pullbackDifferential_invariantDifferential_eq_smul φ
      (algebraMap K (v.adicCompletion K)) hc)
    h2v (by rwa [hdegv])
    (C₁.baseChange (v.adicCompletion K)) (C₂.baseChange (v.adicCompletion K))
  have hval : algebraMap K (v.adicCompletion K) c *
      ↑(C₂.baseChange (v.adicCompletion K)).u / ↑(C₁.baseChange (v.adicCompletion K)).u =
      algebraMap K (v.adicCompletion K) (c * C₂.u / C₁.u) := by
    simp [VariableChange.baseChange]
  rw [hval, hkr, ← E₁.tamagawaNumberAt_def v, ← E₂.tamagawaNumberAt_def v] at hloc
  have hlocR := congrArg (Rat.cast (K := ℝ)) hloc
  push_cast at hlocR
  rwa [← zpow_natCard_residueField_eq_adicAbv v hq0]

/-- **The finite-place Kummer ratio and Tamagawa number between globally minimal equations.** If
`φ : E₁ → E₂` is an isogeny between globally minimal equations over `R` with `φ^*ω₂ = c ω₁`,
`2 ≠ 0` in `K`, and `(deg φ : R) ≠ 0`, then `|c|_v · z_v(φ) · c_v(E₁) = c_v(E₂)`. -/
theorem adicAbv_mul_finiteKummerRatio_mul_tamagawaNumberAt_of_isGlobalMinimal
    {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hφ : (φ.degree : R) ≠ 0)
    (h₁ : IsGlobalMinimal R E₁) (h₂ : IsGlobalMinimal R E₂) (v : HeightOneSpectrum R) :
    NumberField.HeightOneSpectrum.adicAbv K v c *
        (φ.finiteKummerRatio v : ℝ) * E₁.tamagawaNumberAt v =
      E₂.tamagawaNumberAt v := by
  have : IsMinimal (Localization.AtPrime v.asIdeal) ((1 : VariableChange K) • E₁) := by
    rw [one_smul]; exact h₁.isMinimal v
  have : IsMinimal (Localization.AtPrime v.asIdeal) ((1 : VariableChange K) • E₂) := by
    rw [one_smul]; exact h₂.isMinimal v
  simpa using adicAbv_mul_finiteKummerRatio_mul_tamagawaNumberAt φ hc h2 hφ 1 1 v

end FinitePlace

/-! ### Archimedean place and global product over `ℚ` -/

section Rational

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **The real Kummer ratio and minimal real period under an isogeny over `ℚ`.** Let `φ : E₁ → E₂`
be an isogeny over `ℚ` with `φ^*ω₂ = c ω₁`, and let `C₁`, `C₂` carry `E₁`, `E₂` to globally minimal
equations over `ℤ`. Then `|c u₂ / u₁| · z_∞(φ) · Ω(E₁) = Ω(E₂)`. -/
theorem abs_mul_realKummerRatio_mul_minimalRealPeriod
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    |((c * C₂.u / C₁.u : ℚ) : ℝ)| * (φ.realKummerRatio : ℝ) * E₁.minimalRealPeriod =
      E₂.minimalRealPeriod := by
  classical
  have h := abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul φ hc hC₁ hC₂
  have := (Hom.ofIsogeny (φ.baseChange ℝ)).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have hker : (Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hkr : (φ.realKummerRatio : ℝ) =
      ((Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index : ℝ) /
        Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker := by
    rw [realKummerRatio_def, kummerRatio_def]
    push_cast
    rfl
  rw [hkr]
  calc |((c * C₂.u / C₁.u : ℚ) : ℝ)| *
        (((Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index : ℝ) /
          Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker) * E₁.minimalRealPeriod
      = (|((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod *
          (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index) /
          Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker := by ring
    _ = E₂.minimalRealPeriod := by
        rw [h]
        field_simp [hker]

/-- **The real Kummer ratio and minimal real period between globally minimal equations.** If
`φ : E₁ → E₂` is an isogeny over `ℚ` between globally minimal equations with `φ^*ω₂ = c ω₁`, then
`|c| · z_∞(φ) · Ω(E₁) = Ω(E₂)`. -/
theorem abs_mul_realKummerRatio_mul_minimalRealPeriod_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    |(c : ℝ)| * (φ.realKummerRatio : ℝ) * E₁.minimalRealPeriod = E₂.minimalRealPeriod := by
  classical
  have h := abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul_of_isGlobalMinimal φ hc h₁ h₂
  have := (Hom.ofIsogeny (φ.baseChange ℝ)).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have hker : (Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hkr : (φ.realKummerRatio : ℝ) =
      ((Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index : ℝ) /
        Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker := by
    rw [realKummerRatio_def, kummerRatio_def]
    push_cast
    rfl
  rw [hkr]
  calc |(c : ℝ)| *
        (((Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index : ℝ) /
          Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker) * E₁.minimalRealPeriod
      = (|(c : ℝ)| * E₁.minimalRealPeriod *
          (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index) /
          Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker := by ring
    _ = E₂.minimalRealPeriod := by
        rw [h]
        field_simp [hker]

/-- Equivalence between height-one primes of `ℤ` and `NumberField.FinitePlace ℚ`. -/
private noncomputable def finitePlaceRatEquiv :
    HeightOneSpectrum ℤ ≃ NumberField.FinitePlace ℚ :=
  (equivOfRingEquiv Rat.ringOfIntegersEquiv).symm.trans
    NumberField.FinitePlace.equivHeightOneSpectrum.symm

/-- At every height-one prime `v` of `ℤ`, `adicAbv ℚ v` agrees with `finitePlaceRatEquiv v`. -/
private theorem adicAbv_eq_finitePlaceRatEquiv (v : HeightOneSpectrum ℤ) (q : ℚ) :
    NumberField.HeightOneSpectrum.adicAbv ℚ v q = finitePlaceRatEquiv v q := by
  let w : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    (equivOfRingEquiv Rat.ringOfIntegersEquiv).symm v
  have hvw : v.asIdeal = Ideal.map Rat.ringOfIntegersEquiv w.asIdeal := by
    rw [← asIdeal_equivOfRingEquiv Rat.ringOfIntegersEquiv w, Equiv.apply_symm_apply]
  have hnorm : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_of_ne_bot w.ne_bot, Ideal.absNorm_of_ne_bot v.ne_bot,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr
      (Ideal.quotientEquiv w.asIdeal v.asIdeal Rat.ringOfIntegersEquiv hvw).toEquiv
  have hσ : IsFractionRing.ringEquivOfRingEquiv Rat.ringOfIntegersEquiv q = q :=
    RingHom.congr_fun (Subsingleton.elim
      (IsFractionRing.ringEquivOfRingEquiv Rat.ringOfIntegersEquiv).toRingHom (RingHom.id ℚ)) q
  have hval : v.valuation ℚ q = w.valuation ℚ q := by
    have hv := valuation_ringEquivOfRingEquiv (K := ℚ) (K' := ℚ) Rat.ringOfIntegersEquiv hvw q
    rwa [hσ] at hv
  simp only [finitePlaceRatEquiv, Equiv.trans_apply,
    NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply,
    NumberField.FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def]
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · rw [WithZeroMulInt.toNNReal_neg_apply _ ((v.valuation ℚ).ne_zero_iff.mpr hq),
      WithZeroMulInt.toNNReal_neg_apply _ ((w.valuation ℚ).ne_zero_iff.mpr hq)]
    push_cast
    rw [hnorm, hval]

/-- A nonzero rational number has nontrivial `v`-adic absolute value at only finitely many
height-one primes of `ℤ`. -/
private theorem hasFiniteMulSupport_adicAbv_rat {q : ℚ} (hq : q ≠ 0) :
    (fun v : HeightOneSpectrum ℤ ↦
      NumberField.HeightOneSpectrum.adicAbv ℚ v q).HasFiniteMulSupport := by
  simp_rw [adicAbv_eq_finitePlaceRatEquiv]
  exact (NumberField.FinitePlace.hasFiniteMulSupport hq).comp_of_injective
    finitePlaceRatEquiv.injective

/-- The product formula over `ℚ` indexed by `HeightOneSpectrum ℤ`: for any nonzero `q ∈ ℚ`,
`|q| · ∏ᶠ v : HeightOneSpectrum ℤ, |q|_v = 1`. -/
private theorem abs_mul_finprod_adicAbv_rat {q : ℚ} (hq : q ≠ 0) :
    |(q : ℝ)| * ∏ᶠ v : HeightOneSpectrum ℤ, NumberField.HeightOneSpectrum.adicAbv ℚ v q = 1 := by
  simp_rw [adicAbv_eq_finitePlaceRatEquiv]
  rw [finprod_comp_equiv finitePlaceRatEquiv (f := fun w ↦ w q),
    NumberField.FinitePlace.prod_eq_inv_abs_norm hq, Algebra.norm_self, MonoidHom.id_apply,
    Rat.cast_inv, Rat.cast_abs, mul_inv_cancel₀ (abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hq))]

/-- Transport `IsGlobalMinimal` across equality of elliptic Weierstrass equations. -/
private theorem isGlobalMinimal_of_eq {W₁ W₂ : WeierstrassCurve ℚ} [W₁.IsElliptic] [W₂.IsElliptic]
    (h : W₁ = W₂) (hW₂ : IsGlobalMinimal ℤ W₂) : IsGlobalMinimal ℤ W₁ := by
  subst h
  exact hW₂

/-- Multiplying the finite-place identities over all `v : HeightOneSpectrum ℤ` relates the global
Tamagawa products of `E₁` and `E₂`. -/
private theorem finprod_adicAbv_mul_finiteKummerRatio_mul_tamagawaProduct
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hGM₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hGM₂ : IsGlobalMinimal ℤ (C₂ • E₂)) (hq0 : c * C₂.u / C₁.u ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum ℤ,
          NumberField.HeightOneSpectrum.adicAbv ℚ v (c * C₂.u / C₁.u)) *
        ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ) *
        (E₁.tamagawaProduct (R := ℤ) : ℝ) =
      (E₂.tamagawaProduct (R := ℤ) : ℝ) := by
  have hfin (v : HeightOneSpectrum ℤ) :
      NumberField.HeightOneSpectrum.adicAbv ℚ v (c * C₂.u / C₁.u) *
          (φ.finiteKummerRatio v : ℝ) * (E₁.tamagawaNumberAt v : ℝ) =
        (E₂.tamagawaNumberAt v : ℝ) := by
    have := hGM₁.isMinimal v
    have := hGM₂.isMinimal v
    exact adicAbv_mul_finiteKummerRatio_mul_tamagawaNumberAt φ hc two_ne_zero
      (Nat.cast_ne_zero.mpr φ.degree_pos.ne') C₁ C₂ v
  have hf₁ := hasFiniteMulSupport_adicAbv_rat hq0
  have hf₂ : (fun v : HeightOneSpectrum ℤ ↦ (φ.finiteKummerRatio v : ℝ)).HasFiniteMulSupport :=
    Function.HasFiniteMulSupport.fun_comp
      φ.hasFiniteMulSupport_finiteKummerRatio_rat (g := Rat.cast) Rat.cast_one
  have hf₃ : (fun v : HeightOneSpectrum ℤ ↦ (E₁.tamagawaNumberAt v : ℝ)).HasFiniteMulSupport :=
    Function.HasFiniteMulSupport.fun_comp
      (E₁.hasFiniteMulSupport_tamagawaNumberAt (R := ℤ)) (g := Nat.cast) Nat.cast_one
  have ht (E : WeierstrassCurve ℚ) [E.IsElliptic] :
      (E.tamagawaProduct (R := ℤ) : ℝ) =
        ∏ᶠ v : HeightOneSpectrum ℤ, (E.tamagawaNumberAt v : ℝ) := by
    rw [E.tamagawaProduct_def]
    exact ((Nat.castRingHom ℝ).toMonoidHom).map_finprod_of_preimage_one (by simp) _
  have hfk : ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum ℤ, (φ.finiteKummerRatio v : ℝ) :=
    ((Rat.castHom ℝ).toMonoidHom).map_finprod_of_preimage_one
      (fun _ hx ↦ (Rat.castHom ℝ).injective (hx.trans (map_one _).symm)) _
  rw [hfk, ht E₁, ht E₂, ← finprod_mul_distrib hf₁ hf₂,
    ← finprod_mul_distrib (Function.HasFiniteMulSupport.fun_mul hf₁ hf₂) hf₃]
  exact finprod_congr hfin

/-- **Cassels' Kummer–Tamagawa–period identity over `ℚ`.** For any isogeny `φ : E₁ → E₂` of
elliptic curves over `ℚ`, the product `z(φ)` of all local Kummer ratios (archimedean and
nonarchimedean) transforms the product of the minimal real period and the global Tamagawa product:

`z(φ) · (Ω(E₁) · ∏_p c_p(E₁)) = Ω(E₂) · ∏_p c_p(E₂)`. -/
theorem kummerRatioProduct_mul_minimalRealPeriod_mul_tamagawaProduct
    (φ : Isogeny E₁.toAffine E₂.toAffine) :
    (φ.kummerRatioProduct : ℝ) * (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ)) =
      E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
  obtain ⟨C₁, hC₁⟩ := exists_smul_eq_reducedMinimalModel E₁
  obtain ⟨C₂, hC₂⟩ := exists_smul_eq_reducedMinimalModel E₂
  have hGM₁ := isGlobalMinimal_of_eq hC₁ (isReducedMinimal_reducedMinimalModel E₁).isGlobalMinimal
  have hGM₂ := isGlobalMinimal_of_eq hC₂ (isReducedMinimal_reducedMinimalModel E₂).isGlobalMinimal
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hc0 : c ≠ 0 := left_ne_zero_of_mul <| by
    rw [φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc']
    exact Nat.cast_ne_zero.mpr φ.degree_pos.ne'
  set q : ℚ := c * C₂.u / C₁.u
  have hq0 : q ≠ 0 := div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have hreal := abs_mul_realKummerRatio_mul_minimalRealPeriod φ hc hGM₁ hGM₂
  have hprod := finprod_adicAbv_mul_finiteKummerRatio_mul_tamagawaProduct φ hc hGM₁ hGM₂ hq0
  calc (φ.kummerRatioProduct : ℝ) * (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ))
      = (|(q : ℝ)| * ∏ᶠ v : HeightOneSpectrum ℤ, NumberField.HeightOneSpectrum.adicAbv ℚ v q) *
          (φ.kummerRatioProduct : ℝ) * (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ)) := by
        rw [abs_mul_finprod_adicAbv_rat hq0, one_mul]
    _ = (|(q : ℝ)| * (φ.realKummerRatio : ℝ) * E₁.minimalRealPeriod) *
          ((∏ᶠ v : HeightOneSpectrum ℤ, NumberField.HeightOneSpectrum.adicAbv ℚ v q) *
            ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ) *
            E₁.tamagawaProduct (R := ℤ)) := by
        rw [kummerRatioProduct_def, Rat.cast_mul]
        ring
    _ = E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
        rw [hreal, hprod]

end Rational

end TauCeti.Isogeny

end
