/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Ratio
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.RealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Index
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MinimalRealPeriod
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AdicCompletion
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny
import TauCeti.NumberTheory.NumberField.Global.Places.Basic
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ProductFormula

/-!
# Local Kummer ratios, Tamagawa numbers, and the period–Tamagawa transformation

In Cassels' proof that the Birch–Swinnerton-Dyer quotient is invariant under rational isogeny,
every place `v` of `ℚ` contributes a local Kummer ratio
`z_v(φ) = [E₂(ℚ_v) : φ E₁(ℚ_v)] / #E₁(ℚ_v)[φ]` to the global Selmer ratio, and these local ratios
govern how the minimal real periods `Ω(Eᵢ)` and local Tamagawa numbers `c_p(Eᵢ)` transform under
`φ : E₁ → E₂`.

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `R` with
finite residue field of cardinality `q = Ideal.absNorm v.asIdeal`. For minimal equations `E₁` and
`E₂` over `v.adicCompletion K` and an isogeny `φ : E₁ → E₂` pulling the invariant differential back
as `φ^*ω₂ = c ω₁` (with `2 ≠ 0` in `v.adicCompletion K` and `deg φ` nonzero in `R`), comparing the
formal-group filtration identity
(`TauCeti.Isogeny.eventually_index_range_pointMapHom_mul_index_formalPointFiltration`) with the
formal-level index decomposition
(`WeierstrassCurve.index_formalPointFiltration_eq_mul_tamagawaNumber`) cancels the common
nonsingular reduction point count (`TauCeti.Isogeny.natCard_point_reduction_eq`) at every reduction
type—good, multiplicative, or additive, including primes dividing `2` or `deg φ`—and yields

  `q ^ log(v(c)) · c_v(E₁) · z_v(φ) = c_v(E₂)`.

Conjugating by `v`-minimal changes of variables `C₁`, `C₂` over `K` (preserved under completion by
`WeierstrassCurve.isMinimal_baseChange_adicCompletion`) expresses this over `K` in terms of the
normalized `v`-adic absolute value `|c · u₂ / u₁|_v`. Multiplying over all height-one primes of
`𝓞 K` for a number field `K` (via `TauCeti.GlobalNumberFields.finprod_normalizedAbsValue_inl`) or
over `HeightOneSpectrum ℤ` together with the archimedean place over `ℚ` (via
`TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul` and
`IsDedekindDomain.HeightOneSpectrum.finprod_adicAbv_rat`) cancels the differential scaling
constants altogether and proves the unconditional global transformation law

  `Ω(E₁) · c(E₁) · φ.kummerRatioProduct = Ω(E₂) · c(E₂)`.

In particular, `φ.kummerRatioProduct = 1` for every endomorphism `φ : E → E` over `ℚ`, and the
global Kummer ratio products of dual isogenies are inverse to one another.

## Main results

* `TauCeti.Isogeny.kummerRatio_variableChangeIsogeny`,
  `TauCeti.Isogeny.finiteKummerRatio_variableChangeIsogeny`,
  `TauCeti.Isogeny.realKummerRatio_variableChangeIsogeny`, and
  `TauCeti.Isogeny.kummerRatioProduct_variableChangeIsogeny`: changes of variables have Kummer
  ratio `1`.
* `TauCeti.Isogeny.zpow_log_valued_mul_tamagawaNumber_mul_kummerRatio`: the completed local
  identity `q ^ log(v(c)) · c_v(E₁) · z_v(φ) = c_v(E₂)` for minimal equations over `K_v`.
* `TauCeti.Isogeny.zpow_log_valuation_mul_tamagawaNumberAt_mul_finiteKummerRatio` and
  `TauCeti.Isogeny.adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio`: the local identity over `K`
  for arbitrary equations with `v`-minimal changes of variables `C₁`, `C₂`.
* `TauCeti.Isogeny.adicAbv_mul_finiteKummerRatio_self` and
  `TauCeti.Isogeny.finprod_finiteKummerRatio_self`: for any endomorphism `φ : W → W` with
  `φ^*ω = c ω`, `|c|_v · z_v(φ) = 1` locally and `∏_v z_v(φ) = |N_{K/ℚ}(c)|` over any number field,
  without global minimality assumptions.
* `TauCeti.Isogeny.tamagawaProduct_mul_finprod_finiteKummerRatio`: global finite-place Tamagawa
  ratio over a number field `K` in terms of `|Algebra.norm ℚ (c * C₂.u / C₁.u)|`.
* `TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_realKummerRatio`: archimedean period–Kummer
  identity `|c · u₂ / u₁| · Ω(E₁) · z_∞(φ) = Ω(E₂)` over `ℚ`.
* `TauCeti.Isogeny.minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct`:
  `Ω(E₁) · c(E₁) · φ.kummerRatioProduct = Ω(E₂) · c(E₂)` for any isogeny over `ℚ`.
* `TauCeti.Isogeny.kummerRatioProduct_self`, `TauCeti.Isogeny.kummerRatioProduct_mul_dual`, and
  `TauCeti.Isogeny.kummerRatioProduct_dual`: endomorphism triviality and duality for
  `kummerRatioProduct`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199, Lemma 6.1 and §7.
* J. Tate, *On the conjectures of Birch and Swinnerton-Dyer and a geometric analog*, Séminaire
  Bourbaki 306 (1966).
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, III.5, VII.6, and
  X.4.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), 79–114, §3.
-/

public noncomputable section

open IsDedekindDomain IsLocalRing WeierstrassCurve
open scoped NumberField ValuativeRel WithZero

namespace TauCeti.Isogeny

/-! ### Kummer ratios of changes of variables -/

section VariableChange

/-- The isogeny attached to a change of Weierstrass variables has Kummer ratio one. -/
@[simp]
theorem kummerRatio_variableChangeIsogeny {F : Type*} [Field F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (C : VariableChange F) (h : C • W₁ = W₂) :
    (variableChangeIsogeny C h).kummerRatio = 1 :=
  kummerRatio_eq_one_of_degree_eq_one _ (degree_variableChangeIsogeny C h)

/-- A change of variables has finite local Kummer ratio one at every height-one prime. -/
@[simp]
theorem finiteKummerRatio_variableChangeIsogeny {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
    (C : VariableChange K) (h : C • W₁.toAffine = W₂.toAffine) (v : HeightOneSpectrum R) :
    (variableChangeIsogeny C h).finiteKummerRatio v = 1 :=
  finiteKummerRatio_eq_one_of_degree_eq_one _ (degree_variableChangeIsogeny C h) v

/-- A change of variables over `ℚ` has real local Kummer ratio one. -/
@[simp]
theorem realKummerRatio_variableChangeIsogeny {E₁ E₂ : WeierstrassCurve ℚ}
    [E₁.IsElliptic] [E₂.IsElliptic] (C : VariableChange ℚ) (h : C • E₁.toAffine = E₂.toAffine) :
    (variableChangeIsogeny C h).realKummerRatio = 1 :=
  realKummerRatio_eq_one_of_degree_eq_one _ (degree_variableChangeIsogeny C h)

/-- A change of variables over `ℚ` has global Kummer ratio product one. -/
@[simp]
theorem kummerRatioProduct_variableChangeIsogeny {E₁ E₂ : WeierstrassCurve ℚ}
    [E₁.IsElliptic] [E₂.IsElliptic] (C : VariableChange ℚ) (h : C • E₁.toAffine = E₂.toAffine) :
    (variableChangeIsogeny C h).kummerRatioProduct = 1 :=
  kummerRatioProduct_eq_one_of_degree_eq_one _ (degree_variableChangeIsogeny C h)

end VariableChange

/-! ### Local Kummer ratios and Tamagawa numbers at a height-one prime -/

section Local

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

private local instance (v : HeightOneSpectrum R) :
    IsDiscreteValuationRing (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring :=
  inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))

open scoped Classical in
private theorem exists_nat_zpow_log_valued_index_eq (v : HeightOneSpectrum R)
    [Finite (R ⧸ v.asIdeal)]
    {C₁ C₂ : WeierstrassCurve (v.adicCompletionIntegers K)}
    [(C₁.baseChange (v.adicCompletion K)).IsElliptic]
    [(C₂.baseChange (v.adicCompletion K)).IsElliptic]
    [IsMinimal (v.adicCompletionIntegers K) (C₁.baseChange (v.adicCompletion K))]
    [IsMinimal (v.adicCompletionIntegers K) (C₂.baseChange (v.adicCompletion K))]
    (φ : Isogeny (C₁.baseChange (v.adicCompletion K)).toAffine
      (C₂.baseChange (v.adicCompletion K)).toAffine)
    {c : v.adicCompletion K}
    (hc : φ.pullbackDifferential
        (Affine.invariantDifferential (C₂.baseChange (v.adicCompletion K)).toAffine) =
      c • Affine.invariantDifferential (C₁.baseChange (v.adicCompletion K)).toAffine)
    (h2 : (2 : v.adicCompletion K) ≠ 0) (hn : (φ.degree : R) ≠ 0) :
    ∃ k₀ j₀ : ℕ, WithZero.log (Valued.v c) + (j₀ : ℤ) = (k₀ : ℤ) ∧
      ((Hom.ofIsogeny φ).pointMapHom.range.index : ℚ) *
        ((Ideal.absNorm v.asIdeal : ℚ) ^ k₀ *
          Nat.card ((C₂.baseChange (v.adicCompletion K)).reduction
            𝒪[v.adicCompletion K]).toAffine.Point *
          ((C₁.baseChange (v.adicCompletion K)).tamagawaNumber Valued.v : ℚ)) =
        ((Ideal.absNorm v.asIdeal : ℚ) ^ j₀ *
          Nat.card ((C₂.baseChange (v.adicCompletion K)).reduction
            𝒪[v.adicCompletion K]).toAffine.Point *
          ((C₂.baseChange (v.adicCompletion K)).tamagawaNumber Valued.v : ℚ)) *
        Nat.card (Hom.ofIsogeny φ).pointMapHom.ker := by
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hdeg0 : (φ.degree : v.adicCompletion K) ≠ 0 := by
    rw [← map_natCast (algebraMap R (v.adicCompletion K)),
      IsScalarTower.algebraMap_apply R K (v.adicCompletion K),
      map_ne_zero_iff _ (RingHom.injective _),
      map_ne_zero_iff _ (IsFractionRing.injective R K)]
    exact hn
  have hvc : Valued.v c ≠ 0 := (Valued.v : Valuation _ ℤᵐ⁰).ne_zero_iff.mpr <|
    left_ne_zero_of_mul ((φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc').trans_ne hdeg0)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_index_range_pointMapHom_mul_index_formalPointFiltration v hc h2 hn)
  set d : ℤ := WithZero.log (Valued.v c)
  let k₀ : ℕ := N + d.natAbs
  let j₀ : ℕ := ((k₀ : ℤ) - d).toNat
  have hcard_res : Nat.card (ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_of_ne_bot v.ne_bot, Submodule.cardQuot_apply]
    exact (Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv).symm
  have hidx := hN (k₀ + 1) (by omega) (j₀ + 1) (by
    rw [← WithZero.exp_log hvc, ← WithZero.exp_add, WithZero.exp_inj]
    push_cast; omega)
  rw [C₁.index_formalPointFiltration_eq_mul_tamagawaNumber v,
    C₂.index_formalPointFiltration_eq_mul_tamagawaNumber v, hcard_res,
    ← natCard_point_reduction_adicCompletion (C₁.baseChange (v.adicCompletion K)),
    ← natCard_point_reduction_adicCompletion (C₂.baseChange (v.adicCompletion K)),
    φ.natCard_point_reduction_eq] at hidx
  exact ⟨k₀, j₀, by omega, by exact_mod_cast hidx⟩

/-- **Local Tamagawa–Kummer identity over `v.adicCompletion K`**: for minimal equations `E₁` and
`E₂` over `v.adicCompletionIntegers K` and an isogeny `φ : E₁ → E₂` with `φ^*ω₂ = c ω₁`, `2 ≠ 0` in
`v.adicCompletion K`, and `(φ.degree : R) ≠ 0`,
`q ^ log(v(c)) · c_v(E₁) · φ.kummerRatio = c_v(E₂)`, where `q = Ideal.absNorm v.asIdeal`. -/
theorem zpow_log_valued_mul_tamagawaNumber_mul_kummerRatio (v : HeightOneSpectrum R)
    [Finite (R ⧸ v.asIdeal)]
    {E₁ E₂ : WeierstrassCurve (v.adicCompletion K)} [E₁.IsElliptic] [E₂.IsElliptic]
    [IsMinimal (v.adicCompletionIntegers K) E₁] [IsMinimal (v.adicCompletionIntegers K) E₂]
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : v.adicCompletion K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (h2 : (2 : v.adicCompletion K) ≠ 0) (hn : (φ.degree : R) ≠ 0) :
    ((Ideal.absNorm v.asIdeal : ℚ) ^ WithZero.log (Valued.v c)) *
        (E₁.tamagawaNumber Valued.v : ℚ) * φ.kummerRatio =
      (E₂.tamagawaNumber Valued.v : ℚ) := by
  classical
  have hE₁ := baseChange_integralModel_eq (v.adicCompletionIntegers K) E₁
  have hE₂ := baseChange_integralModel_eq (v.adicCompletionIntegers K) E₂
  set C₁ := integralModel (v.adicCompletionIntegers K) E₁
  set C₂ := integralModel (v.adicCompletionIntegers K) E₂
  clear_value C₁ C₂
  subst hE₁ hE₂
  obtain ⟨k₀, j₀, hdj, hQ⟩ := exists_nat_zpow_log_valued_index_eq v φ hc h2 hn
  set d : ℤ := WithZero.log (Valued.v c)
  have hq0 : (Ideal.absNorm v.asIdeal : ℚ) ≠ 0 := by
    simpa [Ideal.absNorm_of_ne_bot v.ne_bot, Submodule.cardQuot_apply] using Nat.card_pos.ne'
  have hq_pow : (Ideal.absNorm v.asIdeal : ℚ) ^ d * (Ideal.absNorm v.asIdeal : ℚ) ^ j₀ =
      (Ideal.absNorm v.asIdeal : ℚ) ^ k₀ := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0, hdj]
  have := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  have hker0 : (Nat.card (Hom.ofIsogeny φ).pointMapHom.ker : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hN0 : (Nat.card ((C₂.baseChange (v.adicCompletion K)).reduction
      𝒪[v.adicCompletion K]).toAffine.Point : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [kummerRatio_def, ← mul_div_assoc, div_eq_iff hker0]
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero k₀ hq0) hN0) ?_
  calc _ = (Ideal.absNorm v.asIdeal : ℚ) ^ d *
        (((Hom.ofIsogeny φ).pointMapHom.range.index : ℚ) *
          ((Ideal.absNorm v.asIdeal : ℚ) ^ k₀ *
            Nat.card ((C₂.baseChange (v.adicCompletion K)).reduction
              𝒪[v.adicCompletion K]).toAffine.Point *
            ((C₁.baseChange (v.adicCompletion K)).tamagawaNumber Valued.v : ℚ))) := by ring
    _ = ((Ideal.absNorm v.asIdeal : ℚ) ^ d * (Ideal.absNorm v.asIdeal : ℚ) ^ j₀) *
          Nat.card ((C₂.baseChange (v.adicCompletion K)).reduction
            𝒪[v.adicCompletion K]).toAffine.Point *
          ((C₂.baseChange (v.adicCompletion K)).tamagawaNumber Valued.v : ℚ) *
          Nat.card (Hom.ofIsogeny φ).pointMapHom.ker := by rw [hQ]; ring
    _ = _ := by rw [hq_pow]; ring

section HasFiniteQuotients

variable [Ring.HasFiniteQuotients R]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

private local instance (v : HeightOneSpectrum R) : Finite (R ⧸ v.asIdeal) :=
  Ring.HasFiniteQuotients.finiteQuotient v.ne_bot

private theorem tamagawaNumberAt_eq_valued (W : WeierstrassCurve K)
    (v : HeightOneSpectrum R) :
    W.tamagawaNumberAt v =
      (W.map (algebraMap K (v.adicCompletion K))).tamagawaNumber
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) := by
  let : IsDiscreteValuationRing (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring :=
    inferInstanceAs (IsDiscreteValuationRing 𝒪[v.adicCompletion K])
  rw [tamagawaNumberAt_def]
  exact tamagawaNumber_congr _ _ _
    (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))

/-- **Local Tamagawa–Kummer identity over `K` (rational `zpow` form)**: let `φ : W₁ → W₂` pull back
the invariant differential as `φ^*ω₂ = c ω₁`, and let `C₁`, `C₂` carry `W₁`, `W₂` to equations
minimal over `Localization.AtPrime v.asIdeal`. When `(2 : K) ≠ 0` and `(φ.degree : R) ≠ 0`,
`q ^ log(v(c u₂ / u₁)) · c_v(W₁) · φ.finiteKummerRatio v = c_v(W₂)`. -/
theorem zpow_log_valuation_mul_tamagawaNumberAt_mul_finiteKummerRatio
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (v : HeightOneSpectrum R) {C₁ C₂ : VariableChange K}
    (hC₁ : IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • W₁))
    (hC₂ : IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • W₂))
    (h2 : (2 : K) ≠ 0) (hn : (φ.degree : R) ≠ 0) :
    ((Ideal.absNorm v.asIdeal : ℚ) ^ WithZero.log (v.valuation K (c * C₂.u / C₁.u))) *
        (W₁.tamagawaNumberAt v : ℚ) * φ.finiteKummerRatio v =
      (W₂.tamagawaNumberAt v : ℚ) := by
  have := hC₁
  have := hC₂
  have : IsMinimal (v.adicCompletionIntegers K)
      ((C₁ • W₁).map (algebraMap K (v.adicCompletion K))) :=
    isMinimal_baseChange_adicCompletion v (C₁ • W₁)
  have : IsMinimal (v.adicCompletionIntegers K)
      ((C₂ • W₂).map (algebraMap K (v.adicCompletion K))) :=
    isMinimal_baseChange_adicCompletion v (C₂ • W₂)
  let ψ : Isogeny (C₁ • W₁).toAffine (C₂ • W₂).toAffine :=
    (variableChangeIsogeny C₂ rfl).comp
      (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ W₁.toAffine)))
  have hψc := pullbackDifferential_variableChangeIsogeny_comp_comp φ hc C₁ C₂
    (inv_smul_smul C₁ W₁.toAffine) rfl
  have hψdeg : ψ.degree = φ.degree := by simp [ψ]
  have hψk : ψ.finiteKummerRatio v = φ.finiteKummerRatio v := by simp [ψ]
  have h2v : (2 : v.adicCompletion K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]
    exact (RingHom.injective _).ne h2
  have h := zpow_log_valued_mul_tamagawaNumber_mul_kummerRatio v
    (E₁ := (C₁ • W₁).map (algebraMap K (v.adicCompletion K)))
    (E₂ := (C₂ • W₂).map (algebraMap K (v.adicCompletion K)))
    (ψ.map (algebraMap K (v.adicCompletion K)))
    (map_pullbackDifferential_invariantDifferential_eq_smul ψ
      (algebraMap K (v.adicCompletion K)) hψc)
    h2v (by rwa [degree_map, hψdeg])
  have hval : Valued.v (algebraMap K (v.adicCompletion K) (c * C₂.u / C₁.u)) =
      v.valuation K (c * C₂.u / C₁.u) := by
    simp [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  rw [hval, ← tamagawaNumberAt_eq_valued (C₁ • W₁) v, ← tamagawaNumberAt_eq_valued (C₂ • W₂) v,
    tamagawaNumberAt_smul, tamagawaNumberAt_smul, ← finiteKummerRatio_def, hψk] at h
  exact h

/-- **Local Tamagawa–Kummer identity over `K` (`adicAbv` form)**: under the hypotheses of
`zpow_log_valuation_mul_tamagawaNumberAt_mul_finiteKummerRatio`,
`|c u₂ / u₁|_v · c_v(W₁) · φ.finiteKummerRatio v = c_v(W₂)` in `ℝ`. -/
theorem adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (v : HeightOneSpectrum R) {C₁ C₂ : VariableChange K}
    (hC₁ : IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • W₁))
    (hC₂ : IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • W₂))
    (h2 : (2 : K) ≠ 0) (hn : (φ.degree : R) ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv K v (c * C₂.u / C₁.u) *
        (W₁.tamagawaNumberAt v : ℝ) * (φ.finiteKummerRatio v : ℝ) =
      (W₂.tamagawaNumberAt v : ℝ) := by
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hdeg0 : (φ.degree : K) ≠ 0 := by
    rw [← map_natCast (algebraMap R K), map_ne_zero_iff _ (IsFractionRing.injective R K)]
    exact hn
  have hc0 : c ≠ 0 :=
    left_ne_zero_of_mul ((φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc').trans_ne hdeg0)
  have hα0 : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have hQ := congrArg (Rat.cast : ℚ → ℝ)
    (zpow_log_valuation_mul_tamagawaNumberAt_mul_finiteKummerRatio φ hc v hC₁ hC₂ h2 hn)
  push_cast at hQ
  rwa [← IsDedekindDomain.HeightOneSpectrum.adicAbv_eq_absNorm_zpow R v hα0] at hQ

/-- **Local Tamagawa–Kummer identity on `v`-minimal equations over `K`**: if `W₁` and `W₂` are
already minimal over `Localization.AtPrime v.asIdeal`, then
`|c|_v · c_v(W₁) · φ.finiteKummerRatio v = c_v(W₂)`. -/
theorem adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio_of_isMinimal
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (v : HeightOneSpectrum R)
    [h₁ : IsMinimal (Localization.AtPrime v.asIdeal) W₁]
    [h₂ : IsMinimal (Localization.AtPrime v.asIdeal) W₂]
    (h2 : (2 : K) ≠ 0) (hn : (φ.degree : R) ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv K v c *
        (W₁.tamagawaNumberAt v : ℝ) * (φ.finiteKummerRatio v : ℝ) =
      (W₂.tamagawaNumberAt v : ℝ) := by
  have hC₁ : IsMinimal (Localization.AtPrime v.asIdeal) ((1 : VariableChange K) • W₁) := by
    simpa only [one_smul] using h₁
  have hC₂ : IsMinimal (Localization.AtPrime v.asIdeal) ((1 : VariableChange K) • W₂) := by
    simpa only [one_smul] using h₂
  simpa [VariableChange.one_def] using
    adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio φ hc v hC₁ hC₂ h2 hn

/-- **Local Kummer ratio of an endomorphism**: for any elliptic curve `W` over `K` (without any
minimality assumption on `W`) and any endomorphism `φ : W → W` with `φ^*ω = c ω`, `(2 : K) ≠ 0`,
and `(φ.degree : R) ≠ 0`, `|c|_v · φ.finiteKummerRatio v = 1`. -/
theorem adicAbv_mul_finiteKummerRatio_self {W : WeierstrassCurve K} [W.IsElliptic]
    (φ : Isogeny W.toAffine W.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W.toAffine) =
      c • Affine.invariantDifferential W.toAffine)
    (v : HeightOneSpectrum R) (h2 : (2 : K) ≠ 0) (hn : (φ.degree : R) ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv K v c * (φ.finiteKummerRatio v : ℝ) = 1 := by
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal)
  have hmin : IsMinimal (Localization.AtPrime v.asIdeal) (C • W) := by
    rw [hC]
    infer_instance
  have h := adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio φ hc v hmin hmin h2 hn
  have hcu : c * C.u / C.u = c := mul_div_cancel_right₀ c C.u.ne_zero
  have htam : (W.tamagawaNumberAt v : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (W.tamagawaNumberAt_pos v).ne'
  rw [hcu] at h
  exact mul_left_cancel₀ htam (by linarith)

end HasFiniteQuotients

end Local

/-! ### Global finite-place products over Dedekind domains, number fields, and `ℚ` -/

section GlobalFinite

/-- Product of the local Tamagawa–Kummer identities over all height-one primes of a Dedekind domain
`R` in characteristic zero, for equations with globally minimal models `C₁ • W₁` and `C₂ • W₂`
over `R`. -/
theorem finprod_adicAbv_mul_tamagawaProduct_mul_finprod_finiteKummerRatio
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    {C₁ C₂ : VariableChange K} (hC₁ : IsGlobalMinimal R (C₁ • W₁))
    (hC₂ : IsGlobalMinimal R (C₂ • W₂)) :
    (∏ᶠ v : HeightOneSpectrum R,
        NumberField.HeightOneSpectrum.adicAbv K v (c * C₂.u / C₁.u)) *
      (W₁.tamagawaProduct (R := R) : ℝ) *
      ((∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v : ℚ) : ℝ) =
      (W₂.tamagawaProduct (R := R) : ℝ) := by
  have : CharZero R := (algebraMap R K).charZero
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  have hα0 : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have hf_abv := IsDedekindDomain.HeightOneSpectrum.hasFiniteMulSupport_adicAbv (R := R) hα0
  have hf_tam₁ := (W₁.hasFiniteMulSupport_tamagawaNumberAt (R := R)).fun_comp
    (Nat.cast_one (R := ℝ))
  have hf_kum_Q := φ.hasFiniteMulSupport_finiteKummerRatio (R := R)
    (Nat.cast_ne_zero.mpr φ.degree_ne_zero)
  have hf_kum := hf_kum_Q.fun_comp (Rat.cast_one (α := ℝ))
  have hcast : ((∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v : ℚ) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum R, (φ.finiteKummerRatio v : ℝ) := by
    simpa using map_finprod (Rat.castHom ℝ) hf_kum_Q
  rw [tamagawaProduct_def, tamagawaProduct_def, Nat.cast_finprod', Nat.cast_finprod', hcast,
    ← finprod_mul_distrib hf_abv hf_tam₁,
    ← finprod_mul_distrib (hf_abv.fun_mul hf_tam₁) hf_kum]
  exact finprod_congr fun v ↦
    adicAbv_mul_tamagawaNumberAt_mul_finiteKummerRatio φ hc v (hC₁.isMinimal v)
      (hC₂.isMinimal v) two_ne_zero (Nat.cast_ne_zero.mpr φ.degree_ne_zero)

section NumberField

variable {K : Type*} [Field K] [NumberField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Global finite-place Tamagawa–Kummer formula over a number field**: if `C₁ • W₁` and `C₂ • W₂`
are globally minimal over `𝓞 K` and `φ^*ω₂ = c ω₁`, then
`c(W₁) · ∏_v φ.finiteKummerRatio v = |Algebra.norm ℚ (c * C₂.u / C₁.u)| · c(W₂)`. -/
theorem tamagawaProduct_mul_finprod_finiteKummerRatio
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    {C₁ C₂ : VariableChange K} (hC₁ : IsGlobalMinimal (𝓞 K) (C₁ • W₁))
    (hC₂ : IsGlobalMinimal (𝓞 K) (C₂ • W₂)) :
    (W₁.tamagawaProduct (R := 𝓞 K) : ℚ) *
        (∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v) =
      |Algebra.norm ℚ (c * C₂.u / C₁.u)| * (W₂.tamagawaProduct (R := 𝓞 K) : ℚ) := by
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  have hα0 : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have hR := finprod_adicAbv_mul_tamagawaProduct_mul_finprod_finiteKummerRatio φ hc hC₁ hC₂
  have habv : (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      NumberField.HeightOneSpectrum.adicAbv K v (c * C₂.u / C₁.u)) =
      |(Algebra.norm ℚ (c * C₂.u / C₁.u) : ℝ)|⁻¹ := by
    simpa only [TauCeti.GlobalNumberFields.normalizedAbsValue_inl, Rat.cast_inv,
      Rat.cast_abs] using TauCeti.GlobalNumberFields.finprod_normalizedAbsValue_inl hα0
  rw [habv] at hR
  have hnorm0 : |(Algebra.norm ℚ (c * C₂.u / C₁.u) : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hα0))
  refine Rat.cast_injective (α := ℝ) ?_
  rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_abs, Rat.cast_natCast, Rat.cast_natCast]
  calc (W₁.tamagawaProduct (R := 𝓞 K) : ℝ) *
        ((∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v : ℚ) : ℝ)
      = |(Algebra.norm ℚ (c * C₂.u / C₁.u) : ℝ)| *
          (|(Algebra.norm ℚ (c * C₂.u / C₁.u) : ℝ)|⁻¹ *
            (W₁.tamagawaProduct (R := 𝓞 K) : ℝ) *
            ((∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v : ℚ) : ℝ)) := by
          field_simp [hnorm0]
    _ = |(Algebra.norm ℚ (c * C₂.u / C₁.u) : ℝ)| * (W₂.tamagawaProduct (R := 𝓞 K) : ℝ) := by
          rw [hR]

/-- **Global finite-place Tamagawa–Kummer formula on globally minimal equations over `𝓞 K`**. -/
theorem tamagawaProduct_mul_finprod_finiteKummerRatio_of_isGlobalMinimal
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (h₁ : IsGlobalMinimal (𝓞 K) W₁) (h₂ : IsGlobalMinimal (𝓞 K) W₂) :
    (W₁.tamagawaProduct (R := 𝓞 K) : ℚ) *
        (∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v) =
      |Algebra.norm ℚ c| * (W₂.tamagawaProduct (R := 𝓞 K) : ℚ) := by
  have hC₁ : IsGlobalMinimal (𝓞 K) ((1 : VariableChange K) • W₁) := by
    simpa only [one_smul] using h₁
  have hC₂ : IsGlobalMinimal (𝓞 K) ((1 : VariableChange K) • W₂) := by
    simpa only [one_smul] using h₂
  simpa [VariableChange.one_def] using
    tamagawaProduct_mul_finprod_finiteKummerRatio φ hc hC₁ hC₂

/-- **Finite-place Kummer product of an endomorphism over any number field**: for any elliptic curve
`W` over a number field `K` (without assuming a global minimal model over `𝓞 K`) and any
endomorphism `φ : W → W` with `φ^*ω = c ω`,
`∏_v φ.finiteKummerRatio v = |Algebra.norm ℚ c|`. -/
theorem finprod_finiteKummerRatio_self {W : WeierstrassCurve K} [W.IsElliptic]
    (φ : Isogeny W.toAffine W.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W.toAffine) =
      c • Affine.invariantDifferential W.toAffine) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v) = |Algebra.norm ℚ c| := by
  have : CharZero (𝓞 K) := (algebraMap (𝓞 K) K).charZero
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  have hf_abv := TauCeti.GlobalNumberFields.hasFiniteMulSupport_adicAbv hc0
  have hf_kum_Q := φ.hasFiniteMulSupport_finiteKummerRatio (R := 𝓞 K)
    (Nat.cast_ne_zero.mpr φ.degree_ne_zero)
  have hf_kum := hf_kum_Q.fun_comp (Rat.cast_one (α := ℝ))
  have hcast : ((∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v : ℚ) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (φ.finiteKummerRatio v : ℝ) := by
    simpa using map_finprod (Rat.castHom ℝ) hf_kum_Q
  have hprod : (∏ᶠ v : HeightOneSpectrum (𝓞 K), NumberField.HeightOneSpectrum.adicAbv K v c) *
      ((∏ᶠ v : HeightOneSpectrum (𝓞 K), φ.finiteKummerRatio v : ℚ) : ℝ) = 1 := by
    rw [hcast, ← finprod_mul_distrib hf_abv hf_kum]
    exact finprod_eq_one_of_forall_eq_one fun v ↦
      adicAbv_mul_finiteKummerRatio_self φ hc v two_ne_zero (Nat.cast_ne_zero.mpr φ.degree_ne_zero)
  have habv : (∏ᶠ v : HeightOneSpectrum (𝓞 K), NumberField.HeightOneSpectrum.adicAbv K v c) =
      |(Algebra.norm ℚ c : ℝ)|⁻¹ := by
    simpa only [TauCeti.GlobalNumberFields.normalizedAbsValue_inl, Rat.cast_inv,
      Rat.cast_abs] using TauCeti.GlobalNumberFields.finprod_normalizedAbsValue_inl hc0
  rw [habv] at hprod
  have hnorm0 : |(Algebra.norm ℚ c : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hc0))
  refine Rat.cast_injective (α := ℝ) ?_
  rw [Rat.cast_abs]
  exact ((inv_mul_eq_one₀ hnorm0).mp hprod).symm

end NumberField

section RationalFinite

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **Global finite-place Tamagawa–Kummer formula over `ℚ`**: if `C₁ • E₁` and `C₂ • E₂` are
globally minimal over `ℤ` and `φ^*ω₂ = c ω₁`, then
`c(E₁) · ∏_p φ.finiteKummerRatio p = |c · C₂.u / C₁.u| · c(E₂)`. -/
theorem tamagawaProduct_mul_finprod_finiteKummerRatio_rat
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    (E₁.tamagawaProduct (R := ℤ) : ℚ) *
        (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) =
      |c * C₂.u / C₁.u| * (E₂.tamagawaProduct (R := ℤ) : ℚ) := by
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  have hα0 : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have hR := finprod_adicAbv_mul_tamagawaProduct_mul_finprod_finiteKummerRatio φ hc hC₁ hC₂
  rw [IsDedekindDomain.HeightOneSpectrum.finprod_adicAbv_rat hα0] at hR
  have habs0 : |((c * C₂.u / C₁.u : ℚ) : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hα0)
  refine Rat.cast_injective (α := ℝ) ?_
  rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_abs, Rat.cast_natCast, Rat.cast_natCast]
  calc (E₁.tamagawaProduct (R := ℤ) : ℝ) *
        ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ)
      = |((c * C₂.u / C₁.u : ℚ) : ℝ)| *
          (|((c * C₂.u / C₁.u : ℚ) : ℝ)|⁻¹ *
            (E₁.tamagawaProduct (R := ℤ) : ℝ) *
            ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ)) := by
          field_simp [habs0]
    _ = |((c * C₂.u / C₁.u : ℚ) : ℝ)| * (E₂.tamagawaProduct (R := ℤ) : ℝ) := by rw [hR]

/-- **Global finite-place Tamagawa–Kummer formula on globally minimal equations over `ℤ`**. -/
theorem tamagawaProduct_mul_finprod_finiteKummerRatio_rat_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    (E₁.tamagawaProduct (R := ℤ) : ℚ) *
        (∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) =
      |c| * (E₂.tamagawaProduct (R := ℤ) : ℚ) := by
  have hC₁ : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E₁) := by
    simpa only [one_smul] using h₁
  have hC₂ : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E₂) := by
    simpa only [one_smul] using h₂
  simpa [VariableChange.one_def] using
    tamagawaProduct_mul_finprod_finiteKummerRatio_rat φ hc hC₁ hC₂

end RationalFinite

end GlobalFinite

/-! ### Archimedean period–Kummer identity and global period–Tamagawa transformation over `ℚ` -/

section PeriodTamagawa

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **Archimedean period–Kummer identity over `ℚ`**: if `φ : E₁ → E₂` pulls back the invariant
differential as `φ^*ω₂ = c ω₁` and `C₁`, `C₂` carry `E₁`, `E₂` to globally minimal equations over
`ℤ`, then `|c · C₂.u / C₁.u| · Ω(E₁) · φ.realKummerRatio = Ω(E₂)`. -/
theorem abs_mul_minimalRealPeriod_mul_realKummerRatio (φ : Isogeny E₁.toAffine E₂.toAffine)
    {c : ℚ} (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod * φ.realKummerRatio =
      E₂.minimalRealPeriod := by
  classical
  have h := abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul φ hc hC₁ hC₂
  have := (Hom.ofIsogeny (φ.baseChange ℝ)).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have hker0 : (Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hk : (φ.realKummerRatio : ℝ) =
      ((Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index : ℝ) /
        Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker := by
    rw [realKummerRatio_def, kummerRatio_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
    -- `Isogeny.baseChange ℝ φ` is defined as `φ.map (algebraMap ℚ ℝ)`.
    rfl
  rw [hk, ← mul_div_assoc, div_eq_iff hker0, h, mul_comm]

/-- **Archimedean period–Kummer identity on globally minimal equations over `ℤ`**: if `E₁` and `E₂`
are globally minimal over `ℤ` and `φ^*ω₂ = c ω₁`, then
`|c| · Ω(E₁) · φ.realKummerRatio = Ω(E₂)`. -/
theorem abs_mul_minimalRealPeriod_mul_realKummerRatio_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    |(c : ℝ)| * E₁.minimalRealPeriod * φ.realKummerRatio = E₂.minimalRealPeriod := by
  have hC₁ : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E₁) := by
    simpa only [one_smul] using h₁
  have hC₂ : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E₂) := by
    simpa only [one_smul] using h₂
  simpa [VariableChange.one_def] using
    abs_mul_minimalRealPeriod_mul_realKummerRatio φ hc hC₁ hC₂

/-- **The global period–Tamagawa transformation law under an isogeny over `ℚ`** (Cassels): for any
isogeny `φ : E₁ → E₂` of elliptic curves over `ℚ`,
`Ω(E₁) · c(E₁) · φ.kummerRatioProduct = Ω(E₂) · c(E₂)`,
where `Ω(Eᵢ)` is the minimal real period and `c(Eᵢ) = ∏_p c_p(Eᵢ)` is the global Tamagawa product.
Neither `E₁` nor `E₂` need be given by a minimal equation. -/
theorem minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct
    (φ : Isogeny E₁.toAffine E₂.toAffine) :
    E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) * φ.kummerRatioProduct =
      E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  obtain ⟨C₁, hC₁_red⟩ := exists_isReducedMinimal_smul E₁
  obtain ⟨C₂, hC₂_red⟩ := exists_isReducedMinimal_smul E₂
  have hC₁ : IsGlobalMinimal ℤ (C₁ • E₁) := hC₁_red.isGlobalMinimal
  have hC₂ : IsGlobalMinimal ℤ (C₂ • E₂) := hC₂_red.isGlobalMinimal
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  have hα0 : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have habs0 : |((c * C₂.u / C₁.u : ℚ) : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hα0)
  have hreal := abs_mul_minimalRealPeriod_mul_realKummerRatio φ hc hC₁ hC₂
  have hfin := congrArg (Rat.cast : ℚ → ℝ)
    (tamagawaProduct_mul_finprod_finiteKummerRatio_rat φ hc hC₁ hC₂)
  rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_abs, Rat.cast_natCast, Rat.cast_natCast] at hfin
  rw [kummerRatioProduct_def, Rat.cast_mul]
  refine mul_left_cancel₀ habs0 ?_
  calc |((c * C₂.u / C₁.u : ℚ) : ℝ)| *
        (E₁.minimalRealPeriod * (E₁.tamagawaProduct (R := ℤ) : ℝ) *
          ((φ.realKummerRatio : ℝ) *
            ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ)))
      = (|((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ)) *
          ((E₁.tamagawaProduct (R := ℤ) : ℝ) *
            ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ)) := by ring
    _ = E₂.minimalRealPeriod *
          (|((c * C₂.u / C₁.u : ℚ) : ℝ)| * (E₂.tamagawaProduct (R := ℤ) : ℝ)) := by
          rw [hreal, hfin]
    _ = |((c * C₂.u / C₁.u : ℚ) : ℝ)| *
          (E₂.minimalRealPeriod * (E₂.tamagawaProduct (R := ℤ) : ℝ)) := by ring

/-- **Every endomorphism of an elliptic curve over `ℚ` has global Kummer ratio product one.** -/
theorem kummerRatioProduct_self {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (φ : Isogeny E.toAffine E.toAffine) :
    φ.kummerRatioProduct = 1 := by
  have h := minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct φ
  have hpos : 0 < E.minimalRealPeriod * (E.tamagawaProduct (R := ℤ) : ℝ) :=
    mul_pos E.minimalRealPeriod_pos (Nat.cast_pos.mpr (E.tamagawaProduct_pos (R := ℤ)))
  refine Rat.cast_injective (α := ℝ) ?_
  rw [Rat.cast_one]
  exact mul_left_cancel₀ hpos.ne' (by simpa only [mul_one] using h)

/-- **The global Kummer ratio products of dual isogenies over `ℚ` multiply to one.** -/
@[simp]
theorem kummerRatioProduct_mul_dual (φ : Isogeny E₁.toAffine E₂.toAffine) :
    φ.kummerRatioProduct * φ.dual.kummerRatioProduct = 1 := by
  rw [mul_comm, ← kummerRatioProduct_comp, kummerRatioProduct_self]

/-- **The global Kummer ratio product of the dual isogeny over `ℚ` is the inverse of that of `φ`.**
-/
theorem kummerRatioProduct_dual (φ : Isogeny E₁.toAffine E₂.toAffine) :
    φ.dual.kummerRatioProduct = (φ.kummerRatioProduct)⁻¹ :=
  eq_inv_of_mul_eq_one_right (kummerRatioProduct_mul_dual φ)

end PeriodTamagawa

end TauCeti.Isogeny

end
