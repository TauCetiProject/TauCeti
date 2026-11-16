/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Ratio
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MinimalRealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Index
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AdicCompletion
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GlobalExistence
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny
import TauCeti.NumberTheory.NumberField.Global.Places.Rat
import TauCeti.RingTheory.DedekindDomain.SelmerGroup

/-!
# Local Tamagawa and global period–Tamagawa–Kummer formulas for isogenies

Let `φ : E₁ → E₂` be an isogeny of elliptic curves. At a finite place `u` with finite residue
field `κ(u)` of size `q_u`, if `E₁` and `E₂` are minimal over the completed valuation ring `O_u`,
`2 ≠ 0` in `F_u`, `(deg φ : A) ≠ 0`, and `φ^*ω₂ = c ω₁`, then combining the deep formal-level
index identity (`eventually_index_range_pointMapHom_mul_index_formalPointFiltration`) with the
decomposition of formal-level indices (`index_formalPointFiltration_eq_mul_tamagawaNumber`) and the
equality of nonsingular reduction counts (`natCard_point_reduction_eq`) yields the local
Tamagawa–differential–Kummer relation:

`q_u ^ log (v c) · φ.kummerRatio · c_u(E₁) = c_u(E₂)`.

Passing from arbitrary models to minimal models replaces `c` by `c · u₂ / u₁`, matching the real
period transformation `|c · u₂ / u₁| · Ω(E₁) · φ.realKummerRatio = Ω(E₂)`. Multiplying the local
identities over all height-one primes of a Dedekind domain `R` with finite quotients gives the
finite-place product identity
(`finprod_zpow_log_valuation_mul_finiteKummerRatio_mul_tamagawaProduct`). Over `ℚ`, combining this
with the real relation and the product formula
(`Rat.HeightOneSpectrum.abs_mul_finprod_zpow_log_valuation`) eliminates the differential constant
and gives Cassels' global period–Tamagawa–Kummer product formula:

`Ω(E₁) · (∏_p c_p(E₁)) · φ.kummerRatioProduct = Ω(E₂) · (∏_p c_p(E₂))`.

In particular, `φ.kummerRatioProduct * φ.dual.kummerRatioProduct = 1`.

## Main results

* `TauCeti.Isogeny.zpow_log_valued_mul_kummerRatio_mul_tamagawaNumber_of_isMinimal` and
  `TauCeti.Isogeny.zpow_log_valued_mul_kummerRatio_mul_tamagawaNumber`: the local
  Tamagawa–differential–Kummer ratio formula over an adic completion `F_u`.
* `TauCeti.Isogeny.zpow_log_valuation_mul_finiteKummerRatio_mul_tamagawaNumberAt_of_isMinimal` and
  `TauCeti.Isogeny.zpow_log_valuation_mul_finiteKummerRatio_mul_tamagawaNumberAt`: the same
  formula for a curve over a global fraction field `K` at a height-one prime `v`.
* `TauCeti.Isogeny.finprod_zpow_log_valuation_mul_finiteKummerRatio_mul_tamagawaProduct`: the
  product of the finite-place identities over all height-one primes of `R`.
* `TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_realKummerRatio` and
  `TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_realKummerRatio_of_isGlobalMinimal`: the real
  period transformation written with `realKummerRatio`.
* `TauCeti.Isogeny.minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct`: Cassels'
  global period–Tamagawa–Kummer formula over `ℚ` for arbitrary Weierstrass equations.
* `TauCeti.Isogeny.kummerRatioProduct_mul_dual` and `TauCeti.Isogeny.kummerRatioProduct_dual`:
  the Kummer ratio products of an isogeny and its dual over `ℚ` are reciprocal.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199, Lemma 3.2.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.
-/

public section

open IsDedekindDomain IsLocalRing ValuativeRel WeierstrassCurve WeierstrassCurve.Affine
  WithZero Filter

namespace TauCeti.Isogeny

/-- Conjugating an isogeny `φ` by changes of variables `C₁` and `C₂` multiplies its invariant
differential pullback constant by `C₂.u / C₁.u`. -/
private theorem pullbackDifferential_conj_variableChange {F : Type*} [Field F]
    {W₁ W₂ : WeierstrassCurve F}
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (C₁ C₂ : VariableChange F) :
    ((variableChangeIsogeny C₂ rfl).comp
        (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ W₁)))).pullbackDifferential
        (invariantDifferential (C₂ • W₂).toAffine) =
      (c * (C₂.u : F) / (C₁.u : F)) • invariantDifferential (C₁ • W₁).toAffine := by
  rw [pullbackDifferential_comp, LinearMap.comp_apply,
    pullbackDifferential_variableChangeIsogeny_invariantDifferential,
    pullbackDifferential_comp, LinearMap.comp_apply,
    map_smul, hc, smul_smul, map_smul,
    pullbackDifferential_variableChangeIsogeny_invariantDifferential, smul_smul]
  congr 1
  simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]
  ring

section Local

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A)

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "R_u" =>
  Valuation.valuationSubring
    (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))

private local instance : IsDiscreteValuationRing R_u :=
  inferInstanceAs (IsDiscreteValuationRing O_u)

/-- The minimal-model local Tamagawa–differential–Kummer relation for models already given over
`O_u`. -/
private theorem zpow_log_valued_mul_kummerRatio_mul_tamagawaNumber_of_baseChange
    [Finite (A ⧸ u.asIdeal)] {C₁ C₂ : WeierstrassCurve O_u}
    [(C₁.baseChange F_u).IsElliptic] [(C₂.baseChange F_u).IsElliptic]
    [IsMinimal O_u (C₁.baseChange F_u)] [IsMinimal O_u (C₂.baseChange F_u)]
    (φ : Isogeny (C₁.baseChange F_u).toAffine (C₂.baseChange F_u).toAffine)
    {c : F_u}
    (hc : φ.pullbackDifferential (invariantDifferential (C₂.baseChange F_u).toAffine) =
      c • invariantDifferential (C₁.baseChange F_u).toAffine)
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    (Nat.card (ResidueField O_u) : ℚ) ^ WithZero.log (Valued.v c) *
        φ.kummerRatio * (C₁.baseChange F_u).tamagawaNumber Valued.v =
      (C₂.baseChange F_u).tamagawaNumber Valued.v := by
  classical
  have hdegF : (φ.degree : F) ≠ 0 := by
    rw [← map_natCast (algebraMap A F)]
    exact map_ne_zero_of_mem_nonZeroDivisors (algebraMap A F)
      (IsFractionRing.injective A F) (mem_nonZeroDivisors_of_ne_zero hn)
  have hdegFu : (φ.degree : F_u) ≠ 0 := by
    rw [← map_natCast (algebraMap F F_u)]
    exact (map_ne_zero_iff (algebraMap F F_u) (RingHom.injective _)).2 hdegF
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 <|
    (isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul φ hc).1
      (φ.isSeparable_dual_and_self_iff.2 hdegFu).2
  have : Finite (ResidueField O_u) :=
    Finite.of_equiv _ (u.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have : Finite (ResidueField R_u) := inferInstanceAs (Finite (ResidueField O_u))
  have hmin₁ : IsMinimal 𝒪[F_u] (C₁.baseChange F_u) :=
    (isMinimal_adicCompletionIntegers_iff_isMinimal_integer u _).1 inferInstance
  have hmin₂ : IsMinimal 𝒪[F_u] (C₂.baseChange F_u) :=
    (isMinimal_adicCompletionIntegers_iff_isMinimal_integer u _).1 inferInstance
  have hred :
      Nat.card ((integralModel R_u (C₁.baseChange F_u)).map (residue R_u)).toAffine.Point =
        Nat.card ((integralModel R_u (C₂.baseChange F_u)).map (residue R_u)).toAffine.Point := by
    rw [← C₁.natCard_point_reduction_baseChange_adicCompletion,
      ← C₂.natCard_point_reduction_baseChange_adicCompletion]
    exact φ.natCard_point_reduction_eq
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_index_range_pointMapHom_mul_index_formalPointFiltration u (φ := φ) hc h2 hn)
  set m : ℤ := WithZero.log (Valued.v c)
  set k' : ℕ := max N m.natAbs
  set j' : ℕ := ((k' : ℤ) - m).toNat
  have hj' : (j' : ℤ) = (k' : ℤ) - m := Int.toNat_of_nonneg (by omega)
  have hjk : Valued.v c * exp ((j' + 1 : ℕ) : ℤ) = exp ((k' + 1 : ℕ) : ℤ) := by
    rw [← exp_log hvc, ← exp_add, exp_inj]; push_cast; omega
  have heq := hN (k' + 1) (by omega) (j' + 1) hjk
  rw [C₁.index_formalPointFiltration_eq_mul_tamagawaNumber u k',
    C₂.index_formalPointFiltration_eq_mul_tamagawaNumber u j', hred] at heq
  have hq_ne : (Nat.card (ResidueField O_u) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hr_ne :
      (Nat.card ((integralModel R_u (C₂.baseChange F_u)).map (residue R_u)).toAffine.Point : ℚ) ≠
        0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : Finite (Hom.ofIsogeny φ).pointMapHom.ker :=
    (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  have hker_ne : (Nat.card (Hom.ofIsogeny φ).pointMapHom.ker : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hq_zpow : (Nat.card (ResidueField O_u) : ℚ) ^ k' =
      (Nat.card (ResidueField O_u) : ℚ) ^ m * (Nat.card (ResidueField O_u) : ℚ) ^ j' := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq_ne]; congr 1; omega
  have heqQ : ((Hom.ofIsogeny φ).pointMapHom.range.index : ℚ) *
      ((Nat.card (ResidueField O_u) : ℚ) ^ k' *
        Nat.card ((integralModel R_u (C₂.baseChange F_u)).map (residue R_u)).toAffine.Point *
        (C₁.baseChange F_u).tamagawaNumber Valued.v) =
      ((Nat.card (ResidueField O_u) : ℚ) ^ j' *
        Nat.card ((integralModel R_u (C₂.baseChange F_u)).map (residue R_u)).toAffine.Point *
        (C₂.baseChange F_u).tamagawaNumber Valued.v) *
        Nat.card (Hom.ofIsogeny φ).pointMapHom.ker := by
    exact_mod_cast heq
  rw [hq_zpow, ← φ.kummerRatio_mul_card_ker] at heqQ
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero j' hq_ne) hr_ne) hker_ne)
  linear_combination heqQ

/-- **Local Tamagawa–differential–Kummer ratio formula for minimal models over an adic completion.**
If `φ : W₁ → W₂` is an isogeny between minimal elliptic curves over `F_u` with finite residue field,
`2 ≠ 0` in `F_u`, `(deg φ : A) ≠ 0`, and `φ^*ω₂ = c ω₁`, then
`(#κ(u)) ^ log (v c) · φ.kummerRatio · c_u(W₁) = c_u(W₂)`. -/
theorem zpow_log_valued_mul_kummerRatio_mul_tamagawaNumber_of_isMinimal
    [Finite (A ⧸ u.asIdeal)] {W₁ W₂ : WeierstrassCurve F_u}
    [W₁.IsElliptic] [W₂.IsElliptic] [IsMinimal O_u W₁] [IsMinimal O_u W₂]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    (Nat.card (ResidueField O_u) : ℚ) ^ WithZero.log (Valued.v c) *
        φ.kummerRatio * W₁.tamagawaNumber Valued.v =
      W₂.tamagawaNumber Valued.v := by
  obtain ⟨C₁, rfl⟩ := (inferInstance : IsIntegral O_u W₁).integral
  obtain ⟨C₂, rfl⟩ := (inferInstance : IsIntegral O_u W₂).integral
  exact zpow_log_valued_mul_kummerRatio_mul_tamagawaNumber_of_baseChange u φ hc h2 hn

/-- **Local Tamagawa–differential–Kummer ratio formula for arbitrary models over an adic
completion.** If `C₁` and `C₂` carry `W₁` and `W₂` to minimal models over `O_u`, then
`(#κ(u)) ^ log (v (c · C₂.u / C₁.u)) · φ.kummerRatio · c_u(W₁) = c_u(W₂)`. -/
theorem zpow_log_valued_mul_kummerRatio_mul_tamagawaNumber
    [Finite (A ⧸ u.asIdeal)] {W₁ W₂ : WeierstrassCurve F_u}
    [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0)
    {C₁ C₂ : VariableChange F_u} [IsMinimal O_u (C₁ • W₁)] [IsMinimal O_u (C₂ • W₂)] :
    (Nat.card (ResidueField O_u) : ℚ) ^ WithZero.log (Valued.v (c * C₂.u / C₁.u)) *
        φ.kummerRatio * W₁.tamagawaNumber Valued.v =
      W₂.tamagawaNumber Valued.v := by
  let ψ : Isogeny (C₁ • W₁).toAffine (C₂ • W₂).toAffine :=
    (variableChangeIsogeny C₂ rfl).comp
      (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ W₁)))
  have hdeg : ψ.degree = φ.degree := by
    simp [ψ, degree_comp, degree_variableChangeIsogeny]
  have hk : ψ.kummerRatio = φ.kummerRatio := by
    simp only [ψ, kummerRatio_comp,
      kummerRatio_eq_one_of_degree_eq_one _ (degree_variableChangeIsogeny C₂ rfl),
      kummerRatio_eq_one_of_degree_eq_one _ (degree_variableChangeIsogeny C₁⁻¹ _),
      one_mul, mul_one]
  have h := zpow_log_valued_mul_kummerRatio_mul_tamagawaNumber_of_isMinimal u ψ
    (pullbackDifferential_conj_variableChange φ hc C₁ C₂) h2 (hdeg.symm ▸ hn)
  simpa only [hk, tamagawaNumber_smul] using h

end Local

section GlobalFinite

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Local Tamagawa–differential–Kummer ratio formula at a finite place of a global fraction
field, for minimal equations.** If `W₁` and `W₂` are minimal over `Localization.AtPrime v.asIdeal`,
`2 ≠ 0` in `K`, `(deg φ : R) ≠ 0`, and `φ^*ω₂ = c ω₁`, then
`(#(R ⧸ v)) ^ log (v c) · φ.finiteKummerRatio v · c_v(W₁) = c_v(W₂)`. -/
theorem zpow_log_valuation_mul_finiteKummerRatio_mul_tamagawaNumberAt_of_isMinimal
    {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
    (v : HeightOneSpectrum R)
    [IsMinimal (Localization.AtPrime v.asIdeal) W₁]
    [IsMinimal (Localization.AtPrime v.asIdeal) W₂]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hn : (φ.degree : R) ≠ 0) :
    (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation K c) *
        φ.finiteKummerRatio v * W₁.tamagawaNumberAt v =
      W₂.tamagawaNumberAt v := by
  have : Finite (R ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have : IsMinimal (v.adicCompletionIntegers K) (W₁.baseChange (v.adicCompletion K)) :=
    (isMinimal_baseChange_adicCompletion_iff v W₁).2 inferInstance
  have : IsMinimal (v.adicCompletionIntegers K) (W₂.baseChange (v.adicCompletion K)) :=
    (isMinimal_baseChange_adicCompletion_iff v W₂).2 inferInstance
  have h2' : (2 : v.adicCompletion K) ≠ 0 := by
    simpa [map_ofNat] using
      (map_ne_zero_iff (algebraMap K (v.adicCompletion K)) (RingHom.injective _)).2 h2
  have hn' : ((φ.baseChange (v.adicCompletion K)).degree : R) ≠ 0 := by
    have hdeg : (φ.baseChange (v.adicCompletion K)).degree = φ.degree := degree_map _ _
    rwa [hdeg]
  have hcard : Nat.card (R ⧸ v.asIdeal) =
      Nat.card (ResidueField (v.adicCompletionIntegers K)) :=
    Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  have hval : Valued.v (algebraMap K (v.adicCompletion K) c) = v.valuation K c := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]
  have h := zpow_log_valued_mul_kummerRatio_mul_tamagawaNumber_of_isMinimal v
    (W₁ := W₁.baseChange (v.adicCompletion K)) (W₂ := W₂.baseChange (v.adicCompletion K))
    (φ.baseChange (v.adicCompletion K))
    (map_pullbackDifferential_invariantDifferential_eq_smul φ
      (algebraMap K (v.adicCompletion K)) hc)
    h2' hn'
  have hk : (φ.baseChange (v.adicCompletion K)).kummerRatio = φ.finiteKummerRatio v :=
    (φ.finiteKummerRatio_def v).symm
  rw [← hcard, hval, hk,
    ← W₁.tamagawaNumberAt_eq_tamagawaNumber_valued v,
    ← W₂.tamagawaNumberAt_eq_tamagawaNumber_valued v] at h
  exact h

/-- **Local Tamagawa–differential–Kummer ratio formula at a finite place of a global fraction
field, for arbitrary equations.** If `C₁` and `C₂` carry `W₁` and `W₂` to minimal equations over
`Localization.AtPrime v.asIdeal`, then
`(#(R ⧸ v)) ^ log (v (c · C₂.u / C₁.u)) · φ.finiteKummerRatio v · c_v(W₁) = c_v(W₂)`. -/
theorem zpow_log_valuation_mul_finiteKummerRatio_mul_tamagawaNumberAt
    {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
    (v : HeightOneSpectrum R)
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hn : (φ.degree : R) ≠ 0)
    {C₁ C₂ : VariableChange K}
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • W₁)]
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • W₂)] :
    (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation K (c * C₂.u / C₁.u)) *
        φ.finiteKummerRatio v * W₁.tamagawaNumberAt v =
      W₂.tamagawaNumberAt v := by
  let ψ : Isogeny (C₁ • W₁).toAffine (C₂ • W₂).toAffine :=
    (variableChangeIsogeny C₂ rfl).comp
      (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ W₁)))
  have hdeg : ψ.degree = φ.degree := by
    simp [ψ, degree_comp, degree_variableChangeIsogeny]
  have hk : ψ.finiteKummerRatio v = φ.finiteKummerRatio v := by
    simp only [ψ, finiteKummerRatio_comp,
      finiteKummerRatio_eq_one_of_degree_eq_one _ v (degree_variableChangeIsogeny C₂ rfl),
      finiteKummerRatio_eq_one_of_degree_eq_one _ v (degree_variableChangeIsogeny C₁⁻¹ _),
      one_mul, mul_one]
  have h := zpow_log_valuation_mul_finiteKummerRatio_mul_tamagawaNumberAt_of_isMinimal v ψ
    (pullbackDifferential_conj_variableChange φ hc C₁ C₂) h2 (hdeg.symm ▸ hn)
  simpa only [hk, tamagawaNumberAt_smul] using h

/-- **Product of the finite-place Tamagawa–differential–Kummer identities**: if `C₁` and `C₂` carry
`W₁` and `W₂` to globally minimal equations over `R`, `2 ≠ 0` in `K`, `(deg φ : R) ≠ 0`, and
`φ^*ω₂ = c ω₁`, then multiplying the local identities over all height-one primes of `R` gives
`(∏_v (#(R ⧸ v)) ^ log (v (c · C₂.u / C₁.u))) · (∏_v φ.finiteKummerRatio v) · ∏_v c_v(W₁) =`
`  ∏_v c_v(W₂)`. -/
theorem finprod_zpow_log_valuation_mul_finiteKummerRatio_mul_tamagawaProduct
    {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential W₂.toAffine) =
      c • invariantDifferential W₁.toAffine)
    (h2 : (2 : K) ≠ 0) (hn : (φ.degree : R) ≠ 0)
    {C₁ C₂ : VariableChange K} (hC₁ : IsGlobalMinimal R (C₁ • W₁))
    (hC₂ : IsGlobalMinimal R (C₂ • W₂)) :
    (∏ᶠ v : HeightOneSpectrum R,
        (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation K (c * C₂.u / C₁.u))) *
      (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) *
      (W₁.tamagawaProduct (R := R) : ℚ) =
    (W₂.tamagawaProduct (R := R) : ℚ) := by
  have hdegK : (φ.degree : K) ≠ 0 := by
    rw [← map_natCast (algebraMap R K)]
    exact map_ne_zero_of_mem_nonZeroDivisors (algebraMap R K)
      (IsFractionRing.injective R K) (mem_nonZeroDivisors_of_ne_zero hn)
  have hc0 : c ≠ 0 := (isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul φ hc).1
    (φ.isSeparable_dual_and_self_iff.2 hdegK).2
  set d : K := c * C₂.u / C₁.u
  have hd : d ≠ 0 := div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have hfin_pt (v : HeightOneSpectrum R) :
      (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation K d) *
          φ.finiteKummerRatio v * W₁.tamagawaNumberAt v =
        W₂.tamagawaNumberAt v := by
    have : IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • W₁) := hC₁.isMinimal v
    have : IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • W₂) := hC₂.isMinimal v
    exact zpow_log_valuation_mul_finiteKummerRatio_mul_tamagawaNumberAt v φ hc h2 hn
  have hsupp_d : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦
      (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation K d)) := by
    refine (HeightOneSpectrum.finite_setOfPred_valuation_ne_one (R := R) hd).subset fun v hv ↦ ?_
    simp only [Function.mem_mulSupport, ne_eq, Set.mem_ofPred_eq] at hv ⊢
    intro h1
    exact hv (by rw [h1, log_one, zpow_zero])
  have hsupp_k : Function.HasFiniteMulSupport (φ.finiteKummerRatio (R := R)) :=
    φ.hasFiniteMulSupport_finiteKummerRatio hdegK
  have hsupp_dk := (hsupp_d.union hsupp_k).subset (Function.mulSupport_mul _ _)
  have hsupp_t₁ : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum R ↦ (W₁.tamagawaNumberAt v : ℚ)) := by
    refine (W₁.hasFiniteMulSupport_tamagawaNumberAt (R := R)).subset fun v hv ↦ ?_
    simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
    exact_mod_cast hv
  have hmul :
      (∏ᶠ v : HeightOneSpectrum R,
        ((Nat.card (R ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation K d) *
          φ.finiteKummerRatio v * W₁.tamagawaNumberAt v)) =
      ∏ᶠ v : HeightOneSpectrum R, (W₂.tamagawaNumberAt v : ℚ) :=
    finprod_congr hfin_pt
  rw [finprod_mul_distrib hsupp_dk hsupp_t₁, finprod_mul_distrib hsupp_d hsupp_k] at hmul
  have hcast (W : WeierstrassCurve K) [W.IsElliptic] :
      (∏ᶠ v : HeightOneSpectrum R, (W.tamagawaNumberAt v : ℚ)) =
        (W.tamagawaProduct (R := R) : ℚ) := by
    rw [W.tamagawaProduct_def (R := R)]
    exact (map_finprod (Nat.castRingHom ℚ)
      (W.hasFiniteMulSupport_tamagawaNumberAt (R := R))).symm
  rwa [hcast W₁, hcast W₂] at hmul

end GlobalFinite

section Rational

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **The real period transformation written with the real Kummer ratio**: if `φ : E₁ → E₂` pulls
`ω₂` back to `c ω₁` and `C₁`, `C₂` carry `E₁`, `E₂` to globally minimal models over `ℤ`, then
`|c · C₂.u / C₁.u| · Ω(E₁) · φ.realKummerRatio = Ω(E₂)`. -/
theorem abs_mul_minimalRealPeriod_mul_realKummerRatio (φ : Isogeny E₁.toAffine E₂.toAffine)
    {c : ℚ} (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod * φ.realKummerRatio =
      E₂.minimalRealPeriod := by
  classical
  have h := abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul φ hc hC₁ hC₂
  have : Finite (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker :=
    (Hom.ofIsogeny (φ.baseChange ℝ)).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have hker : (Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hrk : (φ.realKummerRatio : ℝ) * Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker =
      (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index := by
    have hdef : φ.realKummerRatio = (φ.baseChange ℝ).kummerRatio := realKummerRatio_def φ
    rw [hdef]
    exact_mod_cast (φ.baseChange ℝ).kummerRatio_mul_card_ker
  apply mul_right_cancel₀ hker
  calc _ = |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod *
        ((φ.realKummerRatio : ℝ) *
          Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker) := by ring
    _ = _ := by rw [hrk, h]; ring

/-- **The real period transformation for globally minimal equations over `ℚ`, written with
`realKummerRatio`**: `|c| · Ω(E₁) · φ.realKummerRatio = Ω(E₂)`. -/
theorem abs_mul_minimalRealPeriod_mul_realKummerRatio_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal ℤ E₁) (h₂ : IsGlobalMinimal ℤ E₂) :
    |(c : ℝ)| * E₁.minimalRealPeriod * φ.realKummerRatio = E₂.minimalRealPeriod := by
  simpa using abs_mul_minimalRealPeriod_mul_realKummerRatio φ hc
    (C₁ := 1) (C₂ := 1) (by simpa using h₁) (by simpa using h₂)

/-- **Cassels' global period–Tamagawa–Kummer product formula over `ℚ`.** For any isogeny
`φ : E₁ → E₂` of elliptic curves over `ℚ`, the differential scaling constants cancel by the
product formula for `ℚ`, leaving
`Ω(E₁) · (∏_p c_p(E₁)) · φ.kummerRatioProduct = Ω(E₂) · (∏_p c_p(E₂))`. -/
theorem minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct
    (φ : Isogeny E₁.toAffine E₂.toAffine) :
    E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) * φ.kummerRatioProduct =
      E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by
  obtain ⟨c, hc, -⟩ := φ.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_eq_smul φ hc
  obtain ⟨C₁, hC₁⟩ := E₁.exists_isGlobalMinimal_smul ℤ
  obtain ⟨C₂, hC₂⟩ := E₂.exists_isGlobalMinimal_smul ℤ
  set d : ℚ := c * C₂.u / C₁.u
  have hd : d ≠ 0 := div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have hfin_real :
      (((∏ᶠ v : HeightOneSpectrum ℤ,
          (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation ℚ d)) : ℚ) : ℝ) *
        (((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) : ℚ) : ℝ) *
        (E₁.tamagawaProduct (R := ℤ) : ℝ) =
      (E₂.tamagawaProduct (R := ℤ) : ℝ) := by
    exact_mod_cast finprod_zpow_log_valuation_mul_finiteKummerRatio_mul_tamagawaProduct (R := ℤ)
      φ hc (by norm_num) (Nat.cast_ne_zero.2 φ.degree_pos.ne') hC₁ hC₂
  have hreal : |(d : ℝ)| * E₁.minimalRealPeriod * φ.realKummerRatio = E₂.minimalRealPeriod :=
    abs_mul_minimalRealPeriod_mul_realKummerRatio φ hc hC₁ hC₂
  have hpf : |(d : ℝ)| *
      (((∏ᶠ v : HeightOneSpectrum ℤ,
          (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation ℚ d)) : ℚ) : ℝ) = 1 := by
    have h := congrArg (fun q : ℚ ↦ (q : ℝ))
      (Rat.HeightOneSpectrum.abs_mul_finprod_zpow_log_valuation (R := ℤ) hd)
    simpa [Rat.cast_mul, Rat.cast_abs] using h
  rw [kummerRatioProduct_def]
  push_cast
  calc E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) *
        ((φ.realKummerRatio : ℝ) *
          ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ))
      = 1 * (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) *
          ((φ.realKummerRatio : ℝ) *
            ((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v : ℚ) : ℝ))) := by ring
    _ = (|(d : ℝ)| * E₁.minimalRealPeriod * (φ.realKummerRatio : ℝ)) *
          ((((∏ᶠ v : HeightOneSpectrum ℤ,
              (Nat.card (ℤ ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation ℚ d)) : ℚ) : ℝ) *
            (((∏ᶠ v : HeightOneSpectrum ℤ, φ.finiteKummerRatio v) : ℚ) : ℝ) *
            (E₁.tamagawaProduct (R := ℤ) : ℝ)) := by rw [← hpf]; ring
    _ = E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) := by rw [hreal, hfin_real]

/-- The products of local Kummer ratios of an isogeny over `ℚ` and its dual multiply to `1`. -/
theorem kummerRatioProduct_mul_dual (φ : Isogeny E₁.toAffine E₂.toAffine) :
    φ.kummerRatioProduct * φ.dual.kummerRatioProduct = 1 := by
  have h₁ := φ.minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct
  have h₂ := φ.dual.minimalRealPeriod_mul_tamagawaProduct_mul_kummerRatioProduct
  have hpos : (0 : ℝ) < E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) :=
    mul_pos E₁.minimalRealPeriod_pos (Nat.cast_pos.2 (E₁.tamagawaProduct_pos (R := ℤ)))
  apply Rat.cast_injective (α := ℝ)
  push_cast
  apply mul_left_cancel₀ hpos.ne'
  calc E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) *
        ((φ.kummerRatioProduct : ℝ) * (φ.dual.kummerRatioProduct : ℝ))
      = (E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) * φ.kummerRatioProduct) *
          φ.dual.kummerRatioProduct := by ring
    _ = E₂.minimalRealPeriod * E₂.tamagawaProduct (R := ℤ) * φ.dual.kummerRatioProduct := by
          rw [h₁]
    _ = E₁.minimalRealPeriod * E₁.tamagawaProduct (R := ℤ) * 1 := by rw [h₂, mul_one]

/-- The product of local Kummer ratios of the dual isogeny over `ℚ` is the inverse of the product
of local Kummer ratios of `φ`. -/
theorem kummerRatioProduct_dual (φ : Isogeny E₁.toAffine E₂.toAffine) :
    φ.dual.kummerRatioProduct = φ.kummerRatioProduct⁻¹ :=
  eq_inv_of_mul_eq_one_right φ.kummerRatioProduct_mul_dual

end Rational

end TauCeti.Isogeny
