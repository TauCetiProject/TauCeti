/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Ratio
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MinimalRealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product
import Mathlib.RingTheory.FractionalIdeal.Norm
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Index
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AdicCompletion
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GlobalExistence
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny
import TauCeti.RingTheory.DedekindDomain.Factorization

/-!
# Local Kummer ratios, Tamagawa numbers, and the real period under an isogeny

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over the fraction field `K` of a Dedekind
domain `R`, pulling the invariant differential back as `φ^*ω₂ = c ω₁`. At a height-one prime `v` of
`R` with finite residue field `κ(v) = R ⧸ v`, if `2 ≠ 0` in `K_v` and `deg φ ≠ 0` in `R`, comparing
`φ` on deep formal-group subgroups with the filtration index formula on minimal equations expresses
the completed local Kummer ratio `[E₂(K_v) : φ E₁(K_v)] / #E₁(K_v)[φ]` in terms of the differential
scaling factor on `v`-minimal models and the local Tamagawa numbers:

`z_v(φ) = (#κ(v)) ^ ord_v(c · u₂ / u₁) · c_v(E₂) / c_v(E₁)`.

Here `C₁` and `C₂` are changes of variables carrying `E₁` and `E₂` to equations minimal at `v`,
with scaling factors `u₁` and `u₂`, and `ord_v = -WithZero.log (v.valuation K ·)` is the additive
`v`-adic valuation. The common nonsingular reduced point count `#E_ns(κ(v))` cancels between the
two minimal models (`TauCeti.Isogeny.natCard_point_reduction_eq`), including at bad reduction and
at places dividing `deg φ`.

When `E₁` and `E₂` admit globally minimal equations `C₁ • E₁` and `C₂ • E₂` over `R` and `R` is
finite and free over `ℤ` (for instance the ring of integers of a number field of class number one,
or any pair of curves with trivial Weierstrass class), taking the product over all finite places
evaluates the valuation factor via unique factorisation of principal fractional ideals to
`|Norm_{K/ℚ}(c · u₂ / u₁)|`.

Over `ℚ`, every elliptic curve admits a globally minimal equation over `ℤ`, and combining the
finite-place product with the transformation of `minimalRealPeriod` at the real place
(`TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul`) cancels `|c · u₂ / u₁|`
between the archimedean and nonarchimedean places to yield the choice-free identity

`φ.kummerRatioProduct * E₁.minimalRealPeriod * E₁.tamagawaProduct =
  E₂.minimalRealPeriod * E₂.tamagawaProduct`.

## Main results

* `TauCeti.Isogeny.kummerRatio_eq_zpow_mul_tamagawaNumber_div_of_isMinimal` and
  `TauCeti.Isogeny.kummerRatio_eq_zpow_mul_tamagawaNumber_div`: the local Kummer ratio over an adic
  completion `F_u` in terms of `Valued.v` and local Tamagawa numbers.
* `TauCeti.Isogeny.finiteKummerRatio_eq_zpow_mul_tamagawaNumberAt_div`: the finite-place formula at
  `v : HeightOneSpectrum R` in terms of `v`-minimal models and `tamagawaNumberAt`.
* `TauCeti.Isogeny.finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul`: the product over
  all finite places when globally minimal models over `R` exist.
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

/-! ### Conjugating an isogeny by changes of variables -/

section VariableChange

variable {F : Type*} [Field F] {E₁ E₂ : WeierstrassCurve F}

/-- The isogeny `C₁ • E₁ → C₂ • E₂` obtained by conjugating `φ : E₁ → E₂` by `C₁` and `C₂`. -/
private noncomputable def conjByVariableChange (φ : Isogeny E₁.toAffine E₂.toAffine)
    (C₁ C₂ : VariableChange F) : Isogeny (C₁ • E₁).toAffine (C₂ • E₂).toAffine :=
  (variableChangeIsogeny C₂ rfl).comp
    (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ E₁)))

private theorem degree_conjByVariableChange (φ : Isogeny E₁.toAffine E₂.toAffine)
    (C₁ C₂ : VariableChange F) :
    (conjByVariableChange φ C₁ C₂).degree = φ.degree := by
  simp [conjByVariableChange]

private theorem kummerRatio_conjByVariableChange [E₁.IsElliptic] [E₂.IsElliptic]
    (φ : Isogeny E₁.toAffine E₂.toAffine) (C₁ C₂ : VariableChange F) :
    (conjByVariableChange φ C₁ C₂).kummerRatio = φ.kummerRatio := by
  simp only [conjByVariableChange, kummerRatio_comp]
  rw [kummerRatio_eq_one_of_degree_eq_one _ (degree_variableChangeIsogeny _ _),
    kummerRatio_eq_one_of_degree_eq_one _ (degree_variableChangeIsogeny _ _), one_mul, mul_one]

private theorem pullbackDifferential_conjByVariableChange (φ : Isogeny E₁.toAffine E₂.toAffine)
    {c : F} (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    (C₁ C₂ : VariableChange F) :
    (conjByVariableChange φ C₁ C₂).pullbackDifferential
        (invariantDifferential (C₂ • E₂).toAffine) =
      (c * C₂.u / C₁.u) • invariantDifferential (C₁ • E₁).toAffine := by
  simp only [conjByVariableChange, pullbackDifferential_comp, LinearMap.comp_apply,
    pullbackDifferential_variableChangeIsogeny_invariantDifferential, map_smul, hc, smul_smul]
  congr 1
  simp [VariableChange.inv_def, div_eq_mul_inv]
  ring

end VariableChange

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

private local instance : IsDiscreteValuationRing R_u :=
  inferInstanceAs (IsDiscreteValuationRing O_u)

private local instance : HenselianLocalRing R_u :=
  inferInstanceAs (HenselianLocalRing O_u)

private local instance : Finite (IsLocalRing.ResidueField R_u) :=
  Finite.of_equiv _ (u.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv

/-- For an equation over `O_u` whose generic fibre is minimal, the nonsingular point count of its
reduction at `𝒪[F_u]` agrees with the count at `Valued.v.valuationSubring` appearing in the formal
filtration index formula. -/
private theorem natCard_point_reduction_baseChange_adicCompletion_of_isMinimal
    (C : WeierstrassCurve O_u) [IsMinimal O_u (C.baseChange F_u)] :
    haveI : IsMinimal 𝒪[F_u] (C.baseChange F_u) :=
      (isMinimal_integer_adicCompletion_iff u (C.baseChange F_u)).mpr inferInstance
    Nat.card ((C.baseChange F_u).reduction 𝒪[F_u]).toAffine.Point =
      Nat.card ((integralModel R_u (C.baseChange F_u)).map
        (IsLocalRing.residue R_u)).toAffine.Point := by
  have : IsMinimal 𝒪[F_u] (C.baseChange F_u) :=
    (isMinimal_integer_adicCompletion_iff u (C.baseChange F_u)).mpr inferInstance
  suffices ∀ (T : ValuationSubring F_u) [IsDiscreteValuationRing T]
      [(C.baseChange F_u).IsMinimal T], O_u = T →
      Nat.card ((C.baseChange F_u).reduction T).toAffine.Point =
        Nat.card ((integralModel R_u (C.baseChange F_u)).map
          (IsLocalRing.residue R_u)).toAffine.Point by
    have hR : IsDiscreteValuationRing (ValuativeRel.valuation F_u).valuationSubring :=
      inferInstanceAs (IsDiscreteValuationRing 𝒪[F_u])
    have hmin : (C.baseChange F_u).IsMinimal (ValuativeRel.valuation F_u).valuationSubring :=
      inferInstanceAs ((C.baseChange F_u).IsMinimal 𝒪[F_u])
    exact this (ValuativeRel.valuation F_u).valuationSubring
      (ValuationSubring.toSubring_injective (u.integer_eq_adicCompletionIntegers (K := F)).symm)
  rintro T _ _ rfl
  rw [reduction]
  rfl

/-- Equivalent valuations on `F_u` give the same local Tamagawa number. -/
private theorem tamagawaNumber_valued_eq_tamagawaNumber_valuation
    (E : WeierstrassCurve F_u) [E.IsElliptic] :
    haveI : IsDiscreteValuationRing (ValuativeRel.valuation F_u).valuationSubring :=
      inferInstanceAs (IsDiscreteValuationRing 𝒪[F_u])
    E.tamagawaNumber (Valued.v : Valuation F_u ℤᵐ⁰) =
      E.tamagawaNumber (ValuativeRel.valuation F_u) := by
  classical
  have : IsDiscreteValuationRing (ValuativeRel.valuation F_u).valuationSubring :=
    inferInstanceAs (IsDiscreteValuationRing 𝒪[F_u])
  obtain ⟨D, hD⟩ := exists_isMinimal O_u E
  let _ : IsMinimal R_u (D • E) := hD
  have hmin_int : IsMinimal 𝒪[F_u] (D • E) :=
    (isMinimal_integer_adicCompletion_iff u (D • E)).mpr hD
  let _ : IsMinimal (ValuativeRel.valuation F_u).valuationSubring (D • E) :=
    inferInstanceAs (IsMinimal 𝒪[F_u] (D • E))
  have hequiv : (Valued.v : Valuation F_u ℤᵐ⁰).IsEquiv (ValuativeRel.valuation F_u) :=
    (ValuativeRel.isEquiv (ValuativeRel.valuation F_u) (Valued.v : Valuation F_u ℤᵐ⁰)).symm
  rw [← tamagawaNumber_smul E (Valued.v : Valuation F_u ℤᵐ⁰) D,
    ← tamagawaNumber_smul E (ValuativeRel.valuation F_u) D,
    tamagawaNumber_eq_index (D • E) (Valued.v : Valuation F_u ℤᵐ⁰),
    tamagawaNumber_eq_index (D • E) (ValuativeRel.valuation F_u),
    Affine.nonsingularReduction_congr _ hequiv]

/-- **The local Kummer ratio on minimal equations over an adic completion.** Let `W₁` and `W₂` be
elliptic equations over `F_u` minimal over `O_u`, and let `φ : W₁ → W₂` pull back the invariant
differential as `φ^*ω₂ = c ω₁`, with `2 ≠ 0` in `F_u` and `deg φ ≠ 0` in `A`. Then
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
  -- `c` is nonzero since `c * c' = deg φ` and `deg φ` is nonzero in `A` (hence in `F_u`).
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hdeg_ne : (φ.degree : F_u) ≠ 0 := by
    intro h0
    rw [← map_natCast (algebraMap A F_u), IsScalarTower.algebraMap_apply A F F_u,
      map_eq_zero_iff _ (RingHom.injective _), map_eq_zero_iff _ (IsFractionRing.injective A F)]
      at h0
    exact hn h0
  have hc0 : c ≠ 0 := left_ne_zero_of_mul <| by
    rw [φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc']
    exact hdeg_ne
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
    (natCard_point_reduction_baseChange_adicCompletion_of_isMinimal u C₁).symm.trans
      (φ.natCard_point_reduction_eq.trans
        (natCard_point_reduction_baseChange_adicCompletion_of_isMinimal u C₂))
  rw [hq, hred_eq] at hdeep
  -- Cast the cross-multiplied natural-number identity to `ℚ` and cancel the positive factors.
  have hdeep_rat : ((Hom.ofIsogeny φ).pointMapHom.range.index : ℚ) *
      ((Nat.card (A ⧸ u.asIdeal) : ℚ) ^ k₀ *
        Nat.card ((integralModel R_u (C₂.baseChange F_u)).map
          (IsLocalRing.residue R_u)).toAffine.Point *
        (C₁.baseChange F_u).tamagawaNumber (Valued.v : Valuation F_u ℤᵐ⁰)) =
      ((Nat.card (A ⧸ u.asIdeal) : ℚ) ^ j₀ *
        Nat.card ((integralModel R_u (C₂.baseChange F_u)).map
          (IsLocalRing.residue R_u)).toAffine.Point *
        (C₂.baseChange F_u).tamagawaNumber (Valued.v : Valuation F_u ℤᵐ⁰)) *
        Nat.card (Hom.ofIsogeny φ).pointMapHom.ker := by
    exact_mod_cast hdeep
  have hq0 : (Nat.card (A ⧸ u.asIdeal) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hN0 : (Nat.card ((integralModel R_u (C₂.baseChange F_u)).map
      (IsLocalRing.residue R_u)).toAffine.Point : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hc₁0 : ((C₁.baseChange F_u).tamagawaNumber (Valued.v : Valuation F_u ℤᵐ⁰) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (tamagawaNumber_pos (C₁.baseChange F_u) _).ne'
  have _ := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
  have hker0 : (Nat.card (Hom.ofIsogeny φ).pointMapHom.ker : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hzpow : (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ j₀ / (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ k₀ =
      (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ (-WithZero.log (Valued.v c)) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hq0]
    congr 1
    omega
  rw [kummerRatio_def, div_eq_iff hker0]
  have hsolve : ((Hom.ofIsogeny φ).pointMapHom.range.index : ℚ) =
      ((Nat.card (A ⧸ u.asIdeal) : ℚ) ^ j₀ / (Nat.card (A ⧸ u.asIdeal) : ℚ) ^ k₀) *
        (C₂.baseChange F_u).tamagawaNumber (Valued.v : Valuation F_u ℤᵐ⁰) /
        (C₁.baseChange F_u).tamagawaNumber (Valued.v : Valuation F_u ℤᵐ⁰) *
        Nat.card (Hom.ofIsogeny φ).pointMapHom.ker := by
    rw [eq_div_iff_mul_eq (mul_ne_zero (mul_ne_zero (pow_ne_zero k₀ hq0) hN0) hc₁0) |>.mpr
      hdeep_rat]
    field_simp [pow_ne_zero k₀ hq0, hN0, hc₁0]
  rw [hsolve, hzpow]

/-- **The local Kummer ratio on arbitrary equations over an adic completion.** If `C₁` and `C₂`
carry `E₁` and `E₂` to equations minimal over `O_u`, and `φ^*ω₂ = c ω₁`, then
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
  rw [← kummerRatio_conjByVariableChange φ C₁ C₂,
    kummerRatio_eq_zpow_mul_tamagawaNumber_div_of_isMinimal u (conjByVariableChange φ C₁ C₂)
      (pullbackDifferential_conjByVariableChange φ hc C₁ C₂) h2
      (by rwa [degree_conjByVariableChange]),
    tamagawaNumber_smul, tamagawaNumber_smul]

end Local

/-! ### Finite places of a global Dedekind domain -/

section FinitePlaces

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero field element has finite multiplicative support for its prime-norm valuation
powers. -/
private theorem hasFiniteMulSupport_zpow_neg_log_valuation {a : K} (ha : a ≠ 0) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
      (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation K a)) := by
  have hcount (v : HeightOneSpectrum R) :
      -WithZero.log (v.valuation K a) =
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a) := by
    have h := (FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation K v
      (Units.mk0 a ha)).symm
    rwa [coe_toPrincipalIdeal, Units.val_mk0] at h
  simp_rw [hcount]
  exact FractionalIdeal.hasFiniteMulSupport_zpow_count (FractionalIdeal.spanSingleton R⁰ a) _

section HasFiniteQuotients

variable [Ring.HasFiniteQuotients R]
  {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **The finite local Kummer ratio in terms of local Tamagawa numbers.** Let `φ : E₁ → E₂` pull
back the invariant differential as `φ^*ω₂ = c ω₁`, with `2 ≠ 0` in `K` and `deg φ ≠ 0` in `R`.
If `C₁` and `C₂` carry `E₁` and `E₂` to equations minimal at `v`, then
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
  let ψ := conjByVariableChange φ C₁ C₂
  have hψ_ratio : ψ.finiteKummerRatio v = φ.finiteKummerRatio v := by
    dsimp only [ψ, conjByVariableChange]
    rw [finiteKummerRatio_comp, finiteKummerRatio_comp, finiteKummerRatio_def,
      finiteKummerRatio_def (variableChangeIsogeny C₁⁻¹ _),
      kummerRatio_eq_one_of_degree_eq_one _ (by rw [degree_map, degree_variableChangeIsogeny]),
      kummerRatio_eq_one_of_degree_eq_one _ (by rw [degree_map, degree_variableChangeIsogeny]),
      one_mul, mul_one]
  have _ : IsMinimal (v.adicCompletionIntegers K) ((C₁ • E₁).baseChange (v.adicCompletion K)) :=
    (isMinimal_baseChange_adicCompletionIntegers_iff v (C₁ • E₁)).mpr inferInstance
  have _ : IsMinimal (v.adicCompletionIntegers K) ((C₂ • E₂).baseChange (v.adicCompletion K)) :=
    (isMinimal_baseChange_adicCompletionIntegers_iff v (C₂ • E₂)).mpr inferInstance
  have h2_comp : (2 : v.adicCompletion K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]
    exact (RingHom.injective _).ne h2
  have hψ_deg : ((ψ.baseChange (v.adicCompletion K)).degree : R) ≠ 0 := by
    have hdeg_eq : (ψ.baseChange (v.adicCompletion K)).degree = ψ.degree :=
      degree_map ψ (algebraMap K (v.adicCompletion K))
    rwa [hdeg_eq, degree_conjByVariableChange]
  have hψ_diff : (ψ.baseChange (v.adicCompletion K)).pullbackDifferential
      (invariantDifferential ((C₂ • E₂).baseChange (v.adicCompletion K)).toAffine) =
      algebraMap K (v.adicCompletion K) (c * C₂.u / C₁.u) •
        invariantDifferential ((C₁ • E₁).baseChange (v.adicCompletion K)).toAffine :=
    map_pullbackDifferential_invariantDifferential_eq_smul ψ (algebraMap K (v.adicCompletion K))
      (pullbackDifferential_conjByVariableChange φ hc C₁ C₂)
  have hval : Valued.v (algebraMap K (v.adicCompletion K) (c * C₂.u / C₁.u)) =
      v.valuation K (c * C₂.u / C₁.u) := by
    rw [algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self_apply]
  have hdef : ψ.finiteKummerRatio v = (ψ.baseChange (v.adicCompletion K)).kummerRatio :=
    finiteKummerRatio_def ψ v
  rw [← hψ_ratio, hdef,
    kummerRatio_eq_zpow_mul_tamagawaNumber_div_of_isMinimal v
      (ψ.baseChange (v.adicCompletion K)) hψ_diff h2_comp hψ_deg,
    hval, tamagawaNumber_valued_eq_tamagawaNumber_valuation v,
    tamagawaNumber_valued_eq_tamagawaNumber_valuation v,
    ← tamagawaNumberAt_def, ← tamagawaNumberAt_def, tamagawaNumberAt_smul, tamagawaNumberAt_smul]

/-- **The finite local Kummer ratio on `v`-minimal equations.** -/
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

/-- **Global finite-place product of Kummer ratios and Tamagawa numbers.** When `C₁ • E₁` and
`C₂ • E₂` are globally minimal over `R`, multiplying all finite local Kummer ratios by the Tamagawa
product of `E₁` yields the Tamagawa product of `E₂` times the product of the prime-norm powers of
`c · C₂.u / C₁.u`. -/
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
  have hφK : (φ.degree : K) ≠ 0 := by
    intro h0
    rw [← map_natCast (algebraMap R K), map_eq_zero_iff _ (IsFractionRing.injective R K)] at h0
    exact hφ h0
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hc0 : c ≠ 0 := left_ne_zero_of_mul <| by
    rw [φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc']
    exact hφK
  have ha0 : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  have hsupp_tam₁ : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum R ↦ (E₁.tamagawaNumberAt v : ℚ)) :=
    E₁.hasFiniteMulSupport_tamagawaNumberAt.subset fun v hv ↦
      Function.mem_mulSupport.mpr fun h ↦
        Function.mem_mulSupport.mp hv (by rw [h, Nat.cast_one])
  have hsupp_tam₂ : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum R ↦ (E₂.tamagawaNumberAt v : ℚ)) :=
    E₂.hasFiniteMulSupport_tamagawaNumberAt.subset fun v hv ↦
      Function.mem_mulSupport.mpr fun h ↦
        Function.mem_mulSupport.mp hv (by rw [h, Nat.cast_one])
  have hcast_tam (E : WeierstrassCurve K) [E.IsElliptic] :
      (E.tamagawaProduct (R := R) : ℚ) =
        ∏ᶠ v : HeightOneSpectrum R, (E.tamagawaNumberAt v : ℚ) := by
    rw [E.tamagawaProduct_def]
    exact MonoidHom.map_finprod (Nat.castRingHom ℚ).toMonoidHom
      E.hasFiniteMulSupport_tamagawaNumberAt
  rw [hcast_tam E₁, hcast_tam E₂,
    ← finprod_mul_distrib (φ.hasFiniteMulSupport_finiteKummerRatio hφK) hsupp_tam₁,
    ← finprod_mul_distrib (hasFiniteMulSupport_zpow_neg_log_valuation ha0) hsupp_tam₂]
  refine finprod_congr fun v ↦ ?_
  have _ := hC₁.isMinimal v
  have _ := hC₂.isMinimal v
  have hc₁0 : (E₁.tamagawaNumberAt v : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (E₁.tamagawaNumberAt_pos v).ne'
  rw [finiteKummerRatio_eq_zpow_mul_tamagawaNumberAt_div φ v hc C₁ C₂ h2 hφ, div_mul_cancel₀ _ hc₁0]

/-- **Global finite-place product of Kummer ratios and Tamagawa numbers between global minimal
equations.** -/
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

/-- For a nonzero element `a ∈ K`, the product over all height-one primes of `(#(R ⧸ v)) ^ ord_v(a)`
equals `|Norm_{K/ℚ}(a)|`. -/
private theorem finprod_zpow_neg_log_valuation_eq_abs_norm {a : K} (ha : a ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R,
        (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation K a))) =
      |Algebra.norm ℚ a| := by
  let f : (FractionalIdeal R⁰ K)ˣ →* ℚ :=
    (FractionalIdeal.absNorm (R := R) (K := K)).toMonoidHom.comp (Units.coeHom _)
  have hfact := congrArg f
    (FractionalIdeal.finprod_unitOfPrime_zpow_count (toPrincipalIdeal R K (Units.mk0 a ha)))
  rw [MonoidHom.map_finprod f
    (FractionalIdeal.hasFiniteMulSupport_zpow_count _ _)] at hfact
  have hLHS : f (toPrincipalIdeal R K (Units.mk0 a ha)) = |Algebra.norm ℚ a| := by
    simp [f, coe_toPrincipalIdeal]
  rw [hLHS] at hfact
  rw [hfact]
  refine (finprod_congr fun v ↦ ?_).symm
  have hcount : FractionalIdeal.count K v
      (toPrincipalIdeal R K (Units.mk0 a ha) : FractionalIdeal R⁰ K) =
      -WithZero.log (v.valuation K a) := by
    simpa using FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation K v (Units.mk0 a ha)
  have hf_unit : f (v.unitOfPrime K) = (Nat.card (R ⧸ v.asIdeal) : ℚ) := by
    simp [f, HeightOneSpectrum.coe_unitOfPrime, FractionalIdeal.coeIdeal_absNorm,
      Ideal.absNorm_of_ne_bot v.ne_bot, Submodule.cardQuot_apply]
  rw [map_zpow, hf_unit, hcount]

/-- **The finite-place Kummer/Tamagawa identity evaluated via the norm to `ℚ`.** Let `R` be a
Dedekind domain finite and free over `ℤ` with fraction field `K` finite over `ℚ`. If `C₁ • E₁` and
`C₂ • E₂` are globally minimal over `R` and `φ^*ω₂ = c ω₁`, then
`(∏_v φ.finiteKummerRatio v) · E₁.tamagawaProduct = |Norm_{K/ℚ}(c · C₂.u / C₁.u)| ·
  E₂.tamagawaProduct`. -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul [Ring.HasFiniteQuotients R]
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange K} (hC₁ : IsGlobalMinimal R (C₁ • E₁))
    (hC₂ : IsGlobalMinimal R (C₂ • E₂)) :
    (∏ᶠ v : HeightOneSpectrum R, φ.finiteKummerRatio v) * E₁.tamagawaProduct (R := R) =
      |Algebra.norm ℚ (c * C₂.u / C₁.u)| * E₂.tamagawaProduct (R := R) := by
  have _ : CharZero K :=
    ⟨fun a b h ↦ Nat.cast_injective <| (algebraMap ℚ K).injective <| by simpa using h⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hφK : (φ.degree : K) ≠ 0 := Nat.cast_ne_zero.mpr φ.degree_pos.ne'
  have hφ : (φ.degree : R) ≠ 0 := by
    intro h0
    exact hφK (by rw [← map_natCast (algebraMap R K), h0, map_zero])
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hc0 : c ≠ 0 := left_ne_zero_of_mul <| by
    rw [φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc']
    exact hφK
  have ha0 : c * C₂.u / C₁.u ≠ 0 :=
    div_ne_zero (mul_ne_zero hc0 C₂.u.ne_zero) C₁.u.ne_zero
  rw [finprod_finiteKummerRatio_mul_tamagawaProduct_eq_finprod_zpow_mul φ hc hC₁ hC₂ h2 hφ,
    finprod_zpow_neg_log_valuation_eq_abs_norm ha0]

/-- **The finite-place Kummer/Tamagawa identity between global minimal equations.** -/
theorem finprod_finiteKummerRatio_mul_tamagawaProduct_eq_abs_norm_mul_of_isGlobalMinimal
    [Ring.HasFiniteQuotients R]
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

/-! ### Global period–Tamagawa transformation over `ℚ` -/

section Rational

variable {E₁ E₂ : WeierstrassCurve ℚ} [E₁.IsElliptic] [E₂.IsElliptic]

/-- Over `ℚ`, the product of all finite local Kummer ratios times `E₁.tamagawaProduct` equals
`|c · C₂.u / C₁.u| · E₂.tamagawaProduct` for any changes of variables `C₁`, `C₂` to globally
minimal equations over `ℤ`. -/
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

/-- At the real place, `φ.realKummerRatio * |c · C₂.u / C₁.u| * Ω(E₁) = Ω(E₂)`. -/
theorem realKummerRatio_mul_abs_mul_minimalRealPeriod_eq
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : ℚ}
    (hc : φ.pullbackDifferential (invariantDifferential E₂.toAffine) =
      c • invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange ℚ} (hC₁ : IsGlobalMinimal ℤ (C₁ • E₁))
    (hC₂ : IsGlobalMinimal ℤ (C₂ • E₂)) :
    (φ.realKummerRatio : ℝ) * |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod =
      E₂.minimalRealPeriod := by
  classical
  have hreal := abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul φ hc hC₁ hC₂
  have _ := (Hom.ofIsogeny (φ.baseChange ℝ)).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero _)
  have hker0 : (Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hreal_def : φ.realKummerRatio = (φ.baseChange ℝ).kummerRatio := realKummerRatio_def φ
  rw [hreal_def, kummerRatio_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
  apply mul_right_cancel₀ hker0
  calc
    (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index /
        Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker *
        |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod *
        Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker
      = |((c * C₂.u / C₁.u : ℚ) : ℝ)| * E₁.minimalRealPeriod *
          (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.range.index := by
        field_simp [hker0]
    _ = E₂.minimalRealPeriod * Nat.card (Hom.ofIsogeny (φ.baseChange ℝ)).pointMapHom.ker := by
        rw [hreal, mul_comm]

/-- Between globally minimal equations over `ℤ`, `φ.realKummerRatio * |c| * Ω(E₁) = Ω(E₂)`. -/
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
