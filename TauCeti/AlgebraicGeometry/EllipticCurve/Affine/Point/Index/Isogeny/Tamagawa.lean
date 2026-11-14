/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Isogeny.Ratio
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Index
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AdicCompletion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ProductFormula

import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny

/-!
# The local Kummer ratio at a finite place, through Tamagawa numbers

Let `A` be a Dedekind domain with fraction field `F`, let `u` be a height-one prime of `A` with
finite residue field, and let `φ : W₁ → W₂` be an isogeny of elliptic curves over the completion
`F_u` with `2 ≠ 0` in `F_u` and `deg φ ≠ 0` in `A`, pulling the invariant differential back as
`φ^*ω₂ = c ω₁`.

On minimal equations over `𝒪[F_u]`, the deep formal-group identity
`TauCeti.Isogeny.eventually_index_range_pointMapHom_mul_index_formalPointFiltration` equates the
local Kummer ratio `z(φ) = [W₂(F_u) : φ W₁(F_u)] / #W₁(F_u)[φ]` with the ratio
`[W₂(F_u) : W₂,(j+1)(F_u)] / [W₁(F_u) : W₁,(k+1)(F_u)]` for `j - k = -log(v c) = ord_u(c)`. By
`WeierstrassCurve.index_formalPointFiltration_eq_mul_tamagawaNumber`, each formal-filtration index
splits into a power of `#𝓀[F_u]`, the count of nonsingular points on the reduction, and the local
Tamagawa number. By `TauCeti.Isogeny.natCard_point_reduction_eq`, isogenous minimal equations have
equally many nonsingular reduced points at every reduction type (good, split or nonsplit
multiplicative, and additive). Cancelling that common factor yields

`|c|_u · c_u(W₁) · z(φ) = c_u(W₂)`,

including at primes dividing `deg φ`.

For arbitrary equations `W₁`, `W₂` carried to minimal equations by changes of variables `C₁`, `C₂`
with scaling factors `u₁`, `u₂`, conjugating `φ` replaces `c` by `c u₂ / u₁` while leaving both
`z(φ)` and the Tamagawa numbers unchanged. Over a global fraction field `K` of a Dedekind domain
`R` with finite quotients, minimal equations over `Localization.AtPrime v.asIdeal` remain minimal
over `𝒪[K_v]` (`WeierstrassCurve.isMinimal_adicCompletion_baseChange`), giving the corresponding
formulas for `TauCeti.Isogeny.finiteKummerRatio` in terms of `WeierstrassCurve.tamagawaNumberAt`.

## Main results

* `TauCeti.Isogeny.normalizedAbsoluteValue_mul_tamagawaNumber_mul_kummerRatio_of_isMinimal` and
  `TauCeti.Isogeny.kummerRatio_eq_of_isMinimal`: on minimal equations over `𝒪[F_u]`,
  `|c|_u · c_u(W₁) · φ.kummerRatio = c_u(W₂)`.
* `TauCeti.Isogeny.normalizedAbsoluteValue_mul_tamagawaNumber_mul_kummerRatio` and
  `TauCeti.Isogeny.kummerRatio_eq_of_isMinimal_smul`: for arbitrary equations with `C₁ • W₁` and
  `C₂ • W₂` minimal over `𝒪[F_u]`, `|c u₂ / u₁|_u · c_u(W₁) · φ.kummerRatio = c_u(W₂)`.
* `TauCeti.Isogeny.finiteKummerRatio_eq_of_isMinimal` and
  `TauCeti.Isogeny.finiteKummerRatio_eq_of_isMinimal_smul`: the global counterparts for
  `φ.finiteKummerRatio v` and `E.tamagawaNumberAt v`.
* `TauCeti.Isogeny.finiteKummerRatio_eq_of_isGlobalMinimal` and
  `TauCeti.Isogeny.finiteKummerRatio_eq_of_isGlobalMinimal_smul`: in characteristic zero, the
  characteristic and degree hypotheses hold automatically at every finite place, including at `2`
  and at primes dividing `deg φ`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199, Lemma 3.3 and §4.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), 79–114,
  Lemma 3.8.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6 and X.4.
-/

public section

open scoped NNRat WithZero

open IsDedekindDomain IsLocalRing ValuativeRel WeierstrassCurve

namespace TauCeti.Isogeny

section Conjugate

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F}

/-- Conjugating an isogeny `φ : W₁ → W₂` with `φ^*ω₂ = c ω₁` by changes of variables `C₁`, `C₂`
scales the pullback constant of the invariant differential to `c * C₂.u / C₁.u`. -/
theorem pullbackDifferential_variableChangeIsogeny_comp_eq_smul
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (C₁ C₂ : VariableChange F) :
    ((variableChangeIsogeny C₂ (rfl : C₂ • W₂.toAffine = (C₂ • W₂).toAffine)).comp
        (φ.comp (variableChangeIsogeny C₁⁻¹
          (inv_smul_smul C₁ W₁.toAffine)))).pullbackDifferential
        (Affine.invariantDifferential (C₂ • W₂).toAffine) =
      (c * C₂.u / C₁.u) • Affine.invariantDifferential (C₁ • W₁).toAffine := by
  rw [pullbackDifferential_comp, pullbackDifferential_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, pullbackDifferential_variableChangeIsogeny_invariantDifferential,
    map_smul, hc, map_smul, map_smul,
    pullbackDifferential_variableChangeIsogeny_invariantDifferential, smul_smul, smul_smul]
  simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]
  congr 1
  ring

end Conjugate

section AdicCompletion

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)]

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F

/-- The normalized absolute value on `F_u` expressed via `Valued.v` and `#ResidueField O_u`. -/
private theorem normalizedAbsoluteValue_adicCompletion_eq_zpow_log {c : F_u} (hc0 : c ≠ 0) :
    TauCeti.normalizedAbsoluteValue F_u c =
      (Nat.card (ResidueField O_u) : ℚ≥0) ^ WithZero.log (Valued.v c) := by
  have hv : (TauCeti.normalizedValuation F_u (Units.mk0 c hc0) : ℤᵐ⁰) =
      WithZero.exp (-WithZero.log (Valued.v c)) := by
    have h := u.normalizedValuationWithZero_adicCompletion (K := F) (Units.mk0 c hc0)
    rw [TauCeti.normalizedValuationWithZero_coe, Units.val_mk0,
      ← WithZero.exp_log ((Valued.v : Valuation F_u ℤᵐ⁰).ne_zero_iff.mpr hc0),
      ← WithZero.exp_neg] at h
    exact h
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.coe_inj] at hv
  have hcard : Nat.card 𝓀[F_u] = Nat.card (ResidueField O_u) :=
    (Nat.card_congr (u.residueFieldEquivAdicCompletion (K := F)).symm.toEquiv).trans
      (Nat.card_congr (u.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv)
  rw [TauCeti.normalizedAbsoluteValue_apply_ne_zero c hc0, congrArg Multiplicative.toAdd hv,
    toAdd_ofAdd, neg_neg, hcard]

omit [Finite (A ⧸ u.asIdeal)] in
/-- The pullback constant `c` of `φ^*ω₂ = c ω₁` is nonzero whenever `deg φ ≠ 0` in `A`. -/
private theorem ne_zero_of_pullbackDifferential_of_degree_ne_zero
    {W₁ W₂ : WeierstrassCurve F_u} [W₁.IsElliptic] [W₂.IsElliptic]
    {φ : Isogeny W₁.toAffine W₂.toAffine} {c : F_u}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (hn : (φ.degree : A) ≠ 0) : c ≠ 0 := by
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hdeg : (φ.degree : F_u) ≠ 0 := by
    rw [← map_natCast (algebraMap A F_u), IsScalarTower.algebraMap_apply A F F_u]
    exact (map_ne_zero_iff _ (algebraMap F F_u).injective).mpr
      ((FaithfulSMul.algebraMap_eq_zero_iff A F).not.mpr hn)
  exact left_ne_zero_of_mul ((φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc').trans_ne hdeg)

/-- Core formal-filtration calculation on minimal models over `O_u`. -/
private theorem normalizedAbsoluteValue_mul_tamagawaNumber_mul_kummerRatio_baseChange
    {C₁ C₂ : WeierstrassCurve O_u}
    [(C₁.baseChange F_u).IsElliptic] [(C₂.baseChange F_u).IsElliptic]
    [IsMinimal O_u (C₁.baseChange F_u)] [IsMinimal O_u (C₂.baseChange F_u)]
    (φ : Isogeny (C₁.baseChange F_u).toAffine (C₂.baseChange F_u).toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential _) =
      c • Affine.invariantDifferential _)
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    (TauCeti.normalizedAbsoluteValue F_u c : ℚ) *
        (C₁.baseChange F_u).tamagawaNumber Valued.v * φ.kummerRatio =
      (C₂.baseChange F_u).tamagawaNumber Valued.v := by
  classical
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_of_degree_ne_zero u hc hn
  have hvc : Valued.v c ≠ 0 := (Valued.v : Valuation F_u ℤᵐ⁰).ne_zero_iff.mpr hc0
  set m : ℤ := WithZero.log (Valued.v c)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_index_range_pointMapHom_mul_index_formalPointFiltration u hc h2 hn)
  set k₀ : ℕ := N + m.natAbs
  set j₀ : ℕ := ((k₀ : ℤ) - m).toNat
  have hj₀ : (j₀ : ℤ) = k₀ - m := Int.toNat_of_nonneg (by omega)
  have hjk : Valued.v c * WithZero.exp ((j₀ + 1 : ℕ) : ℤ) =
      WithZero.exp ((k₀ + 1 : ℕ) : ℤ) := by
    rw [← WithZero.exp_log hvc, ← WithZero.exp_add, WithZero.exp_inj]
    push_cast
    omega
  have hidx := congrArg (Nat.cast (R := ℚ)) (hN (k₀ + 1) (by omega) (j₀ + 1) hjk)
  rw [C₁.index_formalPointFiltration_eq_mul_tamagawaNumber u k₀,
    C₂.index_formalPointFiltration_eq_mul_tamagawaNumber u j₀,
    ← C₁.natCard_point_reduction_baseChange_adicCompletion,
    ← C₂.natCard_point_reduction_baseChange_adicCompletion, φ.natCard_point_reduction_eq] at hidx
  push_cast at hidx
  have hker : (Nat.card (Hom.ofIsogeny φ).pointMapHom.ker : ℚ) ≠ 0 := by
    have := (Hom.ofIsogeny φ).finite_ker_pointMapHom (Hom.ofIsogeny_ne_zero φ)
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hred : (Nat.card ((C₂.baseChange F_u).reduction 𝒪[F_u]).toAffine.Point : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hq : (Nat.card (ResidueField O_u) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [normalizedAbsoluteValue_adicCompletion_eq_zpow_log u hc0, NNRat.cast_zpow,
    NNRat.cast_natCast, kummerRatio_def]
  have hpow : (Nat.card (ResidueField O_u) : ℚ) ^ m * (Nat.card (ResidueField O_u) : ℚ) ^ j₀ =
      (Nat.card (ResidueField O_u) : ℚ) ^ k₀ := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq, hj₀]
    congr 1
    omega
  apply mul_right_cancel₀ hker
  rw [mul_assoc, div_mul_cancel₀ _ hker]
  apply mul_right_cancel₀ hred
  apply mul_right_cancel₀ (pow_ne_zero k₀ hq)
  linear_combination (Nat.card (ResidueField O_u) : ℚ) ^ m * hidx +
    (C₂.baseChange F_u).tamagawaNumber Valued.v *
      Nat.card (Hom.ofIsogeny φ).pointMapHom.ker *
      Nat.card ((C₂.baseChange F_u).reduction 𝒪[F_u]).toAffine.Point * hpow

/-- **The local Kummer ratio on minimal equations over `𝒪[F_u]`, multiplicative form**: if
`W₁` and `W₂` are minimal over `𝒪[F_u]` and `φ^*ω₂ = c ω₁`, with `2 ≠ 0` in `F_u` and `deg φ ≠ 0`
in `A`, then `|c|_u · c_u(W₁) · φ.kummerRatio = c_u(W₂)`, including at places dividing `deg φ`. -/
theorem normalizedAbsoluteValue_mul_tamagawaNumber_mul_kummerRatio_of_isMinimal
    {W₁ W₂ : WeierstrassCurve F_u} [W₁.IsElliptic] [W₂.IsElliptic]
    [W₁.IsMinimal 𝒪[F_u]] [W₂.IsMinimal 𝒪[F_u]]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    (TauCeti.normalizedAbsoluteValue F_u c : ℚ) *
        W₁.tamagawaNumber (valuation F_u) * φ.kummerRatio =
      W₂.tamagawaNumber (valuation F_u) := by
  have model (V : WeierstrassCurve F_u) [V.IsMinimal 𝒪[F_u]] :
      ∃ C : WeierstrassCurve O_u,
        IsMinimal O_u (C.baseChange F_u) ∧ C.baseChange F_u = V := by
    have hmin : IsMinimal O_u V := (isMinimal_adicCompletion_iff V).mp inferInstance
    exact ⟨integralModel O_u V, by rwa [baseChange_integralModel_eq],
      baseChange_integralModel_eq O_u V⟩
  obtain ⟨C₁, _, rfl⟩ := model W₁
  obtain ⟨C₂, _, rfl⟩ := model W₂
  have hequiv := ValuativeRel.isEquiv (valuation F_u) (Valued.v : Valuation F_u ℤᵐ⁰)
  rw [(C₁.baseChange F_u).tamagawaNumber_congr _ hequiv,
    (C₂.baseChange F_u).tamagawaNumber_congr _ hequiv]
  exact normalizedAbsoluteValue_mul_tamagawaNumber_mul_kummerRatio_baseChange u φ hc h2 hn

/-- **The local Kummer ratio on minimal equations over `𝒪[F_u]`, solved for `φ.kummerRatio`**:
`φ.kummerRatio = |c|_u⁻¹ · c_u(W₂) / c_u(W₁)`. -/
theorem kummerRatio_eq_of_isMinimal
    {W₁ W₂ : WeierstrassCurve F_u} [W₁.IsElliptic] [W₂.IsElliptic]
    [W₁.IsMinimal 𝒪[F_u]] [W₂.IsMinimal 𝒪[F_u]]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    φ.kummerRatio =
      (TauCeti.normalizedAbsoluteValue F_u c : ℚ)⁻¹ *
        W₂.tamagawaNumber (valuation F_u) / W₁.tamagawaNumber (valuation F_u) := by
  have hc0 : c ≠ 0 := ne_zero_of_pullbackDifferential_of_degree_ne_zero u hc hn
  have habs : (TauCeti.normalizedAbsoluteValue F_u c : ℚ) ≠ 0 :=
    NNRat.cast_ne_zero.mpr ((TauCeti.normalizedAbsoluteValue F_u).ne_zero_iff.mpr hc0)
  have htam : (W₁.tamagawaNumber (valuation F_u) : ℚ) ≠ 0 := by
    let : HenselianLocalRing (valuation F_u).valuationSubring :=
      inferInstanceAs (HenselianLocalRing 𝒪[F_u])
    let : Finite (ResidueField (valuation F_u).valuationSubring) :=
      inferInstanceAs (Finite 𝓀[F_u])
    exact Nat.cast_ne_zero.mpr (W₁.tamagawaNumber_pos (valuation F_u)).ne'
  have h := normalizedAbsoluteValue_mul_tamagawaNumber_mul_kummerRatio_of_isMinimal u φ hc h2 hn
  rw [eq_div_iff htam]
  linear_combination (TauCeti.normalizedAbsoluteValue F_u c : ℚ)⁻¹ * h -
    φ.kummerRatio * W₁.tamagawaNumber (valuation F_u) * (inv_mul_cancel₀ habs)

/-- **The local Kummer ratio on arbitrary equations over `F_u`**: if `C₁` and `C₂` carry `W₁` and
`W₂` to minimal equations over `𝒪[F_u]`, with scaling factors `u₁` and `u₂`, and `φ^*ω₂ = c ω₁`,
then `|c u₂ / u₁|_u · c_u(W₁) · φ.kummerRatio = c_u(W₂)`. -/
theorem normalizedAbsoluteValue_mul_tamagawaNumber_mul_kummerRatio
    {W₁ W₂ : WeierstrassCurve F_u} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    {C₁ C₂ : VariableChange F_u}
    [(C₁ • W₁).IsMinimal 𝒪[F_u]] [(C₂ • W₂).IsMinimal 𝒪[F_u]]
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    (TauCeti.normalizedAbsoluteValue F_u (c * C₂.u / C₁.u) : ℚ) *
        W₁.tamagawaNumber (valuation F_u) * φ.kummerRatio =
      W₂.tamagawaNumber (valuation F_u) := by
  set ψ : Isogeny (C₁ • W₁).toAffine (C₂ • W₂).toAffine :=
    (variableChangeIsogeny C₂ (rfl : C₂ • W₂.toAffine = (C₂ • W₂).toAffine)).comp
      (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ W₁.toAffine)))
  have hdeg : ψ.degree = φ.degree := by
    simp [ψ]
  have hkr : ψ.kummerRatio = φ.kummerRatio := by
    simp [ψ]
  have h := normalizedAbsoluteValue_mul_tamagawaNumber_mul_kummerRatio_of_isMinimal u ψ
    (pullbackDifferential_variableChangeIsogeny_comp_eq_smul φ hc C₁ C₂) h2 (hdeg ▸ hn)
  rwa [hkr, tamagawaNumber_smul, tamagawaNumber_smul] at h

/-- **The local Kummer ratio on arbitrary equations over `F_u`, solved for `φ.kummerRatio`**. -/
theorem kummerRatio_eq_of_isMinimal_smul
    {W₁ W₂ : WeierstrassCurve F_u} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {c : F_u}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential W₂.toAffine) =
      c • Affine.invariantDifferential W₁.toAffine)
    {C₁ C₂ : VariableChange F_u}
    [(C₁ • W₁).IsMinimal 𝒪[F_u]] [(C₂ • W₂).IsMinimal 𝒪[F_u]]
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    φ.kummerRatio =
      (TauCeti.normalizedAbsoluteValue F_u (c * C₂.u / C₁.u) : ℚ)⁻¹ *
        W₂.tamagawaNumber (valuation F_u) / W₁.tamagawaNumber (valuation F_u) := by
  set ψ : Isogeny (C₁ • W₁).toAffine (C₂ • W₂).toAffine :=
    (variableChangeIsogeny C₂ (rfl : C₂ • W₂.toAffine = (C₂ • W₂).toAffine)).comp
      (φ.comp (variableChangeIsogeny C₁⁻¹ (inv_smul_smul C₁ W₁.toAffine)))
  have h := kummerRatio_eq_of_isMinimal u ψ
    (pullbackDifferential_variableChangeIsogeny_comp_eq_smul φ hc C₁ C₂) h2 (by simpa [ψ] using hn)
  simpa [ψ, tamagawaNumber_smul] using h

end AdicCompletion

section FinitePlace

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]

/-- **The finite local Kummer ratio at `v` on locally minimal equations**: if `E₁` and `E₂` are
minimal at `v` (`Localization.AtPrime v.asIdeal`) and `φ^*ω₂ = c ω₁`, with `2 ≠ 0` in `K_v` and
`deg φ ≠ 0` in `R`, then
`φ.finiteKummerRatio v = |c|_v⁻¹ · E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v`. -/
theorem finiteKummerRatio_eq_of_isMinimal (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (v : HeightOneSpectrum R)
    [IsMinimal (Localization.AtPrime v.asIdeal) E₁]
    [IsMinimal (Localization.AtPrime v.asIdeal) E₂]
    (h2 : (2 : v.adicCompletion K) ≠ 0) (hn : (φ.degree : R) ≠ 0) :
    φ.finiteKummerRatio v =
      (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
          (algebraMap K (v.adicCompletion K) c) : ℚ)⁻¹ *
        E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v := by
  have hdeg : (φ.baseChange (v.adicCompletion K)).degree = φ.degree :=
    degree_map φ (algebraMap K (v.adicCompletion K))
  rw [finiteKummerRatio_def, E₁.tamagawaNumberAt_def, E₂.tamagawaNumberAt_def]
  exact kummerRatio_eq_of_isMinimal v (φ.baseChange (v.adicCompletion K))
    (map_pullbackDifferential_invariantDifferential_eq_smul φ (algebraMap K (v.adicCompletion K))
      hc)
    h2 (hdeg ▸ hn)

/-- **The finite local Kummer ratio at `v`, multiplicative form on locally minimal equations.** -/
theorem normalizedAbsoluteValue_mul_tamagawaNumberAt_mul_finiteKummerRatio_of_isMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (v : HeightOneSpectrum R)
    [IsMinimal (Localization.AtPrime v.asIdeal) E₁]
    [IsMinimal (Localization.AtPrime v.asIdeal) E₂]
    (h2 : (2 : v.adicCompletion K) ≠ 0) (hn : (φ.degree : R) ≠ 0) :
    (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
        (algebraMap K (v.adicCompletion K) c) : ℚ) *
      E₁.tamagawaNumberAt v * φ.finiteKummerRatio v = E₂.tamagawaNumberAt v := by
  have hdeg : (φ.baseChange (v.adicCompletion K)).degree = φ.degree :=
    degree_map φ (algebraMap K (v.adicCompletion K))
  rw [finiteKummerRatio_def, E₁.tamagawaNumberAt_def, E₂.tamagawaNumberAt_def]
  exact normalizedAbsoluteValue_mul_tamagawaNumber_mul_kummerRatio_of_isMinimal v
    (φ.baseChange (v.adicCompletion K))
    (map_pullbackDifferential_invariantDifferential_eq_smul φ (algebraMap K (v.adicCompletion K))
      hc)
    h2 (hdeg ▸ hn)

/-- **The finite local Kummer ratio at `v` on arbitrary equations**: if `C₁` and `C₂` carry `E₁`
and `E₂` to equations minimal over `Localization.AtPrime v.asIdeal`, then
`φ.finiteKummerRatio v = |c u₂ / u₁|_v⁻¹ · E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v`. -/
theorem finiteKummerRatio_eq_of_isMinimal_smul (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (v : HeightOneSpectrum R) {C₁ C₂ : VariableChange K}
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₁ • E₁)]
    [IsMinimal (Localization.AtPrime v.asIdeal) (C₂ • E₂)]
    (h2 : (2 : v.adicCompletion K) ≠ 0) (hn : (φ.degree : R) ≠ 0) :
    φ.finiteKummerRatio v =
      (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
          (algebraMap K (v.adicCompletion K) (c * C₂.u / C₁.u)) : ℚ)⁻¹ *
        E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v := by
  have hdeg : (φ.baseChange (v.adicCompletion K)).degree = φ.degree :=
    degree_map φ (algebraMap K (v.adicCompletion K))
  have hmin₁ : ((C₁.baseChange (v.adicCompletion K)) •
      (E₁.baseChange (v.adicCompletion K))).IsMinimal 𝒪[v.adicCompletion K] := by
    rw [baseChange_smul_baseChange]
    infer_instance
  have hmin₂ : ((C₂.baseChange (v.adicCompletion K)) •
      (E₂.baseChange (v.adicCompletion K))).IsMinimal 𝒪[v.adicCompletion K] := by
    rw [baseChange_smul_baseChange]
    infer_instance
  rw [finiteKummerRatio_def, E₁.tamagawaNumberAt_def, E₂.tamagawaNumberAt_def]
  have h := kummerRatio_eq_of_isMinimal_smul v
    (C₁ := C₁.baseChange (v.adicCompletion K)) (C₂ := C₂.baseChange (v.adicCompletion K))
    (φ.baseChange (v.adicCompletion K))
    (map_pullbackDifferential_invariantDifferential_eq_smul φ (algebraMap K (v.adicCompletion K))
      hc)
    h2 (hdeg ▸ hn)
  change (φ.baseChange (v.adicCompletion K)).kummerRatio = _
  rw [h]
  congr 4
  simp [VariableChange.baseChange]

end FinitePlace

section CharZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  {K : Type*} [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  {E₁ E₂ : WeierstrassCurve K} [E₁.IsElliptic] [E₂.IsElliptic]

omit [Ring.HasFiniteQuotients R] in
private theorem two_ne_zero_adicCompletion (v : HeightOneSpectrum R) :
    (2 : v.adicCompletion K) ≠ 0 := by
  rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]
  exact (map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).mpr two_ne_zero

omit [IsDedekindDomain R] [Ring.HasFiniteQuotients R] [IsFractionRing R K]
  [E₁.IsElliptic] [E₂.IsElliptic] in
private theorem degree_ne_zero_ring (φ : Isogeny E₁.toAffine E₂.toAffine) :
    (φ.degree : R) ≠ 0 := by
  intro h
  exact (Nat.cast_ne_zero (R := K)).mpr φ.degree_ne_zero
    (by simpa only [map_natCast, map_zero] using congrArg (algebraMap R K) h)

/-- **In characteristic zero, the finite local Kummer ratio on globally minimal equations**: for
every height-one prime `v` of `R` (including those above `2` and those dividing `deg φ`),
`φ.finiteKummerRatio v = |c|_v⁻¹ · E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v`. -/
theorem finiteKummerRatio_eq_of_isGlobalMinimal (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal R E₁) (h₂ : IsGlobalMinimal R E₂) (v : HeightOneSpectrum R) :
    φ.finiteKummerRatio v =
      (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
          (algebraMap K (v.adicCompletion K) c) : ℚ)⁻¹ *
        E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v := by
  have := h₁.isMinimal v
  have := h₂.isMinimal v
  exact finiteKummerRatio_eq_of_isMinimal φ hc v
    (two_ne_zero_adicCompletion (K := K) v) (degree_ne_zero_ring (K := K) φ)

/-- **In characteristic zero, the finite local Kummer ratio on globally minimal equations,
multiplicative form.** -/
theorem normalizedAbsoluteValue_mul_tamagawaNumberAt_mul_finiteKummerRatio_of_isGlobalMinimal
    (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    (h₁ : IsGlobalMinimal R E₁) (h₂ : IsGlobalMinimal R E₂) (v : HeightOneSpectrum R) :
    (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
        (algebraMap K (v.adicCompletion K) c) : ℚ) *
      E₁.tamagawaNumberAt v * φ.finiteKummerRatio v = E₂.tamagawaNumberAt v := by
  have := h₁.isMinimal v
  have := h₂.isMinimal v
  exact normalizedAbsoluteValue_mul_tamagawaNumberAt_mul_finiteKummerRatio_of_isMinimal φ hc v
    (two_ne_zero_adicCompletion (K := K) v) (degree_ne_zero_ring (K := K) φ)

/-- **In characteristic zero, the finite local Kummer ratio via changes to globally minimal
equations**: parallel to `TauCeti.Isogeny.abs_mul_minimalRealPeriod_mul_index_eq_card_ker_mul`. -/
theorem finiteKummerRatio_eq_of_isGlobalMinimal_smul (φ : Isogeny E₁.toAffine E₂.toAffine) {c : K}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential E₂.toAffine) =
      c • Affine.invariantDifferential E₁.toAffine)
    {C₁ C₂ : VariableChange K} (h₁ : IsGlobalMinimal R (C₁ • E₁))
    (h₂ : IsGlobalMinimal R (C₂ • E₂)) (v : HeightOneSpectrum R) :
    φ.finiteKummerRatio v =
      (TauCeti.normalizedAbsoluteValue (v.adicCompletion K)
          (algebraMap K (v.adicCompletion K) (c * C₂.u / C₁.u)) : ℚ)⁻¹ *
        E₂.tamagawaNumberAt v / E₁.tamagawaNumberAt v := by
  have := h₁.isMinimal v
  have := h₂.isMinimal v
  exact finiteKummerRatio_eq_of_isMinimal_smul φ hc v
    (two_ne_zero_adicCompletion (K := K) v) (degree_ne_zero_ring (K := K) φ)

end CharZero

end TauCeti.Isogeny

end
