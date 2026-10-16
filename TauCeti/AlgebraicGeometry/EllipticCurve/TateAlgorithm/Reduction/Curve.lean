/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Invariance
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Type
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel

/-!
# The reduction symbol and the algorithmic Ogg exponent of an elliptic curve

Let `R` be a discrete valuation ring with fraction field `K` and perfect residue field, and let `W`
be an elliptic curve over `K`. Tate's algorithm, run on a minimal equation of `W` over `R`, stops
with a symbol (`WeierstrassCurve.exists_isTateTerminal`), and this symbol does not depend on the
minimal equation, on the changes of variables made along the way, or on the uniformiser
(`WeierstrassCurve.IsTateTerminal.eq_of_isMinimal_smul`). This file names it as an invariant of
the curve, `W.reductionSymbol R`, and with it the **algorithmic Ogg exponent**

`f = v(Δ_min) − m + 1`,

where `m` is the component count of the symbol (`TauCeti.ReductionSymbol.componentCount`) and
`v(Δ_min)` the valuation of the minimal discriminant
(`WeierstrassCurve.localMinimalDiscriminantValuation`). It is the exponent read off Tate's
algorithm (Silverman, *Advanced Topics*, IV.9); by Ogg's formula (*Advanced Topics*, IV.11) it is
the exponent of the conductor, an identification not made here.

Both are invariant under a change of variables over `K`, and both detect the reduction type: the
symbol is `I₀` at good reduction, `Iₙ` with `n = v(Δ_min) ≥ 1` at multiplicative reduction, and
none of the `Iₙ` at additive reduction; correspondingly the exponent is `0`, `1`, or at least `2`.
The exponent never exceeds `v(Δ_min)`, so it vanishes at every prime of good reduction.

## Main definitions

* `WeierstrassCurve.reductionSymbol`: the symbol at which Tate's algorithm stops on a minimal
  equation of `W`.
* `WeierstrassCurve.algorithmicOggExponent`: the algorithmic Ogg exponent `v(Δ_min) − m + 1`.

## Main results

* `WeierstrassCurve.reductionSymbol_eq_of_isTateTerminal` and
  `WeierstrassCurve.reductionSymbol_eq_iff`: the symbol is the output of Tate's algorithm on any
  minimal equation of `W`, with any uniformiser.
* `WeierstrassCurve.reductionSymbol_smul`: the symbol is invariant under a change of variables.
* `WeierstrassCurve.reductionSymbol_eq_I_iff`, `WeierstrassCurve.reductionSymbol_eq_I_zero_iff`,
  `WeierstrassCurve.exists_reductionSymbol_eq_I_add_one_iff` and
  `WeierstrassCurve.forall_reductionSymbol_ne_I_iff`: the symbol detects the reduction type.
* `WeierstrassCurve.natCast_algorithmicOggExponent`: the exponent is `v(Δ_min) − m + 1`.
* `WeierstrassCurve.algorithmicOggExponent_eq_zero_iff`,
  `WeierstrassCurve.algorithmicOggExponent_eq_one_iff` and
  `WeierstrassCurve.two_le_algorithmicOggExponent_iff`: the exponent is `0` at good, `1` at
  multiplicative and at least `2` at additive reduction.
* `WeierstrassCurve.algorithmicOggExponent_le_localMinimalDiscriminantValuation`: `f ≤ v(Δ_min)`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9 and IV.11.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

open IsLocalRing IsDiscreteValuationRing TauCeti

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The integral model of the chosen minimal equation, transformed by a change of variables over
`R`, is a model of the transformed minimal equation. -/
private theorem baseChange_smul_integralModel_minimal (W : WeierstrassCurve K)
    (C : VariableChange R) :
    (C • (W.minimal R).integralModel R).baseChange K = C.baseChange K • W.minimal R := by
  rw [← integralModel_baseChange_smul, baseChange_integralModel_eq]

variable [PerfectField (ResidueField R)]

/-- Tate's algorithm stops on the integral model of the chosen minimal equation, after a change of
variables over `R`. -/
private theorem exists_isTateTerminal_minimal (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (s : ReductionSymbol) (C : VariableChange R) (ϖ : R), Irreducible ϖ ∧
      (C • (W.minimal R).integralModel R).IsTateTerminal ϖ s := by
  have : IsMinimal R (((W.minimal R).integralModel R).baseChange K) :=
    (baseChange_integralModel_eq R (W.minimal R)).symm ▸ inferInstance
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨C, s, h⟩ := exists_isTateTerminal (K := K) hϖ _ (integralModel_minimal_Δ_ne_zero R W)
  exact ⟨s, C, ϖ, hϖ, h⟩

/-- **The reduction symbol of an elliptic curve**: the symbol at which Tate's algorithm stops on a
minimal equation of `W` over `R`. It does not depend on the minimal equation, on the changes of
variables made by the algorithm, or on the uniformiser (`reductionSymbol_eq_of_isTateTerminal`). -/
noncomputable def reductionSymbol (W : WeierstrassCurve K) [W.IsElliptic] : ReductionSymbol :=
  (W.exists_isTateTerminal_minimal R).choose

/-- **Tate's algorithm computes the reduction symbol**: it stops with output `W.reductionSymbol R`
on some minimal equation of `W` over `R`. -/
theorem exists_isTateTerminal_reductionSymbol (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (W' : WeierstrassCurve R) (D : VariableChange K) (ϖ : R), IsMinimal R (W'.baseChange K) ∧
      D • W = W'.baseChange K ∧ Irreducible ϖ ∧ W'.IsTateTerminal ϖ (W.reductionSymbol R) := by
  obtain ⟨C, ϖ, hϖ, h⟩ := (W.exists_isTateTerminal_minimal R).choose_spec
  obtain ⟨C₀, hC₀⟩ := W.exists_smul_eq_minimal R
  refine ⟨_, C.baseChange K * C₀, ϖ, ?_, ?_, hϖ, h⟩
  · rw [baseChange_smul_integralModel_minimal]
    infer_instance
  · rw [baseChange_smul_integralModel_minimal, mul_smul, hC₀]

variable {R}

/-- **The reduction symbol is the output of Tate's algorithm on any minimal equation.** If `W'` is
an equation over `R`, minimal over `K` and related to `W` by a change of variables over `K`, and
Tate's algorithm, run with any uniformiser, stops on `W'` with output `s`, then `s` is the
reduction symbol of `W`. -/
theorem reductionSymbol_eq_of_isTateTerminal {W : WeierstrassCurve K} [W.IsElliptic]
    {W' : WeierstrassCurve R} [IsMinimal R (W'.baseChange K)] (D : VariableChange K)
    (hD : D • W = W'.baseChange K) {ϖ : R} (hϖ : Irreducible ϖ) {s : ReductionSymbol}
    (h : W'.IsTateTerminal ϖ s) : W.reductionSymbol R = s := by
  obtain ⟨W₁, D₁, ϖ₁, hmin, hD₁, hϖ₁, h₁⟩ := W.exists_isTateTerminal_reductionSymbol R
  have : (W₁.baseChange K).IsElliptic := hD₁ ▸ inferInstance
  exact (IsTateTerminal.eq_of_isMinimal_smul hϖ₁ hϖ (D * D₁⁻¹)
    (by rw [mul_smul, ← hD₁, inv_smul_smul, hD]) h₁ h).symm

/-- **Characterisation of the reduction symbol**: `W.reductionSymbol R = s` exactly when Tate's
algorithm stops with output `s` on some minimal equation of `W`. -/
theorem reductionSymbol_eq_iff {W : WeierstrassCurve K} [W.IsElliptic] {s : ReductionSymbol} :
    W.reductionSymbol R = s ↔
      ∃ (W' : WeierstrassCurve R) (D : VariableChange K) (ϖ : R), IsMinimal R (W'.baseChange K) ∧
        D • W = W'.baseChange K ∧ Irreducible ϖ ∧ W'.IsTateTerminal ϖ s := by
  refine ⟨fun h ↦ h ▸ W.exists_isTateTerminal_reductionSymbol R, ?_⟩
  rintro ⟨W', D, ϖ, hmin, hD, hϖ, h⟩
  exact reductionSymbol_eq_of_isTateTerminal D hD hϖ h

/-- **The reduction symbol is an invariant of the curve**: it does not change under a change of
variables. -/
@[simp]
theorem reductionSymbol_smul (D : VariableChange K) (W : WeierstrassCurve K) [W.IsElliptic] :
    (D • W).reductionSymbol R = W.reductionSymbol R := by
  obtain ⟨W', D', ϖ, hmin, hD', hϖ, h⟩ := W.exists_isTateTerminal_reductionSymbol R
  exact reductionSymbol_eq_of_isTateTerminal (D' * D⁻¹) (by rw [mul_smul, inv_smul_smul, hD']) hϖ h

/-- **The reduction symbol detects additive reduction**: it is none of the `Iₙ` exactly when the
minimal equation of `W` has additive reduction. -/
@[simp]
theorem forall_reductionSymbol_ne_I_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    (∀ n, W.reductionSymbol R ≠ .I n) ↔ (W.minimal R).HasAdditiveReduction R := by
  obtain ⟨W', D, ϖ, hmin, hD, hϖ, h⟩ := W.exists_isTateTerminal_reductionSymbol R
  obtain ⟨C₀, hC₀⟩ := W.exists_smul_eq_minimal R
  have : (W.minimal R).IsElliptic := hC₀ ▸ inferInstance
  rw [← h.hasAdditiveReduction_iff (K := K) hϖ,
    hasAdditiveReduction_iff_of_isMinimal_smul R (W₁ := W.minimal R) (W₂ := W'.baseChange K)
      (D * C₀⁻¹) (by rw [mul_smul, ← hC₀, inv_smul_smul, hD])]

/-- **The reduction symbol is `Iₙ` exactly at good or multiplicative reduction, with `n` the
valuation of the minimal discriminant.** -/
theorem reductionSymbol_eq_I_iff (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ) :
    W.reductionSymbol R = .I n ↔
      ¬ (W.minimal R).HasAdditiveReduction R ∧ W.localMinimalDiscriminantValuation R = n := by
  obtain ⟨W', D, ϖ, hmin, hD, hϖ, h⟩ := W.exists_isTateTerminal_reductionSymbol R
  have hv := W.localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_baseChange R D hD
  rw [← forall_reductionSymbol_ne_I_iff, not_forall_not]
  constructor
  · intro hn
    rw [hn] at h
    exact ⟨⟨n, hn⟩, by exact_mod_cast hv.trans (h.addVal_Δ_eq hϖ)⟩
  · rintro ⟨⟨m, hm⟩, hmn⟩
    rw [hm] at h ⊢
    have hm' := hv.trans (h.addVal_Δ_eq hϖ)
    rw [hmn, Nat.cast_inj] at hm'
    rw [hm']

/-- **The reduction symbol is `I₀` exactly at good reduction.** -/
@[simp]
theorem reductionSymbol_eq_I_zero_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    W.reductionSymbol R = .I 0 ↔ (W.minimal R).HasGoodReduction R := by
  rw [reductionSymbol_eq_I_iff, localMinimalDiscriminantValuation_eq_zero_iff]
  exact ⟨And.right, fun h ↦ ⟨fun ha ↦ ha.not_hasGoodReduction R h, h⟩⟩

/-- **The reduction symbol is `Iₙ` with `n ≥ 1` exactly at multiplicative reduction.** -/
@[simp]
theorem exists_reductionSymbol_eq_I_add_one_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    (∃ n, W.reductionSymbol R = .I (n + 1)) ↔ (W.minimal R).HasMultiplicativeReduction R := by
  simp_rw [reductionSymbol_eq_I_iff]
  constructor
  · rintro ⟨n, ha, hn⟩
    have hg : ¬ (W.minimal R).HasGoodReduction R := by
      rw [← localMinimalDiscriminantValuation_eq_zero_iff, hn]
      exact n.succ_ne_zero
    exact ((W.minimal R).hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction
      R).resolve_left hg |>.resolve_right ha
  · intro hm
    have hg := hm.not_hasGoodReduction R
    rw [← localMinimalDiscriminantValuation_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hg
    exact ⟨n, hm.not_hasAdditiveReduction R, hn⟩

variable (R)

/-- **The algorithmic Ogg exponent of an elliptic curve**, `v(Δ_min) − m + 1`, where `m` is the
component count of the reduction symbol and `v(Δ_min)` the valuation of the minimal discriminant
(`natCast_algorithmicOggExponent`). It is `0` at good reduction, `1` at multiplicative reduction
and at least `2` at additive reduction. -/
noncomputable def algorithmicOggExponent (W : WeierstrassCurve K) [W.IsElliptic] : ℕ :=
  ((W.reductionSymbol R).algorithmicOggExponent (W.localMinimalDiscriminantValuation R)).toNat

variable {R}

/-- The value of the integer-valued exponent of the reduction symbol in each reduction type. -/
private theorem algorithmicOggExponent_reductionSymbol_cases (W : WeierstrassCurve K)
    [W.IsElliptic] :
    ((W.minimal R).HasGoodReduction R →
        (W.reductionSymbol R).algorithmicOggExponent (W.localMinimalDiscriminantValuation R) = 0) ∧
      ((W.minimal R).HasMultiplicativeReduction R →
        (W.reductionSymbol R).algorithmicOggExponent (W.localMinimalDiscriminantValuation R) = 1) ∧
      ((W.minimal R).HasAdditiveReduction R → 2 ≤
        (W.reductionSymbol R).algorithmicOggExponent (W.localMinimalDiscriminantValuation R)) := by
  refine ⟨fun hg ↦ ?_, fun hm ↦ ?_, fun ha ↦ ?_⟩
  · rw [(reductionSymbol_eq_I_zero_iff W).2 hg,
      (localMinimalDiscriminantValuation_eq_zero_iff R W).2 hg]
    exact ReductionSymbol.algorithmicOggExponent_I_zero
  · obtain ⟨n, hn⟩ := (exists_reductionSymbol_eq_I_add_one_iff W).2 hm
    rw [hn, ((reductionSymbol_eq_I_iff W _).1 hn).2]
    exact ReductionSymbol.algorithmicOggExponent_I _ n.succ_pos
  · obtain ⟨W', D, ϖ, hmin, hD, hϖ, h⟩ := W.exists_isTateTerminal_reductionSymbol R
    exact h.two_le_algorithmicOggExponent hϖ ((forall_reductionSymbol_ne_I_iff W).2 ha)
      (W.localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_baseChange R D hD).symm

/-- **The algorithmic Ogg exponent is `v(Δ_min) − m + 1`**, with `m` the component count of the
reduction symbol: the integer `v(Δ_min) − m + 1` is nonnegative, so no truncation occurs. -/
theorem natCast_algorithmicOggExponent (W : WeierstrassCurve K) [W.IsElliptic] :
    (W.algorithmicOggExponent R : ℤ) =
      (W.reductionSymbol R).algorithmicOggExponent (W.localMinimalDiscriminantValuation R) := by
  obtain ⟨hg, hm, ha⟩ := W.algorithmicOggExponent_reductionSymbol_cases (R := R)
  refine Int.toNat_of_nonneg ?_
  rcases (W.minimal R).hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R
    with h | h | h
  · exact (hg h).ge
  · rw [hm h]
    exact zero_le_one
  · exact zero_le_two.trans (ha h)

/-- **The algorithmic Ogg exponent is an invariant of the curve**: it does not change under a
change of variables. -/
@[simp]
theorem algorithmicOggExponent_smul (D : VariableChange K) (W : WeierstrassCurve K)
    [W.IsElliptic] : (D • W).algorithmicOggExponent R = W.algorithmicOggExponent R := by
  simp only [algorithmicOggExponent, reductionSymbol_smul, localMinimalDiscriminantValuation_smul]

/-- **The algorithmic Ogg exponent vanishes exactly at good reduction.** -/
@[simp]
theorem algorithmicOggExponent_eq_zero_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    W.algorithmicOggExponent R = 0 ↔ (W.minimal R).HasGoodReduction R := by
  obtain ⟨hg, hm, ha⟩ := W.algorithmicOggExponent_reductionSymbol_cases (R := R)
  rw [← Nat.cast_inj (R := ℤ), natCast_algorithmicOggExponent, Nat.cast_zero]
  refine ⟨fun h ↦ ?_, hg⟩
  rcases (W.minimal R).hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R
    with h' | h' | h'
  · exact h'
  · exact absurd (hm h') (by rw [h]; exact zero_ne_one)
  · exact absurd (ha h') (by rw [h]; decide)

/-- **The algorithmic Ogg exponent is positive exactly at bad reduction.** -/
@[simp]
theorem algorithmicOggExponent_pos_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    0 < W.algorithmicOggExponent R ↔ ¬ (W.minimal R).HasGoodReduction R := by
  rw [Nat.pos_iff_ne_zero, ne_eq, algorithmicOggExponent_eq_zero_iff]

/-- **The algorithmic Ogg exponent is `1` exactly at multiplicative reduction.** -/
@[simp]
theorem algorithmicOggExponent_eq_one_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    W.algorithmicOggExponent R = 1 ↔ (W.minimal R).HasMultiplicativeReduction R := by
  obtain ⟨hg, hm, ha⟩ := W.algorithmicOggExponent_reductionSymbol_cases (R := R)
  rw [← Nat.cast_inj (R := ℤ), natCast_algorithmicOggExponent, Nat.cast_one]
  refine ⟨fun h ↦ ?_, hm⟩
  rcases (W.minimal R).hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R
    with h' | h' | h'
  · exact absurd (hg h') (by rw [h]; exact one_ne_zero)
  · exact h'
  · exact absurd (ha h') (by rw [h]; decide)

/-- **The algorithmic Ogg exponent is at least `2` exactly at additive reduction.** -/
@[simp]
theorem two_le_algorithmicOggExponent_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    2 ≤ W.algorithmicOggExponent R ↔ (W.minimal R).HasAdditiveReduction R := by
  obtain ⟨hg, hm, ha⟩ := W.algorithmicOggExponent_reductionSymbol_cases (R := R)
  rw [← Nat.cast_le (α := ℤ), natCast_algorithmicOggExponent, Nat.cast_ofNat]
  refine ⟨fun h ↦ ?_, ha⟩
  rcases (W.minimal R).hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R
    with h' | h' | h'
  · exact absurd h (by rw [hg h']; decide)
  · exact absurd h (by rw [hm h']; decide)
  · exact h'

/-- **The algorithmic Ogg exponent is at most the valuation of the minimal discriminant**, since
every reduction symbol has at least one component. -/
theorem algorithmicOggExponent_le_localMinimalDiscriminantValuation (W : WeierstrassCurve K)
    [W.IsElliptic] : W.algorithmicOggExponent R ≤ W.localMinimalDiscriminantValuation R := by
  rw [← Nat.cast_le (α := ℤ), natCast_algorithmicOggExponent,
    ReductionSymbol.algorithmicOggExponent_eq]
  have := (W.reductionSymbol R).componentCount_pos
  omega

end WeierstrassCurve

end
