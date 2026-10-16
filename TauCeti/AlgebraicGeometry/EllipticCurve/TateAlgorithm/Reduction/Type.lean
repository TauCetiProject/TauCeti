/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Semistable
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Valuation
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Invariance
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import TauCeti.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The reduction type read off Tate's algorithm, and semistability

Let `R` be a discrete valuation ring with uniformiser `ϖ` and fraction field `K`, and let `W` be a
Weierstrass equation over `R` on which Tate's algorithm stops with symbol `s`
(`WeierstrassCurve.IsTateTerminal`). Such an equation is minimal over `K`
(`WeierstrassCurve.IsTateTerminal.isMinimal_baseChange`), and this file shows that `s` determines
the reduction type of `W` in Mathlib's good/multiplicative/additive trichotomy:

* the reduction is good exactly when `s = I₀`;
* it is multiplicative exactly when `s = Iₙ` with `n ≥ 1`, and then `n` is the valuation of the
  minimal discriminant, and the reduction is split exactly when the tangent quadratic
  `T² + a₁ T − a₂` splits over the residue field;
* it is additive exactly when `s` is none of the `Iₙ`.

The additive symbols are recognised by divisibilities alone: at each of them `ϖ` divides `b₂`, `a₃`,
`a₄` and `a₆`, hence `c₄` and `Δ` (`WeierstrassCurve.IsTateTerminal.dvd_c₄` and
`WeierstrassCurve.IsTateTerminal.dvd_Δ_iff`). At `Iₙ` with `n ≥ 1` the reduction is singular at the
origin and the stopping test asks for `ϖ ∤ b₂`, which is Tate's test for multiplicative reduction
(`WeierstrassCurve.hasMultiplicativeReduction_iff_reduction_b₂_ne_zero`).

Over a Dedekind domain `O` with fraction field `F`, an elliptic curve is semistable
(`WeierstrassCurve.IsSemistable`) exactly when, at every height-one prime `v`, Tate's algorithm run
on an equation of the curve over the localisation `O_v` stops at some `Iₙ` whenever it stops; the
reverse direction needs the residue fields to be perfect, so that the algorithm runs at all.

## Main results

* `WeierstrassCurve.IsTateTerminal.hasGoodReduction_iff`,
  `WeierstrassCurve.IsTateTerminal.hasMultiplicativeReduction_iff` and
  `WeierstrassCurve.IsTateTerminal.hasAdditiveReduction_iff`: the reduction type of an
  equation from the symbol at which the algorithm stops on it.
* `WeierstrassCurve.IsTateTerminal.hasGoodReduction_minimal_iff`,
  `WeierstrassCurve.IsTateTerminal.hasMultiplicativeReduction_minimal_iff` and
  `WeierstrassCurve.IsTateTerminal.hasAdditiveReduction_minimal_iff`: the same, for Mathlib's
  chosen minimal equation `E.minimal R` of a curve `E` with a minimal equation on which the
  algorithm stops.
* `WeierstrassCurve.IsTateTerminal.hasGoodReduction_minimal_baseChange_iff`,
  `WeierstrassCurve.IsTateTerminal.hasMultiplicativeReduction_minimal_baseChange_iff` and
  `WeierstrassCurve.IsTateTerminal.hasAdditiveReduction_minimal_baseChange_iff`: the same, for an
  equation defined over a ring mapping into `R`, such as an equation over `ℤ`.
* `WeierstrassCurve.IsTateTerminal.hasSplitMultiplicativeReduction_iff`: at `Iₙ` with `n ≥ 1`, the
  split test.
* `WeierstrassCurve.IsTateTerminal.localMinimalDiscriminantValuation_eq`: at `Iₙ`, `n` is the
  valuation of the minimal discriminant.
* `WeierstrassCurve.IsSemistable.exists_eq_I_of_isTateTerminal` and
  `WeierstrassCurve.isSemistable_iff_forall_isTateTerminal`: a curve over the fraction field of a
  Dedekind domain is semistable exactly when Tate's algorithm only ever stops at symbols `Iₙ`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, GTM 106, VII.5.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

namespace WeierstrassCurve

open IsLocalRing IsDiscreteValuationRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Polynomial TauCeti

section DiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {W : WeierstrassCurve R} {ϖ : R} {s : ReductionSymbol}

/-- At `Iₙ` with `n ≥ 1`, the reduction of a minimal equation is singular at the origin. -/
private theorem IsTateTerminal.reduction_isSingular_zero [IsMinimal R (W.baseChange K)]
    (hϖ : Irreducible ϖ) {n : ℕ} (h : W.IsTateTerminal ϖ (.I (n + 1))) :
    ((W.baseChange K).reduction R).toAffine.IsSingular 0 0 := by
  obtain ⟨h₃, h₄, h₆, -⟩ := isTateTerminal_I_add_one.1 h
  rw [reduction, integralModel_baseChange_self, map_residue_isSingular_zero_iff,
    hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton]
  exact ⟨h₆, h₄, h₃⟩

/-- **Tate's algorithm detects good reduction.** If the algorithm stops on `W` at `s`, the
reduction is good exactly when `s = I₀`. -/
theorem IsTateTerminal.hasGoodReduction_iff (hϖ : Irreducible ϖ) (h : W.IsTateTerminal ϖ s) :
    (W.baseChange K).HasGoodReduction R ↔ s = .I 0 := by
  have := h.isMinimal_baseChange (K := K) hϖ
  have hΔ : (W.baseChange K).Δ = algebraMap R K W.Δ := map_Δ W _
  rw [WeierstrassCurve.hasGoodReduction_iff, hΔ, hϖ.valuation_algebraMap_eq_one_iff_not_dvd,
    h.dvd_Δ_iff hϖ.prime, not_not]
  exact and_iff_right inferInstance

/-- **Tate's split test.** If the algorithm stops on `W` at `Iₙ` with `n ≥ 1`, the reduction is
split multiplicative exactly when the tangent quadratic `T² + a₁ T − a₂` splits over the residue
field. -/
theorem IsTateTerminal.hasSplitMultiplicativeReduction_iff (hϖ : Irreducible ϖ) {n : ℕ}
    (h : W.IsTateTerminal ϖ (.I (n + 1))) :
    (W.baseChange K).HasSplitMultiplicativeReduction R ↔
      (X ^ 2 + C (residue R W.a₁) * X - C (residue R W.a₂)).Splits := by
  have := h.isMinimal_baseChange (K := K) hϖ
  rw [hasSplitMultiplicativeReduction_iff_reduction_b₂_ne_zero_and_splits R
    (h.reduction_isSingular_zero hϖ), reduction, integralModel_baseChange_self, map_b₂, map_a₁,
    map_a₂, Ne, residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  exact and_iff_right (isTateTerminal_I_add_one.1 h).2.2.2.1

/-- At `Iₙ` with `n ≥ 1`, the reduction is multiplicative. -/
private theorem IsTateTerminal.hasMultiplicativeReduction (hϖ : Irreducible ϖ) {n : ℕ}
    (h : W.IsTateTerminal ϖ (.I (n + 1))) : (W.baseChange K).HasMultiplicativeReduction R := by
  have := h.isMinimal_baseChange (K := K) hϖ
  rw [hasMultiplicativeReduction_iff_reduction_b₂_ne_zero R (h.reduction_isSingular_zero hϖ),
    reduction, integralModel_baseChange_self, map_b₂, Ne, residue_eq_zero_iff,
    hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  exact (isTateTerminal_I_add_one.1 h).2.2.2.1

/-- **Tate's algorithm detects multiplicative reduction.** If the algorithm stops on `W` at `s`, the
reduction is multiplicative exactly when `s = Iₙ` for some `n ≥ 1`. -/
theorem IsTateTerminal.hasMultiplicativeReduction_iff (hϖ : Irreducible ϖ)
    (h : W.IsTateTerminal ϖ s) :
    (W.baseChange K).HasMultiplicativeReduction R ↔ ∃ n, s = .I (n + 1) := by
  refine ⟨fun hm ↦ ?_, fun ⟨n, hn⟩ ↦ (hn ▸ h).hasMultiplicativeReduction hϖ⟩
  have hΔ : (W.baseChange K).Δ = algebraMap R K W.Δ := map_Δ W _
  have hc₄ : (W.baseChange K).c₄ = algebraMap R K W.c₄ := map_c₄ W _
  rw [WeierstrassCurve.hasMultiplicativeReduction_iff, hΔ, hc₄,
    hϖ.valuation_algebraMap_lt_one_iff_dvd, hϖ.valuation_algebraMap_eq_one_iff_not_dvd,
    h.dvd_Δ_iff hϖ.prime] at hm
  obtain ⟨-, hs₀, hc₄⟩ := hm
  by_contra hne
  simp only [not_exists] at hne
  refine hc₄ (h.dvd_c₄ fun n hn ↦ ?_)
  cases n with
  | zero => exact hs₀ hn
  | succ n => exact hne n hn

/-- **Tate's algorithm detects additive reduction.** If the algorithm stops on `W` at `s`, the
reduction is additive exactly when `s` is none of the `Iₙ`. -/
theorem IsTateTerminal.hasAdditiveReduction_iff (hϖ : Irreducible ϖ) (h : W.IsTateTerminal ϖ s) :
    (W.baseChange K).HasAdditiveReduction R ↔ ∀ n, s ≠ .I n := by
  have := h.isMinimal_baseChange (K := K) hϖ
  refine ⟨fun ha n hn ↦ ?_, fun hs ↦ ?_⟩
  · subst hn
    cases n with
    | zero => exact ha.not_hasGoodReduction R ((h.hasGoodReduction_iff hϖ).2 rfl)
    | succ n => exact ha.not_hasMultiplicativeReduction R (h.hasMultiplicativeReduction hϖ)
  have hΔ : (W.baseChange K).Δ = algebraMap R K W.Δ := map_Δ W _
  have hc₄ : (W.baseChange K).c₄ = algebraMap R K W.c₄ := map_c₄ W _
  rw [WeierstrassCurve.hasAdditiveReduction_iff, hΔ, hc₄, hϖ.valuation_algebraMap_lt_one_iff_dvd,
    hϖ.valuation_algebraMap_lt_one_iff_dvd, h.dvd_Δ_iff hϖ.prime]
  exact ⟨inferInstance, hs 0, h.dvd_c₄ hs⟩

/-- If Tate's algorithm stops on `W` at `s`, the reduction is good or multiplicative exactly when
`s = Iₙ` for some `n`. -/
theorem IsTateTerminal.not_hasAdditiveReduction_iff (hϖ : Irreducible ϖ)
    (h : W.IsTateTerminal ϖ s) :
    ¬ (W.baseChange K).HasAdditiveReduction R ↔ ∃ n, s = .I n := by
  simp only [h.hasAdditiveReduction_iff hϖ, ne_eq, not_forall_not]

/-! The symbol at which the algorithm stops on one minimal equation of a curve `E` decides the
reduction type of Mathlib's chosen minimal equation `E.minimal R`. -/

/-- **Tate's algorithm detects good reduction of the chosen minimal equation.** If a change of
variables carries `E` to a minimal equation on which the algorithm stops at `s`, then
`E.minimal R` has good reduction exactly when `s = I₀`. -/
theorem IsTateTerminal.hasGoodReduction_minimal_iff {E : WeierstrassCurve K} (D : VariableChange K)
    (hD : D • E = W.baseChange K) (hϖ : Irreducible ϖ) (h : W.IsTateTerminal ϖ s) :
    (E.minimal R).HasGoodReduction R ↔ s = .I 0 := by
  have := h.isMinimal_baseChange (K := K) hϖ
  obtain ⟨D', hD'⟩ := exists_smul_minimal_eq_of_smul_eq R D hD
  rw [WeierstrassCurve.hasGoodReduction_minimal_iff, ← valuation_Δ_eq_of_isMinimal_smul R _ hD',
    ← h.hasGoodReduction_iff (K := K) hϖ, WeierstrassCurve.hasGoodReduction_iff,
    and_iff_right ‹IsMinimal R (W.baseChange K)›]

/-- **Tate's algorithm detects additive reduction of the chosen minimal equation.** If a change of
variables carries the elliptic curve `E` to a minimal equation on which the algorithm stops at
`s`, then `E.minimal R` has additive reduction exactly when `s` is none of the `Iₙ`. -/
theorem IsTateTerminal.hasAdditiveReduction_minimal_iff {E : WeierstrassCurve K} [E.IsElliptic]
    (D : VariableChange K) (hD : D • E = W.baseChange K) (hϖ : Irreducible ϖ)
    (h : W.IsTateTerminal ϖ s) : (E.minimal R).HasAdditiveReduction R ↔ ∀ n, s ≠ .I n := by
  have := h.isMinimal_baseChange (K := K) hϖ
  obtain ⟨C, hC⟩ := E.exists_smul_eq_minimal R
  have : (E.minimal R).IsElliptic := hC ▸ inferInstance
  obtain ⟨D', hD'⟩ := exists_smul_minimal_eq_of_smul_eq R D hD
  rw [← hasAdditiveReduction_iff_of_isMinimal_smul R _ hD']
  exact h.hasAdditiveReduction_iff hϖ

/-- **Tate's algorithm detects multiplicative reduction of the chosen minimal equation.** If a
change of variables carries the elliptic curve `E` to a minimal equation on which the algorithm
stops at `s`, then `E.minimal R` has multiplicative reduction exactly when `s = Iₙ` with
`n ≥ 1`. -/
theorem IsTateTerminal.hasMultiplicativeReduction_minimal_iff {E : WeierstrassCurve K}
    [E.IsElliptic] (D : VariableChange K) (hD : D • E = W.baseChange K) (hϖ : Irreducible ϖ)
    (h : W.IsTateTerminal ϖ s) :
    (E.minimal R).HasMultiplicativeReduction R ↔ ∃ n, s = .I (n + 1) := by
  have hg := h.hasGoodReduction_minimal_iff (K := K) D hD hϖ
  have ha := h.hasAdditiveReduction_minimal_iff (K := K) D hD hϖ
  refine ⟨fun hm ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, s = .I m := by
      simpa only [ne_eq, not_forall_not] using mt ha.2 (hm.not_hasAdditiveReduction R)
    cases m with
    | zero => exact absurd (hg.2 rfl) (hm.not_hasGoodReduction R)
    | succ m => exact ⟨m, rfl⟩
  rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction (R := R)
    (W := E.minimal R) with hgood | hm | hadd
  · exact absurd (hn.symm.trans (hg.1 hgood)) nofun
  · exact hm
  · exact absurd hn (ha.1 hadd _)

/-! The same for an equation `W₀` over a ring `A` mapping into `R`, such as an equation over `ℤ`,
when a change of variables over `R` carries it to an equation on which the algorithm stops. -/

variable {A : Type*} [CommRing A] [Algebra A K] {φ : A →+* R} {W₀ : WeierstrassCurve A}

/-- **Tate's algorithm, run on an equation over a ring mapping into `R`, detects
good reduction of its chosen minimal equation.** Let `W₀` be an equation over `A`,
mapped into `R` by `φ` compatibly with `K`. If a change of variables `C` over `R` carries it to
an equation on which the algorithm stops at `s`, then `(W₀.baseChange K).minimal R` has good
reduction exactly when `s = I₀`. -/
theorem IsTateTerminal.hasGoodReduction_minimal_baseChange_iff
    (hφ : (algebraMap R K).comp φ = algebraMap A K) (C : VariableChange R) (hϖ : Irreducible ϖ)
    (h : (C • W₀.map φ).IsTateTerminal ϖ s) :
    ((W₀.baseChange K).minimal R).HasGoodReduction R ↔ s = .I 0 :=
  h.hasGoodReduction_minimal_iff _ (smul_baseChange_eq_baseChange_smul_map hφ C W₀) hϖ

/-- **Tate's algorithm, run on an equation over a ring mapping into `R`, detects
multiplicative reduction of its chosen minimal equation.** Let `W₀` be an equation over `A`,
mapped into `R` by `φ` compatibly with `K`. If a change of variables `C` over `R` carries it to
an equation on which the algorithm stops at `s`, then `(W₀.baseChange K).minimal R` has
multiplicative reduction exactly when `s = Iₙ` with `n ≥ 1`. -/
theorem IsTateTerminal.hasMultiplicativeReduction_minimal_baseChange_iff
    [(W₀.baseChange K).IsElliptic] (hφ : (algebraMap R K).comp φ = algebraMap A K)
    (C : VariableChange R) (hϖ : Irreducible ϖ) (h : (C • W₀.map φ).IsTateTerminal ϖ s) :
    ((W₀.baseChange K).minimal R).HasMultiplicativeReduction R ↔ ∃ n, s = .I (n + 1) :=
  h.hasMultiplicativeReduction_minimal_iff _ (smul_baseChange_eq_baseChange_smul_map hφ C W₀) hϖ

/-- **Tate's algorithm, run on an equation over a ring mapping into `R`, detects
additive reduction of its chosen minimal equation.** Let `W₀` be an equation over `A`,
mapped into `R` by `φ` compatibly with `K`. If a change of variables `C` over `R` carries it to
an equation on which the algorithm stops at `s`, then `(W₀.baseChange K).minimal R` has
additive reduction exactly when `s` is none of the `Iₙ`. -/
theorem IsTateTerminal.hasAdditiveReduction_minimal_baseChange_iff
    [(W₀.baseChange K).IsElliptic] (hφ : (algebraMap R K).comp φ = algebraMap A K)
    (C : VariableChange R) (hϖ : Irreducible ϖ) (h : (C • W₀.map φ).IsTateTerminal ϖ s) :
    ((W₀.baseChange K).minimal R).HasAdditiveReduction R ↔ ∀ n, s ≠ .I n :=
  h.hasAdditiveReduction_minimal_iff _ (smul_baseChange_eq_baseChange_smul_map hφ C W₀) hϖ

/-- **At `Iₙ`, the index is the valuation of the minimal discriminant.** -/
theorem IsTateTerminal.localMinimalDiscriminantValuation_eq [(W.baseChange K).IsElliptic]
    (hϖ : Irreducible ϖ) {n : ℕ} (h : W.IsTateTerminal ϖ (.I n)) :
    (W.baseChange K).localMinimalDiscriminantValuation R = n := by
  have := h.isMinimal_baseChange (K := K) hϖ
  have key := (W.baseChange K).localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_smul R 1
    (one_smul _ _)
  rw [integralModel_baseChange_self, h.addVal_Δ_eq hϖ] at key
  exact_mod_cast key

end DiscreteValuationRing

/-! ### Semistability over a Dedekind domain -/

section Semistable

variable {O : Type*} [CommRing O] [IsDedekindDomain O]
  {F : Type*} [Field F] [Algebra O F] [IsFractionRing O F] {W : WeierstrassCurve F} [W.IsElliptic]

/-- **On a semistable curve, Tate's algorithm only stops at symbols `Iₙ`.** At a height-one prime
`v`, let `W'` be an equation over the localisation `O_v` of the curve, and suppose Tate's
algorithm, run with a uniformiser `ϖ`, stops on `W'` at `s`. Then `s = Iₙ` for some `n`. -/
theorem IsSemistable.exists_eq_I_of_isTateTerminal (h : IsSemistable O W) (v : HeightOneSpectrum O)
    {W' : WeierstrassCurve (Localization.AtPrime v.asIdeal)} (D : VariableChange F)
    (hD : D • W = W'.baseChange F) {ϖ : Localization.AtPrime v.asIdeal} (hϖ : Irreducible ϖ)
    {s : ReductionSymbol} (hs : W'.IsTateTerminal ϖ s) : ∃ n, s = .I n := by
  simpa only [hs.hasAdditiveReduction_minimal_iff D hD hϖ, ne_eq, not_forall_not] using
    h.not_hasAdditiveReduction v

/-- **Semistability is read off Tate's algorithm.** Over a Dedekind domain whose localisations at
height-one primes have perfect residue fields, an elliptic curve is semistable exactly when, at
every height-one prime `v`, Tate's algorithm run on any equation of the curve over `O_v`, with any
uniformiser, stops at some `Iₙ` whenever it stops. -/
theorem isSemistable_iff_forall_isTateTerminal
    [∀ v : HeightOneSpectrum O, PerfectField (ResidueField (Localization.AtPrime v.asIdeal))] :
    IsSemistable O W ↔ ∀ (v : HeightOneSpectrum O)
      (W' : WeierstrassCurve (Localization.AtPrime v.asIdeal)) (D : VariableChange F)
      (ϖ : Localization.AtPrime v.asIdeal) (s : ReductionSymbol),
        D • W = W'.baseChange F → Irreducible ϖ → W'.IsTateTerminal ϖ s → ∃ n, s = .I n := by
  refine ⟨fun h v W' D ϖ s hD hϖ hs ↦ h.exists_eq_I_of_isTateTerminal v D hD hϖ hs,
    fun h ↦ IsSemistable.of_forall_not_hasAdditiveReduction fun v ↦ ?_⟩
  -- Run Tate's algorithm on the integral model of the chosen minimal equation at `v`.
  set Rv := Localization.AtPrime v.asIdeal
  obtain ⟨C₀, hC₀⟩ := W.exists_smul_eq_minimal Rv
  have : (W.minimal Rv).IsElliptic := hC₀ ▸ inferInstance
  set W₀ := (W.minimal Rv).integralModel Rv
  have hW₀ : W₀.baseChange F = W.minimal Rv := baseChange_integralModel_eq Rv _
  have : IsMinimal Rv (W₀.baseChange F) := hW₀ ▸ inferInstance
  have hΔ : W₀.Δ ≠ 0 := integralModel_minimal_Δ_ne_zero Rv W
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible Rv
  obtain ⟨C, s, hs⟩ := exists_isTateTerminal (K := F) hϖ W₀ hΔ
  -- The equation it stops on is again minimal, and in the orbit of `W`.
  have hCW₀ : (C • W₀).baseChange F = C.baseChange F • W.minimal Rv := by
    rw [baseChange, ← map_variableChange, ← baseChange, hW₀, VariableChange.baseChange]
  have : IsMinimal Rv ((C • W₀).baseChange F) := hCW₀ ▸ inferInstance
  have hD : (C.baseChange F * C₀) • W = (C • W₀).baseChange F := by
    rw [mul_smul, hC₀, hCW₀]
  obtain ⟨n, rfl⟩ := h v (C • W₀) _ ϖ s hD hϖ hs
  exact fun ha ↦ (hs.hasAdditiveReduction_minimal_iff _ hD hϖ).1 ha n rfl

end Semistable

end WeierstrassCurve

end
