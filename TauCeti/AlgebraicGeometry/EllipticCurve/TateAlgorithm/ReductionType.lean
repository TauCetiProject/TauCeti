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

/-!
# The reduction type read off Tate's algorithm, and semistability

Let `R` be a discrete valuation ring with uniformiser `ϖ` and fraction field `K`, and let `W` be a
Weierstrass equation over `R` that is minimal over `K` and on which Tate's algorithm stops with
symbol `s` (`WeierstrassCurve.IsTateTerminal`). This file shows that `s` determines the reduction
type of `W` in Mathlib's good/multiplicative/additive trichotomy:

* the reduction is good exactly when `s = I₀`;
* it is multiplicative exactly when `s = Iₙ` with `n ≥ 1`, and then `n` is the valuation of the
  minimal discriminant, and the reduction is split exactly when the tangent quadratic
  `T² + a₁ T − a₂` splits over the residue field;
* it is additive exactly when `s` is none of the `Iₙ`.

The additive symbols are recognised by divisibilities alone: at each of them `ϖ` divides `b₂`, `a₃`,
`a₄` and `a₆`, hence `c₄` and `Δ`. At `Iₙ` with `n ≥ 1` the stopping test asks for `ϖ ∤ b₂`, and
since `c₄ ≡ b₂² (mod ϖ)` there, `ϖ ∤ c₄`.

Since the reduction type and the valuation of the minimal discriminant are invariants of the curve,
the output of the algorithm is independent of the choices made along the way whenever one run of it
stops at some `Iₙ`: any other minimal equation of the same curve, run with any uniformiser, stops at
the same `Iₙ`. In particular two runs either both stop at an additive symbol or both stop at the
same `Iₙ`.

Over a Dedekind domain `O` with fraction field `F`, an elliptic curve is semistable
(`WeierstrassCurve.IsSemistable`) exactly when, at every height-one prime `v`, Tate's algorithm run
on a minimal equation over the localisation `O_v` stops at some `Iₙ`; the reverse direction needs
the residue fields to be perfect, so that the algorithm runs at all.

## Main results

* `WeierstrassCurve.IsTateTerminal.dvd_c₄`: at an additive symbol, `ϖ ∣ c₄`.
* `WeierstrassCurve.IsTateTerminal.dvd_Δ_iff`: the algorithm stops at a symbol other than `I₀`
  exactly when `ϖ ∣ Δ`.
* `WeierstrassCurve.IsTateTerminal.hasGoodReduction_iff`,
  `WeierstrassCurve.IsTateTerminal.hasMultiplicativeReduction_iff` and
  `WeierstrassCurve.IsTateTerminal.hasAdditiveReduction_iff`: the reduction type of a minimal
  equation from the symbol at which the algorithm stops on it.
* `WeierstrassCurve.IsTateTerminal.hasSplitMultiplicativeReduction_iff`: at `Iₙ` with `n ≥ 1`, the
  split test.
* `WeierstrassCurve.IsTateTerminal.localMinimalDiscriminantValuation_eq`: at `Iₙ`, `n` is the
  valuation of the minimal discriminant.
* `WeierstrassCurve.IsTateTerminal.eq_I_iff_of_isMinimal_smul`: two runs of the algorithm on
  minimal equations of the same curve stop at the same `Iₙ`, or both at additive symbols.
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

section CommRing

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {ϖ : R} {s : ReductionSymbol}

/-- At a stopping symbol other than `Iₙ`, the equation is in the additive normal form of Step 2 of
Tate's algorithm: `ϖ` divides `b₂`, `a₃`, `a₄` and `a₆`. -/
theorem IsTateTerminal.dvd_b₂_and_dvd_a₃_and_dvd_a₄_and_dvd_a₆ (h : W.IsTateTerminal ϖ s)
    (hs : ∀ n, s ≠ .I n) : ϖ ∣ W.b₂ ∧ ϖ ∣ W.a₃ ∧ ϖ ∣ W.a₄ ∧ ϖ ∣ W.a₆ := by
  have hb₂ (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ∣ W.a₂) : ϖ ∣ W.b₂ := by
    rw [b₂]
    exact dvd_add (dvd_pow h₁ two_ne_zero) (dvd_mul_of_dvd_right h₂ 4)
  have hp {k : ℕ} {x : R} (hk : k ≠ 0) (hx : ϖ ^ k ∣ x) : ϖ ∣ x := (dvd_pow_self ϖ hk).trans hx
  match s, h with
  | .I n, _ => exact absurd rfl (hs n)
  | .II, h =>
    obtain ⟨hb₂, h₃, h₄, h₆, -⟩ := isTateTerminal_II.1 h
    exact ⟨hb₂, h₃, h₄, h₆⟩
  | .III, h =>
    obtain ⟨hb₂, h₃, h₄, h₆, -⟩ := isTateTerminal_III.1 h
    exact ⟨hb₂, h₃, h₄, hp (by omega) h₆⟩
  | .IV, h =>
    obtain ⟨hb₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IV.1 h
    exact ⟨hb₂, h₃, h₄, hp (by omega) h₆⟩
  | .IStar 0, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IStar_zero.1 h
    exact ⟨hb₂ h₁ h₂, hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩
  | .IStar (_ + 1), h =>
    rcases isTateTerminal_IStar_add_one.1 h with ⟨_, -, hW, -⟩ | ⟨_, -, hW, -⟩
    · obtain ⟨h₁, h₂, -, h₃, h₄, h₆⟩ := isTateOddStage_iff.1 hW
      exact ⟨hb₂ h₁ h₂, hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩
    · obtain ⟨h₁, h₂, -, h₃, h₄, h₆⟩ := isTateEvenStage_iff.1 hW
      exact ⟨hb₂ h₁ h₂, hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩
  | .IVStar, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IVStar.1 h
    exact ⟨hb₂ h₁ (hp (by omega) h₂), hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩
  | .IIIStar, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IIIStar.1 h
    exact ⟨hb₂ h₁ (hp (by omega) h₂), hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩
  | .IIStar, h =>
    obtain ⟨h₁, h₂, h₃, h₄, h₆, -⟩ := isTateTerminal_IIStar.1 h
    exact ⟨hb₂ h₁ (hp (by omega) h₂), hp (by omega) h₃, hp (by omega) h₄, hp (by omega) h₆⟩

/-- **At a stopping symbol other than `Iₙ`, `ϖ` divides `c₄`.** In the additive normal form `ϖ`
divides `b₂` and `b₄`, and `c₄ = b₂² − 24 b₄`. -/
theorem IsTateTerminal.dvd_c₄ (h : W.IsTateTerminal ϖ s) (hs : ∀ n, s ≠ .I n) : ϖ ∣ W.c₄ := by
  obtain ⟨hb₂, h₃, h₄, h₆⟩ := h.dvd_b₂_and_dvd_a₃_and_dvd_a₄_and_dvd_a₆ hs
  have hb₄ := (W.dvd_b₄_and_dvd_b₆_and_sq_dvd_b₈_of_dvd_b₂_of_dvd_a₃_of_dvd_a₄_of_dvd_a₆
    ϖ hb₂ h₃ h₄ h₆).1
  rw [c₄]
  exact dvd_sub (dvd_pow hb₂ two_ne_zero) (dvd_mul_of_dvd_right hb₄ _)

/-- **At a symbol `Iₙ` with `n ≥ 1`, `ϖ` does not divide `c₄`.** The reduction is singular at the
origin, so `ϖ ∣ b₄` and `c₄ ≡ b₂² (mod ϖ)`, while the stopping test asks for `ϖ ∤ b₂`. -/
theorem IsTateTerminal.not_dvd_c₄ (hϖ : Prime ϖ) {n : ℕ} (h : W.IsTateTerminal ϖ (.I (n + 1))) :
    ¬ ϖ ∣ W.c₄ := by
  obtain ⟨h₃, h₄, -, hb₂, -⟩ := isTateTerminal_I_add_one.1 h
  have hb₄ : ϖ ∣ W.b₄ := by
    rw [b₄]
    exact dvd_add (dvd_mul_of_dvd_right h₄ _) (dvd_mul_of_dvd_right h₃ _)
  refine fun hc₄ ↦ hb₂ (hϖ.dvd_of_dvd_pow (n := 2) ?_)
  have hb₂c₄ : W.b₂ ^ 2 = W.c₄ + 24 * W.b₄ := by rw [c₄]; ring
  rw [hb₂c₄]
  exact dvd_add hc₄ (dvd_mul_of_dvd_right hb₄ _)

/-- **Tate's algorithm stops at a symbol other than `I₀` exactly when `ϖ` divides the
discriminant.** -/
theorem IsTateTerminal.dvd_Δ_iff [IsDomain R] (hϖ : Prime ϖ) (h : W.IsTateTerminal ϖ s) :
    ϖ ∣ W.Δ ↔ s ≠ .I 0 := by
  refine ⟨fun hΔ hs ↦ (isTateTerminal_I_zero.1 (hs ▸ h)) hΔ, fun hs ↦ ?_⟩
  by_cases hI : ∃ n, s = .I n
  · obtain ⟨n, rfl⟩ := hI
    cases n with
    | zero => exact absurd rfl hs
    | succ n => exact (dvd_pow_self ϖ n.succ_ne_zero).trans (isTateTerminal_I_add_one.1 h).2.2.2.2.1
  · simp only [not_exists] at hI
    exact (dvd_pow_self ϖ (Nat.succ_ne_zero _)).trans (h.pow_componentCount_add_one_dvd_Δ hϖ hI)

end CommRing

section DiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {W : WeierstrassCurve R} {ϖ : R} {s : ReductionSymbol}

/-- An element of `R` has valuation less than one in `K` exactly when the uniformiser divides it. -/
private theorem valuation_algebraMap_lt_one_iff_dvd (hϖ : Irreducible ϖ) (r : R) :
    valuation K (maximalIdeal R) (algebraMap R K r) < 1 ↔ ϖ ∣ r := by
  rw [valuation_lt_one_iff_mem, ← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
  -- `(maximalIdeal R).asIdeal` is by definition `IsLocalRing.maximalIdeal R`
  rfl

/-- An element of `R` has valuation one in `K` exactly when the uniformiser does not divide it. -/
private theorem valuation_algebraMap_eq_one_iff_not_dvd (hϖ : Irreducible ϖ) (r : R) :
    valuation K (maximalIdeal R) (algebraMap R K r) = 1 ↔ ¬ ϖ ∣ r := by
  rw [← valuation_algebraMap_lt_one_iff_dvd (K := K) hϖ,
    (valuation_le_one (K := K) _ r).lt_iff_ne, not_not]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The integral model of the base change of an equation over `R` is that equation. -/
private theorem integralModel_baseChange_self [IsIntegral R (W.baseChange K)] :
    (W.baseChange K).integralModel R = W :=
  integralModel_eq_of_baseChange_eq rfl

variable [IsMinimal R (W.baseChange K)]

/-- **Tate's algorithm detects good reduction.** On a minimal equation, the algorithm stops at
`I₀` exactly when the reduction is good. -/
theorem IsTateTerminal.hasGoodReduction_iff (hϖ : Irreducible ϖ) (h : W.IsTateTerminal ϖ s) :
    (W.baseChange K).HasGoodReduction R ↔ s = .I 0 := by
  have hΔ : (W.baseChange K).Δ = algebraMap R K W.Δ := map_Δ W _
  rw [WeierstrassCurve.hasGoodReduction_iff, hΔ, valuation_algebraMap_eq_one_iff_not_dvd hϖ,
    h.dvd_Δ_iff hϖ.prime, not_not]
  exact and_iff_right inferInstance

/-- **Tate's algorithm detects multiplicative reduction.** On a minimal equation, the algorithm
stops at some `Iₙ` with `n ≥ 1` exactly when the reduction is multiplicative. -/
theorem IsTateTerminal.hasMultiplicativeReduction_iff (hϖ : Irreducible ϖ)
    (h : W.IsTateTerminal ϖ s) :
    (W.baseChange K).HasMultiplicativeReduction R ↔ ∃ n, s = .I (n + 1) := by
  have hΔ : (W.baseChange K).Δ = algebraMap R K W.Δ := map_Δ W _
  have hc₄ : (W.baseChange K).c₄ = algebraMap R K W.c₄ := map_c₄ W _
  rw [WeierstrassCurve.hasMultiplicativeReduction_iff, hΔ, hc₄,
    valuation_algebraMap_lt_one_iff_dvd hϖ, valuation_algebraMap_eq_one_iff_not_dvd hϖ,
    h.dvd_Δ_iff hϖ.prime]
  constructor
  · rintro ⟨-, hs₀, hc₄⟩
    by_contra hne
    simp only [not_exists] at hne
    refine hc₄ (h.dvd_c₄ fun n hn ↦ ?_)
    cases n with
    | zero => exact hs₀ hn
    | succ n => exact hne n hn
  · rintro ⟨n, rfl⟩
    exact ⟨inferInstance, by simp, h.not_dvd_c₄ hϖ.prime⟩

/-- **Tate's algorithm detects additive reduction.** On a minimal equation, the algorithm stops at
a symbol other than every `Iₙ` exactly when the reduction is additive. -/
theorem IsTateTerminal.hasAdditiveReduction_iff (hϖ : Irreducible ϖ) (h : W.IsTateTerminal ϖ s) :
    (W.baseChange K).HasAdditiveReduction R ↔ ∀ n, s ≠ .I n := by
  have hΔ : (W.baseChange K).Δ = algebraMap R K W.Δ := map_Δ W _
  have hc₄ : (W.baseChange K).c₄ = algebraMap R K W.c₄ := map_c₄ W _
  rw [WeierstrassCurve.hasAdditiveReduction_iff, hΔ, hc₄, valuation_algebraMap_lt_one_iff_dvd hϖ,
    valuation_algebraMap_lt_one_iff_dvd hϖ, h.dvd_Δ_iff hϖ.prime]
  constructor
  · rintro ⟨-, hs₀, hc₄⟩ n rfl
    cases n with
    | zero => exact hs₀ rfl
    | succ n => exact h.not_dvd_c₄ hϖ.prime hc₄
  · exact fun hs ↦ ⟨inferInstance, hs 0, h.dvd_c₄ hs⟩

/-- On a minimal equation, the reduction is good or multiplicative exactly when Tate's algorithm
stops at some `Iₙ`. -/
theorem IsTateTerminal.not_hasAdditiveReduction_iff (hϖ : Irreducible ϖ)
    (h : W.IsTateTerminal ϖ s) :
    ¬ (W.baseChange K).HasAdditiveReduction R ↔ ∃ n, s = .I n := by
  simp only [h.hasAdditiveReduction_iff hϖ, ne_eq, not_forall_not]

/-- **Tate's split test.** On a minimal equation at which the algorithm stops at `Iₙ` with
`n ≥ 1`, the reduction is split multiplicative exactly when the tangent quadratic
`T² + a₁ T − a₂` splits over the residue field. -/
theorem IsTateTerminal.hasSplitMultiplicativeReduction_iff (hϖ : Irreducible ϖ) {n : ℕ}
    (h : W.IsTateTerminal ϖ (.I (n + 1))) :
    (W.baseChange K).HasSplitMultiplicativeReduction R ↔
      (X ^ 2 + C (residue R W.a₁) * X - C (residue R W.a₂)).Splits := by
  have key (x : R) : residue R x = 0 ↔ ϖ ∣ x := by
    rw [residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  have hred : (W.baseChange K).reduction R = W.map (residue R) := by
    rw [reduction, integralModel_baseChange_self]
  obtain ⟨h₃, h₄, h₆, hb₂, -⟩ := isTateTerminal_I_add_one.1 h
  have hsing : ((W.baseChange K).reduction R).toAffine.IsSingular 0 0 := by
    rw [hred, map_residue_isSingular_zero_iff, ← residue_eq_zero_iff, ← residue_eq_zero_iff,
      ← residue_eq_zero_iff, key, key, key]
    exact ⟨h₆, h₄, h₃⟩
  rw [hasSplitMultiplicativeReduction_iff_reduction_b₂_ne_zero_and_splits R hsing, hred, map_b₂,
    map_a₁, map_a₂, Ne, key]
  exact and_iff_right hb₂

/-- **At `Iₙ`, the index is the valuation of the minimal discriminant.** -/
theorem IsTateTerminal.localMinimalDiscriminantValuation_eq [(W.baseChange K).IsElliptic]
    (hϖ : Irreducible ϖ) {n : ℕ} (h : W.IsTateTerminal ϖ (.I n)) :
    (W.baseChange K).localMinimalDiscriminantValuation R = n := by
  have key := (W.baseChange K).localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_smul R 1
    (one_smul _ _)
  rw [integralModel_baseChange_self, h.addVal_Δ_eq hϖ] at key
  exact_mod_cast key

omit [IsMinimal R (W.baseChange K)] in
/-- **Tate's algorithm stops at the same `Iₙ` on every minimal equation of a curve.** If `W₁` and
`W₂` are minimal equations over `R` of the same elliptic curve over `K`, and the algorithm stops on
them, with any uniformisers, at `s₁` and `s₂`, then `s₁ = Iₙ` exactly when `s₂ = Iₙ`. So the two
runs stop at the same `Iₙ`, or both at symbols other than every `Iₙ`. -/
theorem IsTateTerminal.eq_I_iff_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve R}
    [IsMinimal R (W₁.baseChange K)] [IsMinimal R (W₂.baseChange K)] [(W₁.baseChange K).IsElliptic]
    {ϖ₁ ϖ₂ : R} (hϖ₁ : Irreducible ϖ₁) (hϖ₂ : Irreducible ϖ₂) {s₁ s₂ : ReductionSymbol}
    (h₁ : W₁.IsTateTerminal ϖ₁ s₁) (h₂ : W₂.IsTateTerminal ϖ₂ s₂) (D : VariableChange K)
    (hD : D • W₁.baseChange K = W₂.baseChange K) (n : ℕ) : s₁ = .I n ↔ s₂ = .I n := by
  have hadd := hasAdditiveReduction_iff_of_isMinimal_smul R D hD
  -- the minimal discriminant valuation of the curve, read off `W₂`
  have hv : ((W₁.baseChange K).localMinimalDiscriminantValuation R : ℕ∞) = addVal R W₂.Δ := by
    rw [localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_smul R _ D hD,
      integralModel_baseChange_self]
  constructor
  · rintro rfl
    obtain ⟨m, rfl⟩ := (h₂.not_hasAdditiveReduction_iff hϖ₂).1
      (hadd.not.2 ((h₁.not_hasAdditiveReduction_iff hϖ₁).2 ⟨n, rfl⟩))
    rw [h₁.localMinimalDiscriminantValuation_eq hϖ₁, h₂.addVal_Δ_eq hϖ₂] at hv
    exact congrArg ReductionSymbol.I (by exact_mod_cast hv.symm)
  · rintro rfl
    obtain ⟨m, rfl⟩ := (h₁.not_hasAdditiveReduction_iff hϖ₁).1
      (hadd.not.1 ((h₂.not_hasAdditiveReduction_iff hϖ₂).2 ⟨n, rfl⟩))
    rw [h₁.localMinimalDiscriminantValuation_eq hϖ₁, h₂.addVal_Δ_eq hϖ₂] at hv
    exact congrArg ReductionSymbol.I (by exact_mod_cast hv)

end DiscreteValuationRing

/-! ### Semistability over a Dedekind domain -/

section Semistable

variable {O : Type*} [CommRing O] [IsDedekindDomain O]
  {F : Type*} [Field F] [Algebra O F] [IsFractionRing O F] {W : WeierstrassCurve F} [W.IsElliptic]

/-- **On a semistable curve, Tate's algorithm only stops at symbols `Iₙ`.** At a height-one prime
`v`, let `W'` be a minimal equation over the localisation `O_v` of the curve, and suppose Tate's
algorithm, run with a uniformiser `ϖ`, stops on `W'` at `s`. Then `s = Iₙ` for some `n`. -/
theorem IsSemistable.exists_eq_I_of_isTateTerminal (h : IsSemistable O W) (v : HeightOneSpectrum O)
    {W' : WeierstrassCurve (Localization.AtPrime v.asIdeal)}
    [IsMinimal (Localization.AtPrime v.asIdeal) (W'.baseChange F)] (D : VariableChange F)
    (hD : D • W = W'.baseChange F) {ϖ : Localization.AtPrime v.asIdeal} (hϖ : Irreducible ϖ)
    {s : ReductionSymbol} (hs : W'.IsTateTerminal ϖ s) : ∃ n, s = .I n := by
  rw [← hs.not_hasAdditiveReduction_iff (K := F) hϖ]
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal)
  have : (W.minimal (Localization.AtPrime v.asIdeal)).IsElliptic := hC ▸ inferInstance
  have hD' : (D * C⁻¹) • W.minimal (Localization.AtPrime v.asIdeal) = W'.baseChange F := by
    rw [mul_smul, ← hC, inv_smul_smul, hD]
  rw [hasAdditiveReduction_iff_of_isMinimal_smul _ _ hD']
  exact h.not_hasAdditiveReduction v

/-- **Semistability is read off Tate's algorithm.** Over a Dedekind domain whose localisations at
height-one primes have perfect residue fields, an elliptic curve is semistable exactly when, at
every height-one prime `v`, Tate's algorithm run on any minimal equation over `O_v`, with any
uniformiser, stops at some `Iₙ`. -/
theorem isSemistable_iff_forall_isTateTerminal
    [∀ v : HeightOneSpectrum O, PerfectField (ResidueField (Localization.AtPrime v.asIdeal))] :
    IsSemistable O W ↔ ∀ (v : HeightOneSpectrum O)
      (W' : WeierstrassCurve (Localization.AtPrime v.asIdeal)) (D : VariableChange F)
      (ϖ : Localization.AtPrime v.asIdeal) (s : ReductionSymbol),
        IsMinimal (Localization.AtPrime v.asIdeal) (W'.baseChange F) →
          D • W = W'.baseChange F → Irreducible ϖ → W'.IsTateTerminal ϖ s → ∃ n, s = .I n := by
  refine ⟨fun h v W' D ϖ s _ hD hϖ hs ↦ h.exists_eq_I_of_isTateTerminal v D hD hϖ hs,
    fun h ↦ IsSemistable.of_forall_not_hasAdditiveReduction fun v ↦ ?_⟩
  -- Run Tate's algorithm on the integral model of the chosen minimal equation at `v`.
  set Rv := Localization.AtPrime v.asIdeal
  obtain ⟨C₀, hC₀⟩ := W.exists_smul_eq_minimal Rv
  have : (W.minimal Rv).IsElliptic := hC₀ ▸ inferInstance
  set W₀ := (W.minimal Rv).integralModel Rv
  have hW₀ : W₀.baseChange F = W.minimal Rv := baseChange_integralModel_eq Rv _
  have : IsMinimal Rv (W₀.baseChange F) := hW₀ ▸ inferInstance
  have hΔ : W₀.Δ ≠ 0 := fun hΔ ↦ (W.minimal Rv).isUnit_Δ.ne_zero <| by
    rw [← hW₀, baseChange, map_Δ, hΔ, map_zero]
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible Rv
  obtain ⟨C, s, hs⟩ := exists_isTateTerminal (K := F) hϖ W₀ hΔ
  -- The equation it stops on is again minimal, and in the orbit of `W`.
  have hCW₀ : (C • W₀).baseChange F = C.baseChange F • W.minimal Rv := by
    rw [baseChange, ← map_variableChange, ← baseChange, hW₀, VariableChange.baseChange]
  have : IsMinimal Rv ((C • W₀).baseChange F) := hCW₀ ▸ inferInstance
  have hD : (C.baseChange F * C₀) • W = (C • W₀).baseChange F := by
    rw [mul_smul, hC₀, hCW₀]
  obtain ⟨n, rfl⟩ := h v (C • W₀) _ ϖ s inferInstance hD hϖ hs
  have hn := (hs.not_hasAdditiveReduction_iff (K := F) hϖ).2 ⟨n, rfl⟩
  rwa [hasAdditiveReduction_iff_of_isMinimal_smul Rv (C.baseChange F) hCW₀.symm] at hn

end Semistable

end WeierstrassCurve

end
