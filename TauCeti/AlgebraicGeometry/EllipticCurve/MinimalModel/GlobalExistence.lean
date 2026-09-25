/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Class
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.NumberTheory.DedekindDomain.FiniteApproximation

/-!
# Existence of globally minimal Weierstrass equations

Let `O` be a Dedekind domain with fraction field `K`, and `E` an elliptic curve over `K`. The
global-minimality class `globalMinimalityClass O E ∈ ClassGroup O` is the class of the defect ideal
`𝔍_W = ∏ᵥ 𝔭ᵥ ^ fᵥ(W)` of any integral model `W` of `E`. This file proves that it is the complete
obstruction: **`E` has a globally minimal Weierstrass equation over `O` if and only if its
global-minimality class is trivial** (Silverman, *AEC*, Proposition VIII.8.2). In particular every
elliptic curve over the fraction field of a principal ideal domain, such as `ℚ`, has a globally
minimal equation (Corollary VIII.8.3).

## Main results

* `WeierstrassCurve.globalMinimalityClass_eq_one_iff`: `globalMinimalityClass O E = 1` if and only
  if some change of variables makes `E` globally minimal over `O`.
* `WeierstrassCurve.exists_isGlobalMinimal_smul_of_weierstrassDefectIdeal_eq_span`: an integral
  model with a principal defect ideal has a globally minimal model with the prescribed scaling
  factor.
* `WeierstrassCurve.exists_isGlobalMinimal_smul`: over the fraction field of a principal ideal
  domain every elliptic curve has a globally minimal equation.

## The obstruction

A globally minimal equation has trivial defect ideal, so a trivial global-minimality class is
necessary. Conversely, if an integral model `W` has principal defect ideal `(g)`, then some change
of variables with scaling factor `g` carries `W` to a globally minimal equation
(`exists_isGlobalMinimal_smul_of_weierstrassDefectIdeal_eq_span`); this is the patching of local
minimal models in Silverman's proof of VIII.8.2.

The argument uses nothing about `O` beyond finite approximation, so it is stated for an arbitrary
Dedekind domain; the ring of integers of a number field is the case Silverman treats.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1.3 and VIII.8.2–8.3.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-! ### Minimality at one prime -/

/-- The four components of `C * D⁻¹`, the change of variables carrying `D • W` to `C • W`. -/
private theorem mul_inv_components (C D : VariableChange K) :
    ((C * D⁻¹).u : K) = C.u / D.u ∧
      (C * D⁻¹).r = (C.r - D.r) / (D.u : K) ^ 2 ∧
      (C * D⁻¹).s = (C.s - D.s) / (D.u : K) ∧
      (C * D⁻¹).t = (C.t - D.t - D.s * (C.r - D.r)) / (D.u : K) ^ 3 := by
  simp only [VariableChange.mul_def, VariableChange.inv_def, Units.val_mul,
    Units.val_inv_eq_inv_val]
  refine ⟨by ring, by ring, by ring, by ring⟩

variable {O}

/-- **Minimality at `v` from approximation of a local minimalising change of variables.** If `D`
carries `W` to a model minimal at `v`, then so does every `C` whose scaling factor has the same
valuation as `D.u` and whose translation parameters agree with those of `D` to the orders
`v (D.u) ^ 2`, `v (D.u)` and `v (D.u) ^ 3`, the last corrected by `D.s * (C.r - D.r)`: these
make `C * D⁻¹` defined over the localisation at `v`. -/
private theorem isMinimal_smul_of_valuation_sub_le (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) (C D : VariableChange K)
    [IsMinimal (Localization.AtPrime v.asIdeal) (D • W)]
    (hu : v.valuation K C.u = v.valuation K D.u)
    (hr : v.valuation K (C.r - D.r) ≤ v.valuation K D.u ^ 2)
    (hs : v.valuation K (C.s - D.s) ≤ v.valuation K D.u)
    (ht : v.valuation K (C.t - D.t - D.s * (C.r - D.r)) ≤ v.valuation K D.u ^ 3) :
    IsMinimal (Localization.AtPrime v.asIdeal) (C • W) := by
  have hv := v.integers_valuation_localizationAtPrime (K := K)
  have hD : 0 < v.valuation K D.u :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 D.u.ne_zero)
  obtain ⟨hBu, hBr, hBs, hBt⟩ := mul_inv_components C D
  -- The four components of `C * D⁻¹` are integral at `v`, the first a unit.
  obtain ⟨u, hu'⟩ := hv.exists_of_le_one (r := ((C * D⁻¹).u : K)) (by
    rw [hBu, map_div₀, hu, div_self hD.ne'])
  obtain ⟨r, hr'⟩ := hv.exists_of_le_one (r := (C * D⁻¹).r) (by
    rw [hBr, map_div₀, map_pow]; exact (div_le_one₀ (pow_pos hD 2)).2 hr)
  obtain ⟨s, hs'⟩ := hv.exists_of_le_one (r := (C * D⁻¹).s) (by
    rw [hBs, map_div₀]; exact (div_le_one₀ hD).2 hs)
  obtain ⟨t, ht'⟩ := hv.exists_of_le_one (r := (C * D⁻¹).t) (by
    rw [hBt, map_div₀, map_pow]; exact (div_le_one₀ (pow_pos hD 3)).2 ht)
  have hunit : IsUnit u := hv.isUnit_of_one' (by
    rw [hu', hBu, map_div₀, hu, div_self hD.ne'])
  have hB : (⟨hunit.unit, r, s, t⟩ : VariableChange _).baseChange K = C * D⁻¹ :=
    VariableChange.ext (Units.ext hu') hr' hs' ht'
  have hCW : C • W = (C * D⁻¹) • (D • W) := by rw [smul_smul, inv_mul_cancel_right]
  rw [hCW, ← hB]
  exact isMinimal_baseChange_smul _ _ _

/-! ### The local data at every prime -/

variable (O) in
/-- **A local minimalising change of variables of an integral model at `v`.** Its scaling factor
has valuation `exp (-fᵥ(W))`, and its translation parameters are integral at `v`. -/
private theorem exists_isMinimal_smul_valuation (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic] [IsIntegral O W] :
    ∃ D : VariableChange K, IsMinimal (Localization.AtPrime v.asIdeal) (D • W) ∧
      v.valuation K D.u = WithZero.exp (-obstructionExponentAt O v W) ∧
      v.valuation K D.r ≤ 1 ∧ v.valuation K D.s ≤ 1 ∧ v.valuation K D.t ≤ 1 := by
  have hv := v.integers_valuation_localizationAtPrime (K := K)
  have : IsIntegral (Localization.AtPrime v.asIdeal) W := IsIntegral.of_isScalarTower (R := O) W
  obtain ⟨D, hD⟩ := exists_isMinimal (Localization.AtPrime v.asIdeal) W
  -- Comparing obstruction exponents: `fᵥ(D • W) = 0` and `fᵥ(D • W) = fᵥ(W) - ord_v(D.u)`.
  have hord : (v.valuation K).ord (D.u : K) = obstructionExponentAt O v W := by
    have h0 := (obstructionExponentAt_eq_zero_iff_isMinimal O v (D • W)).2 hD
    rw [obstructionExponentAt_smul] at h0
    omega
  have hu : v.valuation K D.u = WithZero.exp (-obstructionExponentAt O v W) := by
    rw [Valuation.valuation_eq_exp_neg_ord _ D.u.ne_zero, hord]
  have hf := obstructionExponentAt_nonneg_of_isIntegral O v W
  obtain ⟨u₀, hu₀⟩ := hv.exists_of_le_one (r := (D.u : K)) (by
    rw [hu, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ :=
    VariableChange.isInteger_r_s_t_of_smul_eq (W₁ := W) _ D rfl u₀ hu₀
  refine ⟨D, hD, hu, ?_, ?_, ?_⟩
  · rw [← hr]; exact hv.map_le_one r
  · rw [← hs]; exact hv.map_le_one s
  · rw [← ht]; exact hv.map_le_one t

/-- A generator of the defect ideal is nonzero. -/
private theorem ne_zero_of_weierstrassDefectIdeal_eq_span (W : WeierstrassCurve K) [W.IsElliptic]
    [IsIntegral O W] {g : O} (hg : weierstrassDefectIdeal O W = Ideal.span {g}) : g ≠ 0 := by
  rintro rfl
  exact weierstrassDefectIdeal_ne_bot O W (by rw [hg]; simp)

/-- The valuation at `v` of a generator of the defect ideal is `exp (-fᵥ(W))`. -/
private theorem valuation_eq_exp_neg_obstructionExponentAt (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic] [IsIntegral O W] {g : O}
    (hg : weierstrassDefectIdeal O W = Ideal.span {g}) :
    v.valuation K (algebraMap O K g) = WithZero.exp (-obstructionExponentAt O v W) := by
  rw [valuation_of_algebraMap,
    v.intValuation_if_neg (ne_zero_of_weierstrassDefectIdeal_eq_span W hg),
    ← count_weierstrassDefectIdeal_eq_obstructionExponentAt O W v, hg]

/-! ### Patching -/

/-- **Approximation to the orders of the obstruction exponents.** Elements `x v` integral at every
height-one prime are approximated by one `a : O` with `v (a - x v) ≤ exp (-fᵥ(W)) ^ m` for every
`v`: finite approximation on the finitely many primes where `fᵥ(W) ≠ 0`, and integrality at the
others, where the bound is `1`. -/
private theorem exists_valuation_sub_le_exp_neg_obstructionExponentAt_pow
    (W : WeierstrassCurve K) [W.IsElliptic] [IsIntegral O W] (m : ℕ)
    (x : HeightOneSpectrum O → K) (hx : ∀ v : HeightOneSpectrum O, v.valuation K (x v) ≤ 1) :
    ∃ a : O, ∀ v : HeightOneSpectrum O, v.valuation K (algebraMap O K a - x v) ≤
      WithZero.exp (-obstructionExponentAt O v W) ^ m := by
  let S := (hasFiniteMulSupport_pow_obstructionExponentAt_toNat O W).toFinset
  have hloc (v : S) : ∃ b : O,
      v.1.valuation K (algebraMap O K b - x v) ≤
        WithZero.exp (-(m * (obstructionExponentAt O v.1 W).toNat : ℤ)) := by
    obtain ⟨b, hb⟩ := v.1.exists_valuation_sub_lt_of_integer (hx v)
      (Units.mk0 (WithZero.exp (-(m * (obstructionExponentAt O v.1 W).toNat : ℤ)))
        WithZero.exp_ne_zero)
    exact ⟨b, hb.le⟩
  choose b hb using hloc
  obtain ⟨a, ha⟩ := TauCeti.DedekindDomain.exists_eq_mod_localized_prime_pow
    (fun v : S ↦ v.1) Subtype.val_injective
    (fun v ↦ m * (obstructionExponentAt O v.1 W).toNat)
    (fun v ↦ Ideal.Quotient.mk _
      (algebraMap O (Localization.AtPrime v.1.asIdeal) (b v)))
  refine ⟨a, fun v ↦ ?_⟩
  have : IsIntegral (Localization.AtPrime v.asIdeal) W := IsIntegral.of_isScalarTower (R := O) W
  rw [← Int.toNat_of_nonneg (obstructionExponentAt_nonneg_of_isIntegral O v W),
    ← WithZero.exp_nsmul, smul_neg, nsmul_eq_mul, ← Nat.cast_mul]
  by_cases hv : v ∈ S
  · have hab : a - b ⟨v, hv⟩ ∈ v.asIdeal ^
        (m * (obstructionExponentAt O v W).toNat) := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      apply (IsLocalization.AtPrime.equivQuotMaximalIdealPow v.asIdeal
        (Localization.AtPrime v.asIdeal) _).injective
      simpa only [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk] using ha ⟨v, hv⟩
    have hab' : v.valuation K (algebraMap O K (a - b ⟨v, hv⟩)) ≤
        WithZero.exp (-(m * (obstructionExponentAt O v W).toNat : ℤ)) := by
      rw [← Nat.cast_mul, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_le_pow_iff_mem]
      exact hab
    rw [map_sub] at hab'
    have hsplit : algebraMap O K a - x v =
        (algebraMap O K a - algebraMap O K (b ⟨v, hv⟩)) +
          (algebraMap O K (b ⟨v, hv⟩) - x v) := by ring
    rw [hsplit]
    exact Valuation.map_add_le _ hab' (hb ⟨v, hv⟩)
  -- Off `S` the obstruction exponent vanishes, and the bound is integrality.
  have hv' : v ∉ Function.mulSupport fun w : HeightOneSpectrum O ↦
      w.asIdeal ^ (obstructionExponentAt O w W).toNat :=
    fun h ↦ hv ((Set.Finite.mem_toFinset _).2 h)
  rw [Function.notMem_mulSupport, Ideal.one_eq_top, Ideal.pow_eq_top_iff] at hv'
  rw [hv'.resolve_left v.isPrime.ne_top, mul_zero, Nat.cast_zero, neg_zero, WithZero.exp_zero]
  exact Valuation.map_sub_le _ (v.valuation_le_one a) (hx v)

/-- **An integral model with principal defect ideal has a globally minimal model** (the patching
step of Silverman VIII.8.2): if `g` generates the defect ideal of the integral model `W`, then some
change of variables with scaling factor `g` carries `W` to an equation minimal at every height-one
prime of `O`. -/
theorem exists_isGlobalMinimal_smul_of_weierstrassDefectIdeal_eq_span
    (W : WeierstrassCurve K) [W.IsElliptic]
    [IsIntegral O W] {g : O} (hg : weierstrassDefectIdeal O W = Ideal.span {g}) :
    ∃ C : VariableChange K, (C.u : K) = algebraMap O K g ∧ IsGlobalMinimal O (C • W) := by
  choose D hDmin hDu hDr hDs hDt using fun v ↦ exists_isMinimal_smul_valuation O v W
  obtain ⟨r, hr⟩ := exists_valuation_sub_le_exp_neg_obstructionExponentAt_pow W 2
    (fun v ↦ (D v).r) hDr
  obtain ⟨s, hs⟩ := exists_valuation_sub_le_exp_neg_obstructionExponentAt_pow W 1
    (fun v ↦ (D v).s) hDs
  -- The target for `t` is corrected by `sᵥ (r - rᵥ)`, now that `r` is fixed.
  obtain ⟨t, ht⟩ := exists_valuation_sub_le_exp_neg_obstructionExponentAt_pow W 3
    (fun v ↦ (D v).t + (D v).s * (algebraMap O K r - (D v).r)) fun v ↦
      Valuation.map_add_le _ (hDt v) (by
        rw [map_mul]
        exact mul_le_one' (hDs v) (Valuation.map_sub_le _ (v.valuation_le_one r) (hDr v)))
  have hg₀ : algebraMap O K g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2
      (ne_zero_of_weierstrassDefectIdeal_eq_span W hg)
  refine ⟨⟨Units.mk0 _ hg₀, algebraMap O K r, algebraMap O K s, algebraMap O K t⟩, rfl,
    IsGlobalMinimal.of_forall_isMinimal fun v ↦ ?_⟩
  have := hDmin v
  refine isMinimal_smul_of_valuation_sub_le v W _ (D v) ?_ ?_ ?_ ?_
  · exact (valuation_eq_exp_neg_obstructionExponentAt v W hg).trans (hDu v).symm
  · rw [hDu]; exact hr v
  · rw [hDu, ← pow_one (WithZero.exp _)]; exact hs v
  · rw [hDu, sub_sub]; exact ht v

/-! ### The global-minimality class is the complete obstruction -/

variable (O)

/-- **The global-minimality class is the obstruction to a globally minimal equation**
(Silverman, *AEC*, Proposition VIII.8.2): an elliptic curve `E` over the fraction field `K` of a
Dedekind domain `O` has a Weierstrass equation minimal at every height-one prime of `O` if and
only if its global-minimality class in `ClassGroup O` is trivial. -/
theorem globalMinimalityClass_eq_one_iff (E : WeierstrassCurve K) [E.IsElliptic] :
    globalMinimalityClass O E = 1 ↔ ∃ C : VariableChange K, IsGlobalMinimal O (C • E) := by
  constructor
  · intro h
    obtain ⟨D, hD⟩ := exists_smul_isIntegral O E
    have hW : (integralModel O (D • E)).baseChange K = D • E := baseChange_integralModel_eq O _
    have : ((integralModel O (D • E)).baseChange K).IsElliptic := by rw [hW]; infer_instance
    let _ : IsIntegral O ((integralModel O (D • E)).baseChange K) := ⟨⟨_, rfl⟩⟩
    rw [globalMinimalityClass_eq_weierstrassDefectClass_of_variableChange O
      (integralModel O (D • E)) E D⁻¹ (by rw [hW, inv_smul_smul]),
      weierstrassDefectClass_def] at h
    have : (weierstrassDefectIdeal O ((integralModel O (D • E)).baseChange K)).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff _).1 h
    obtain ⟨C, -, hC⟩ := exists_isGlobalMinimal_smul_of_weierstrassDefectIdeal_eq_span
      ((integralModel O (D • E)).baseChange K)
      (Ideal.span_singleton_generator
        (weierstrassDefectIdeal O ((integralModel O (D • E)).baseChange K))).symm
    refine ⟨C * D, ?_⟩
    rw [isGlobalMinimal_iff] at hC ⊢
    rwa [mul_smul, ← hW]
  · rintro ⟨C, hC⟩
    have := hC.isIntegral
    have hW : (integralModel O (C • E)).baseChange K = C • E := baseChange_integralModel_eq O _
    have : ((integralModel O (C • E)).baseChange K).IsElliptic := by rw [hW]; infer_instance
    rw [globalMinimalityClass_eq_weierstrassDefectClass_of_variableChange O
      (integralModel O (C • E)) E C⁻¹ (by rw [hW, inv_smul_smul])]
    refine IsGlobalMinimal.weierstrassDefectClass_eq_one O ?_
    rw [isGlobalMinimal_iff] at hC ⊢
    rwa [hW]

/-- **Over the fraction field of a principal ideal domain every elliptic curve has a globally
minimal Weierstrass equation** (Silverman, *AEC*, Corollary VIII.8.3), the class group being
trivial. This applies to `ℚ` over `ℤ`, and to a number field of class number one over its ring of
integers. -/
theorem exists_isGlobalMinimal_smul [IsPrincipalIdealRing O] (E : WeierstrassCurve K)
    [E.IsElliptic] : ∃ C : VariableChange K, IsGlobalMinimal O (C • E) :=
  have : Subsingleton (ClassGroup O) :=
    Fintype.card_le_one_iff_subsingleton.mp card_classGroup_eq_one.le
  (globalMinimalityClass_eq_one_iff O E).1 (Subsingleton.elim _ _)

end WeierstrassCurve

end
