/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# Minimal Weierstrass equations under adic completion

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `R`.
A Weierstrass equation `W` over `K` may be tested for integrality and minimality either over the
localisation `Localization.AtPrime v.asIdeal` inside `K` or, after base change to the completion
`K_v`, over the completed valuation ring `v.adicCompletionIntegers K` (equivalently over the ring
of integers `𝒪[K_v]` of the valuative relation).

Integrality over the localisation and over the completed valuation ring are equivalent because both
amount to bounding the `v`-adic valuations of the five Weierstrass coefficients by `1`. Minimality
requires more: a minimal model over `Localization.AtPrime v.asIdeal` maximises the discriminant
valuation only over changes of variables defined over `K`, whereas minimality over `K_v` quantifies
over changes of variables with parameters in `K_v`. Because the transformed Weierstrass
coefficients are polynomials in `(u⁻¹, r, s, t)` and `K` is dense in `K_v`, any integral
change of variables over `K_v` can be approximated by a change of variables over `K` whose
transformed equation remains integral at `v` and has the same discriminant valuation. Hence
minimality over `Localization.AtPrime v.asIdeal` and minimality over `K_v` coincide for every
Weierstrass equation, without residue-field or ellipticity hypotheses.

## Main results

* `WeierstrassCurve.isIntegral_adicCompletion_iff` and
  `WeierstrassCurve.isMinimal_adicCompletion_iff`: integrality and minimality over `𝒪[K_v]` agree
  with those over `v.adicCompletionIntegers K`.
* `WeierstrassCurve.isIntegral_localizationAtPrime_iff_adicCompletionIntegers` and
  `WeierstrassCurve.isIntegral_localizationAtPrime_iff_adicCompletion`: integrality at the
  localisation agrees with integrality in the completion.
* `WeierstrassCurve.isMinimal_localizationAtPrime_iff_adicCompletionIntegers` and
  `WeierstrassCurve.isMinimal_localizationAtPrime_iff_adicCompletion`: minimality at the
  localisation agrees with minimality in the completion.
* `WeierstrassCurve.IsGlobalMinimal.isMinimal_adicCompletionIntegers` and
  `WeierstrassCurve.IsGlobalMinimal.isMinimal_adicCompletion`: a globally minimal equation remains
  minimal over every adic completion.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1 and VIII.8.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ValuativeRel
open scoped WithZero

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Integrality over the ring of integers `𝒪[K_v]` of the valuative relation agrees with
integrality over `v.adicCompletionIntegers K`. -/
theorem isIntegral_adicCompletion_iff (v : HeightOneSpectrum R)
    (W' : WeierstrassCurve (v.adicCompletion K)) :
    IsIntegral 𝒪[v.adicCompletion K] W' ↔ IsIntegral (v.adicCompletionIntegers K) W' := by
  suffices ∀ (T : ValuationSubring (v.adicCompletion K)),
      v.adicCompletionIntegers K = T →
        (IsIntegral T W' ↔ IsIntegral (v.adicCompletionIntegers K) W') from
    this (valuation (v.adicCompletion K)).valuationSubring
      (ValuationSubring.toSubring_injective (v.integer_eq_adicCompletionIntegers (K := K)).symm)
  rintro T rfl
  rfl

/-- Minimality over the ring of integers `𝒪[K_v]` of the valuative relation agrees with
minimality over `v.adicCompletionIntegers K`. -/
theorem isMinimal_adicCompletion_iff (v : HeightOneSpectrum R)
    [IsDiscreteValuationRing 𝒪[v.adicCompletion K]]
    (W' : WeierstrassCurve (v.adicCompletion K)) :
    IsMinimal 𝒪[v.adicCompletion K] W' ↔ IsMinimal (v.adicCompletionIntegers K) W' := by
  suffices ∀ (T : ValuationSubring (v.adicCompletion K)) [IsDiscreteValuationRing T],
      v.adicCompletionIntegers K = T →
        (IsMinimal T W' ↔ IsMinimal (v.adicCompletionIntegers K) W') by
    have hR : IsDiscreteValuationRing (valuation (v.adicCompletion K)).valuationSubring :=
      inferInstanceAs (IsDiscreteValuationRing 𝒪[v.adicCompletion K])
    exact this (valuation (v.adicCompletion K)).valuationSubring
      (ValuationSubring.toSubring_injective (v.integer_eq_adicCompletionIntegers (K := K)).symm)
  rintro T instT rfl
  cases Subsingleton.elim instT
    (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers K))
  rfl

/-- An element of `K` comes from the localisation at `v` if and only if its image in `K_v` lies in
`v.adicCompletionIntegers K`. -/
private theorem exists_localizationAtPrime_iff_mem_adicCompletionIntegers
    (v : HeightOneSpectrum R) (x : K) :
    (∃ r : Localization.AtPrime v.asIdeal, algebraMap _ K r = x) ↔
      algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  have hv := v.integers_valuation_of_isLocalizationAtPrime (Localization.AtPrime v.asIdeal) (K := K)
  rw [mem_adicCompletionIntegers, algebraMap_adicCompletion, Function.comp_apply,
    valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]
  exact ⟨fun ⟨r, hr⟩ ↦ hr ▸ hv.map_le_one r, fun hx ↦ hv.exists_of_le_one hx⟩

/-- A Weierstrass equation over `K` is integral over `Localization.AtPrime v.asIdeal` if and only
if its base change to `K_v` is integral over `v.adicCompletionIntegers K`. -/
theorem isIntegral_localizationAtPrime_iff_adicCompletionIntegers
    (v : HeightOneSpectrum R) (W : WeierstrassCurve K) :
    IsIntegral (Localization.AtPrime v.asIdeal) W ↔
      IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) := by
  have lift (x : K) :
      (∃ r : Localization.AtPrime v.asIdeal, algebraMap _ K r = x) ↔
        ∃ r : v.adicCompletionIntegers K,
          algebraMap _ (v.adicCompletion K) r = algebraMap K (v.adicCompletion K) x := by
    rw [exists_localizationAtPrime_iff_mem_adicCompletionIntegers]
    exact ⟨fun hx ↦ ⟨⟨_, hx⟩, rfl⟩, fun ⟨r, hr⟩ ↦ hr ▸ r.2⟩
  refine ⟨fun _ ↦ isIntegral_of_exists_lift _
      ((lift W.a₁).mp ⟨_, integralModel_a₁_eq _ W⟩)
      ((lift W.a₂).mp ⟨_, integralModel_a₂_eq _ W⟩)
      ((lift W.a₃).mp ⟨_, integralModel_a₃_eq _ W⟩)
      ((lift W.a₄).mp ⟨_, integralModel_a₄_eq _ W⟩)
      ((lift W.a₆).mp ⟨_, integralModel_a₆_eq _ W⟩),
    fun _ ↦ isIntegral_of_exists_lift _
      ((lift W.a₁).mpr ⟨_, integralModel_a₁_eq _ (W.baseChange (v.adicCompletion K))⟩)
      ((lift W.a₂).mpr ⟨_, integralModel_a₂_eq _ (W.baseChange (v.adicCompletion K))⟩)
      ((lift W.a₃).mpr ⟨_, integralModel_a₃_eq _ (W.baseChange (v.adicCompletion K))⟩)
      ((lift W.a₄).mpr ⟨_, integralModel_a₄_eq _ (W.baseChange (v.adicCompletion K))⟩)
      ((lift W.a₆).mpr ⟨_, integralModel_a₆_eq _ (W.baseChange (v.adicCompletion K))⟩)⟩

/-- A Weierstrass equation over `K` is integral over `Localization.AtPrime v.asIdeal` if and only
if its base change to `K_v` is integral over `𝒪[K_v]`. -/
theorem isIntegral_localizationAtPrime_iff_adicCompletion
    (v : HeightOneSpectrum R) (W : WeierstrassCurve K) :
    IsIntegral (Localization.AtPrime v.asIdeal) W ↔
      IsIntegral 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)) :=
  (isIntegral_localizationAtPrime_iff_adicCompletionIntegers v W).trans
    (isIntegral_adicCompletion_iff v _).symm

/-- The transformed Weierstrass coefficients of `C • W'` expressed as polynomials in
`(u⁻¹, r, s, t)`. -/
private def invVariableChangeCurve {F : Type*} [CommRing F] (W' : WeierstrassCurve F)
    (p : F × F × F × F) : WeierstrassCurve F :=
  let ⟨w, r, s, t⟩ := p
  { a₁ := w * (W'.a₁ + 2 * s)
    a₂ := w ^ 2 * (W'.a₂ - s * W'.a₁ + 3 * r - s ^ 2)
    a₃ := w ^ 3 * (W'.a₃ + r * W'.a₁ + 2 * t)
    a₄ := w ^ 4 * (W'.a₄ - s * W'.a₃ + 2 * r * W'.a₂ - (t + r * s) * W'.a₁ +
      3 * r ^ 2 - 2 * s * t)
    a₆ := w ^ 6 * (W'.a₆ + r * W'.a₄ + r ^ 2 * W'.a₂ + r ^ 3 - t * W'.a₃ - t ^ 2 -
      r * t * W'.a₁) }

private theorem invVariableChangeCurve_eq_smul {F : Type*} [CommRing F] (W' : WeierstrassCurve F)
    (C : VariableChange F) :
    invVariableChangeCurve W' (↑C.u⁻¹, C.r, C.s, C.t) = C • W' := by
  ext <;> simp [invVariableChangeCurve, variableChange_def]

/-- Any integral transform `C_v • (W.baseChange K_v)` over `K_v` can be approximated by a change of
variables `C` over `K` such that `C • W` is integral at `v` and has the same discriminant
valuation. -/
private theorem exists_variableChange_isIntegral_and_valued_Δ_eq
    (v : HeightOneSpectrum R) (W : WeierstrassCurve K)
    (C_v : VariableChange (v.adicCompletion K))
    [IsIntegral (v.adicCompletionIntegers K) (C_v • W.baseChange (v.adicCompletion K))] :
    ∃ C : VariableChange K, IsIntegral (Localization.AtPrime v.asIdeal) (C • W) ∧
      Valued.v (algebraMap K (v.adicCompletion K) (C • W).Δ) =
        Valued.v (C_v • W.baseChange (v.adicCompletion K)).Δ := by
  let K_v := v.adicCompletion K
  let P := invVariableChangeCurve (W.baseChange K_v)
  let B : Set K_v := ((Valued.v (R := K_v)).integer : Set K_v)
  have hB : IsOpen B := Valued.isOpen_integer K_v
  let w₀ : K_v := ↑C_v.u⁻¹
  have hw₀ : Valued.v.restrict w₀ ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff]
    exact (Valued.v : Valuation K_v ℤᵐ⁰).ne_zero_iff.mpr C_v.u⁻¹.ne_zero
  let U : Set (K_v × K_v × K_v × K_v) :=
    {p | Valued.v.restrict p.1 = Valued.v.restrict w₀} ∩
      ((fun p ↦ (P p).a₁) ⁻¹' B ∩ (fun p ↦ (P p).a₂) ⁻¹' B ∩
        (fun p ↦ (P p).a₃) ⁻¹' B ∩ (fun p ↦ (P p).a₄) ⁻¹' B ∩ (fun p ↦ (P p).a₆) ⁻¹' B)
  have hUopen : IsOpen U := by
    refine ((Valued.isOpen_sphere _ hw₀).preimage continuous_fst).inter ?_
    refine (((((hB.preimage ?_).inter (hB.preimage ?_)).inter (hB.preimage ?_)).inter
      (hB.preimage ?_)).inter (hB.preimage ?_)) <;>
      (dsimp only [P, invVariableChangeCurve]; fun_prop)
  have hP₀ : P (w₀, C_v.r, C_v.s, C_v.t) = C_v • W.baseChange K_v :=
    invVariableChangeCurve_eq_smul _ C_v
  have hp₀ : (w₀, C_v.r, C_v.s, C_v.t) ∈ U := by
    refine ⟨rfl, ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩⟩ <;>
    · simp only [Set.mem_preimage, hP₀, ← integralModel_a₁_eq (v.adicCompletionIntegers K),
        ← integralModel_a₂_eq (v.adicCompletionIntegers K),
        ← integralModel_a₃_eq (v.adicCompletionIntegers K),
        ← integralModel_a₄_eq (v.adicCompletionIntegers K),
        ← integralModel_a₆_eq (v.adicCompletionIntegers K)]
      exact Subtype.prop _
  have hd : DenseRange (fun q : K × K × K × K ↦
      (algebraMap K K_v q.1, algebraMap K K_v q.2.1,
        algebraMap K K_v q.2.2.1, algebraMap K K_v q.2.2.2)) :=
    (v.denseRange_algebraMap K).prodMap <| (v.denseRange_algebraMap K).prodMap <|
      (v.denseRange_algebraMap K).prodMap (v.denseRange_algebraMap K)
  obtain ⟨⟨w, r, s, t⟩, hw, ⟨⟨⟨⟨ha₁, ha₂⟩, ha₃⟩, ha₄⟩, ha₆⟩⟩ := hd.exists_mem_open hUopen ⟨_, hp₀⟩
  have hvalw : Valued.v (algebraMap K K_v w) = Valued.v w₀ := Valued.v.restrict_inj.mp hw
  have hw0 : w ≠ 0 := fun h0 ↦ hw₀ <| by rw [← hw, h0, map_zero, map_zero]
  let C : VariableChange K := ⟨(Units.mk0 w hw0)⁻¹, r, s, t⟩
  have hCW : (C • W).baseChange K_v =
      P (algebraMap K K_v w, algebraMap K K_v r, algebraMap K K_v s, algebraMap K K_v t) := by
    rw [← baseChange_smul_baseChange (L := K_v) C W, ← invVariableChangeCurve_eq_smul]
    dsimp only [C, P, VariableChange.baseChange, VariableChange.map]
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, map_inv, inv_inv]
  have hInt_v : IsIntegral (v.adicCompletionIntegers K) ((C • W).baseChange K_v) := by
    rw [hCW]
    exact isIntegral_of_exists_lift _
      ⟨⟨_, ha₁⟩, rfl⟩ ⟨⟨_, ha₂⟩, rfl⟩ ⟨⟨_, ha₃⟩, rfl⟩ ⟨⟨_, ha₄⟩, rfl⟩ ⟨⟨_, ha₆⟩, rfl⟩
  refine ⟨C, (isIntegral_localizationAtPrime_iff_adicCompletionIntegers v (C • W)).mpr hInt_v, ?_⟩
  dsimp only [C, K_v, w₀] at hvalw ⊢
  simp [variableChange_Δ, baseChange, Units.val_inv_eq_inv_val, inv_pow, hvalw]

/-- **Minimality at the localisation agrees with minimality in the completion.** A Weierstrass
equation over `K` is minimal over `Localization.AtPrime v.asIdeal` if and only if its base change
to `K_v` is minimal over `v.adicCompletionIntegers K`. -/
theorem isMinimal_localizationAtPrime_iff_adicCompletionIntegers
    (v : HeightOneSpectrum R) (W : WeierstrassCurve K) :
    IsMinimal (Localization.AtPrime v.asIdeal) W ↔
      IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) := by
  have hΔ (W' : WeierstrassCurve K) :
      (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).valuation
          (v.adicCompletion K) (W'.baseChange (v.adicCompletion K)).Δ =
        (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation
          K W'.Δ := by
    rw [valuation_maximalIdeal_adicCompletionIntegers, baseChange, map_Δ,
      algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self_apply, v.valuation_maximalIdeal_localizationAtPrime]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : IsIntegral (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
      (isIntegral_localizationAtPrime_iff_adicCompletionIntegers v W).mp inferInstance
    refine ⟨⟨by simpa using this, fun {C_v} hC_v _ ↦ ?_⟩⟩
    dsimp only at hC_v ⊢
    have : IsIntegral (v.adicCompletionIntegers K) (C_v • W.baseChange (v.adicCompletion K)) := hC_v
    obtain ⟨C, hC, hval⟩ := exists_variableChange_isIntegral_and_valued_Δ_eq v W C_v
    rw [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral _ (C_v • _),
      valuation_Δ_aux_eq_of_isIntegral _ (W.baseChange (v.adicCompletion K)), hΔ W,
      valuation_maximalIdeal_adicCompletionIntegers, ← hval,
      ← valuation_maximalIdeal_adicCompletionIntegers,
      show algebraMap K (v.adicCompletion K) (C • W).Δ =
        ((C • W).baseChange (v.adicCompletion K)).Δ by simp [baseChange], hΔ (C • W)]
    exact valuation_Δ_le_of_isMinimal_smul (Localization.AtPrime v.asIdeal) C rfl
  · have : IsIntegral (Localization.AtPrime v.asIdeal) W :=
      (isIntegral_localizationAtPrime_iff_adicCompletionIntegers v W).mpr inferInstance
    refine ⟨⟨by simpa using this, fun {C} hC _ ↦ ?_⟩⟩
    dsimp only at hC ⊢
    have : IsIntegral (Localization.AtPrime v.asIdeal) (C • W) := hC
    have hsmul : C.baseChange (v.adicCompletion K) • W.baseChange (v.adicCompletion K) =
        (C • W).baseChange (v.adicCompletion K) :=
      baseChange_smul_baseChange (L := v.adicCompletion K) C W
    have : IsIntegral (v.adicCompletionIntegers K)
        (C.baseChange (v.adicCompletion K) • W.baseChange (v.adicCompletion K)) := by
      rw [hsmul]
      exact (isIntegral_localizationAtPrime_iff_adicCompletionIntegers v (C • W)).mp inferInstance
    rw [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral _ (C • W),
      valuation_Δ_aux_eq_of_isIntegral _ W, ← hΔ (C • W), ← hΔ W, ← hsmul]
    exact valuation_Δ_le_of_isMinimal_smul (v.adicCompletionIntegers K)
      (C.baseChange (v.adicCompletion K)) rfl

/-- A Weierstrass equation over `K` is minimal over `Localization.AtPrime v.asIdeal` if and only
if its base change to `K_v` is minimal over `𝒪[K_v]`. -/
theorem isMinimal_localizationAtPrime_iff_adicCompletion
    (v : HeightOneSpectrum R) [IsDiscreteValuationRing 𝒪[v.adicCompletion K]]
    (W : WeierstrassCurve K) :
    IsMinimal (Localization.AtPrime v.asIdeal) W ↔
      IsMinimal 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_localizationAtPrime_iff_adicCompletionIntegers v W).trans
    (isMinimal_adicCompletion_iff v _).symm

/-- A globally minimal equation over `R` remains minimal over `v.adicCompletionIntegers K` at
every height-one prime `v`. -/
theorem IsGlobalMinimal.isMinimal_adicCompletionIntegers {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal R W) (v : HeightOneSpectrum R) :
    IsMinimal (v.adicCompletionIntegers K) (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_localizationAtPrime_iff_adicCompletionIntegers v W).mp (h.isMinimal v)

/-- A globally minimal equation over `R` remains minimal over `𝒪[K_v]` at every height-one prime
`v`. -/
theorem IsGlobalMinimal.isMinimal_adicCompletion {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal R W) (v : HeightOneSpectrum R)
    [IsDiscreteValuationRing 𝒪[v.adicCompletion K]] :
    IsMinimal 𝒪[v.adicCompletion K] (W.baseChange (v.adicCompletion K)) :=
  (isMinimal_localizationAtPrime_iff_adicCompletion v W).mp (h.isMinimal v)

end WeierstrassCurve

end
