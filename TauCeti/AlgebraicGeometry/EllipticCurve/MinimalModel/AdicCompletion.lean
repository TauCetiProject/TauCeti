/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# Minimal Weierstrass equations over an adic completion

Let `A` be a Dedekind domain with fraction field `F`, and let `u` be a height-one prime of `A`.
A Weierstrass equation `W` over `F` can be tested for integrality and minimality either at the
localisation `A_(u) = Localization.AtPrime u.asIdeal` inside `F` or, after base change to the
completion `F_u = u.adicCompletion F`, over the completed valuation ring
`O_u = u.adicCompletionIntegers F`. This file proves that the two notions coincide, without
ellipticity or residue-field hypotheses.

Integrality agrees because `F ↪ F_u` is valuation-preserving, so an element of `F` lies in `A_(u)`
if and only if its image in `F_u` lies in `O_u`. Minimality over `O_u` implies minimality over
`A_(u)` immediately, since every change of variables over `F` base changes to `F_u`. For the
converse, `F` is dense in `F_u`: any change of variables `D` over `F_u` carrying `W` to an
equation over `O_u` can be approximated by a change of variables `C` over `F` so closely that
`C.baseChange F_u * D⁻¹` is defined over `O_u` with a unit scaling factor. Then `(C • W)` is
integral over `A_(u)` and has the same discriminant valuation as `D • W.baseChange F_u`, bounding
the latter by the discriminant valuation of `W`.

## Main results

* `WeierstrassCurve.isIntegral_adicCompletionIntegers_baseChange_iff`: `W.baseChange F_u` is
  integral over `O_u` if and only if `W` is integral over `A_(u)`.
* `WeierstrassCurve.isMinimal_adicCompletionIntegers_baseChange_iff`: `W.baseChange F_u` is
  minimal over `O_u` if and only if `W` is minimal over `A_(u)`.
* `WeierstrassCurve.isMinimal_adicCompletionIntegers_of_isMinimal`: instance carrying minimality
  from `A_(u)` to `O_u`.
* `WeierstrassCurve.IsGlobalMinimal.isMinimal_adicCompletionIntegers` and
  `WeierstrassCurve.isGlobalMinimal_iff_forall_isMinimal_adicCompletionIntegers`: global minimality
  over `A` read on the completions.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1 and VIII.8.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

namespace WeierstrassCurve

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)

local notation "S_u" => Localization.AtPrime u.asIdeal
local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F

/-- The completion map `F → F_u` preserves the `u`-adic valuation. -/
private theorem valued_algebraMap_eq_valuation (x : F) :
    Valued.v (algebraMap F F_u x) = u.valuation F x := by
  rw [u.algebraMap_adicCompletion (K := F), Function.comp_apply,
    u.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]

/-- An element of `F` lifts to `O_u` in `F_u` if and only if it lifts to `A_(u)` in `F`. -/
private theorem exists_algebraMap_adicCompletionIntegers_iff (x : F) :
    (∃ r : O_u, algebraMap O_u F_u r = algebraMap F F_u x) ↔
      ∃ r : S_u, algebraMap S_u F r = x := by
  have hvLoc := u.integers_valuation_of_isLocalizationAtPrime S_u (K := F)
  have hvComp : (Valued.v : Valuation F_u _).Integers O_u := adicCompletionIntegers.integers F u
  have hComp : (∃ r : O_u, algebraMap O_u F_u r = algebraMap F F_u x) ↔
      Valued.v (algebraMap F F_u x) ≤ 1 :=
    ⟨fun ⟨r, hr⟩ ↦ hr ▸ hvComp.map_le_one r, fun h ↦ hvComp.exists_of_le_one h⟩
  have hLoc : (∃ r : S_u, algebraMap S_u F r = x) ↔ u.valuation F x ≤ 1 :=
    ⟨fun ⟨r, hr⟩ ↦ hr ▸ hvLoc.map_le_one r, fun h ↦ hvLoc.exists_of_le_one h⟩
  rw [hComp, hLoc, valued_algebraMap_eq_valuation]

/-- **Integrality over the completion agrees with integrality over the localisation**: `W` has
coefficients in `A_(u)` if and only if its base change to `F_u` has coefficients in `O_u`. -/
@[simp]
theorem isIntegral_adicCompletionIntegers_baseChange_iff (W : WeierstrassCurve F) :
    IsIntegral O_u (W.baseChange F_u) ↔ IsIntegral S_u W := by
  constructor
  · intro hI
    refine isIntegral_of_exists_lift S_u
      ((exists_algebraMap_adicCompletionIntegers_iff u W.a₁).mp
        ⟨(integralModel O_u (W.baseChange F_u)).a₁, integralModel_a₁_eq O_u (W.baseChange F_u)⟩)
      ((exists_algebraMap_adicCompletionIntegers_iff u W.a₂).mp
        ⟨(integralModel O_u (W.baseChange F_u)).a₂, integralModel_a₂_eq O_u (W.baseChange F_u)⟩)
      ((exists_algebraMap_adicCompletionIntegers_iff u W.a₃).mp
        ⟨(integralModel O_u (W.baseChange F_u)).a₃, integralModel_a₃_eq O_u (W.baseChange F_u)⟩)
      ((exists_algebraMap_adicCompletionIntegers_iff u W.a₄).mp
        ⟨(integralModel O_u (W.baseChange F_u)).a₄, integralModel_a₄_eq O_u (W.baseChange F_u)⟩)
      ((exists_algebraMap_adicCompletionIntegers_iff u W.a₆).mp
        ⟨(integralModel O_u (W.baseChange F_u)).a₆, integralModel_a₆_eq O_u (W.baseChange F_u)⟩)
  · intro hI
    refine isIntegral_of_exists_lift O_u
      ((exists_algebraMap_adicCompletionIntegers_iff u W.a₁).mpr
        ⟨(integralModel S_u W).a₁, integralModel_a₁_eq S_u W⟩)
      ((exists_algebraMap_adicCompletionIntegers_iff u W.a₂).mpr
        ⟨(integralModel S_u W).a₂, integralModel_a₂_eq S_u W⟩)
      ((exists_algebraMap_adicCompletionIntegers_iff u W.a₃).mpr
        ⟨(integralModel S_u W).a₃, integralModel_a₃_eq S_u W⟩)
      ((exists_algebraMap_adicCompletionIntegers_iff u W.a₄).mpr
        ⟨(integralModel S_u W).a₄, integralModel_a₄_eq S_u W⟩)
      ((exists_algebraMap_adicCompletionIntegers_iff u W.a₆).mpr
        ⟨(integralModel S_u W).a₆, integralModel_a₆_eq S_u W⟩)

/-- A Weierstrass equation integral at `A_(u)` has base change integral over `O_u`. -/
instance isIntegral_adicCompletionIntegers_of_isIntegral (W : WeierstrassCurve F)
    [IsIntegral S_u W] : IsIntegral O_u (W.baseChange F_u) :=
  (isIntegral_adicCompletionIntegers_baseChange_iff u W).mpr inferInstance

/-- Every change of variables `D` over `F_u` is congruent on the left, modulo changes of variables
defined over `O_u`, to the base change of some `C : VariableChange F`. -/
private theorem exists_variableChange_baseChange_mul_inv (D : VariableChange F_u) :
    ∃ (C : VariableChange F) (B : VariableChange O_u),
      B.baseChange F_u = C.baseChange F_u * D⁻¹ := by
  have hdense : DenseRange (algebraMap F F_u) := u.denseRange_algebraMap (K := F)
  have approx (x : F_u) {a : F_u} (ha : a ≠ 0) :
      ∃ y : F, Valued.v (algebraMap F F_u y - x) < Valued.v a := by
    have hva : (Valued.v : Valuation F_u _).restrict a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
    have hx : {z : F_u | (Valued.v : Valuation F_u _).restrict (z - x) <
        (Units.mk0 _ hva).1} ∈ nhds x := Valued.mem_nhds.mpr ⟨Units.mk0 _ hva, fun _ h ↦ h⟩
    obtain ⟨y, hy⟩ := hdense.mem_nhds hx
    exact ⟨y, (Valued.v : Valuation F_u _).restrict_lt_iff.mp hy⟩
  have hDu_ne : Valued.v (D.u : F_u) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr D.u.ne_zero
  have hDu_pos : 0 < Valued.v (D.u : F_u) := zero_lt_iff.mpr hDu_ne
  obtain ⟨cu, hcu⟩ := approx D.u D.u.ne_zero
  have hval_cu : Valued.v (algebraMap F F_u cu) = Valued.v (D.u : F_u) := by
    have hadd : algebraMap F F_u cu = (algebraMap F F_u cu - D.u) + D.u := (sub_add_cancel _ _).symm
    rw [hadd, Valuation.map_add_eq_of_lt_right _ hcu]
  have hcu0 : cu ≠ 0 := by
    rintro rfl
    simp [hDu_ne.symm] at hval_cu
  obtain ⟨cr, hcr⟩ := approx D.r (pow_ne_zero 2 D.u.ne_zero)
  obtain ⟨cs, hcs⟩ := approx D.s D.u.ne_zero
  obtain ⟨ct, hct⟩ := approx (D.t + D.s * (algebraMap F F_u cr - D.r)) (pow_ne_zero 3 D.u.ne_zero)
  let C : VariableChange F := ⟨Units.mk0 cu hcu0, cr, cs, ct⟩
  let M : VariableChange F_u := C.baseChange F_u * D⁻¹
  have hvComp : (Valued.v : Valuation F_u _).Integers O_u := adicCompletionIntegers.integers F u
  have hMu : Valued.v (M.u : F_u) = 1 := by
    change Valued.v ((C.baseChange F_u * D⁻¹).u : F_u) = 1
    rw [VariableChange.mul_inv_u, Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv,
      map_div₀]
    change Valued.v (algebraMap F F_u cu) / Valued.v (D.u : F_u) = 1
    rw [hval_cu, div_self hDu_ne]
  have hMr : Valued.v M.r ≤ 1 := by
    change Valued.v (C.baseChange F_u * D⁻¹).r ≤ 1
    rw [VariableChange.mul_inv_r, Units.val_inv_eq_inv_val, inv_pow, ← div_eq_mul_inv, map_div₀,
      map_pow, div_le_one₀ (pow_pos hDu_pos 2)]
    change Valued.v (algebraMap F F_u cr - D.r) ≤ Valued.v (D.u : F_u) ^ 2
    exact (hcr.trans_eq (map_pow _ _ _)).le
  have hMs : Valued.v M.s ≤ 1 := by
    change Valued.v (C.baseChange F_u * D⁻¹).s ≤ 1
    rw [VariableChange.mul_inv_s, Units.val_inv_eq_inv_val, ← div_eq_mul_inv, map_div₀,
      div_le_one₀ hDu_pos]
    exact hcs.le
  have hMt : Valued.v M.t ≤ 1 := by
    change Valued.v (C.baseChange F_u * D⁻¹).t ≤ 1
    rw [VariableChange.mul_inv_t, Units.val_inv_eq_inv_val, inv_pow, ← div_eq_mul_inv, map_div₀,
      map_pow, div_le_one₀ (pow_pos hDu_pos 3)]
    have hsub : (C.baseChange F_u).t - D.t - D.s * ((C.baseChange F_u).r - D.r) =
        algebraMap F F_u ct - (D.t + D.s * (algebraMap F F_u cr - D.r)) := by
      change algebraMap F F_u ct - D.t - D.s * (algebraMap F F_u cr - D.r) = _
      ring
    rw [hsub]
    exact (hct.trans_eq (map_pow _ _ _)).le
  obtain ⟨bu, hbu⟩ := hvComp.exists_of_le_one hMu.le
  obtain ⟨br, hbr⟩ := hvComp.exists_of_le_one hMr
  obtain ⟨bs, hbs⟩ := hvComp.exists_of_le_one hMs
  obtain ⟨bt, hbt⟩ := hvComp.exists_of_le_one hMt
  have hunit : IsUnit bu := hvComp.isUnit_of_one' (by rwa [hbu])
  exact ⟨C, ⟨hunit.unit, br, bs, bt⟩, VariableChange.ext (Units.ext hbu) hbr hbs hbt⟩

/-- **Minimality over the completion agrees with minimality over the localisation**: `W` is minimal
over `A_(u)` if and only if its base change to `F_u` is minimal over `O_u`. -/
@[simp]
theorem isMinimal_adicCompletionIntegers_baseChange_iff (W : WeierstrassCurve F) :
    IsMinimal O_u (W.baseChange F_u) ↔ IsMinimal S_u W := by
  constructor
  · intro hm
    have hIW : IsIntegral S_u W := (isIntegral_adicCompletionIntegers_baseChange_iff u W).mp
      inferInstance
    refine ⟨⟨by change IsIntegral S_u (1 • W); rwa [one_smul], fun {C} hC _ ↦ ?_⟩⟩
    dsimp only at hC ⊢
    have hIC : IsIntegral S_u (C • W) := hC
    rw [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral S_u (C • W),
      valuation_Δ_aux_eq_of_isIntegral S_u W, u.valuation_maximalIdeal_localizationAtPrime,
      u.valuation_maximalIdeal_localizationAtPrime, ← valued_algebraMap_eq_valuation u,
      ← valued_algebraMap_eq_valuation u]
    have hle := valuation_Δ_le_of_isMinimal_smul O_u (C.baseChange F_u)
      (baseChange_smul_baseChange F_u C W)
    simpa only [u.valuation_maximalIdeal_adicCompletionIntegers, baseChange, map_Δ] using hle
  · intro hm
    have hIW : IsIntegral O_u (W.baseChange F_u) := inferInstance
    refine ⟨⟨by change IsIntegral O_u (1 • W.baseChange F_u); rwa [one_smul], fun {D} hD _ ↦ ?_⟩⟩
    dsimp only at hD ⊢
    have hID : IsIntegral O_u (D • W.baseChange F_u) := hD
    rw [one_smul, ← Subtype.coe_le_coe,
      valuation_Δ_aux_eq_of_isIntegral O_u (D • W.baseChange F_u),
      valuation_Δ_aux_eq_of_isIntegral O_u (W.baseChange F_u)]
    obtain ⟨C, B, hB⟩ := exists_variableChange_baseChange_mul_inv u D
    have hCW : (C • W).baseChange F_u = B.baseChange F_u • (D • W.baseChange F_u) := by
      rw [← baseChange_smul_baseChange, hB, mul_smul, inv_smul_smul]
    have hIC_comp : IsIntegral O_u ((C • W).baseChange F_u) := by
      rw [hCW]
      infer_instance
    have hIC : IsIntegral S_u (C • W) :=
      (isIntegral_adicCompletionIntegers_baseChange_iff u (C • W)).mp hIC_comp
    have hvalB : valuation F_u (maximalIdeal O_u) ((C • W).baseChange F_u).Δ =
        valuation F_u (maximalIdeal O_u) (D • W.baseChange F_u).Δ := by
      rw [hCW, valuation_Δ_baseChange_smul]
    rw [← hvalB]
    simp only [u.valuation_maximalIdeal_adicCompletionIntegers, baseChange, map_Δ,
      valued_algebraMap_eq_valuation, ← u.valuation_maximalIdeal_localizationAtPrime]
    exact valuation_Δ_le_of_isMinimal_smul S_u C rfl

/-- A Weierstrass equation minimal at `A_(u)` has base change minimal over `O_u`. -/
instance isMinimal_adicCompletionIntegers_of_isMinimal (W : WeierstrassCurve F)
    [IsMinimal S_u W] : IsMinimal O_u (W.baseChange F_u) :=
  (isMinimal_adicCompletionIntegers_baseChange_iff u W).mpr inferInstance

variable {u} in
/-- A globally minimal equation over `A` is minimal over the completed valuation ring `O_u` at
every height-one prime `u`. -/
theorem IsGlobalMinimal.isMinimal_adicCompletionIntegers {W : WeierstrassCurve F} [W.IsElliptic]
    (h : IsGlobalMinimal A W) (u : HeightOneSpectrum A) :
    IsMinimal (u.adicCompletionIntegers F) (W.baseChange (u.adicCompletion F)) := by
  have := h.isMinimal u
  infer_instance

/-- Global minimality over `A` is equivalent to minimality over every completed valuation ring
`O_u`. -/
theorem isGlobalMinimal_iff_forall_isMinimal_adicCompletionIntegers
    (W : WeierstrassCurve F) [W.IsElliptic] :
    IsGlobalMinimal A W ↔
      ∀ u : HeightOneSpectrum A,
        IsMinimal (u.adicCompletionIntegers F) (W.baseChange (u.adicCompletion F)) := by
  simp only [isGlobalMinimal_iff, isMinimal_adicCompletionIntegers_baseChange_iff]

end WeierstrassCurve

end
