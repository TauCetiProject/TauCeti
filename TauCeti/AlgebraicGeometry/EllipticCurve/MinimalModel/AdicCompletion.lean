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
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Localization

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

/-- **Integrality over the completion agrees with integrality over the localisation**: `W` has
coefficients in `A_(u)` if and only if its base change to `F_u` has coefficients in `O_u`. -/
@[simp]
theorem isIntegral_adicCompletionIntegers_baseChange_iff (W : WeierstrassCurve F) :
    IsIntegral O_u (W.baseChange F_u) ↔ IsIntegral S_u W := by
  constructor
  · intro hI
    refine isIntegral_of_exists_lift S_u
      ((u.exists_algebraMap_adicCompletionIntegers_iff W.a₁).mp
        ⟨(integralModel O_u (W.baseChange F_u)).a₁, integralModel_a₁_eq O_u (W.baseChange F_u)⟩)
      ((u.exists_algebraMap_adicCompletionIntegers_iff W.a₂).mp
        ⟨(integralModel O_u (W.baseChange F_u)).a₂, integralModel_a₂_eq O_u (W.baseChange F_u)⟩)
      ((u.exists_algebraMap_adicCompletionIntegers_iff W.a₃).mp
        ⟨(integralModel O_u (W.baseChange F_u)).a₃, integralModel_a₃_eq O_u (W.baseChange F_u)⟩)
      ((u.exists_algebraMap_adicCompletionIntegers_iff W.a₄).mp
        ⟨(integralModel O_u (W.baseChange F_u)).a₄, integralModel_a₄_eq O_u (W.baseChange F_u)⟩)
      ((u.exists_algebraMap_adicCompletionIntegers_iff W.a₆).mp
        ⟨(integralModel O_u (W.baseChange F_u)).a₆, integralModel_a₆_eq O_u (W.baseChange F_u)⟩)
  · intro hI
    refine isIntegral_of_exists_lift O_u
      ((u.exists_algebraMap_adicCompletionIntegers_iff W.a₁).mpr
        ⟨(integralModel S_u W).a₁, integralModel_a₁_eq S_u W⟩)
      ((u.exists_algebraMap_adicCompletionIntegers_iff W.a₂).mpr
        ⟨(integralModel S_u W).a₂, integralModel_a₂_eq S_u W⟩)
      ((u.exists_algebraMap_adicCompletionIntegers_iff W.a₃).mpr
        ⟨(integralModel S_u W).a₃, integralModel_a₃_eq S_u W⟩)
      ((u.exists_algebraMap_adicCompletionIntegers_iff W.a₄).mpr
        ⟨(integralModel S_u W).a₄, integralModel_a₄_eq S_u W⟩)
      ((u.exists_algebraMap_adicCompletionIntegers_iff W.a₆).mpr
        ⟨(integralModel S_u W).a₆, integralModel_a₆_eq S_u W⟩)

/-- A Weierstrass equation integral at `A_(u)` has base change integral over `O_u`. -/
instance isIntegral_adicCompletionIntegers_of_isIntegral (W : WeierstrassCurve F)
    [IsIntegral S_u W] : IsIntegral O_u (W.baseChange F_u) :=
  (isIntegral_adicCompletionIntegers_baseChange_iff u W).mpr inferInstance

/-- Since `F` is dense in `F_u`, every element of `F_u` can be approximated by an element of `F`
within the valuation of any nonzero `a : F_u`. -/
private theorem exists_valued_algebraMap_sub_lt (x : F_u) {a : F_u} (ha : a ≠ 0) :
    ∃ y : F, Valued.v (algebraMap F F_u y - x) < Valued.v a := by
  have hva : (Valued.v : Valuation F_u _).restrict a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have hx : {z : F_u | (Valued.v : Valuation F_u _).restrict (z - x) <
      (Units.mk0 _ hva).1} ∈ nhds x := Valued.mem_nhds.mpr ⟨Units.mk0 _ hva, fun _ h ↦ h⟩
  obtain ⟨y, hy⟩ := (u.denseRange_algebraMap (K := F)).mem_nhds hx
  exact ⟨y, (Valued.v : Valuation F_u _).restrict_lt_iff.mp hy⟩

/-- Every change of variables `D` over `F_u` is congruent on the left, modulo changes of variables
defined over `O_u`, to the base change of some `C : VariableChange F`. -/
private theorem exists_variableChange_baseChange_mul_inv (D : VariableChange F_u) :
    ∃ (C : VariableChange F) (B : VariableChange O_u),
      B.baseChange F_u = C.baseChange F_u * D⁻¹ := by
  have hDu_ne : Valued.v (D.u : F_u) ≠ 0 := (Valuation.ne_zero_iff _).mpr D.u.ne_zero
  obtain ⟨cu, hcu⟩ := exists_valued_algebraMap_sub_lt u D.u D.u.ne_zero
  have hval_cu : Valued.v (algebraMap F F_u cu) = Valued.v (D.u : F_u) := by
    rw [← sub_add_cancel (algebraMap F F_u cu) D.u, Valuation.map_add_eq_of_lt_right _ hcu]
  have hcu0 : cu ≠ 0 := by rintro rfl; simp [hDu_ne.symm] at hval_cu
  obtain ⟨cr, hcr⟩ := exists_valued_algebraMap_sub_lt u D.r (pow_ne_zero 2 D.u.ne_zero)
  obtain ⟨cs, hcs⟩ := exists_valued_algebraMap_sub_lt u D.s D.u.ne_zero
  obtain ⟨ct, hct⟩ := exists_valued_algebraMap_sub_lt u
    (D.t + D.s * (algebraMap F F_u cr - D.r)) (pow_ne_zero 3 D.u.ne_zero)
  let C : VariableChange F := ⟨Units.mk0 cu hcu0, cr, cs, ct⟩
  refine ⟨C, VariableChange.exists_baseChange_eq_mul_inv_of_valuation_sub_le
    (adicCompletionIntegers.integers F u) (C.baseChange F_u) D ?_ ?_ ?_ ?_⟩
  · simpa only [C, VariableChange.baseChange, VariableChange.map_u, Units.coe_map,
      MonoidHom.coe_ofClass, Units.val_mk0] using hval_cu
  · simpa only [C, VariableChange.baseChange, VariableChange.map_r, map_pow] using hcr.le
  · simpa only [C, VariableChange.baseChange, VariableChange.map_s] using hcs.le
  · simp only [C, VariableChange.baseChange, VariableChange.map_r, VariableChange.map_t]
    rw [show algebraMap F F_u ct - D.t - D.s * (algebraMap F F_u cr - D.r) =
      algebraMap F F_u ct - (D.t + D.s * (algebraMap F F_u cr - D.r)) by ring]
    exact (hct.trans_eq (map_pow _ _ _)).le

/-- **Minimality over the completion agrees with minimality over the localisation**: `W` is minimal
over `A_(u)` if and only if its base change to `F_u` is minimal over `O_u`. -/
@[simp]
theorem isMinimal_adicCompletionIntegers_baseChange_iff (W : WeierstrassCurve F) :
    IsMinimal O_u (W.baseChange F_u) ↔ IsMinimal S_u W := by
  constructor
  · intro hm
    have hIW : IsIntegral S_u W := (isIntegral_adicCompletionIntegers_baseChange_iff u W).mp
      inferInstance
    refine ⟨⟨by simpa only [one_smul] using hIW, fun {C} hC _ ↦ ?_⟩⟩
    dsimp only at hC ⊢
    have hIC : IsIntegral S_u (C • W) := hC
    rw [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral S_u (C • W),
      valuation_Δ_aux_eq_of_isIntegral S_u W, u.valuation_maximalIdeal_localizationAtPrime,
      u.valuation_maximalIdeal_localizationAtPrime, ← u.valued_algebraMap_adicCompletion,
      ← u.valued_algebraMap_adicCompletion]
    have hle := valuation_Δ_le_of_isMinimal_smul O_u (C.baseChange F_u)
      (baseChange_smul_baseChange F_u C W)
    simpa only [u.valuation_maximalIdeal_adicCompletionIntegers, baseChange, map_Δ] using hle
  · intro hm
    have hIW : IsIntegral O_u (W.baseChange F_u) := inferInstance
    refine ⟨⟨by simpa only [one_smul] using hIW, fun {D} hD _ ↦ ?_⟩⟩
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
      u.valued_algebraMap_adicCompletion, ← u.valuation_maximalIdeal_localizationAtPrime]
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
