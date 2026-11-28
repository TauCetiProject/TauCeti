/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic
public import Mathlib.Topology.LocallyConstant.Algebra

import TauCeti.NumberTheory.Padics.QuotientTower

/-!
# Locally constant functions as locally analytic functions

Every locally constant function on `ℤ_p` factors through a finite congruence quotient and is
represented by a degree-zero analytic stage (`exists_eval_ofStage_polynomial_zero`). With
p-regular coefficients, evaluation is injective, so this gives the linear inclusion
`ofLocallyConstant` with evaluation rule `eval_ofLocallyConstant`.
-/

public section

namespace TauCeti.LocallyAnalytic

variable {p : ℕ} [Fact p.Prime] {E : Type*} [NormedAddCommGroup E]
  [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]
  [SMulCommClass ℤ_[p] S E]

/-- Every locally constant function is evaluated from a degree-zero analytic stage. -/
theorem exists_eval_ofStage_polynomial_zero (f : LocallyConstant ℤ_[p] E) :
    ∃ h, ∃ c : AnalyticStage.polynomialSubmodule (p := p) (h := h) (E := E) S 0,
      eval S (ofStage S h c.val) = f.toContinuousMap := by
  obtain ⟨h, g, hg⟩ := (FiniteQuotientTower.padicTower p).exists_comp_q_eq
    (f.isLocallyConstant.comp_continuous continuous_toAdd)
  let e := AnalyticStage.polynomialEquiv (p := p) (h := h) (E := E) S 0
  let v : ZMod (p ^ h) × Fin 1 → E := fun i ↦ g (Multiplicative.ofAdd i.1)
  let c := e.symm v
  refine ⟨h, c, ?_⟩
  ext x
  rw [eval_ofStage, AnalyticStage.eval_polynomial_zero]
  calc
    _ = e c (PadicInt.toZModPow h x, 0) :=
      (AnalyticStage.polynomialEquiv_apply (p := p) (h := h) S c
        (PadicInt.toZModPow h x, 0)).symm
    _ = g (Multiplicative.ofAdd (PadicInt.toZModPow h x)) := congrFun (e.apply_symm_apply v) _
    _ = _ := by
      simpa only [Function.comp_apply, FiniteQuotientTower.padicTower_q_ofAdd, toAdd_ofAdd,
        LocallyConstant.toFun_eq_coe, LocallyConstant.coe_continuousMap]
        using congrFun hg (Multiplicative.ofAdd x)

/-- With p-regular coefficients, a locally analytic function whose evaluation is locally
constant has a degree-zero stage representative. -/
theorem exists_ofStage_polynomial_zero_of_isLocallyConstant (hpE : IsSMulRegular E (p : ℤ_[p]))
    {f : LocallyAnalytic p S E} (hf : IsLocallyConstant (eval S f)) :
    ∃ h, ∃ c : AnalyticStage.polynomialSubmodule (p := p) (h := h) (E := E) S 0,
      ofStage S h c.val = f := by
  obtain ⟨h, c, hc⟩ := exists_eval_ofStage_polynomial_zero S ⟨eval S f, hf⟩
  exact ⟨h, c, eval_injective S hpE hc⟩

/-- The linear inclusion of locally constant functions into locally analytic functions, for
p-regular coefficients. -/
noncomputable def ofLocallyConstant (hpE : IsSMulRegular E (p : ℤ_[p])) :
    LocallyConstant ℤ_[p] E →ₗ[S] LocallyAnalytic p S E :=
  let e := LinearEquiv.ofInjective (eval S) (eval_injective S hpE)
  let L : LocallyConstant ℤ_[p] E →ₗ[S] (eval (p := p) (E := E) S).range :=
    { toFun f := ⟨f.toContinuousMap, by
        obtain ⟨h, c, hc⟩ := exists_eval_ofStage_polynomial_zero S f
        exact ⟨ofStage S h c.val, hc⟩⟩
      map_add' f g := by ext; rfl
      map_smul' a f := by ext; rfl }
  e.symm.toLinearMap.comp L

/-- The locally analytic inclusion evaluates to the original locally constant function. -/
@[simp]
theorem eval_ofLocallyConstant (hpE : IsSMulRegular E (p : ℤ_[p]))
    (f : LocallyConstant ℤ_[p] E) :
    eval S (ofLocallyConstant S hpE f) = f.toContinuousMap := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective (eval S) (eval_injective S hpE)).apply_symm_apply _)

/-- The linear inclusion of locally constant functions is injective. -/
theorem ofLocallyConstant_injective (hpE : IsSMulRegular E (p : ℤ_[p])) :
    Function.Injective (ofLocallyConstant (p := p) (E := E) S hpE) := by
  intro f g hfg
  apply LocallyConstant.toContinuousMap_injective
  simpa using congrArg (eval S) hfg

end TauCeti.LocallyAnalytic
