/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import Mathlib.Tactic.NormNum

/-!
# A trivial zero absent from the Dirichlet completion

The native quadratic character modulo five is even. At zero its ordinary L-function vanishes,
whereas its entire completion does not. Thus the positive-real-part hypothesis in the comparison
of ordinary and completed zero multiplicities cannot be extended to include the origin.
-/

public section

open Complex DirichletCharacter

namespace TauCeti.LFunctions

/-- The quadratic character modulo five witnesses the origin boundary of the order comparison. -/
example :
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let χ : DirichletCharacter ℂ 5 :=
      (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)
    ∃ hχ : χ.IsPrimitive, χ.Even ∧ χ ≠ 1 ∧ χ.LFunction 0 = 0 ∧
      (dirichletData χ hχ).entireCompletion 0 ≠ 0 ∧
      analyticOrderAt χ.LFunction 0 ≠
        analyticOrderAt (dirichletData χ hχ).entireCompletion 0 := by
  intro _ χ
  have he : χ.Even := by
    have hneg : (quadraticChar (ZMod 5)) (-1) = 1 := by
      rw [quadraticChar_neg_one (F := ZMod 5) (by norm_num [ZMod.ringChar_zmod_n]), ZMod.card]
      exact ZMod.χ₄_nat_one_mod_four (by norm_num)
    simp only [χ, DirichletCharacter.Even, MulChar.ringHomComp_apply, hneg, map_one]
  have hne : χ ≠ 1 := quadraticChar_ringHomComp_ne_one
    (by simp [ringChar.eq_zero]) (by norm_num)
  have hprim : χ.IsPrimitive := by
    simpa [χ, isPrimitive_def] using conductor_changeLevel_quadraticChar
      (R := ℂ) (p := 5) (by simp [ringChar.eq_zero]) (by norm_num) (dvd_refl 5)
  have hzero : χ.LFunction 0 = 0 := by
    simpa [DirichletCharacter.LFunction, χ.map_zero' (by decide : 5 ≠ 1)] using
      ZMod.LFunction_apply_zero_of_even he.to_fun
  have hc := dirichletData_entireCompletion_zero_ne_zero χ hprim
  refine ⟨hprim, he, hne, hzero, hc, ?_⟩
  rw [((dirichletData_hasMeromorphicContinuation χ hprim).analyticAt_entireCompletion 0)
    |>.analyticOrderAt_eq_zero.mpr hc]
  exact ((DirichletCharacter.differentiable_LFunction hne).analyticAt 0)
    |>.analyticOrderAt_ne_zero.mpr hzero

end TauCeti.LFunctions
