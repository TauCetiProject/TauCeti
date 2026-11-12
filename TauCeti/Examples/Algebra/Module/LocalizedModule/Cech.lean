/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Module.LocalizedModule.Cech

/-!
# Examples of the Čech complex of localizations

For the empty family the degree `0` term has no factors, so the augmentation from `ℤ` is not
injective: the hypothesis that the family generate the unit ideal cannot be dropped from
`TauCeti.injective_cechLocalizationAugmentation`. For the constant family `(1, 1)` the
differential sends the rational cochain with values `2` and `5` to `5 - 2 = 3`, and kills the
augmentation of `7`, as exactness requires.
-/

open LocalizedModule TauCeti

-- For the empty family the augmentation from `ℤ` is not injective.
example : ¬ Function.Injective (cechLocalizationAugmentation ℤ (Fin.elim0 : Fin 0 → ℤ)) := by
  intro h
  refine one_ne_zero (h (funext fun S ↦ ?_))
  have hS : S.1 = ∅ := Subsingleton.elim _ _
  exact absurd S.2 (by simp [hS])

-- The differential sends the cochain with values `2` at `{0}` and `5` at `{1}` to `5 - 2 = 3`.
example : cechLocalizationDifferential ℚ (fun _ : Fin 2 ↦ (1 : ℚ)) 0
    (fun S ↦ mk (if (0 : Fin 2) ∈ S.1 then 2 else 5) 1) ⟨{0, 1}, rfl⟩ = mk 3 1 := by
  rw [cechLocalizationDifferential_apply]
  -- `simp` lists `attach` of `{0, 1}` up to the attached singleton `{1}`, computed here.
  have h1 : ({1} : Finset (Fin 2)).attach = {⟨1, Finset.mem_singleton_self 1⟩} := rfl
  simp [h1, Finset.filter_insert, Finset.filter_singleton]
  norm_num

-- The differential kills the augmentation of `7`.
example : cechLocalizationDifferential ℚ (fun _ : Fin 2 ↦ (1 : ℚ)) 0
    (cechLocalizationAugmentation ℚ _ 7) = 0 :=
  LinearMap.congr_fun (cechLocalizationDifferential_comp_augmentation ℚ _) 7
