/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.Codimension
public import TauCeti.NumberTheory.ModularForms.Cusps.Residue
import TauCeti.NumberTheory.ModularForms.SturmBound
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The weight-two cusp codimension bound

For every finite-index subgroup `H` of `SL(2, ℤ)`, the codimension of the cusp forms in
`M₂(H)` is at most the number of cusps minus one. The same bound holds for every subspace
disjoint from the cusp forms. This is the upper bound used when comparing a family of
weight-two Eisenstein series with the full cusp boundary image.

Constant terms at representatives of the ordinary cusp orbits detect cusp forms. In weight
two, equivalent representatives have equal constant terms even when `-I ∉ H`. The residue
relation prevents the constant function `1` from belonging to their image, improving the
general cusp-count bound by one.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005],
  §§3.1, 4.2 and 4.6.
-/

public noncomputable section

open Matrix.SpecialLinearGroup ModularForm
open scoped MatrixGroups

namespace TauCeti.ModularForm

variable {H : Subgroup SL(2, ℤ)} [H.FiniteIndex]

/-- A subspace of weight-two modular forms disjoint from the cusp forms has dimension at
most the number of ordinary cusps minus one. No assumption that `-I ∈ H` is needed. -/
theorem finrank_le_card_cuspOrbit_sub_one_of_disjoint
    {V : Submodule ℂ (ModularForm (H.map (mapGL ℝ)) 2)}
    (hV : Disjoint V (cuspFormSubmodule (H.map (mapGL ℝ)) 2)) :
    Module.finrank ℂ V ≤ Nat.card (H.map sl2zToPSL2R).CuspOrbit - 1 := by
  classical
  let r := Function.surjInv H.cuspOrbitOfSL2Z_surjective
  let L := (LinearMap.funLeft ℂ ℂ r).comp
    (constantTerms (Γ := H.map (mapGL ℝ)) (k := 2))
  have hrep (γ : SL(2, ℤ)) :
      constantTermAt (Γ := H.map (mapGL ℝ)) (k := 2) γ =
        constantTermAt (r (H.cuspOrbitOfSL2Z γ)) := by
    obtain ⟨u, hu⟩ := exists_constantTermAt_eq_zpow_smul_of_cuspOrbitOfSL2Z_eq (k := 2)
      (Function.surjInv_eq H.cuspOrbitOfSL2Z_surjective (H.cuspOrbitOfSL2Z γ))
    rcases Int.units_eq_one_or u with rfl | rfl <;> simpa using hu
  have hker (f : ModularForm (H.map (mapGL ℝ)) 2) (hf : L f = 0) :
      f ∈ cuspFormSubmodule (H.map (mapGL ℝ)) 2 := by
    rw [mem_cuspFormSubmodule_iff_constantTermAt_eq_zero]
    intro γ
    rw [hrep γ]
    simpa only [L, LinearMap.comp_apply, LinearMap.funLeft_apply, constantTerms_apply,
      Pi.zero_apply] using congrFun hf (H.cuspOrbitOfSL2Z γ)
  have hinj : Function.Injective (L.comp V.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    exact Subtype.ext <| (Submodule.disjoint_def.mp hV) _ f.2 (hker _ hf)
  let _ := Fintype.ofFinite (H.map sl2zToPSL2R).CuspOrbit
  have hproper : LinearMap.range L ≠ ⊤ := by
    intro htop
    obtain ⟨f, hf⟩ := LinearMap.range_eq_top.mp htop (fun _ ↦ (1 : ℂ))
    have hconst (γ : SL(2, ℤ)) : constantTermAt γ f = 1 := by
      rw [hrep γ]
      simpa only [L, LinearMap.comp_apply, LinearMap.funLeft_apply, constantTerms_apply] using
        congrFun hf (H.cuspOrbitOfSL2Z γ)
    exact one_ne_zero (weight_two_eq_zero_of_forall_constantTermAt_eq hconst)
  have hlt : Module.finrank ℂ (LinearMap.range L) <
      Nat.card (H.map sl2zToPSL2R).CuspOrbit := by
    simpa only [finrank_top, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using
      Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)
  have hle : Module.finrank ℂ V ≤ Module.finrank ℂ (LinearMap.range L) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (L.comp V.subtype).codRestrict (LinearMap.range L)
        fun f ↦ ⟨f, rfl⟩) (fun _ _ h ↦ hinj (congrArg Subtype.val h))
  omega

/-- The quotient of the weight-two modular forms by the cusp forms has dimension at most
the number of ordinary cusps minus one. -/
theorem finrank_quotient_cuspFormSubmodule_le_card_cuspOrbit_sub_one :
    Module.finrank ℂ
        (ModularForm (H.map (mapGL ℝ)) 2 ⧸ cuspFormSubmodule (H.map (mapGL ℝ)) 2) ≤
      Nat.card (H.map sl2zToPSL2R).CuspOrbit - 1 := by
  obtain ⟨V, hV⟩ := (cuspFormSubmodule (H.map (mapGL ℝ)) 2).exists_isCompl
  have hdim := Submodule.finrank_add_eq_of_isCompl hV
  have hquot := (cuspFormSubmodule (H.map (mapGL ℝ)) 2).finrank_quotient_add_finrank
  have hbound := finrank_le_card_cuspOrbit_sub_one_of_disjoint hV.symm.disjoint
  omega

/-- The dimension of the weight-two modular forms is at most the cusp-form dimension plus
the number of ordinary cusps minus one. -/
theorem finrank_weight_two_le_finrank_cuspForm_add_card_cuspOrbit_sub_one :
    Module.finrank ℂ (ModularForm (H.map (mapGL ℝ)) 2) ≤
      Module.finrank ℂ (CuspForm (H.map (mapGL ℝ)) 2) +
        (Nat.card (H.map sl2zToPSL2R).CuspOrbit - 1) := by
  have hdim := (cuspFormSubmodule (H.map (mapGL ℝ)) 2).finrank_quotient_add_finrank
  rw [← (CuspForm.equivCuspFormSubmodule (H.map (mapGL ℝ)) 2).finrank_eq] at hdim
  have hbound := finrank_quotient_cuspFormSubmodule_le_card_cuspOrbit_sub_one (H := H)
  omega

end TauCeti.ModularForm
