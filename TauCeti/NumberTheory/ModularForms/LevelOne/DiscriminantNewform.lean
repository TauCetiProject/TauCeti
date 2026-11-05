/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform
public import TauCeti.NumberTheory.ModularForms.Newforms.Fields
public import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# The discriminant as a newform

At level one there are no oldforms (`TauCeti.cuspFormsNew_one`), so the normalized full Hecke
eigenform `TauCeti.discriminantEigenform` upgrades via `HeckeRing.GL2.Eigenform.toNewformOfLevelOne`
to `TauCeti.discriminantNewform : HeckeRing.GL2.Newform 1 12`. Because every Ramanujan `τ`-number is
an integer, its coefficient field `CoefficientField discriminantNewform` is `⊥` (`ℚ`).

## Main definitions and results

* `TauCeti.discriminantNewform`: the modular discriminant `Δ` bundled as a `Newform 1 12`.
* `TauCeti.coe_discriminantNewform`, `TauCeti.discriminantNewform_χ`: underlying function and
  trivial nebentypus character of `discriminantNewform`.
* `TauCeti.CoefficientField_discriminantNewform`: `CoefficientField discriminantNewform = ⊥`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
* J.-P. Serre, *A Course in Arithmetic*, VII.4.
-/

public noncomputable section

open IntermediateField UpperHalfPlane ModularForm HeckeRing.GL2
open scoped ModularForm

namespace TauCeti

/-- The modular discriminant `Δ`, bundled as a newform of level `1` and weight `12`. -/
def discriminantNewform : Newform 1 12 :=
  discriminantEigenform.toNewformOfLevelOne (by simpa using discriminant_qExpansion_coeff_one)

/-- The underlying function of `discriminantNewform` is `discriminant`. -/
@[simp]
theorem coe_discriminantNewform :
    (discriminantNewform.toCuspForm : ℍ → ℂ) = discriminant := by
  simp [discriminantNewform]

/-- `discriminantNewform` has trivial nebentypus character. -/
@[simp]
theorem discriminantNewform_χ : discriminantNewform.χ = 1 := by
  simp [discriminantNewform]

/-- Every Fourier coefficient of `Δ` is an integer, so `CoefficientField discriminantNewform = ⊥`.
-/
@[simp]
theorem CoefficientField_discriminantNewform :
    CoefficientField discriminantNewform = ⊥ := by
  apply eq_bot_iff.mpr
  rw [CoefficientField_le_iff]
  intro n
  obtain ⟨m, hm⟩ := TauCeti.ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast n
  rw [coe_discriminantNewform, hm]
  exact (⊥ : IntermediateField ℚ ℂ).intCast_mem m

end TauCeti

end
