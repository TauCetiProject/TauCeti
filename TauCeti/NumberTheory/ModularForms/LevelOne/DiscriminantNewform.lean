/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform
public import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
public import TauCeti.NumberTheory.ModularForms.Newforms.GaloisCertification

import Mathlib.Tactic.ComputeDegree

/-!
# The discriminant as a newform

At level one there are no oldforms (`TauCeti.cuspFormsNew_one`), so the normalized full Hecke
eigenform `TauCeti.discriminantEigenform` upgrades via `HeckeRing.GL2.Eigenform.toNewformOfLevelOne`
to `TauCeti.discriminantNewform : HeckeRing.GL2.Newform 1 12`. Because every Ramanujan `τ`-number is
an integer, its coefficient field `CoefficientField discriminantNewform` and its Galois closure
`CoefficientFieldGaloisClosure discriminantNewform` in `ℂ` are both `⊥` (`ℚ`), and the certificate
pipeline of `TauCeti.NumberTheory.ModularForms.Newforms.GaloisCertification` certifies solvability
of `Gal(CoefficientFieldGaloisClosure discriminantNewform/ℚ)` at `n = 2` (`τ(2) = -24`).

## Main definitions and results

* `TauCeti.discriminantNewform`: the modular discriminant `Δ` bundled as a `Newform 1 12`.
* `TauCeti.coe_discriminantNewform`, `TauCeti.discriminantNewform_χ`: underlying function and
  trivial nebentypus character of `discriminantNewform`.
* `TauCeti.CoefficientField_discriminantNewform`,
  `TauCeti.CoefficientFieldGaloisClosure_discriminantNewform`:
  `CoefficientField discriminantNewform = ⊥` and
  `CoefficientFieldGaloisClosure discriminantNewform = ⊥`.
* `TauCeti.isSolvable_CoefficientFieldGaloisClosure_discriminantNewform`: end-to-end solvability
  certification of `Gal(CoefficientFieldGaloisClosure discriminantNewform/ℚ)` via `X + 24`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
* J.-P. Serre, *A Course in Arithmetic*, VII.4.
-/

public noncomputable section

open IntermediateField Polynomial UpperHalfPlane ModularForm HeckeRing.GL2
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

/-- The Galois closure of `CoefficientField discriminantNewform` in `ℂ` is `⊥` (`ℚ`). -/
@[simp]
theorem CoefficientFieldGaloisClosure_discriminantNewform :
    CoefficientFieldGaloisClosure discriminantNewform = ⊥ := by
  have : Normal ℚ (⊥ : IntermediateField ℚ ℂ) :=
    Normal.of_algEquiv (IntermediateField.botEquiv ℚ ℂ).symm
  apply eq_bot_iff.mpr
  rw [CoefficientFieldGaloisClosure_le_iff_of_normal, CoefficientField_discriminantNewform]

/-- End-to-end solvability certification of
`Gal(CoefficientFieldGaloisClosure discriminantNewform/ℚ)` via
`isSolvable_CoefficientFieldGaloisClosure_iff_of_check_eq_true` at `n = 2` (`τ(2) = -24`,
annihilated by `X + 24`). -/
theorem isSolvable_CoefficientFieldGaloisClosure_discriminantNewform :
    Group.IsSolvable Gal(CoefficientFieldGaloisClosure discriminantNewform/ℚ) := by
  have hP : (X + 24 : ℤ[X]).Monic := by
    rw [← C_ofNat 24]
    exact monic_X_add_C 24
  have hirr : Irreducible ((X + 24 : ℤ[X]).map (Int.castRingHom ℚ)) := by
    rw [← C_ofNat 24, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
    exact irreducible_of_degree_eq_one (degree_X_add_C _)
  have hroot : aeval ((qExpansion 1 discriminantNewform.toCuspForm).coeff (2 : ℕ+))
      (X + 24 : ℤ[X]) = 0 := by
    have h2 : ((2 : ℕ+) : ℕ) = 2 := rfl
    rw [h2, coe_discriminantNewform, map_add, aeval_X, map_ofNat,
      TauCeti.ModularForm.discriminant_qExpansion_coeff_two]
    norm_num
  have hdeg : (letI := finiteDimensional_CoefficientField discriminantNewform (by decide)
      Module.finrank ℚ (CoefficientField discriminantNewform)) ≤ (X + 24 : ℤ[X]).natDegree := by
    have hd1 : (X + 24 : ℤ[X]).natDegree = 1 := by compute_degree!
    rw [CoefficientField_discriminantNewform, IntermediateField.finrank_bot, hd1]
  exact (isSolvable_CoefficientFieldGaloisClosure_iff_of_check_eq_true
    discriminantNewform (by decide) 2 hP hirr hroot hdeg
    SolvabilityCertificate.check_smallDegree_X_add_twenty_four).mpr
    SolvabilityCertificate.isSolvable_smallDegree

end TauCeti

end
