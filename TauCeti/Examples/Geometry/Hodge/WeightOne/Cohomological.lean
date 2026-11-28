/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm.Cohomological
public import TauCeti.Geometry.Hodge.WeightOne.Standard

/-!
# Homological and cohomological structures on the Gaussian lattice

On the Gaussian lattice `Λ = ℤ + iℤ`, written `ℤ^{1 ⊕ 1}` with the standard complex structure `J`
and the standard principal Riemann form `E₀` (`TauCeti.Hodge.StandardWeightOne`):

* the homological structure on `Λ = H₁` has Weil operator `C = -J`, and its polarizing form is
  `Q = -E₀`: at `v = 1`, `Q(Cv, v) = E₀(Jv, v) = 1 > 0`, while `E₀(Cv, v) = -1 < 0`, so `E₀` itself
  does not polarize it;
* the cohomological structure on `H¹ = Hom(Λ, ℤ)` has Weil operator the transpose of `J`, and is
  polarized by the dual form `(-E₀)^∨`;
* for the doubled form `E = 2E₀`, which is not principal, the integral form `2 (-E)^∨` polarizes
  the cohomological structure.
-/

public section

namespace TauCeti.CohomologicalHodgeExamples

open LinearMap Matrix TauCeti.Hodge TauCeti.Hodge.StandardWeightOne
open TauCeti.AlmostComplexStructure

/-- The lattice `ℤ + iℤ`, as `ℤ^{1 ⊕ 1}`. -/
abbrev Λ : Type := StandardWeightOne.Lattice Unit

/-- The standard complex structure on `ℝ ⊗ Λ = ℂ`. -/
noncomputable abbrev J₀ : AlmostComplexStructure (Realification Λ) :=
  StandardWeightOne.almostComplexStructure Unit

/-- The standard principal Riemann form `E₀` on `ℤ + iℤ`. -/
noncomputable abbrev E₀ : LinearMap.BilinForm ℤ Λ := riemannForm Unit

/-- The base change `ℤ^{1 ⊕ 1} → ℂ^{1 ⊕ 1}`. -/
abbrev hℂ : IsBaseChange ℂ (latticeToComplex Unit) := isBaseChange_latticeToComplex Unit

/-- The vector `1 ∈ ℤ + iℤ`. -/
abbrev one : Λ := Pi.single (Sum.inl ()) 1

/-- `E₀` is principal. -/
instance instIsPerfPairE₀ : E₀.IsPerfPair := isPerfPair_riemannForm Unit

/-- `E₀` is a Riemann form for `J₀`. -/
theorem isRiemannForm_E₀ : J₀.IsRiemannForm E₀ := isRiemannForm_riemannForm Unit

/-- The complexification of `J₀` is the matrix `J`. -/
theorem latticeComplexification_J₀ : J₀.latticeComplexification hℂ = toLin' (J Unit ℂ) :=
  latticeComplexification_almostComplexStructure Unit

/-- **The homological Weil operator is `C = -J`.** -/
theorem homological_weilOperator_J₀ :
    (RiemannForm.homological J₀ hℂ).weilOperator = -toLin' (J Unit ℂ) := by
  rw [RiemannForm.homological_weilOperator, latticeComplexification_J₀]

/-- On the lattice, `J` sends `1` to `i`. -/
theorem J_mulVec_one : J Unit ℤ *ᵥ one = Pi.single (Sum.inr ()) 1 := by
  ext (_ | _) <;> simp [J]

/-- **`Q = -E₀` is positive against `C = -J`:** `Q(Cv, v) = E₀(Jv, v) = 1` at `v = 1`. -/
theorem neg_E₀_neg_J_one : (-E₀) (-(J Unit ℤ *ᵥ one)) one = 1 := by
  rw [J_mulVec_one]
  simp

/-- **`E₀` is negative against `C = -J`:** `E₀(Cv, v) = -1` at `v = 1`. -/
theorem E₀_neg_J_one : E₀ (-(J Unit ℤ *ᵥ one)) one = -1 := by
  rw [J_mulVec_one]
  simp

/-- `-E₀` polarizes the homological structure. -/
theorem isPolarization_homological_J₀ :
    IsPolarization hℂ (RiemannForm.homological J₀ hℂ) (-E₀) :=
  isRiemannForm_E₀.isPolarization_homological hℂ

/-- **The cohomological Weil operator is the transpose of `J`.** -/
theorem cohomological_weilOperator_J₀ :
    (RiemannForm.cohomological J₀ hℂ).weilOperator = (toLin' (J Unit ℂ)).dualMap := by
  rw [RiemannForm.cohomological_weilOperator, latticeComplexification_J₀]

/-- **The dual form of `-E₀` polarizes the cohomological structure.** -/
theorem isPolarization_cohomological_J₀ :
    IsPolarization (isBaseChange_dualLatticeMap hℂ) (RiemannForm.cohomological J₀ hℂ)
      ((-E₀).scaledDualForm isRiemannForm_E₀.injective_neg 1
        E₀.one_smul_mem_range_neg_of_isPerfPair) :=
  isRiemannForm_E₀.isPolarization_cohomological_one hℂ

/-- The doubled form `E = 2 E₀`. -/
noncomputable abbrev E : LinearMap.BilinForm ℤ Λ := (2 : ℕ) • E₀

/-- `2 E₀` is a Riemann form for `J₀`. -/
theorem isRiemannForm_E : J₀.IsRiemannForm E := isRiemannForm_E₀.scale two_pos

/-- The cokernel of `E♭` is killed by `2`. -/
theorem two_smul_mem_range_E (η : Module.Dual ℤ Λ) : (2 : ℤ) • η ∈ LinearMap.range E :=
  ⟨E₀.toPerfPair.symm η, by simp [ofNat_zsmul]⟩

/-- **For `E = 2 E₀`, the integral form `2 (-E)^∨` polarizes the cohomological structure.** -/
theorem isPolarization_cohomological_E :
    IsPolarization (isBaseChange_dualLatticeMap hℂ) (RiemannForm.cohomological J₀ hℂ)
      ((-E).scaledDualForm isRiemannForm_E.injective_neg 2
        (E.smul_mem_range_neg 2 two_smul_mem_range_E)) :=
  isRiemannForm_E.isPolarization_cohomological hℂ two_smul_mem_range_E two_pos

end TauCeti.CohomologicalHodgeExamples
