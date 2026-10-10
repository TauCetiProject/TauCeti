/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Resolution
public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Resolution

/-!
# Graded module resolutions supply q-Euler admissibility

Over a finite-dimensional graded algebra, a finite resolution by finitely generated graded
projectives supplies both finiteness conditions needed for the q-Euler characteristic against
any finite graded module. The graded Hom spaces of the resolving terms are finite-dimensional
and have finite Laurent support, and the resolution gives a cohomological vanishing bound
uniform in the target's internal shift.

Thus the subcategory of modules admitting finite graded-projective resolutions pairs with all
finite graded modules. If every finite graded module admits such a resolution, the
module/module q-Euler form can be constructed using this admissibility witness. No uniform
bound on all resolution lengths, splitness hypothesis, or positivity of the algebra grading is
required.

## Main results

* `TauCeti.isGradedEulerAdmissible_of_admitsFiniteProjectiveResolution`: admissibility for one
  resolved source and one finite target.
* `TauCeti.isGradedEulerAdmissibleOn_admitsFiniteProjectiveResolution_gradedFiniteModules`:
  admissibility on the finite-resolution subcategory against all finite graded modules.
* `TauCeti.isGradedEulerAdmissibleOn_gradedFiniteModules`: admissibility on all finite graded
  modules under the finite graded-projective resolution hypothesis.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.

The graded Hom support input is
`TauCeti.GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj`; the resolution criterion is
`TauCeti.ExactStructure.FiniteResolution.isGradedEulerAdmissible`.
-/

public section

namespace TauCeti

open CategoryTheory

universe w uk uA

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{w} (GradedModuleCat.{uA} 𝒜)]

/-- A finite resolution by finitely generated graded projectives makes the source graded
Euler-admissible against every finite-dimensional graded target. The algebra itself need not
be finite-dimensional. -/
theorem isGradedEulerAdmissible_of_admitsFiniteProjectiveResolution
    {X Y : GradedModuleCat.{uA} 𝒜} [Module.Finite k Y]
    (hX : (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
      (gradedFiniteProjectiveModules 𝒜) X) :
    IsGradedEulerAdmissible.{w} k (GradedModuleCat.shift 𝒜) X Y := by
  obtain ⟨r⟩ := (ExactStructure.admitsFiniteResolution_iff _ _).mp hX
  -- The canonical graded exact structure has the abelian exact structure underneath.
  rw [gradedModuleCanonicalExactStructure, GradedExactStructure.abelian_toExactStructure] at r
  refine r.isGradedEulerAdmissible gradedFiniteProjectiveModules_le_isProjective
    fun Z hZ ↦ ?_
  have : Module.Finite A Z := (gradedFiniteProjectiveModules_iff.1 hZ).1
  exact (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj Z Y).of_equiv fun j ↦
    (GradedModuleCat.homShiftPowEquiv 𝒜 Z Y j).symm

variable [Module.Finite k A]

/-- Modules admitting finite resolutions by finite graded projectives pair with all finite
graded modules under the q-Euler characteristic. The cohomological bound may depend on the
source, but is uniform in the internal degree. -/
theorem isGradedEulerAdmissibleOn_admitsFiniteProjectiveResolution_gradedFiniteModules :
    IsGradedEulerAdmissibleOn.{w} (k := k) (e := GradedModuleCat.shift 𝒜)
      ((gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
        (gradedFiniteProjectiveModules 𝒜)) (gradedFiniteModules 𝒜) :=
  ⟨fun _ Y hX hY ↦ by
    have : Module.Finite A Y := gradedFiniteModules_iff.1 hY
    have : Module.Finite k Y := Module.Finite.trans A Y
    exact isGradedEulerAdmissible_of_admitsFiniteProjectiveResolution hX⟩

/-- If every finite graded module over a finite-dimensional graded algebra has a finite
resolution by finite graded projectives, every pair of finite graded modules is graded
Euler-admissible. In particular this supplies the finiteness witness for the module/module
q-Euler form, without assuming Euler-admissibility separately. -/
theorem isGradedEulerAdmissibleOn_gradedFiniteModules
    (h : gradedFiniteModules 𝒜 ≤
      (gradedModuleCanonicalExactStructure 𝒜).admitsFiniteResolution
        (gradedFiniteProjectiveModules 𝒜)) :
    IsGradedEulerAdmissibleOn.{w} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜) :=
  isGradedEulerAdmissibleOn_admitsFiniteProjectiveResolution_gradedFiniteModules.mono h le_rfl

end TauCeti
