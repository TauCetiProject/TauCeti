/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ModuleResolution
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ProjectiveDimension
public import TauCeti.RingTheory.GlobalDimension

/-!
# Ungraded global dimension bounds graded Ext

An ungraded projective-dimension bound on a finite graded module over a left Noetherian
algebra bounds its graded Ext in every internal degree, with no increase of the bound.
This follows by realizing the ungraded bound by a finite graded-projective resolution.
Consequently a global-dimension bound supplies one cohomological bound for every pair of
finite graded modules and every internal shift.

Over a finite-dimensional algebra these resolutions also supply finite Laurent support,
so the q-Euler pairing is defined. The cohomological bound alone is not used to infer
internal finiteness. Neither a nonnegative grading nor a semisimple degree-zero part is needed.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7 and Chapter 4.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

namespace TauCeti

open CategoryTheory

universe w uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{w} (GradedModuleCat.{uA} 𝒜)]

/-- An ungraded projective-dimension bound on a finite graded source bounds graded Ext
against every target, uniformly in the internal degree. Only left Noetherianity is required. -/
theorem isGradedExtBoundedBy_of_hasProjectiveDimensionLE [IsNoetherianRing A]
    {X Y : GradedModuleCat.{uA} 𝒜} [Module.Finite A X] {n : ℕ}
    (hX : HasProjectiveDimensionLE (GradedModuleCat.toModuleCat.obj X) n) :
    IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) X Y (n + 1) := by
  have hr := exists_gradedFiniteProjectiveResolution_of_hasProjectiveDimensionLE hX
  -- Retype the resolution and its length bound together in the abelian exact structure.
  rw [gradedModuleCanonicalExactStructure, GradedExactStructure.abelian_toExactStructure] at hr
  obtain ⟨r, hr⟩ := hr
  exact (r.isGradedExtBoundedBy gradedFiniteProjectiveModules_le_isProjective).mono
    (Nat.add_le_add_right hr 1)

/-- A bound on ungraded global dimension gives the same graded Ext bound for every finite
source and every graded target, simultaneously in all internal degrees. -/
theorem isGradedExtBoundedBy_of_globalDimension_le [IsNoetherianRing A] {n : ℕ}
    (h : globalDimension.{uA} A ≤ n) (X Y : GradedModuleCat.{uA} 𝒜)
    [Module.Finite A X] :
    IsGradedExtBoundedBy.{w} (GradedModuleCat.shift 𝒜) X Y (n + 1) :=
  isGradedExtBoundedBy_of_hasProjectiveDimensionLE
    ((globalDimension_le_iff_hasProjectiveDimensionLE A n).1 h _)

section Field

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{w} (GradedModuleCat.{uA} 𝒜)]

/-- Finite ungraded global dimension of a finite-dimensional graded algebra supplies the
admissibility witness for the q-Euler pairing on all finite graded modules. -/
theorem isGradedEulerAdmissibleOn_gradedFiniteModules_of_globalDimension_le {n : ℕ}
    (h : globalDimension.{uA} A ≤ n) :
    IsGradedEulerAdmissibleOn.{w} (k := k) (e := GradedModuleCat.shift 𝒜)
      (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜) := by
  have : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  apply isGradedEulerAdmissibleOn_gradedFiniteModules
  apply gradedFiniteModules_le_admitsFiniteResolution_of_finite_projectiveDimension
  exact fun M _ ↦ ⟨n, (globalDimension_le_iff_hasProjectiveDimensionLE A n).1 h _⟩

end Field

end TauCeti
