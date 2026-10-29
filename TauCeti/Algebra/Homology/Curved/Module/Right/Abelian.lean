/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Kernel
public import TauCeti.Algebra.Homology.Curved.Module.Right.Cokernel
public import TauCeti.Algebra.Homology.Curved.Module.Right.Biproduct
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# The closed category of curved right modules is abelian

Kernels and cokernels carry their inherited differentials. The faithful graded forgetful
functor preserves these constructions and reflects isomorphisms. The coimage-to-image
comparison in the closed category is an isomorphism, as detected in the abelian graded module
category. This characterizes the abelian structure on the closed category of curved modules.

The graded forgetful functor preserves finite limits and colimits. This ambient abelian
category and its forgetful functor support the graded-split exact structure on curved modules.

## References

* The Tau Ceti contributors, `TauCeti.Algebra.Category.GradedModuleCat.Abelian`.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed category keeps the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- The closed category's coimage-to-image comparison is an isomorphism. -/
noncomputable instance
    {M N : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)}
    (f : M ⟶ N) : IsIso (Abelian.coimageImageComparison f) := by
  have := IsIso.of_isIso_fac_right
    (Abelian.PreservesCoimage.hom_coimageImageComparison (forgetDifferential (h := h)) f).symm
  exact isIso_of_reflects_iso _ (forgetDifferential (h := h))

/-- The closed category of curved right modules is abelian, as detected by graded modules. -/
noncomputable instance instAbelianClosedCategory : Abelian
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  Abelian.ofCoimageImageComparisonIsIso

/-- The graded forgetful functor preserves finite limits of closed curved-module diagrams. -/
noncomputable instance : PreservesFiniteLimits (forgetDifferential (h := h)) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The graded forgetful functor preserves finite colimits of closed curved-module diagrams. -/
noncomputable instance : PreservesFiniteColimits (forgetDifferential (h := h)) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

end TauCeti.CurvedDGRightModuleCat
