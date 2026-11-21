/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.PolynomialResolution.Augmented
public import TauCeti.AlgebraicTopology.SimplicialObject.ExtraDegeneracy

/-!
# Homology of the standard polynomial resolution

After forgetting to modules over the base ring, the alternating face complex of the standard
simplicial polynomial resolution is quasi-isomorphic to the resolved algebra in degree zero,
via its evaluation augmentation. No flatness of the resolved algebra is required.

See the Stacks Project, Definition 92.3.1 and Remark 92.5.5 (Tags 08PM and 08QI).
-/

public section

open AlgebraicTopology CategoryTheory SimplicialObject.Augmented

namespace CommAlgCat

universe u v

/-- The evaluation augmentation of the standard polynomial resolution induces a
quasi-isomorphism from its alternating face complex of base-ring modules to the resolved
algebra placed in degree zero. -/
theorem quasiIso_polynomialAugmentedResolution_ε {R : Type u} [CommRing R]
    (B : CommAlgCat.{max u v} R) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (((whiskering _ _).obj
        (forget₂ (CommAlgCat.{max u v} R) (AlgCat.{max u v} R) ⋙
          forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R))).obj
        ((polynomialAugmentedResolution R).obj B))) := by
  apply ExtraDegeneracy.quasiIso_ε_of_forget
  exact polynomialResolutionExtraDegeneracy R B

end CommAlgCat
