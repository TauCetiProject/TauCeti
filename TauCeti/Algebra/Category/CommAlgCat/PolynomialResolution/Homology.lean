/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.PolynomialResolution.Augmented
public import TauCeti.AlgebraicTopology.SimplicialObject.ExtraDegeneracy

/-!
# The standard polynomial resolution is a resolution

For a commutative `R`-algebra `B`, the standard simplicial polynomial resolution `P• → B` has its
evaluation augmentation. After forgetting to `R`-modules, the augmentation of its alternating face
map complex `C(P•) ⟶ B[0]` is a quasi-isomorphism
(`CommAlgCat.quasiIso_polynomialAugmentedResolution_ε`). No flatness or finiteness of `B` is
needed. The proof applies `SimplicialObject.Augmented.ExtraDegeneracy.quasiIso_ε_of_forget` to the
extra degeneracy `CommAlgCat.polynomialResolutionExtraDegeneracy`, which sends an element to the
polynomial variable it indexes and is only a map of sets.

## References

* The Stacks Project, Definition 92.3.1 and Remark 92.5.5 (Tags 08PM and 08QI).
-/

public section

open AlgebraicTopology CategoryTheory SimplicialObject.Augmented

namespace CommAlgCat

universe u v

/-- **The standard polynomial resolution is a resolution.** For a commutative `R`-algebra `B`, the
evaluation augmentation of the standard simplicial polynomial resolution induces a
quasi-isomorphism from the alternating face map complex of its underlying `R`-modules to `B`
placed in degree zero. -/
theorem quasiIso_polynomialAugmentedResolution_ε {R : Type u} [CommRing R]
    (B : CommAlgCat.{max u v} R) :
    QuasiIso (AlternatingFaceMapComplex.ε.app
      (((whiskering _ _).obj
        (forget₂ (CommAlgCat.{max u v} R) (AlgCat.{max u v} R) ⋙
          forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R))).obj
        ((polynomialAugmentedResolution R).obj B))) :=
  -- The underlying set of the underlying module of a commutative algebra is its underlying set by
  -- definition, so the extra degeneracy on the underlying sets of `P• → B` applies.
  ExtraDegeneracy.quasiIso_ε_of_forget (polynomialResolutionExtraDegeneracy R B)

end CommAlgCat
