/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
public import TauCeti.AlgebraicGeometry.Curves.Node.Nodal

/-!
# The singular locus of a proper nodal curve

For a proper nodal curve over a field, the relative singular subscheme is finite étale over the
field. Finiteness follows from properness and the fact that a nodal singular locus is
unramified; flatness over a field then gives étaleness. This is the scheme that records the
nodes before passing to a separable extension that labels them.

## References

* [Stacks Project, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58)
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-- The singular subscheme of a proper nodal relative curve over an affine base is finite.
The nodal hypothesis is expressed by the scheme-theoretic criterion for an affine base. -/
theorem _root_.AlgebraicGeometry.Scheme.isFinite_singularLocus_subschemeι_comp
    (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [IsProper (X ↘ Spec (.of R))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R))) :
    letI : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
    IsFinite ((X.singularLocus R).subschemeι ≫ (X ↘ Spec (.of R))) := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
  have : Unramified
      ((X.singularLocus R).subschemeι ≫ (X ↘ Spec (.of R))) :=
    hnodal.unramified_singularLocus
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

variable {K : Type u} [Field K]

/-- The singular subscheme of a nodal relative curve over a field is étale over that field.
The nodal hypothesis is expressed by the scheme-theoretic criterion for an affine base. -/
theorem _root_.AlgebraicGeometry.Scheme.etale_singularLocus_subschemeι_comp
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
    Etale ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))) := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
  have : Unramified
      ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))) :=
    hnodal.unramified_singularLocus
  have : Flat ((X.singularLocus K).subschemeι ≫ (X ↘ Spec (.of K))) := inferInstance
  exact Etale.of_formallyUnramified_of_flat _

end TauCeti.AlgebraicGeometry
