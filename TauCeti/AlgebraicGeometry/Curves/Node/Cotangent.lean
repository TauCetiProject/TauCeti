/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.RingTheory.Node.Cotangent.Relative

/-!
# The differentials of a nodal curve along its singular locus

Let `X` be a nodal relative curve over an arbitrary affine base `Spec R`: syntomic of relative
dimension one, with relative singular subscheme `Sing(X/R)` unramified over `R`. At every point
`x` of `Sing(X/R)` the fibre `κ(x) ⊗ Ω_{X/R}` has dimension exactly two. It is at least two by
the definition of the singular locus as the zero locus of the first Fitting ideal of `Ω_{X/R}`.
The upper bound is `TauCeti.finrank_tensor_kaehlerDifferential_le_two`, applied to `Γ(X, U)`;
it follows by base change to the residue field of the image of `x` in the base.

When `R` is a field, the ring-level result `TauCeti.finrank_cotangentSpace_eq_two` also identifies
the Zariski cotangent space `𝔪/𝔪²` of the local ring at a node with this plane. For a general
base, the assertion here is only about relative differentials: the absolute cotangent space can
have larger dimension.

The input from the nodal criterion is
`AlgebraicGeometry.Scheme.formallyUnramified_quotient_singularLocus_ideal`: on an affine open `U`,
the quotient of `Γ(X, U)` by the ideal of the singular locus is unramified over the base.

## Main results

* `AlgebraicGeometry.Scheme.finrank_residueField_tensor_kaehlerDifferential_eq_two`: at every point
  of the singular locus of a nodal relative curve over an arbitrary affine base, the fibre of
  the relative differentials has dimension two.

## References

* [Stacks Project, Section 53.19, Tag 0C46](https://stacks.math.columbia.edu/tag/0C46): nodal
  curves over a field.
* [Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): the
  singular-locus criterion for families of nodal curves.
-/

public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry

universe u

/-- **The relative differentials of a nodal curve along its nodes.** Let `X` be a nodal relative
curve over `Spec R`. At every point `x` of the singular locus, and on every affine open `U`
containing it, the fibre `κ(x) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]` has dimension two. -/
theorem _root_.AlgebraicGeometry.Scheme.finrank_residueField_tensor_kaehlerDifferential_eq_two
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus R).support)
    {U : X.affineOpens} (hxU : x ∈ U.1) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    letI : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
    Module.finrank (X.residueField x) (X.residueField x ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = 2 := by
  let : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
  let := (X.evaluation U x hxU).hom.toAlgebra
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  have := finiteType_sections_of_locallyOfFiniteType R X U
  have hI := X.singularLocus_ideal (R := R) U
  have : Algebra.FormallyUnramified R (Γ(X, U) ⧸ fittingIdeal Γ(X, U) Ω[Γ(X, U)⁄R] 1) :=
    hI ▸ X.formallyUnramified_quotient_singularLocus_ideal hnodal U
  refine le_antisymm (finrank_tensor_kaehlerDifferential_le_two (R := R)) ?_
  exact (Scheme.mem_support_singularLocus_iff (R := R) (X := X) hxU).1 hx

end TauCeti.AlgebraicGeometry
