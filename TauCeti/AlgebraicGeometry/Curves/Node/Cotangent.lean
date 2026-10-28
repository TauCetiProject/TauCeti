/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.RingTheory.Node.Cotangent

/-!
# The differentials of a nodal curve along its singular locus

Let `X` be a nodal curve over a field `K`: syntomic of relative dimension one, with relative
singular subscheme `Sing(X/K)` unramified over `K`. At every point `x` of `Sing(X/K)` the fibre
`κ(x) ⊗ Ω_{X/K}` has dimension exactly two. It is at least two by the definition of the singular
locus as the zero locus of the first Fitting ideal of `Ω_{X/K}`. It is at most two because the
singular locus is reduced at `x`, so that its ideal in the local ring is the maximal ideal, while
the first Fitting ideal of a module needing three generators lies in the square of the maximal
ideal. The ring-level statement used here is `TauCeti.finrank_tensor_kaehlerDifferential_eq_two`,
applied to `Γ(X, U)`.
For a local algebra, the ring-level result `TauCeti.finrank_cotangentSpace_eq_two` also shows
that the Zariski cotangent space `𝔪/𝔪²` at a node, which is the conormal space of the singular
locus there, is this plane; this file proves no cotangent-space statement of its own. The two
branches through a node are lines in this plane.

The input from the nodal criterion is
`AlgebraicGeometry.Scheme.formallyUnramified_quotient_singularLocus_ideal`: on an affine open `U`,
the quotient of `Γ(X, U)` by the ideal of the singular locus is unramified over the base.

## Main results

* `AlgebraicGeometry.Scheme.finrank_residueField_tensor_kaehlerDifferential_eq_two`: at every point
  of the singular locus of a nodal curve over a field, the fibre of the differentials has
  dimension two.

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

/-- **The differentials of a nodal curve along its nodes.** Let `X` be a nodal curve over a field
`K`. At every point `x` of the singular locus, and on every affine open `U` containing it, the
fibre `κ(x) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄K]` of the differentials has dimension two. -/
theorem _root_.AlgebraicGeometry.Scheme.finrank_residueField_tensor_kaehlerDifferential_eq_two
    {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) {x : X}
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus K).support)
    {U : X.affineOpens} (hxU : x ∈ U.1) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    letI : Algebra K Γ(X, U) := ((X.baseRingToStructurePresheaf K).app (op U.val)).hom.toAlgebra
    Module.finrank (X.residueField x) (X.residueField x ⊗[Γ(X, U)] Ω[Γ(X, U)⁄K]) = 2 := by
  let : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
  let := (X.evaluation U x hxU).hom.toAlgebra
  let : Algebra K Γ(X, U) := ((X.baseRingToStructurePresheaf K).app (op U.val)).hom.toAlgebra
  have := finiteType_sections_of_locallyOfFiniteType K X U
  have hI := X.singularLocus_ideal (R := K) U
  have : Algebra.FormallyUnramified K (Γ(X, U) ⧸ fittingIdeal Γ(X, U) Ω[Γ(X, U)⁄K] 1) :=
    hI ▸ X.formallyUnramified_quotient_singularLocus_ideal hnodal U
  refine finrank_tensor_kaehlerDifferential_eq_two ?_
  rw [← Ideal.map_eq_bot_iff_le_ker, fittingIdeal_map_eq_bot_iff_lt_finrank]
  exact (Scheme.mem_support_singularLocus_iff (R := K) (X := X) hxU).1 hx

end TauCeti.AlgebraicGeometry
