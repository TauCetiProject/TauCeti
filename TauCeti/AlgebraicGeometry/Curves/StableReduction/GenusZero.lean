/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Genus.Zero
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.ProjectiveLine
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NodalReduction

/-!
# Nodal reduction of curves of genus zero with a divisor of degree one

Let `R` be a discrete valuation ring with fraction field `K`. The projective line `ℙ¹_R` is a
smooth proper model over `R` of the projective line `ℙ¹_K` (`TauCeti.Model.projectiveLine`).
Consequently `ℙ¹_K` has nodal reduction, indeed good reduction, over `R`.

A regular proper curve of genus zero over `K` with a divisor of degree one, for instance with a
`K`-rational point, and with `K` integrally closed in its function field, is isomorphic to `ℙ¹_K`
(`AlgebraicGeometry.Scheme.exists_iso_projectiveLine_of_genus_eq_zero_of_divisor_degree_eq_one`).
Since nodal reduction only depends on the curve up to isomorphism over `K`, every such curve has
nodal reduction over `R`, without any extension of `R`. This is the case of a curve of genus zero
whose generic fibre already has a divisor of degree one; in general a curve of genus zero acquires
a rational point only after a finite separable extension of `K`.

## Main results

* `TauCeti.HasNodalReduction.projectiveLine`: `ℙ¹_K` has nodal reduction over `R`.
* `TauCeti.HasNodalReduction.of_genus_eq_zero_of_divisor_degree_eq_one`: a regular proper curve
  of genus zero over `K` with a divisor of degree one has nodal reduction over `R`.

## References

* [The Stacks Project, Chapter 55, Semistable Reduction](https://stacks.math.columbia.edu/tag/0C2P)
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002,
  Section 10.1: models of curves.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Module (finrank)

namespace TauCeti

universe u

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

namespace HasNodalReduction

/-- **The projective line has nodal reduction**: `ℙ¹_R` is a smooth proper model of `ℙ¹_K`. -/
theorem projectiveLine :
    HasNodalReduction R K (AlgebraicGeometry.projectiveLine K)
      (AlgebraicGeometry.projectiveLine K ↘ Spec (.of K)) :=
  of_smooth_model (Model.projectiveLine R K) (Model.isProper_projectiveLine R K)

variable {R K}

/-- **A curve of genus zero with a divisor of degree one has nodal reduction.** Let `C` be a
regular proper curve over the fraction field `K` of a discrete valuation ring `R`, with `K`
integrally closed in `K(C)`. If `dim_K H¹(C, 𝒪_C) = 0` and some divisor on `C` has degree one,
then `C` has a proper at-worst-nodal model over `R`; indeed `C ≅ ℙ¹_K`, which has the smooth proper
model `ℙ¹_R`. -/
theorem of_genus_eq_zero_of_divisor_degree_eq_one (C : Scheme.{u}) [C.Over (Spec (.of K))]
    [C.IsCurveOver K]
    [∀ y : AlgebraicGeometry.CodimensionOnePoint C,
      IsDiscreteValuationRing (C.presheaf.stalk (y : C))]
    (hk : IsIntegrallyClosedIn K C.functionField)
    (hg : finrank K (AlgebraicGeometry.Scheme.Modules.Cohomology
      (AlgebraicGeometry.InvertibleSheaf.trivial C).obj 1) = 0)
    {D : AlgebraicGeometry.SchemeWeilDivisor C}
    (hD : AlgebraicGeometry.SchemeWeilDivisor.relativeDegree (C ↘ Spec (.of K)) D = 1) :
    HasNodalReduction R K C (C ↘ Spec (.of K)) := by
  obtain ⟨e, _⟩ := C.exists_iso_projectiveLine_of_genus_eq_zero_of_divisor_degree_eq_one hk hg hD
  exact (projectiveLine R K).of_iso
    (Over.isoMk (f := Over.mk (AlgebraicGeometry.projectiveLine K ↘ Spec (.of K)))
      (g := Over.mk (C ↘ Spec (.of K))) e.symm (by simp))

end HasNodalReduction

end TauCeti
