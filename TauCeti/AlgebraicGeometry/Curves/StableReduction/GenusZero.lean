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
# Nodal reduction of curves of genus zero

Let `R` be a discrete valuation ring with fraction field `K`. The projective line `ℙ¹_R` is a
smooth proper model over `R` of the projective line `ℙ¹_K` (`TauCeti.Model.projectiveLine`).
Consequently `ℙ¹_K` has nodal reduction, indeed good reduction, over `R`.

A regular proper curve of genus zero over `K` with a divisor of degree one, for instance with a
`K`-rational point, and with `K` integrally closed in its function field, is isomorphic to `ℙ¹_K`
(`AlgebraicGeometry.Scheme.exists_iso_projectiveLine_of_genus_eq_zero_of_divisor_degree_eq_one`).
Since nodal reduction only depends on the curve up to isomorphism over `K`, every such curve has
nodal reduction over `R`, without any extension of `R`. This is the case of a curve of genus zero
whose generic fibre already has a divisor of degree one.

In general a smooth proper geometrically integral curve `C` of genus zero over `K` acquires a
rational point only after a finite separable extension of `K`, and one of degree at most two
suffices: over it, `C` becomes `ℙ¹`
(`AlgebraicGeometry.Scheme.exists_finrank_le_two_and_iso_projectiveLine_of_genus_eq_zero`). Choosing
a place of that extension above the closed point of `R`, with local ring `R'`, the base change of
`C` has the smooth proper model `ℙ¹_{R'}`.

## Main results

* `TauCeti.HasNodalReduction.projectiveLine`: `ℙ¹_K` has nodal reduction over `R`.
* `TauCeti.HasNodalReduction.of_genus_eq_zero_of_divisor_degree_eq_one`: a regular proper curve
  of genus zero over `K` with a divisor of degree one has nodal reduction over `R`.
* `TauCeti.HasNodalReduction.exists_finrank_le_two_of_genus_eq_zero`: a smooth proper
  geometrically integral curve of genus zero over `K` has nodal reduction after a finite separable
  extension of `K` of degree at most two, with a chosen place above the closed point of `R`.

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

/-- **A smooth curve of genus zero has nodal reduction after a separable extension of degree at
most two.** Let `C` be a smooth proper geometrically integral curve over the fraction field `K` of
a discrete valuation ring `R`, with `dim_K H¹(C, 𝒪_C) = 0`. Then there is a finite separable
extension `K'` of `K` of degree at most two, with a chosen place above the closed point of `R` and
local ring `R'`, such that `C_{K'}` has a proper at-worst-nodal model over `R'`; indeed
`C_{K'} ≅ ℙ¹_{K'}`, which has the smooth proper model `ℙ¹_{R'}`. -/
theorem exists_finrank_le_two_of_genus_eq_zero (C : Scheme.{u}) [C.Over (Spec (.of K))]
    [IsProper (C ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
    [GeometricallyIntegral (C ↘ Spec (.of K))]
    (hg : finrank K (AlgebraicGeometry.Scheme.Modules.Cohomology
      (AlgebraicGeometry.InvertibleSheaf.trivial C).obj 1) = 0) :
    ∃ E : FiniteDVRExtension R K, finrank K E.extensionField ≤ 2 ∧
      HasNodalReduction E.localRing E.extensionField
        (genericFiber K E.extensionField (C ↘ Spec (.of K))).left
        (genericFiber K E.extensionField (C ↘ Spec (.of K))).hom := by
  obtain ⟨x, _, hx, _⟩ := C.exists_finrank_residueField_le_two_and_isSeparable_of_genus_eq_zero hg
  let : Algebra R (C.residueField x) :=
    ((algebraMap K (C.residueField x)).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K (C.residueField x) := .of_algebraMap_eq' rfl
  obtain ⟨E, ⟨e⟩⟩ := FiniteDVRExtension.exists_algEquiv_extensionField R K (C.residueField x)
  let _ : (genericFiber K E.extensionField (C ↘ Spec (.of K))).left.Over
      (Spec (.of E.extensionField)) := ⟨(genericFiber K E.extensionField (C ↘ Spec (.of K))).hom⟩
  obtain ⟨f, hf⟩ := C.exists_iso_projectiveLine_of_isPullback_of_genus_eq_zero
    (isPullback_genericFiber K E.extensionField (C ↘ Spec (.of K))) hg x e.symm.toAlgHom
  refine ⟨E, e.toLinearEquiv.finrank_eq ▸ hx, (projectiveLine E.localRing E.extensionField).of_iso
    (Over.isoMk (f := Over.mk (AlgebraicGeometry.projectiveLine E.extensionField ↘
      Spec (.of E.extensionField))) f.symm ?_)⟩
  rw [Iso.symm_hom, Iso.inv_comp_eq]
  exact hf.comp_over.symm

end HasNodalReduction

end TauCeti
