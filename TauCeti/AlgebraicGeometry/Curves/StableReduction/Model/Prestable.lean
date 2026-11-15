/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Prestable
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Basic

/-!
# Nodal and prestable models are detected on two fibres

Let `R` be a discrete valuation ring with fraction field `K` and residue field `k`. Every point of
`Spec R` is its generic or its closed point, so a flat morphism `X ⟶ Spec R` locally of finite
presentation is at worst nodal of relative dimension one exactly when its generic fibre
`X_K ⟶ Spec K` and its special fibre `X_k ⟶ Spec k` are
(`TauCeti.AlgebraicGeometry.atWorstNodalOfRelativeDimensionOne_iff_genericFiber_and_specialFiber`),
and similarly for prestable families
(`TauCeti.AlgebraicGeometry.prestableFamily_iff_genericFiber_and_specialFiber`).

For a model `M` of a curve `C ⟶ Spec K` over `R`, flatness and finite presentation are part of the
data and the generic fibre is identified with `C`. Hence `M` is a nodal model exactly when `C` is a
nodal curve and the special fibre of `M` is a nodal curve over `k`, and `M` is a prestable model
exactly when it is proper and `C` and the special fibre are prestable curves.

## Main results

* `TauCeti.Model.atWorstNodalOfRelativeDimensionOne_toBase_iff`: a model is at worst nodal exactly
  when its generic curve and its special fibre are.
* `TauCeti.Model.prestableFamily_toBase_iff`: a model is prestable exactly when it is proper and
  its generic curve and its special fibre are prestable.

## References

* [The Stacks Project, Section 55.18, Semistable reduction](https://stacks.math.columbia.edu/tag/0CDL)
* [The Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58)
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- A model over a discrete valuation ring is at worst nodal of relative dimension one exactly when
its generic curve and its special fibre are at worst nodal. -/
theorem atWorstNodalOfRelativeDimensionOne_toBase_iff (M : Model R K C toK) :
    AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne M.toBase ↔
      AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne toK ∧
        AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne (specialFiber R M.toBase).hom := by
  rw [AlgebraicGeometry.atWorstNodalOfRelativeDimensionOne_iff_genericFiber_and_specialFiber
    (R := .of R) K, MorphismProperty.over_iso_iff
      @AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne M.genericFiberIso]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨M.flat, M.locallyOfFinitePresentation, h⟩⟩

/-- A model over a discrete valuation ring is a prestable family exactly when it is proper and its
generic curve and its special fibre are prestable curves. -/
theorem prestableFamily_toBase_iff (M : Model R K C toK) :
    AlgebraicGeometry.PrestableFamily M.toBase ↔
      M.IsProper ∧ AlgebraicGeometry.PrestableFamily toK ∧
        AlgebraicGeometry.PrestableFamily (specialFiber R M.toBase).hom := by
  rw [AlgebraicGeometry.prestableFamily_iff_genericFiber_and_specialFiber (R := .of R) K,
    MorphismProperty.over_iso_iff @AlgebraicGeometry.PrestableFamily M.genericFiberIso]
  exact ⟨fun h ↦ ⟨h.1, h.2.2.2⟩,
    fun h ↦ ⟨h.1, M.flat, M.locallyOfFinitePresentation, h.2⟩⟩

end Model

end TauCeti
