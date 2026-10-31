/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Fiber
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NodalReduction
public import TauCeti.AlgebraicGeometry.SpecialFiber.Basic

/-!
# Nodal and prestable models are detected on two fibres

Let `R` be a local domain of Krull dimension at most one, for instance a discrete valuation ring,
with fraction field `K` and residue field `k`. The base `Spec R` has only two points, so the
fibrewise criterion for nodal curves reduces to the generic and the special fibre: a flat morphism
`X ⟶ Spec R` locally of finite presentation is at worst nodal of relative dimension one exactly
when its generic fibre `X_K ⟶ Spec K` and its special fibre `X_k ⟶ Spec k` are. Adding properness
and geometric connectedness of the two fibres gives the same criterion for prestable families.

For a model `M` of a curve `C ⟶ Spec K` over a discrete valuation ring, flatness and finite
presentation are part of the data and the generic fibre is identified with `C`. Hence `M` is a
nodal model exactly when `C` is a nodal curve and the special fibre of `M` is a nodal curve over
`k`, and `M` is a prestable model exactly when it is proper and `C` and the special fibre are
prestable curves. In particular a smooth curve over `K` has nodal reduction as soon as it has a
proper model whose special fibre is at worst nodal: nodal reduction is a condition on the special
fibre of a proper model alone. This is how a regular model whose special fibre has been shown to
be reduced with at worst nodal singularities yields nodal reduction.

## Main results

* `TauCeti.AlgebraicGeometry.atWorstNodalOfRelativeDimensionOne_iff_genericFiber_and_specialFiber`:
  over a local domain of dimension at most one, a morphism is at worst nodal exactly when it is
  flat and locally of finite presentation and its generic and special fibres are at worst nodal.
* `TauCeti.AlgebraicGeometry.prestableFamily_iff_genericFiber_and_specialFiber`: the same
  criterion for prestable families, which are moreover proper.
* `TauCeti.Model.atWorstNodalOfRelativeDimensionOne_toBase_iff`: a model is at worst nodal exactly
  when its generic curve and its special fibre are.
* `TauCeti.Model.prestableFamily_toBase_iff`: a model is prestable exactly when it is proper and
  its generic curve and its special fibre are prestable.
* `TauCeti.hasNodalReduction_iff_exists_specialFiber`: a curve has nodal reduction exactly when it
  is at worst nodal and has a proper model whose special fibre is at worst nodal.

## References

* [The Stacks Project, Section 55.18, Semistable reduction](https://stacks.math.columbia.edu/tag/0CDL)
* [The Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58)
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} [IsLocalRing R] [IsDomain R] [Ring.DimensionLEOne R]
variable (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
variable {X : Scheme.{u}} (toBase : X ⟶ Spec R)

/-- **The two-fibre criterion for nodal curves.** Over a local domain of dimension at most one,
for instance a discrete valuation ring, a morphism is at worst nodal of relative dimension one
exactly when it is flat and locally of finite presentation and both its generic fibre over the
fraction field and its special fibre over the residue field are at worst nodal. -/
theorem atWorstNodalOfRelativeDimensionOne_iff_genericFiber_and_specialFiber :
    AtWorstNodalOfRelativeDimensionOne toBase ↔
      Flat toBase ∧ LocallyOfFinitePresentation toBase ∧
        AtWorstNodalOfRelativeDimensionOne (genericFiber R K toBase).hom ∧
          AtWorstNodalOfRelativeDimensionOne (specialFiber R toBase).hom := by
  rw [atWorstNodalOfRelativeDimensionOne_iff_flat_and_fiberToSpecResidueField,
    forall_fiberToSpecResidueField_iff K toBase]

/-- **The two-fibre criterion for prestable families.** Over a local domain of dimension at most
one, for instance a discrete valuation ring, a morphism is a prestable family exactly when it is
proper, flat and locally of finite presentation and both its generic fibre over the fraction field
and its special fibre over the residue field are prestable curves. -/
theorem prestableFamily_iff_genericFiber_and_specialFiber :
    PrestableFamily toBase ↔
      IsProper toBase ∧ Flat toBase ∧ LocallyOfFinitePresentation toBase ∧
        PrestableFamily (genericFiber R K toBase).hom ∧
          PrestableFamily (specialFiber R toBase).hom := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance,
      .of_isPullback (isPullback_genericFiber R K toBase),
      .of_isPullback (isPullback_specialFiber R toBase)⟩, ?_⟩
  rintro ⟨hp, hf, hl, hg, hs⟩
  refine
    { toIsProper := hp
      toGeometricallyConnected := ?_
      atWorstNodalOfRelativeDimensionOne :=
        (atWorstNodalOfRelativeDimensionOne_iff_genericFiber_and_specialFiber K toBase).mpr
          ⟨hf, hl, hg.atWorstNodalOfRelativeDimensionOne, hs.atWorstNodalOfRelativeDimensionOne⟩ }
  -- Fixing the universe lets instance search find isomorphism invariance.
  have : MorphismProperty.RespectsIso @GeometricallyConnected.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber,
    forall_fiberToSpecResidueField_iff K toBase @GeometricallyConnected]
  exact ⟨hg.toGeometricallyConnected, hs.toGeometricallyConnected⟩

end AlgebraicGeometry

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

namespace HasNodalReduction

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- A nodal curve over `K` has nodal reduction if it has a proper model whose special fibre is at
worst nodal. -/
theorem of_specialFiber (M : Model R K C toK) (hproper : M.IsProper)
    (hC : AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne toK)
    (hs : AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne (specialFiber R M.toBase).hom) :
    HasNodalReduction R K C toK :=
  of_model M hproper (M.atWorstNodalOfRelativeDimensionOne_toBase_iff.mpr ⟨hC, hs⟩)

/-- A smooth curve over `K` has nodal reduction if it has a proper model whose special fibre is at
worst nodal. -/
theorem of_smooth_of_specialFiber [SmoothOfRelativeDimension 1 toK] (M : Model R K C toK)
    (hproper : M.IsProper)
    (hs : AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne (specialFiber R M.toBase).hom) :
    HasNodalReduction R K C toK :=
  of_specialFiber M hproper (AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne.of_smooth toK) hs

/-- A curve with nodal reduction is itself at worst nodal. -/
theorem atWorstNodalOfRelativeDimensionOne (h : HasNodalReduction R K C toK) :
    AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne toK := by
  obtain ⟨M, -, hM⟩ := (hasNodalReduction_iff R K C toK).mp h
  exact MorphismProperty.of_isPullback M.isPullback_genericι hM

end HasNodalReduction

/-- **Nodal reduction is a condition on the special fibre.** A curve over the fraction field of a
discrete valuation ring has nodal reduction exactly when it is at worst nodal and has a proper
model whose special fibre is at worst nodal. -/
theorem hasNodalReduction_iff_exists_specialFiber (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Scheme.{u}) (toK : C ⟶ Spec (.of K)) :
    HasNodalReduction R K C toK ↔
      AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne toK ∧
        ∃ M : Model R K C toK, M.IsProper ∧
          AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne (specialFiber R M.toBase).hom := by
  refine ⟨fun h ↦ ⟨h.atWorstNodalOfRelativeDimensionOne, ?_⟩,
    fun ⟨hC, M, hproper, hs⟩ ↦ .of_specialFiber M hproper hC hs⟩
  obtain ⟨M, hproper, hM⟩ := (hasNodalReduction_iff R K C toK).mp h
  exact ⟨M, hproper, (M.atWorstNodalOfRelativeDimensionOne_toBase_iff.mp hM).2⟩

end TauCeti
