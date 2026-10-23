/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.UnitIntervalModel
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Basic
public import TauCeti.MeasureTheory.Measure.AtomlessStandardBorel.Transport

/-!
# Every graphon space embeds isometrically in the unit-interval graphon space

Every graphon on an arbitrary probability carrier is at cut distance zero from a graphon on
`(I, volume)` (`exists_graphon_unitInterval_cutDist_eq_zero`, Janson, Theorem 7.1). This file
fixes such a unit-interval representative for each strict graphon and descends the assignment to
the cut-distance quotients: the resulting map `toGraphonSpaceI : GraphonSpace Ω μ → GraphonSpaceI`
is an isometry, and it is the identity on `GraphonSpaceI` itself.

The embedding is the bridge from the canonical carrier back to arbitrary fixed carriers: every
fixed-carrier graphon space is isometric to a subspace of the canonical one, so the metric
properties of `GraphonSpaceI` that pass to subspaces -- total boundedness in the first place --
hold on every fixed-carrier graphon space. The embedding also preserves homomorphism densities;
see `homDensityOnSpace_toGraphonSpaceI` in `GraphonSpace/HomDensity.lean`.

Over an atomless standard Borel carrier the embedding is onto: such a carrier maps
measure-preservingly onto `(I, volume)`
(`MeasureTheory.Measure.exists_measurePreserving_of_nullSingleton`), so every graphon, on any
carrier, is at cut distance zero from a graphon on it. The graphon space over such a carrier is then
isometric to the unit-interval graphon space, and every metric property of `GraphonSpaceI` --
compactness in the first place -- transfers to it.

## Main definitions

* `TauCeti.DenseGraphLimits.Graphon.unitIntervalRepr` -- a unit-interval graphon at cut distance
  zero from a given graphon on an arbitrary probability carrier;
* `TauCeti.DenseGraphLimits.toGraphonSpaceI` -- the induced map on graphon spaces;
* `TauCeti.DenseGraphLimits.isometryEquivGraphonSpaceI` -- over an atomless standard Borel
  carrier, the induced map as an isometry equivalence.

## Main results

* `TauCeti.DenseGraphLimits.Graphon.cutDist_unitIntervalRepr_left` and
  `TauCeti.DenseGraphLimits.Graphon.cutDist_unitIntervalRepr_right` -- the representative has the
  same cut distance to every graphon as the original;
* `TauCeti.DenseGraphLimits.Graphon.isometry_unitIntervalRepr` -- taking representatives is an
  isometry of strict graphons;
* `TauCeti.DenseGraphLimits.isometry_toGraphonSpaceI` -- the induced map is an isometry;
* `TauCeti.DenseGraphLimits.toGraphonSpaceI_eq_self` -- on the unit-interval graphon space the
  induced map is the identity;
* `TauCeti.DenseGraphLimits.exists_graphon_cutDist_eq_zero` -- every graphon is at cut distance
  zero from a graphon on a given atomless standard Borel carrier;
* `TauCeti.DenseGraphLimits.toGraphonSpaceI_surjective` -- over an atomless standard Borel
  carrier the induced map is onto.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Theorem 7.1 and Theorem A.7.
-/

public section

noncomputable section

open MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {μ' : Measure Ω'}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

namespace Graphon

/-- A graphon on the unit interval at cut distance zero from `W`, for `W` on an arbitrary
probability carrier.

The representative is an arbitrary choice; `cutDist_unitIntervalRepr_left` and
`cutDist_unitIntervalRepr_right` show that no cut distance depends on it. -/
def unitIntervalRepr (W : Graphon Ω μ) : Graphon I (volume : Measure I) :=
  (exists_graphon_unitInterval_cutDist_eq_zero W).choose

/-- The unit-interval representative is at cut distance zero from the graphon it represents. -/
theorem cutDist_unitIntervalRepr (W : Graphon Ω μ) : cutDist W W.unitIntervalRepr = 0 :=
  (exists_graphon_unitInterval_cutDist_eq_zero W).choose_spec

/-- The unit-interval representative has the same cut distance to every graphon as the original
graphon. -/
@[simp]
theorem cutDist_unitIntervalRepr_left (W : Graphon Ω μ) (X : Graphon Ω' μ') :
    cutDist W.unitIntervalRepr X = cutDist W X :=
  (cutDist_congr_left (cutDist_unitIntervalRepr W) X).symm

/-- Every graphon has the same cut distance to the unit-interval representative as to the original
graphon. -/
@[simp]
theorem cutDist_unitIntervalRepr_right (X : Graphon Ω' μ') (W : Graphon Ω μ) :
    cutDist X W.unitIntervalRepr = cutDist X W :=
  (cutDist_congr_right (cutDist_unitIntervalRepr W) X).symm

/-- Taking unit-interval representatives is an isometry for the cut-distance pseudometrics on
strict graphons. -/
theorem isometry_unitIntervalRepr : Isometry (unitIntervalRepr (μ := μ)) :=
  Isometry.of_dist_eq fun U W => by
    simp only [dist_eq_cutDist, cutDist_unitIntervalRepr_left, cutDist_unitIntervalRepr_right]

end Graphon

/-- The map from the graphon space over an arbitrary probability carrier to the unit-interval
graphon space, sending the class of a graphon to the class of its unit-interval representative:
the descent of the isometry `Graphon.unitIntervalRepr` to the cut-distance quotients.

It is an isometry (`isometry_toGraphonSpaceI`). -/
def toGraphonSpaceI : GraphonSpace Ω μ → GraphonSpaceI :=
  SeparationQuotient.map Graphon.unitIntervalRepr

/-- The embedding sends the class of a graphon to the class of its unit-interval
representative. -/
@[simp]
theorem toGraphonSpaceI_mk (W : Graphon Ω μ) :
    toGraphonSpaceI (SeparationQuotient.mk W) = SeparationQuotient.mk W.unitIntervalRepr :=
  SeparationQuotient.map_mk Graphon.isometry_unitIntervalRepr.uniformContinuous W

/-- **Every graphon space embeds isometrically in the unit-interval graphon space.** -/
theorem isometry_toGraphonSpaceI : Isometry (toGraphonSpaceI (μ := μ)) := by
  refine Isometry.of_dist_eq (SeparationQuotient.surjective_mk.forall₂.2 fun U W => ?_)
  simp

/-- On the unit-interval graphon space the embedding is the identity. -/
@[simp]
theorem toGraphonSpaceI_eq_self (x : GraphonSpaceI) : toGraphonSpaceI x = x := by
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  simp

section Atomless

variable [StandardBorelSpace Ω] [NullSingletonClass μ]

variable (μ) in
/-- **Every graphon is represented on every atomless standard Borel carrier**: a graphon on an
arbitrary probability carrier is at cut distance zero from a graphon on `(Ω, μ)` whenever `Ω` is
standard Borel and `μ` has no atoms.

This generalizes `exists_graphon_unitInterval_cutDist_eq_zero`, which represents every graphon on
the particular atomless carrier `(I, volume)`, to every atomless standard Borel carrier. -/
theorem exists_graphon_cutDist_eq_zero (V : Graphon Ω' μ') :
    ∃ W : Graphon Ω μ, cutDist V W = 0 := by
  obtain ⟨f, hf⟩ := Measure.exists_measurePreserving_of_nullSingleton μ (volume : Measure I)
  refine ⟨V.unitIntervalRepr.comap f hf.measurable μ, ?_⟩
  rw [← Graphon.cutDist_unitIntervalRepr_left, cutDist_comap_right _ _ hf, cutDist_self]

/-- Over an atomless standard Borel carrier the embedding into the unit-interval graphon space is
onto. -/
theorem toGraphonSpaceI_surjective : Function.Surjective (toGraphonSpaceI (μ := μ)) := by
  refine SeparationQuotient.surjective_mk.forall.2 fun V => ?_
  obtain ⟨W, hW⟩ := exists_graphon_cutDist_eq_zero μ V
  exact ⟨SeparationQuotient.mk W, by simpa using (cutDist_comm W V).trans hW⟩

/-- **The graphon space over an atomless standard Borel carrier is isometric to the unit-interval
graphon space**, through the embedding `toGraphonSpaceI`. -/
def isometryEquivGraphonSpaceI : GraphonSpace Ω μ ≃ᵢ GraphonSpaceI where
  toEquiv := .ofBijective toGraphonSpaceI
    ⟨isometry_toGraphonSpaceI.injective, toGraphonSpaceI_surjective⟩
  isometry_toFun := isometry_toGraphonSpaceI

/-- The isometry equivalence acts as the embedding `toGraphonSpaceI`. -/
@[simp]
theorem coe_isometryEquivGraphonSpaceI :
    ⇑(isometryEquivGraphonSpaceI (μ := μ)) = toGraphonSpaceI :=
  (rfl)

/-- The inverse isometry sends the class of a unit-interval graphon `V` to the class of any graphon
on `(Ω, μ)` at cut distance zero from `V`. -/
@[simp]
theorem isometryEquivGraphonSpaceI_symm_mk_eq_mk_iff (V : Graphon I (volume : Measure I))
    (W : Graphon Ω μ) :
    isometryEquivGraphonSpaceI.symm (SeparationQuotient.mk V) = SeparationQuotient.mk W ↔
      cutDist V W = 0 := by
  simp [IsometryEquiv.symm_apply_eq]

end Atomless

end DenseGraphLimits

end TauCeti
