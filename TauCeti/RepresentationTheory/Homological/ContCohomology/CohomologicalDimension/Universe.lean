/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Universe
import Mathlib.Algebra.Group.ULift
import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2.Character

/-!
# Independence of cohomological dimension from the redundant coefficient universe

For a topological group `G : Type u` and an auxiliary universe `v`, the predicates
`CohomologicalDimensionLE.{v} p G n` and `StrictCohomologicalDimensionLE.{v} p G n` quantify over
discrete `G`-modules `M : Type (max u v)`. Replacing `v` by `max u v` leaves the domain of
quantification `Type (max u (max u v)) = Type (max u v)` unchanged, while replacing the continuous
cohomology objects `continuousCohomology.{0, u, v} i (ofDiscreteModule ℤ G M)` inside the
predicates with `continuousCohomology.{0, u, max u v} i (ofDiscreteModule ℤ G M)`.

In particular, at `v = 0` (`max u 0 = u`), the invariants `cohomologicalDimensionAt.{u} p G` and
`cohomologicalDimensionAt.{0} p G` (and likewise `strictCohomologicalDimensionAt.{u} p G` and
`strictCohomologicalDimensionAt.{0} p G`) test the exact same discrete `G`-modules `M : Type u`
through two universe instantiations of Mathlib's continuous cohomology that are not definitionally
equal. Several results whose proofs pass through the long exact sequence in `Type u` fix the
auxiliary universe parameter to `u`, whereas callers that omit the explicit universe parameter
obtain `0`.

This file transports both vanishing predicates and all three dimension invariants across the
canonical comparison isomorphism `TopRep.continuousCohomologyUniverseIso` of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Universe`, first comparing `max u v` with
`v` for an arbitrary universe `v` and then specializing to `v = 0` (`u` versus `0`), with no
compactness, profiniteness, or size assumption on `G`.

## Main results

* `TauCeti.cohomologicalDimensionLE_max_iff` and `TauCeti.strictCohomologicalDimensionLE_max_iff`:
  `CohomologicalDimensionLE` and `StrictCohomologicalDimensionLE` at `max u v` agree with those at
  `v`.
* `TauCeti.cohomologicalDimensionAt_max_eq`, `TauCeti.strictCohomologicalDimensionAt_max_eq`, and
  `TauCeti.cohomologicalDimension_max_eq`: `cd_p`, `scd_p`, and `cd` at `max u v` equal those at
  `v`.
* `TauCeti.cohomologicalDimensionLE_universe_iff` and
  `TauCeti.strictCohomologicalDimensionLE_universe_iff`: at `v = u` and `v = 0` the vanishing
  predicates coincide.
* `TauCeti.cohomologicalDimensionAt_universe_eq`,
  `TauCeti.strictCohomologicalDimensionAt_universe_eq`, and
  `TauCeti.cohomologicalDimension_universe_eq`: `cd_p G`, `scd_p G`, and `cd G` at `v = u` equal
  their counterparts at `v = 0`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III §3,
  (3.3.1).
* J.-P. Serre, *Galois Cohomology*, Ch. I §3.1.
-/

public section

namespace TauCeti

open CategoryTheory

/-! ### Comparison between `max u v` and `v` -/

section MaxUniverse

universe v u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `CohomologicalDimensionLE` descends from the auxiliary universe `max u v` to `v`. -/
theorem CohomologicalDimensionLE.of_max {n : ℕ}
    (h : CohomologicalDimensionLE.{max u v} p G n) :
    CohomologicalDimensionLE.{v} p G n := by
  rw [cohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ hM i hi
  have := h M hM i hi
  exact ((ofDiscreteModule ℤ G M).continuousCohomologyUniverseIso.{v}
    i).symm.toContinuousLinearEquiv.toEquiv.subsingleton

/-- `CohomologicalDimensionLE` lifts from the auxiliary universe `v` to `max u v`. -/
theorem CohomologicalDimensionLE.to_max {n : ℕ}
    (h : CohomologicalDimensionLE.{v} p G n) :
    CohomologicalDimensionLE.{max u v} p G n := by
  rw [cohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ hM i hi
  have := h M hM i hi
  exact ((ofDiscreteModule ℤ G M).continuousCohomologyUniverseIso.{v}
    i).toContinuousLinearEquiv.toEquiv.subsingleton

/-- The ordinary vanishing predicate at `max u v` is equivalent to that at `v`. -/
theorem cohomologicalDimensionLE_max_iff {n : ℕ} :
    CohomologicalDimensionLE.{max u v} p G n ↔ CohomologicalDimensionLE.{v} p G n :=
  ⟨CohomologicalDimensionLE.of_max, CohomologicalDimensionLE.to_max⟩

/-- `StrictCohomologicalDimensionLE` descends from the auxiliary universe `max u v` to `v`. -/
theorem StrictCohomologicalDimensionLE.of_max {n : ℕ}
    (h : StrictCohomologicalDimensionLE.{max u v} p G n) :
    StrictCohomologicalDimensionLE.{v} p G n := by
  rw [strictCohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ i hi
  let e := ((ofDiscreteModule ℤ G M).continuousCohomologyUniverseIso.{v}
    i).toContinuousLinearEquiv.toLinearEquiv.toAddEquiv
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun y hy ↦ ?_
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.1 hy
  have hx : e.symm y ∈ AddCommGroup.primaryComponent
      (continuousCohomology.{0, u, max u v} i (ofDiscreteModule ℤ G M)) p :=
    AddCommGroup.mem_primaryComponent.2 ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  rw [h M i hi, AddSubgroup.mem_bot] at hx
  exact e.symm.injective (hx.trans (map_zero e.symm).symm)

/-- `StrictCohomologicalDimensionLE` lifts from the auxiliary universe `v` to `max u v`. -/
theorem StrictCohomologicalDimensionLE.to_max {n : ℕ}
    (h : StrictCohomologicalDimensionLE.{v} p G n) :
    StrictCohomologicalDimensionLE.{max u v} p G n := by
  rw [strictCohomologicalDimensionLE_iff] at h ⊢
  intro M _ _ _ _ _ i hi
  let e := ((ofDiscreteModule ℤ G M).continuousCohomologyUniverseIso.{v}
    i).toContinuousLinearEquiv.toLinearEquiv.toAddEquiv
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun x hx ↦ ?_
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.1 hx
  have hy : e x ∈ AddCommGroup.primaryComponent
      (continuousCohomology.{0, u, v} i (ofDiscreteModule ℤ G M)) p :=
    AddCommGroup.mem_primaryComponent.2 ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  rw [h M i hi, AddSubgroup.mem_bot] at hy
  exact e.injective (hy.trans (map_zero e).symm)

/-- The strict vanishing predicate at `max u v` is equivalent to that at `v`. -/
theorem strictCohomologicalDimensionLE_max_iff {n : ℕ} :
    StrictCohomologicalDimensionLE.{max u v} p G n ↔ StrictCohomologicalDimensionLE.{v} p G n :=
  ⟨StrictCohomologicalDimensionLE.of_max, StrictCohomologicalDimensionLE.to_max⟩

variable (p G)

-- None of the universe-equality theorems below carry `@[simp]`: over `G : Type 0` (or whenever
-- `max u v` and `v` unify), both sides have the same head symbol and identical arguments, so a
-- `simp` attribute would loop.

/-- The `p`-cohomological dimension at `max u v` equals that at `v`. -/
theorem cohomologicalDimensionAt_max_eq :
    cohomologicalDimensionAt.{max u v} p G = cohomologicalDimensionAt.{v} p G := by
  refine le_antisymm ?_ ?_
  · induction h : cohomologicalDimensionAt.{v} p G using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      exact (cohomologicalDimensionAt_le_iff p G n).2
        (((cohomologicalDimensionAt_le_iff p G n).1 h.le).to_max)
  · induction h : cohomologicalDimensionAt.{max u v} p G using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      exact (cohomologicalDimensionAt_le_iff p G n).2
        (((cohomologicalDimensionAt_le_iff p G n).1 h.le).of_max)

/-- The strict `p`-cohomological dimension at `max u v` equals that at `v`. -/
theorem strictCohomologicalDimensionAt_max_eq :
    strictCohomologicalDimensionAt.{max u v} p G = strictCohomologicalDimensionAt.{v} p G := by
  refine le_antisymm ?_ ?_
  · induction h : strictCohomologicalDimensionAt.{v} p G using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      exact (strictCohomologicalDimensionAt_le_iff p G n).2
        (((strictCohomologicalDimensionAt_le_iff p G n).1 h.le).to_max)
  · induction h : strictCohomologicalDimensionAt.{max u v} p G using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      exact (strictCohomologicalDimensionAt_le_iff p G n).2
        (((strictCohomologicalDimensionAt_le_iff p G n).1 h.le).of_max)

/-- The cohomological dimension at `max u v` equals that at `v`. -/
theorem cohomologicalDimension_max_eq :
    cohomologicalDimension.{max u v} G = cohomologicalDimension.{v} G := by
  refine le_antisymm ?_ ?_
  · induction h : cohomologicalDimension.{v} G using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      exact (cohomologicalDimension_le_iff G n).2 fun q hq ↦
        (((cohomologicalDimension_le_iff G n).1 h.le q hq).to_max)
  · induction h : cohomologicalDimension.{max u v} G using ENat.recTopCoe with
    | top => exact le_top
    | coe n =>
      exact (cohomologicalDimension_le_iff G n).2 fun q hq ↦
        (((cohomologicalDimension_le_iff G n).1 h.le q hq).of_max)

end MaxUniverse

/-! ### Independence of the extra coefficient universe (`v = u` versus `v = 0`) -/

section UniverseEq

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For `G : Type u`, `CohomologicalDimensionLE` at `v = u` is equivalent to that at `v = 0`. -/
theorem cohomologicalDimensionLE_universe_iff {n : ℕ} :
    CohomologicalDimensionLE.{u} p G n ↔ CohomologicalDimensionLE.{0} p G n :=
  cohomologicalDimensionLE_max_iff.{0}

/-- For `G : Type u`, `StrictCohomologicalDimensionLE` at `v = u` is equivalent to that at
`v = 0`. -/
theorem strictCohomologicalDimensionLE_universe_iff {n : ℕ} :
    StrictCohomologicalDimensionLE.{u} p G n ↔ StrictCohomologicalDimensionLE.{0} p G n :=
  strictCohomologicalDimensionLE_max_iff.{0}

variable (p G)

/-- **`cd_p` does not depend on the redundant coefficient universe**: for every topological group
`G : Type u`, `cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G`. -/
theorem cohomologicalDimensionAt_universe_eq :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{0} p G :=
  cohomologicalDimensionAt_max_eq.{0} p G

/-- **`scd_p` does not depend on the redundant coefficient universe**: for every topological group
`G : Type u`, `strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G`. -/
theorem strictCohomologicalDimensionAt_universe_eq :
    strictCohomologicalDimensionAt.{u} p G = strictCohomologicalDimensionAt.{0} p G :=
  strictCohomologicalDimensionAt_max_eq.{0} p G

/-- **`cd` does not depend on the redundant coefficient universe**: for every topological group
`G : Type u`, `cohomologicalDimension.{u} G = cohomologicalDimension.{0} G`. -/
theorem cohomologicalDimension_universe_eq :
    cohomologicalDimension.{u} G = cohomologicalDimension.{0} G :=
  cohomologicalDimension_max_eq.{0} G

end UniverseEq

/-! ### Concrete checks of the comparison on low-degree classes -/

section Examples

open TauCeti.ContinuousCohomology TauCeti.ContCohomology

universe u

/-- Over the trivial group `PUnit.{u + 1}` with coefficients `ULift.{u} ℤ` in degree `0`, the
universe comparison sends the class of `1` to the class of `1` (and not to its negation). -/
example :
    let X := TopRep.of (ContRepresentation.trivial ℤ PUnit.{u + 1} (ULift.{u} ℤ))
    let h1 : ∀ g : PUnit.{u + 1}, X.ρ g (ULift.up (1 : ℤ)) = ULift.up 1 :=
      fun g ↦ ContRepresentation.trivial_apply g _
    (X.continuousCohomologyUniverseIso.{0} 0).hom (degreeZeroClass.{0, u, u} X (ULift.up 1) h1) =
      degreeZeroClass.{0, u, 0} X (ULift.up 1) h1 ∧
    (X.continuousCohomologyUniverseIso.{0} 0).hom (degreeZeroClass.{0, u, u} X (ULift.up 1) h1) ≠
      -degreeZeroClass.{0, u, 0} X (ULift.up 1) h1 := by
  intro X h1
  refine ⟨continuousCohomologyUniverseIso_hom_degreeZeroClass.{0} X (ULift.up 1) h1, ?_⟩
  rw [continuousCohomologyUniverseIso_hom_degreeZeroClass.{0}]
  intro h
  have hval := congrArg
    (fun c ↦ (((_root_.ContinuousCohomology.zeroIso.{0, u, 0} X).hom c : X.V)).down) h
  rw [map_neg, NegMemClass.coe_neg, coe_zeroIso_hom_degreeZeroClass] at hval
  have h1 : (1 : ℤ) = -1 := hval
  omega

/-- Naturality in degree `0` for multiplication by `2` on the trivial module `ULift.{u} ℤ`: both
paths around the square send the class of `1` to the class of `2`. -/
example (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    let X := TopRep.of (ContRepresentation.trivial ℤ G (ULift.{u} ℤ))
    let clm : ULift.{u} ℤ →L[ℤ] ULift.{u} ℤ :=
      ContinuousLinearMap.id ℤ (ULift.{u} ℤ) + ContinuousLinearMap.id ℤ (ULift.{u} ℤ)
    let f : X ⟶ X := TopRep.ofHom ⟨clm, fun g ↦ by
      ext x
      simp [clm, ContRepresentation.trivial_apply]⟩
    let h1 : ∀ g : G, X.ρ g (ULift.up (1 : ℤ)) = ULift.up 1 :=
      fun g ↦ ContRepresentation.trivial_apply g _
    let h2 : ∀ g : G, X.ρ g (ULift.up (2 : ℤ)) = ULift.up 2 :=
      fun g ↦ ContRepresentation.trivial_apply g _
    (X.continuousCohomologyUniverseIso.{0} 0).hom
        (coeffMap.{0, u, u} f 0 (degreeZeroClass.{0, u, u} X (ULift.up 1) h1)) =
      degreeZeroClass.{0, u, 0} X (ULift.up 2) h2 ∧
    coeffMap.{0, u, 0} f 0
        ((X.continuousCohomologyUniverseIso.{0} 0).hom
          (degreeZeroClass.{0, u, u} X (ULift.up 1) h1)) =
      degreeZeroClass.{0, u, 0} X (ULift.up 2) h2 := by
  intro X clm f h1 h2
  have hf : f.hom (ULift.up (1 : ℤ)) = ULift.up 2 := rfl
  have hpath2 : coeffMap.{0, u, 0} f 0
      ((X.continuousCohomologyUniverseIso.{0} 0).hom
        (degreeZeroClass.{0, u, u} X (ULift.up 1) h1)) =
      degreeZeroClass.{0, u, 0} X (ULift.up 2) h2 := by
    rw [continuousCohomologyUniverseIso_hom_degreeZeroClass.{0}]
    apply (_root_.ContinuousCohomology.zeroIso.{0, u, 0} X).toContinuousLinearEquiv.injective
    apply Subtype.ext
    have hcoeff := ConcreteCategory.congr_hom (coeffMap_comp_zeroIso_hom.{0, u, 0} f)
      (degreeZeroClass.{0, u, 0} X (ULift.up 1) h1)
    simp only [ConcreteCategory.comp_apply] at hcoeff
    rw [Iso.toContinuousLinearEquiv_apply, Iso.toContinuousLinearEquiv_apply, hcoeff]
    simp only [ConcreteCategory.hom_ofHom, ContIntertwiningMap.mapInvariants_apply,
      coe_zeroIso_hom_degreeZeroClass]
    exact hf
  refine ⟨?_, hpath2⟩
  have hsq := ConcreteCategory.congr_hom
    (coeffMap_comp_continuousCohomologyUniverseIso_hom.{0} f 0)
    (degreeZeroClass.{0, u, u} X (ULift.up 1) h1)
  simp only [ConcreteCategory.comp_apply] at hsq
  exact hsq.trans hpath2

/-- Over `C₂ = ULift.{u} (Multiplicative (ZMod 2))` with trivial `𝔽₂` coefficients in degree `1`,
the identity character has nonzero cohomology class and the universe comparison sends it to a
nonzero class. -/
example :
    let G := ULift.{u} (Multiplicative (ZMod 2))
    let α : G →* Multiplicative (ZMod 2) := MulEquiv.ulift.toMonoidHom
    ((trivialF2 G).continuousCohomologyUniverseIso.{0} 1).hom
      (homClass G α continuous_of_discreteTopology) ≠ 0 := by
  intro G α
  have hα : α ≠ 1 := fun h ↦ by
    have h1 : α (ULift.up (Multiplicative.ofAdd (1 : ZMod 2))) = 1 :=
      DFunLike.congr_fun h (ULift.up (Multiplicative.ofAdd (1 : ZMod 2)))
    exact Nat.one_ne_zero (congrArg Fin.val (Multiplicative.ofAdd.injective h1))
  have hc : homClass G α continuous_of_discreteTopology ≠ 0 := by
    rw [← homClass_one (H := G), ne_eq, homClass_inj]
    exact hα
  intro h0
  apply hc
  exact (ConcreteCategory.bijective_of_isIso
    ((trivialF2 G).continuousCohomologyUniverseIso.{0} 1).hom).1
    (h0.trans (_root_.map_zero _).symm)

end Examples

end TauCeti
