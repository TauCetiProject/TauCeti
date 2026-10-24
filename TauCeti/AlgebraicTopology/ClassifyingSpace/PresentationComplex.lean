/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import TauCeti.AlgebraicTopology.FundamentalGroup.TwoCellAttachment
public import TauCeti.AlgebraicTopology.FundamentalGroup.WedgeSum
public import TauCeti.Topology.CWComplex.Abstract.TwoCellAttachment
public import TauCeti.Topology.CWComplex.Classical.WedgeCircles
import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic

/-!
# The presentation complex of a group presentation

For a group presentation `⟨S | R⟩`, with generators `S` and relators `R ⊆ FreeGroup S`, the
presentation complex `TauCeti.PresentationComplex R` is the 2-dimensional complex with one vertex,
one 1-cell for each generator and one 2-cell for each relator. It is the wedge of circles indexed
by `S`, whose fundamental group is the free group on `S`
(`TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`), with a 2-cell attached along a loop
representing each relator (`TauCeti.TwoCellAttachment`).

The attached cells make the relators trivial in the fundamental group, so sending the generator
`s` to the loop around the `s`-th circle defines a homomorphism
`TauCeti.PresentationComplex.fundamentalGroupHom R` from the presented group `PresentedGroup R`
to the fundamental group of the presentation complex at its vertex.

Every homomorphism `ψ` from the presented group to the fundamental group of a pointed space `Z`
is realized by a based map from the presentation complex to `Z`
(`TauCeti.PresentationComplex.exists_mapOfEq_comp_fundamentalGroupHom`): send the `s`-th circle
to a loop representing `ψ s`, and extend over the 2-cells, which is possible because the image of
each relator is trivial. Applied to the classifying space of the presented group, which is a
`K(G, 1)` whose fundamental group is identified with `G`, this shows that the homomorphism from
the presented group is injective (`TauCeti.PresentationComplex.fundamentalGroupHom_injective`).

It is also surjective, because attaching 2-cells induces a surjection on fundamental groups
(`TauCeti.TwoCellAttachment.surjective_map_incl`). So the fundamental group of the presentation
complex is the presented group (`TauCeti.PresentationComplex.fundamentalGroupMulEquiv`). With no
relators the presentation complex is the wedge of circles, and this is the free group.

The presentation complex is a CW complex (`TauCeti.PresentationComplex.instCWComplex`), built
from the CW structure of the wedge of circles by attaching the 2-cells: its only `0`-cell is the
vertex, its `1`-cells are the circles of the generators
(`TauCeti.PresentationComplex.cellOneEquiv`), its `2`-cells are the disks of the relators
(`TauCeti.PresentationComplex.cellTwoEquiv`), and it has no cells of higher dimension.

## Main definitions

* `TauCeti.PresentationComplex.attachingLoop`: a loop in the wedge of circles representing an
  element of the free group.
* `TauCeti.PresentationComplex R`: the presentation complex of `⟨S | R⟩`.
* `TauCeti.PresentationComplex.basepoint`: its vertex.
* `TauCeti.PresentationComplex.fundamentalGroupHom`: the homomorphism from the presented group to
  the fundamental group of the presentation complex.
* `TauCeti.PresentationComplex.fundamentalGroupMulEquiv`: the isomorphism
  `π₁(PresentationComplex R) ≃* PresentedGroup R`.
* `TauCeti.PresentationComplex.instCWComplex`: the CW structure on the presentation complex.
* `TauCeti.PresentationComplex.cellOneEquiv`, `TauCeti.PresentationComplex.cellTwoEquiv`: its
  `1`-cells are indexed by the generators and its `2`-cells by the relators.

## Main results

* `TauCeti.PresentationComplex.fundamentalGroupHom_of`: the generator `s` goes to the loop around
  the `s`-th circle.
* `TauCeti.PresentationComplex.exists_mapOfEq_comp_fundamentalGroupHom`: every homomorphism from
  the presented group to a fundamental group is induced by a based map.
* `TauCeti.PresentationComplex.fundamentalGroupHom_injective`,
  `TauCeti.PresentationComplex.fundamentalGroupHom_surjective`: the homomorphism from the presented
  group to the fundamental group of the presentation complex is injective and surjective.
* `TauCeti.PresentationComplex.fundamentalGroupMulEquiv_mapOfEq_expLoop`: the isomorphism sends
  the loop around the `s`-th circle to the generator `s`.
* `TauCeti.PresentationComplex.skeletonLT_one`, `TauCeti.PresentationComplex.isEmpty_cell`: the
  `0`-skeleton is the vertex, and there are no cells of dimension at least `3`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.2, Proposition 1.26, Corollary 1.28 and the presentation complex `X_G` described
  before it, and Section 1.B for maps into a `K(G, 1)`.
-/

public section

noncomputable section

namespace TauCeti

open WedgeSum (base circleFundamentalGroupMulEquiv circleFundamentalGroupMulEquiv_expLoop)

universe u v

variable {S : Type u}

/-- A loop in the wedge of circles indexed by `S`, at the wedge point, representing the element
`w` of the free group on `S` under `WedgeSum.circleFundamentalGroupMulEquiv`. -/
def PresentationComplex.attachingLoop (w : FreeGroup S) :
    Path (base fun _ : S => (1 : Circle)) (base fun _ : S => (1 : Circle)) :=
  Quotient.out (FundamentalGroup.toPath ((circleFundamentalGroupMulEquiv S).symm w))

/-- The loop `attachingLoop w` represents `w`. -/
@[simp]
theorem PresentationComplex.circleFundamentalGroupMulEquiv_attachingLoop (w : FreeGroup S) :
    circleFundamentalGroupMulEquiv S
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (attachingLoop w))) = w := by
  rw [← MulEquiv.eq_symm_apply]
  exact FundamentalGroup.fromPath_mk_out _

/-- The **presentation complex** of the presentation `⟨S | R⟩`: the wedge of circles indexed by
the generators `S`, with a 2-cell attached along the loop `attachingLoop r` for each relator
`r ∈ R`. It has one vertex, one 1-cell for each generator and one 2-cell for each relator. -/
abbrev PresentationComplex (R : Set (FreeGroup S)) : Type u :=
  TwoCellAttachment fun r : R => PresentationComplex.attachingLoop r.1

namespace PresentationComplex

variable (R : Set (FreeGroup S))

/-- The inclusion of the wedge of circles, the 1-skeleton of the presentation complex. -/
abbrev incl : C(WedgeSum fun _ : S => (1 : Circle), PresentationComplex R) :=
  TwoCellAttachment.incl _

/-- The vertex of the presentation complex, the image of the wedge point. -/
abbrev basepoint : PresentationComplex R :=
  incl R (base _)

/-- The homomorphism from the presented group `PresentedGroup R` to the fundamental group of the
presentation complex at its vertex, sending the generator `s` to the loop around the `s`-th
circle. It is well defined because the 2-cells make the relators trivial. -/
def fundamentalGroupHom :
    PresentedGroup R →* FundamentalGroup (PresentationComplex R) (basepoint R) :=
  PresentedGroup.toGroup (f := fun s => FundamentalGroup.map (incl R) _
    ((circleFundamentalGroupMulEquiv S).symm (FreeGroup.of s))) fun r hr => by
    have h : FreeGroup.lift (fun s => FundamentalGroup.map (incl R) _
        ((circleFundamentalGroupMulEquiv S).symm (FreeGroup.of s))) =
        (FundamentalGroup.map (incl R) _).comp
          (circleFundamentalGroupMulEquiv S).symm.toMonoidHom :=
      FreeGroup.ext_hom _ _ fun s => by simp
    rw [h, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      (MulEquiv.symm_apply_eq _).2 (circleFundamentalGroupMulEquiv_attachingLoop r).symm]
    exact TwoCellAttachment.map_incl_fromPath (γ := fun r : R => attachingLoop r.1) ⟨r, hr⟩

variable {R}

/-- The homomorphism from the presented group is induced by the inclusion of the wedge of
circles, through the identification of its fundamental group with the free group. -/
theorem fundamentalGroupHom_mk (w : FreeGroup S) :
    fundamentalGroupHom R (PresentedGroup.mk R w) =
      FundamentalGroup.map (incl R) _
        ((circleFundamentalGroupMulEquiv S).symm w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of s => exact PresentedGroup.toGroup.of _
  | inv_of s h => simp only [map_inv, h]
  | mul w₁ w₂ h₁ h₂ => simp only [map_mul, h₁, h₂]

/-- **The generator `s` goes to the loop around the `s`-th circle.** -/
theorem fundamentalGroupHom_of (s : S) :
    fundamentalGroupHom R (PresentedGroup.of s) =
      FundamentalGroup.mapOfEq ((incl R).comp (WedgeSum.incl _ s))
        (congrArg (incl R) (WedgeSum.incl_apply_self s))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop)) := by
  rw [fundamentalGroupHom, PresentedGroup.toGroup.of,
    (MulEquiv.symm_apply_eq _).2 (circleFundamentalGroupMulEquiv_expLoop s).symm,
    ← TauCeti.FundamentalGroup.mapOfEq_rfl, TauCeti.FundamentalGroup.mapOfEq_comp]

/-- **Homomorphisms out of the presented group are induced by based maps.** For a pointed space
`(Z, z)`, every homomorphism `ψ` from the presented group to `π₁(Z, z)` is the map induced on
fundamental groups by a based map from the presentation complex to `Z`, composed with
`fundamentalGroupHom R`. The map sends the `s`-th circle around a loop representing `ψ s`, and
extends over the 2-cells because `ψ` kills the relators. -/
theorem exists_mapOfEq_comp_fundamentalGroupHom {Z : Type v} [TopologicalSpace Z] {z : Z}
    (ψ : PresentedGroup R →* FundamentalGroup Z z) :
    ∃ (f : C(PresentationComplex R, Z)) (hf : f (basepoint R) = z),
      (FundamentalGroup.mapOfEq f hf).comp (fundamentalGroupHom R) = ψ := by
  -- The `s`-th circle goes around a loop representing `ψ s`.
  let δ (s : S) : Path z z :=
    Quotient.out (FundamentalGroup.toPath (ψ (PresentedGroup.mk R (FreeGroup.of s))))
  have hδ (s : S) : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (δ s)) =
      ψ (PresentedGroup.mk R (FreeGroup.of s)) :=
    FundamentalGroup.fromPath_mk_out _
  let f₀ := WedgeSum.lift (fun s => (δ s).toCircle) z fun s => (δ s).toCircle_one
  have hf₀ : f₀ (base _) = z := WedgeSum.lift_base _ _ _
  -- On the wedge of circles, `f₀` induces `ψ` composed with the quotient map of the free group.
  have key (w : FreeGroup S) : FundamentalGroup.mapOfEq f₀ hf₀
      ((circleFundamentalGroupMulEquiv S).symm w) = ψ (PresentedGroup.mk R w) := by
    refine DFunLike.congr_fun (FreeGroup.ext_hom ((FundamentalGroup.mapOfEq f₀ hf₀).comp
      (circleFundamentalGroupMulEquiv S).symm.toMonoidHom) (ψ.comp (PresentedGroup.mk R))
      fun s => ?_) w
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      (MulEquiv.symm_apply_eq _).2 (circleFundamentalGroupMulEquiv_expLoop s).symm,
      TauCeti.FundamentalGroup.mapOfEq_comp,
      TauCeti.FundamentalGroup.mapOfEq_congr (f₂ := (δ s).toCircle)
        (ContinuousMap.ext fun _ => WedgeSum.lift_incl _ _ _ s _) _ (δ s).toCircle_one,
      Circle.mapOfEq_toCircle_expLoop, hδ]
  -- So `f₀` makes every relator nullhomotopic, and extends over the 2-cells.
  obtain ⟨f, hf⟩ := (TwoCellAttachment.exists_comp_incl_eq_iff f₀).2 fun r : R =>
    (TauCeti.FundamentalGroup.mapOfEq_fromPath_eq_one_iff f₀ hf₀ _).1 <| by
      rw [← (MulEquiv.symm_apply_eq _).2 (circleFundamentalGroupMulEquiv_attachingLoop r.1).symm,
        key, PresentedGroup.one_of_mem r.2, map_one]
  have hfb : f (basepoint R) = z := by
    rw [← ContinuousMap.comp_apply, hf, hf₀]
  refine ⟨f, hfb, MonoidHom.ext fun g => ?_⟩
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective R g
  rw [MonoidHom.comp_apply, fundamentalGroupHom_mk, ← TauCeti.FundamentalGroup.mapOfEq_rfl,
    TauCeti.FundamentalGroup.mapOfEq_comp, TauCeti.FundamentalGroup.mapOfEq_congr hf _ hf₀, key]

/-- **The presented group injects into the fundamental group of the presentation complex.** The
homomorphism `fundamentalGroupHom R` has a left inverse, induced by a based map from the
presentation complex to the classifying space of the presented group, a `K(G, 1)` whose
fundamental group is identified with the presented group by
`classifyingSpaceFundamentalGroupMulEquiv`. -/
theorem fundamentalGroupHom_injective : Function.Injective (fundamentalGroupHom R) := by
  obtain ⟨f, hf, hψ⟩ := exists_mapOfEq_comp_fundamentalGroupHom
    (classifyingSpaceFundamentalGroupMulEquiv (PresentedGroup R)).symm.toMonoidHom
  refine Function.Injective.of_comp (f := FundamentalGroup.mapOfEq f hf) ?_
  rw [← MonoidHom.coe_comp, hψ]
  exact (classifyingSpaceFundamentalGroupMulEquiv _).symm.injective

/-- **The homomorphism from the presented group to the fundamental group of the presentation
complex is surjective.** Every loop at the vertex is homotopic into the wedge of circles
(`TwoCellAttachment.surjective_map_incl`), whose fundamental group is the free group. -/
theorem fundamentalGroupHom_surjective : Function.Surjective (fundamentalGroupHom R) := by
  intro g
  obtain ⟨h, rfl⟩ := TwoCellAttachment.surjective_map_incl g
  exact ⟨PresentedGroup.mk R (circleFundamentalGroupMulEquiv S h), by
    rw [fundamentalGroupHom_mk, MulEquiv.symm_apply_apply]⟩

variable (R) in
/-- **The fundamental group of the presentation complex is the presented group.** The
isomorphism `π₁(PresentationComplex R) ≃* PresentedGroup R` is the inverse of
`fundamentalGroupHom R`, so the loop around the `s`-th circle goes to the generator `s`. -/
def fundamentalGroupMulEquiv :
    FundamentalGroup (PresentationComplex R) (basepoint R) ≃* PresentedGroup R :=
  (MulEquiv.ofBijective (fundamentalGroupHom R)
    ⟨fundamentalGroupHom_injective, fundamentalGroupHom_surjective⟩).symm

@[simp]
theorem fundamentalGroupMulEquiv_symm_apply (g : PresentedGroup R) :
    (fundamentalGroupMulEquiv R).symm g = fundamentalGroupHom R g :=
  (rfl)

@[simp]
theorem fundamentalGroupMulEquiv_fundamentalGroupHom (g : PresentedGroup R) :
    fundamentalGroupMulEquiv R (fundamentalGroupHom R g) = g :=
  (fundamentalGroupMulEquiv R).apply_symm_apply g

/-- **The loop around the `s`-th circle goes to the generator `s`.** -/
theorem fundamentalGroupMulEquiv_mapOfEq_expLoop (s : S) :
    fundamentalGroupMulEquiv R (FundamentalGroup.mapOfEq ((incl R).comp (WedgeSum.incl _ s))
        (congrArg (incl R) (WedgeSum.incl_apply_self s))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop))) =
      PresentedGroup.of s := by
  rw [← fundamentalGroupHom_of, fundamentalGroupMulEquiv_fundamentalGroupHom]

/-! ### The CW structure -/

section CWComplex

open Set Topology
open Topology.RelCWComplex (map skeletonLT)

variable (R)

/-- **The CW structure on the presentation complex.** It has one `0`-cell, the vertex
(`TauCeti.PresentationComplex.map_zero`), one `1`-cell for each generator, the circles of the
wedge (`TauCeti.PresentationComplex.cellOneEquiv`), one `2`-cell for each relator, attached along
the loop `attachingLoop r` (`TauCeti.PresentationComplex.cellTwoEquiv`), and no cells of higher
dimension (`TauCeti.PresentationComplex.isEmpty_cell`). -/
instance instCWComplex : CWComplex (univ : Set (PresentationComplex R)) :=
  TwoCellAttachment.cwComplex _ fun _ ↦ WedgeSum.isEmpty_cell_circleCWComplex

/-- The presentation complex has a single `0`-cell. -/
instance : Unique (RelCWComplex.cell (univ : Set (PresentationComplex R)) 0) :=
  (TwoCellAttachment.cwComplexCellEquiv _ _ (by norm_num)).unique

/-- The `0`-cell of the presentation complex is its vertex. -/
@[simp]
theorem map_zero (i : RelCWComplex.cell (univ : Set (PresentationComplex R)) 0)
    (y : Fin 0 → ℝ) : map (C := (univ : Set (PresentationComplex R))) 0 i y = basepoint R := by
  obtain ⟨j, rfl⟩ := (TwoCellAttachment.cwComplexCellEquiv _ _ (by norm_num)).symm.surjective i
  rw [TwoCellAttachment.coe_map_cwComplexCellEquiv_symm, Function.comp_apply,
    WedgeSum.map_zero_circleCWComplex]

/-- The `1`-cells of the presentation complex are indexed by the generators. -/
def cellOneEquiv : RelCWComplex.cell (univ : Set (PresentationComplex R)) 1 ≃ S :=
  (TwoCellAttachment.cwComplexCellEquiv _ _ (by norm_num)).trans WedgeSum.circleCellOneEquiv

/-- The characteristic map of the `1`-cell of the generator `s` wraps the interval once around the
`s`-th circle of the wedge, `TauCeti.WedgeSum.circleCellMap s`. -/
@[simp]
theorem coe_map_cellOneEquiv_symm (s : S) :
    ⇑(map (C := (univ : Set (PresentationComplex R))) 1 ((cellOneEquiv R).symm s)) =
      incl R ∘ WedgeSum.circleCellMap S s := by
  rw [cellOneEquiv, Equiv.symm_trans_apply, TwoCellAttachment.coe_map_cwComplexCellEquiv_symm,
    WedgeSum.map_one_circleCWComplex, Equiv.apply_symm_apply]

/-- The `2`-cells of the presentation complex are indexed by the relators. -/
def cellTwoEquiv : RelCWComplex.cell (univ : Set (PresentationComplex R)) 2 ≃ R :=
  TwoCellAttachment.cwComplexCellTwoEquiv _ _

/-- The characteristic map of the `2`-cell of the relator `r` is the square attached along the
loop `attachingLoop r`, read on the disk. -/
@[simp]
theorem map_cellTwoEquiv_symm (r : R) (y : Metric.closedBall (0 : Fin 2 → ℝ) 1) :
    map (C := (univ : Set (PresentationComplex R))) 2 ((cellTwoEquiv R).symm r) y =
      TwoCellAttachment.diskCell _ r ((diskHomeomorphClosedBall 2).symm y) :=
  TwoCellAttachment.map_cwComplexCellTwoEquiv_symm _ _ r y

/-- The presentation complex has no cells of dimension at least `3`. -/
theorem isEmpty_cell {n : ℕ} (hn : 3 ≤ n) :
    IsEmpty (RelCWComplex.cell (univ : Set (PresentationComplex R)) n) :=
  have := WedgeSum.isEmpty_cell_circleCWComplex (S := S) (by omega : 2 ≤ n)
  (TwoCellAttachment.cwComplexCellEquiv _ _ (by omega)).isEmpty

/-- The `0`-skeleton of the presentation complex is its vertex. -/
theorem skeletonLT_one :
    (skeletonLT (univ : Set (PresentationComplex R)) 1 : Set (PresentationComplex R)) =
      {basepoint R} := by
  simp [skeletonLT_one_eq_insert]

end CWComplex

end PresentationComplex

end TauCeti
