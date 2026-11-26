/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.FiniteCWType

/-!
# Lifting CW complexes to a higher universe

The cells of a classical CW complex `C` in `X : Type w` are indexed by types in `Type w`, so a CW
structure on `C` is not by itself a CW structure on a copy of `C` in a larger universe. This file
lifts it along `ULift`: if `C` is a CW complex relative to `D` in `X`, then `ULift.down ⁻¹' C` is a
CW complex relative to `ULift.down ⁻¹' D` in `ULift.{v} X`
(`Topology.RelCWComplex.ulift`), whose `n`-cells are the lifts `ULift (cell C n)` of the `n`-cells
of `C` (`Topology.RelCWComplex.uliftCellEquiv`) and whose characteristic maps are those of `C`
followed by `ULift.up` (`Topology.RelCWComplex.coe_map_ulift`). It is finite when `C` is.

Consequently `ULift.{v} X` has finite CW type when `X` has (`TauCeti.FiniteCWType.ulift`). This is
how invariants computed from finite CW models, such as the Euler characteristic, are compared for
homeomorphic spaces in different universes.

## Main definitions

* `Topology.RelCWComplex.ulift`: the CW structure on `ULift.down ⁻¹' C` relative to
  `ULift.down ⁻¹' D`.
* `Topology.RelCWComplex.uliftCellEquiv`: its `n`-cells are the `n`-cells of `C`.
* `Topology.CWComplex.ulift`: the lift of an absolute CW complex, with empty base.
* `Topology.CWComplex.uliftCellEquiv`: its `n`-cells are the `n`-cells of `C`.
* `ContinuousMap.HomotopyEquiv.ulift`: a homotopy equivalence `X ≃ₕ C` lifted to
  `ULift.{v} X ≃ₕ ULift.down ⁻¹' C`; its forward and inverse maps are described by
  `ContinuousMap.HomotopyEquiv.ulift_apply` and `ContinuousMap.HomotopyEquiv.ulift_symm_apply`.

## Main results

* `Topology.RelCWComplex.finite_ulift`, `Topology.CWComplex.finite_ulift`: the lift of a finite
  (relative) CW complex is finite.
* `TauCeti.FiniteCWType.ulift`: `ULift.{v} X` has finite CW type when `X` has.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and the Appendix, for CW complexes and relative CW complexes.
-/

public section

noncomputable section

open Function Metric Set

universe v w

namespace Topology.RelCWComplex

variable {X : Type w} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

/-- The characteristic map of a cell of `C`, followed by `ULift.up`. -/
private def uliftCellMap (n : ℕ) (i : cell C n) : PartialEquiv (Fin n → ℝ) (ULift.{v} X) :=
  (map n i).transEquiv Equiv.ulift.symm

private lemma coe_uliftCellMap (n : ℕ) (i : cell C n) :
    ⇑(uliftCellMap.{v} n i) = ULift.up ∘ map n i :=
  rfl

private lemma image_uliftCellMap (n : ℕ) (i : cell C n) (s : Set (Fin n → ℝ)) :
    uliftCellMap.{v} n i '' s = ULift.down ⁻¹' (map n i '' s) := by
  ext ⟨x⟩
  simp [coe_uliftCellMap]

/-- **The lift of a relative CW complex to a higher universe.** If `C` is a CW complex relative
to `D` in `X`, then `ULift.down ⁻¹' C` is a CW complex relative to `ULift.down ⁻¹' D` in
`ULift.{v} X`, with the cells of `C`, lifted to `ULift`, and the characteristic maps of `C`
followed by `ULift.up`. -/
@[instance_reducible]
def ulift : RelCWComplex (ULift.down ⁻¹' C : Set (ULift.{v} X)) (ULift.down ⁻¹' D) where
  cell n := ULift.{v} (cell C n)
  map n i := uliftCellMap n i.down
  source_eq n i := source_eq n i.down
  continuousOn n i := continuous_uliftUp.comp_continuousOn (continuousOn n i.down)
  continuousOn_symm n i :=
    (continuousOn_symm n i.down).comp continuous_uliftDown.continuousOn fun _ hy ↦ hy
  pairwiseDisjoint' := by
    rintro ⟨n, i⟩ - ⟨m, j⟩ - hne
    simp only [onFun, image_uliftCellMap]
    refine (pairwiseDisjoint (C := C) (mem_univ ⟨n, i.down⟩) (mem_univ ⟨m, j.down⟩) ?_).preimage _
    rintro h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
    exact hne (congrArg (Sigma.mk n) (ULift.ext (eq_of_heq h)))
  disjointBase' n i := by
    rw [image_uliftCellMap]
    exact (disjointBase (C := C) n i.down).preimage _
  mapsTo n i := by
    obtain ⟨I, hI⟩ := RelCWComplex.mapsTo n i.down
    refine ⟨fun m ↦ (I m).map ⟨ULift.up, ULift.up_injective⟩, fun x hx ↦ ?_⟩
    rcases hI hx with hxD | hx
    · exact .inl hxD
    · obtain ⟨m, hm, j, hj, hxj⟩ := by simpa only [mem_iUnion] using hx
      refine .inr (mem_iUnion₂.2 ⟨m, hm, mem_iUnion₂.2 ⟨⟨j⟩, Finset.mem_map_of_mem _ hj, ?_⟩⟩)
      rw [image_uliftCellMap]
      exact hxj
  closed' A hAC hA := by
    -- `A` is the preimage of `ULift.up ⁻¹' A` under the homeomorphism `ULift.down`.
    rw [← Homeomorph.ulift.symm.isClosed_preimage]
    refine RelCWComplex.closed' (C := C) _ (fun x hx ↦ hAC hx) ⟨fun n j ↦ ?_, ?_⟩
    · have := (hA.1 n ⟨j⟩).preimage continuous_uliftUp
      rwa [image_uliftCellMap, preimage_inter] at this
    · exact hA.2.preimage continuous_uliftUp
  isClosedBase := (isClosedBase C).preimage continuous_uliftDown
  union' := by
    simp only [image_uliftCellMap, ← preimage_iUnion, ← preimage_union]
    refine congrArg (ULift.down ⁻¹' ·) (Eq.trans ?_ (RelCWComplex.union' (C := C)))
    exact congrArg (D ∪ ·) <| iUnion_congr fun n ↦
      ULift.down_surjective.iUnion_comp fun j ↦ map n j '' closedBall 0 1

/-- The `n`-cells of the lift `Topology.RelCWComplex.ulift` are the `n`-cells of `C`. -/
def uliftCellEquiv (n : ℕ) :
    @cell (ULift.{v} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) ulift n ≃ cell C n :=
  Equiv.ulift

private lemma map_ulift_eq_uliftCellMap (n : ℕ)
    (i : @cell (ULift.{v} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) ulift n) :
    @map (ULift.{v} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) ulift n i =
      uliftCellMap n (uliftCellEquiv n i) :=
  rfl

/-- The characteristic maps of the lift `Topology.RelCWComplex.ulift` are those of `C` followed by
`ULift.up`. -/
@[simp]
lemma coe_map_ulift (n : ℕ)
    (i : @cell (ULift.{v} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) ulift n) :
    ⇑(@map (ULift.{v} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) ulift n i) =
      ULift.up ∘ map n (uliftCellEquiv n i) := by
  rw [map_ulift_eq_uliftCellMap, coe_uliftCellMap]

/-- The lift of a finite relative CW complex to a higher universe is finite. -/
lemma finite_ulift [RelCWComplex.Finite C] :
    @RelCWComplex.Finite (ULift.{v} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) ulift :=
  letI : RelCWComplex (ULift.down ⁻¹' C : Set (ULift.{v} X)) (ULift.down ⁻¹' D) := ulift
  { eventually_isEmpty_cell := (FiniteDimensional.eventually_isEmpty_cell (C := C)).mono
      fun _ h ↦ (uliftCellEquiv _).isEmpty_congr.2 h
    finite_cell n := (uliftCellEquiv n).finite_iff.2 (FiniteType.finite_cell n) }

end Topology.RelCWComplex

namespace Topology.CWComplex

variable {X : Type w} [TopologicalSpace X] {C : Set X} [CWComplex C]

/-- The lift of a CW complex `C` in `X` to the CW complex `ULift.down ⁻¹' C` in `ULift.{v} X`:
`Topology.RelCWComplex.ulift` with empty base, since the preimage of the empty base is empty. -/
@[expose, instance_reducible]
def ulift : CWComplex (ULift.down ⁻¹' C : Set (ULift.{v} X)) :=
  @RelCWComplex.toCWComplex _ _ _ (RelCWComplex.ulift (C := C) (D := ∅))

/-- The `n`-cells of the lift `Topology.CWComplex.ulift` are the `n`-cells of `C`. -/
def uliftCellEquiv (n : ℕ) :
    @cell (ULift.{v} X) _ (ULift.down ⁻¹' C) ∅ (@instRelCWComplex _ _ _ ulift) n ≃ cell C n :=
  -- The base `ULift.down ⁻¹' ∅` of the relative lift is `∅` by definition of the preimage.
  RelCWComplex.uliftCellEquiv (D := ∅) n

/-- The lift of a finite CW complex to a higher universe is finite. -/
instance finite_ulift [RelCWComplex.Finite C] :
    @RelCWComplex.Finite (ULift.{v} X) _ (ULift.down ⁻¹' C) ∅ (@instRelCWComplex _ _ _ ulift) :=
  -- The base `ULift.down ⁻¹' ∅` of the relative lift is `∅` by definition of the preimage.
  RelCWComplex.finite_ulift (D := ∅)

end Topology.CWComplex

/-- A homotopy equivalence `X ≃ₕ C` with a subset `C` of `Y` lifts to a homotopy equivalence
`ULift.{v} X ≃ₕ ULift.down ⁻¹' C` with the preimage of `C` in `ULift.{v} Y`. -/
def ContinuousMap.HomotopyEquiv.ulift {X : Type*} {Y : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] {C : Set Y} (e : ContinuousMap.HomotopyEquiv X C) :
    ContinuousMap.HomotopyEquiv (ULift.{v} X) (ULift.down ⁻¹' C : Set (ULift.{v} Y)) :=
  (Homeomorph.ulift.toHomotopyEquiv.trans e).trans
    (Homeomorph.ulift.subtype fun _ ↦ Iff.rfl).symm.toHomotopyEquiv

/-- The forward map of `ContinuousMap.HomotopyEquiv.ulift` is `e` followed by `ULift.up`. -/
@[simp]
lemma ContinuousMap.HomotopyEquiv.ulift_apply {X : Type*} {Y : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] {C : Set Y} (e : ContinuousMap.HomotopyEquiv X C) (x : ULift.{v} X) :
    e.ulift x = ⟨ULift.up (e x.down), (e x.down).property⟩ :=
  (rfl)

/-- The inverse map of `ContinuousMap.HomotopyEquiv.ulift` is `ULift.down` followed by the inverse
of `e`. -/
@[simp]
lemma ContinuousMap.HomotopyEquiv.ulift_symm_apply {X : Type*} {Y : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] {C : Set Y} (e : ContinuousMap.HomotopyEquiv X C)
    (y : (ULift.down ⁻¹' C : Set (ULift.{v} Y))) :
    e.ulift.symm y = ULift.up (e.symm ⟨y.val.down, y.property⟩) :=
  (rfl)

namespace TauCeti

open Topology Topology.RelCWComplex

/-- **Finite CW type is preserved by `ULift`.** If `X` is homotopy equivalent to a finite CW
complex `C` in `Y`, then `ULift.{v} X` is homotopy equivalent to its lift
`ULift.down ⁻¹' C` in `ULift.{v} Y`. -/
instance FiniteCWType.ulift (X : Type w) [TopologicalSpace X] [h : FiniteCWType X] :
    FiniteCWType (ULift.{v} X) := by
  obtain ⟨Y, _, _, C, _, _, ⟨e⟩⟩ := h.exists_homotopyEquiv
  exact ⟨ULift.{v} Y, _, inferInstance, _, CWComplex.ulift (C := C),
    CWComplex.finite_ulift (C := C), ⟨e.ulift⟩⟩

end TauCeti
