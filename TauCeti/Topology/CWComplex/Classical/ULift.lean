/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Universe lift of classical relative CW complexes

In Mathlib's classical `Topology.RelCWComplex`, a relative CW complex `(C, D)` in a space
`X : Type u` has cell-indexing types `cell C n : Type u` in the same universe as `X`. When gluing or
comparing spaces that live in different universes `Type u` and `Type v`, lifting `X` to
`ULift.{v, u} X : Type (max u v)` transports `(C, D)` to a classical relative CW complex
`Topology.RelCWComplex.ulift` on `(ULift.down ⁻¹' C, ULift.down ⁻¹' D)` in `ULift.{v, u} X`.

Its `n`-cells are `ULift.{v, u} (cell C n)`, equivalent to `cell C n` via `Equiv.ulift`
(`Topology.RelCWComplex.uliftCellEquiv`), and its characteristic maps are those of `C` followed by
`ULift.up` (`Topology.RelCWComplex.coe_map_ulift`). In particular `ULift.down ⁻¹' univ = univ` and
`ULift.down ⁻¹' ∅ = ∅` definitionally, so an absolute CW complex on `C` (or `univ`) lifts directly
to an absolute CW complex `Topology.CWComplex.ulift` (and `Topology.CWComplex.uliftUniv`), with
matching cell equivalences, `@[simp]` map/cell lemmas, and finiteness instances.

## Main declarations

* `Topology.RelCWComplex.ulift`: the lifted relative CW structure on `ULift.down ⁻¹' C` relative to
  `ULift.down ⁻¹' D` in `ULift.{v, u} X`.
* `Topology.RelCWComplex.uliftCellEquiv`: equivalence of its `n`-cells with `cell C n`.
* `Topology.CWComplex.ulift` and `Topology.CWComplex.uliftUniv`: lifted absolute CW structures on
  `ULift.down ⁻¹' C` and `univ : Set (ULift.{v, u} X)`, with cell equivalences, map/cell lemmas,
  and `FiniteDimensional`/`FiniteType`/`Finite` instances.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0.
-/

public section

noncomputable section

open Function Metric Set Topology Topology.RelCWComplex

universe v u

namespace Topology.RelCWComplex

section RelCWComplex

variable {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X} [RelCWComplex C D]

/-- The characteristic map of a cell of `C`, lifted to `ULift.{v, u} X`. -/
private def uliftMap (n : ℕ) (i : ULift.{v, u} (cell C n)) :
    PartialEquiv (Fin n → ℝ) (ULift.{v, u} X) :=
  (map n i.down).trans Equiv.ulift.symm.toPartialEquiv

private lemma coe_uliftMap (n : ℕ) (i : ULift.{v, u} (cell C n)) :
    ⇑(uliftMap C n i) = ULift.up ∘ map n i.down :=
  (rfl)

private lemma image_uliftMap (n : ℕ) (i : ULift.{v, u} (cell C n)) (S : Set (Fin n → ℝ)) :
    uliftMap C n i '' S = ULift.down ⁻¹' (map n i.down '' S) := by
  ext ⟨x⟩
  simp [coe_uliftMap]

/-- **Universe lift of a classical relative CW complex.** Lifting `X : Type u` to
`ULift.{v, u} X : Type (max u v)` carries a relative CW complex `(C, D)` to a relative CW complex on
`ULift.down ⁻¹' C` relative to `ULift.down ⁻¹' D`, with cells `ULift.{v, u} (cell C n)` and
characteristic maps `ULift.up ∘ map n i.down`. -/
@[instance_reducible]
def ulift :
    RelCWComplex (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) (ULift.down ⁻¹' D) where
  cell n := ULift.{v, u} (cell C n)
  map := uliftMap C
  source_eq n i := by simp [uliftMap, source_eq]
  continuousOn n i := continuous_uliftUp.comp_continuousOn (RelCWComplex.continuousOn n i.down)
  continuousOn_symm n i := by
    rw [uliftMap, PartialEquiv.coe_trans_symm, PartialEquiv.trans_target]
    exact (continuousOn_symm n i.down).comp
      (continuous_uliftDown.continuousOn.mono inter_subset_right) fun y hy ↦ hy.2
  pairwiseDisjoint' := by
    rintro ⟨n, ⟨i⟩⟩ - ⟨m, ⟨j⟩⟩ - hne
    simp only [Function.onFun, image_uliftMap]
    refine (pairwiseDisjoint (C := C) (mem_univ ⟨n, i⟩) (mem_univ ⟨m, j⟩) fun h ↦ hne ?_).preimage _
    obtain ⟨rfl, hij⟩ := Sigma.mk.inj_iff.1 h
    cases hij
    rfl
  disjointBase' n i := by
    rw [image_uliftMap]
    exact (disjointBase n i.down).preimage _
  mapsTo n i := by
    obtain ⟨I, hI⟩ := RelCWComplex.mapsTo (C := C) n i.down
    refine ⟨fun m ↦ (I m).map ⟨ULift.up, ULift.up_injective⟩, fun x hx ↦ ?_⟩
    simp only [image_uliftMap]
    rcases hI hx with hxD | hxJ
    · exact Or.inl hxD
    · obtain ⟨m, hmn, hxJ⟩ := mem_iUnion₂.1 hxJ
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hxJ
      exact Or.inr (mem_iUnion₂_of_mem hmn
        (mem_iUnion₂_of_mem (Finset.mem_map_of_mem _ hj) hxj))
  closed' A hAC hA := by
    refine Homeomorph.ulift.symm.isClosed_preimage.1
      (RelCWComplex.closed' (C := C) (ULift.up ⁻¹' A) (fun x hx ↦ hAC hx) ⟨fun n j ↦ ?_, ?_⟩)
    · have := (hA.1 n (ULift.up j)).preimage continuous_uliftUp
      rwa [preimage_inter, image_uliftMap, preimage_preimage] at this
    · have h2 := hA.2.preimage continuous_uliftUp
      rwa [preimage_inter, preimage_preimage] at h2
  isClosedBase := (isClosedBase C).preimage continuous_uliftDown
  union' := by
    ext ⟨x⟩
    have hx := Set.ext_iff.1 (RelCWComplex.union (C := C)) x
    simpa only [image_uliftMap, closedCell, mem_union, mem_preimage, mem_iUnion, ULift.exists]
      using hx

/-- The `n`-cells of `RelCWComplex.ulift C` are equivalent to the `n`-cells of `C`. -/
def uliftCellEquiv (n : ℕ) :
    @cell (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) n ≃ cell C n :=
  Equiv.ulift

@[simp]
lemma coe_map_ulift (n : ℕ)
    (i : @cell (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) n) :
    ⇑(@map (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) n i) =
      ULift.up ∘ map n (uliftCellEquiv C n i) :=
  (rfl)

@[simp]
lemma openCell_ulift (n : ℕ)
    (i : @cell (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) n) :
    @openCell (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) n i =
      ULift.down ⁻¹' openCell n (uliftCellEquiv C n i) :=
  image_uliftMap C n i (ball 0 1)

@[simp]
lemma closedCell_ulift (n : ℕ)
    (i : @cell (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) n) :
    @closedCell (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) n i =
      ULift.down ⁻¹' closedCell n (uliftCellEquiv C n i) :=
  image_uliftMap C n i (closedBall 0 1)

@[simp]
lemma cellFrontier_ulift (n : ℕ)
    (i : @cell (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) n) :
    @cellFrontier (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) n i =
      ULift.down ⁻¹' cellFrontier n (uliftCellEquiv C n i) :=
  image_uliftMap C n i (sphere 0 1)

/-- The universe lift of a finite-dimensional relative CW complex is finite-dimensional. -/
lemma finiteDimensional_ulift [FiniteDimensional C] :
    @FiniteDimensional (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) :=
  @FiniteDimensional.mk _ _ _ _ (ulift.{v} C) <| by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n _
    exact (uliftCellEquiv.{v} C n).isEmpty_congr.2 inferInstance

/-- The universe lift of a relative CW complex of finite type has finite type. -/
lemma finiteType_ulift [FiniteType C] :
    @FiniteType (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) :=
  @FiniteType.mk _ _ _ _ (ulift.{v} C) fun n ↦
    have := FiniteType.finite_cell (C := C) (D := D) n
    (uliftCellEquiv.{v} C n).finite_iff.2 inferInstance

/-- The universe lift of a finite relative CW complex is finite. -/
lemma finite_ulift [Finite C] :
    @Finite (ULift.{v, u} X) _ (ULift.down ⁻¹' C) (ULift.down ⁻¹' D) (ulift.{v} C) :=
  @finite_of_finiteDimensional_finiteType _ _ _ _ (ulift.{v} C)
    (finiteDimensional_ulift C) (finiteType_ulift C)

end RelCWComplex

end Topology.RelCWComplex

namespace Topology.CWComplex

variable {X : Type u} [TopologicalSpace X] (C : Set X) [CWComplex C]

/-- Universe lift of an absolute CW complex `C` in `X : Type u` to `ULift.{v, u} X`. -/
instance ulift : CWComplex (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) :=
  (RelCWComplex.ulift.{v} C).toCWComplex

/-- The `n`-cells of the lifted absolute CW complex `ULift.down ⁻¹' C` are equivalent to the
`n`-cells of `C`. -/
def uliftCellEquiv (n : ℕ) :
    RelCWComplex.cell (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) n ≃ RelCWComplex.cell C n :=
  Equiv.ulift

lemma coe_map_ulift (n : ℕ)
    (i : RelCWComplex.cell (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) n) :
    ⇑(RelCWComplex.map (C := (ULift.down ⁻¹' C : Set (ULift.{v, u} X))) n i) =
      ULift.up ∘ RelCWComplex.map (C := C) n (uliftCellEquiv.{v} C n i) :=
  (rfl)

lemma openCell_ulift (n : ℕ)
    (i : RelCWComplex.cell (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) n) :
    RelCWComplex.openCell (C := (ULift.down ⁻¹' C : Set (ULift.{v, u} X))) n i =
      ULift.down ⁻¹' RelCWComplex.openCell (C := C) n (uliftCellEquiv.{v} C n i) :=
  RelCWComplex.openCell_ulift.{v} C n i

lemma closedCell_ulift (n : ℕ)
    (i : RelCWComplex.cell (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) n) :
    RelCWComplex.closedCell (C := (ULift.down ⁻¹' C : Set (ULift.{v, u} X))) n i =
      ULift.down ⁻¹' RelCWComplex.closedCell (C := C) n (uliftCellEquiv.{v} C n i) :=
  RelCWComplex.closedCell_ulift.{v} C n i

lemma cellFrontier_ulift (n : ℕ)
    (i : RelCWComplex.cell (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) n) :
    RelCWComplex.cellFrontier (C := (ULift.down ⁻¹' C : Set (ULift.{v, u} X))) n i =
      ULift.down ⁻¹' RelCWComplex.cellFrontier (C := C) n (uliftCellEquiv.{v} C n i) :=
  RelCWComplex.cellFrontier_ulift.{v} C n i

/-- The universe lift of a finite-dimensional absolute CW complex is finite-dimensional. -/
instance instFiniteDimensionalUlift [RelCWComplex.FiniteDimensional C] :
    RelCWComplex.FiniteDimensional (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) :=
  ⟨by
    filter_upwards [RelCWComplex.FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)]
      with n _
    exact (uliftCellEquiv.{v} C n).isEmpty_congr.2 inferInstance⟩

/-- The universe lift of an absolute CW complex of finite type has finite type. -/
instance instFiniteTypeUlift [RelCWComplex.FiniteType C] :
    RelCWComplex.FiniteType (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) :=
  ⟨fun n ↦
    have := RelCWComplex.FiniteType.finite_cell (C := C) (D := ∅) n
    (uliftCellEquiv.{v} C n).finite_iff.2 inferInstance⟩

/-- The universe lift of a finite absolute CW complex is finite. -/
instance instFiniteUlift [RelCWComplex.Finite C] :
    RelCWComplex.Finite (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) :=
  RelCWComplex.finite_of_finiteDimensional_finiteType (ULift.down ⁻¹' C : Set (ULift.{v, u} X))

section Univ

variable [CWComplex (univ : Set X)]

/-- Universe lift of an absolute CW complex structure on `univ : Set X` to
`univ : Set (ULift.{v, u} X)`. Definitionally equal to `CWComplex.ulift univ`. -/
instance uliftUniv : CWComplex (univ : Set (ULift.{v, u} X)) :=
  ulift.{v} (univ : Set X)

/-- The `n`-cells of `univ : Set (ULift.{v, u} X)` are equivalent to those of `univ : Set X`. -/
def uliftUnivCellEquiv (n : ℕ) :
    RelCWComplex.cell (univ : Set (ULift.{v, u} X)) n ≃ RelCWComplex.cell (univ : Set X) n :=
  Equiv.ulift

@[simp]
lemma coe_map_uliftUniv (n : ℕ) (i : RelCWComplex.cell (univ : Set (ULift.{v, u} X)) n) :
    ⇑(RelCWComplex.map (C := (univ : Set (ULift.{v, u} X))) n i) =
      ULift.up ∘ RelCWComplex.map (C := (univ : Set X)) n (uliftUnivCellEquiv.{v} n i) :=
  (rfl)

@[simp]
lemma openCell_uliftUniv (n : ℕ) (i : RelCWComplex.cell (univ : Set (ULift.{v, u} X)) n) :
    RelCWComplex.openCell (C := (univ : Set (ULift.{v, u} X))) n i =
      ULift.down ⁻¹' RelCWComplex.openCell (C := (univ : Set X)) n
        (uliftUnivCellEquiv.{v} n i) :=
  RelCWComplex.openCell_ulift.{v} (univ : Set X) n i

@[simp]
lemma closedCell_uliftUniv (n : ℕ) (i : RelCWComplex.cell (univ : Set (ULift.{v, u} X)) n) :
    RelCWComplex.closedCell (C := (univ : Set (ULift.{v, u} X))) n i =
      ULift.down ⁻¹' RelCWComplex.closedCell (C := (univ : Set X)) n
        (uliftUnivCellEquiv.{v} n i) :=
  RelCWComplex.closedCell_ulift.{v} (univ : Set X) n i

@[simp]
lemma cellFrontier_uliftUniv (n : ℕ) (i : RelCWComplex.cell (univ : Set (ULift.{v, u} X)) n) :
    RelCWComplex.cellFrontier (C := (univ : Set (ULift.{v, u} X))) n i =
      ULift.down ⁻¹' RelCWComplex.cellFrontier (C := (univ : Set X)) n
        (uliftUnivCellEquiv.{v} n i) :=
  RelCWComplex.cellFrontier_ulift.{v} (univ : Set X) n i

/-- The universe lift of a finite-dimensional CW space `X` is finite-dimensional. -/
instance instFiniteDimensionalUliftUniv [RelCWComplex.FiniteDimensional (univ : Set X)] :
    RelCWComplex.FiniteDimensional (univ : Set (ULift.{v, u} X)) :=
  instFiniteDimensionalUlift.{v} (univ : Set X)

/-- The universe lift of a CW space `X` of finite type has finite type. -/
instance instFiniteTypeUliftUniv [RelCWComplex.FiniteType (univ : Set X)] :
    RelCWComplex.FiniteType (univ : Set (ULift.{v, u} X)) :=
  instFiniteTypeUlift.{v} (univ : Set X)

/-- The universe lift of a finite CW space `X` is finite. -/
instance instFiniteUliftUniv [RelCWComplex.Finite (univ : Set X)] :
    RelCWComplex.Finite (univ : Set (ULift.{v, u} X)) :=
  instFiniteUlift.{v} (univ : Set X)

end Univ

end Topology.CWComplex
