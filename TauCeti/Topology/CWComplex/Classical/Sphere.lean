/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.Compactification.OnePoint.UnitBall
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType

/-!
# The CW structure on a sphere

The unit sphere `Sⁿ` of a Euclidean space `EuclideanSpace ℝ ι` of dimension `n + 1` is a finite
CW complex with one `0`-cell, a pole, and one `n`-cell attached along the constant map to it
(`TauCeti.sphereCWComplex`).  The characteristic map of the `n`-cell collapses the boundary of the
closed unit cube `closedBall (0 : Fin n → ℝ) 1` to `∞` (`TauCeti.unitBallToOnePoint`) and then
identifies the one-point compactification of `Fin n → ℝ` with `Sⁿ`
(`onePointEquivSphereOfFinrankEq`); the pole is the image of `∞`.  For `n = 0` the two cells are
the two points of `S⁰`.

* `TauCeti.spherePole h`: the `0`-cell of `Sⁿ`, for `h : Fintype.card ι = n + 1`.
* `TauCeti.sphereTopCellMap h`: the characteristic map of the `n`-cell, a bijection from the open
  unit cube onto the complement of the pole.
* `TauCeti.sphereCWComplex h`: the CW structure, which is finite
  (`TauCeti.finite_sphereCWComplex`) with one cell in dimension `0` and one in dimension `n`
  (`TauCeti.nat_card_cell_sphereCWComplex`).
* `TauCeti.finiteCWType_sphere`: the unit sphere of every finite-dimensional real normed space has
  finite CW type.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.3.
-/

public section

noncomputable section

open Metric Module OnePoint Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {ι : Type u} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1)

/-- The homeomorphism from the one-point compactification of `Fin n → ℝ` to the unit sphere of
the `(n + 1)`-dimensional Euclidean space `EuclideanSpace ℝ ι`. -/
private def sphereOnePointEquiv : OnePoint (Fin n → ℝ) ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1 :=
  onePointEquivSphereOfFinrankEq (by simp [h])

/-- The pole of the unit sphere `Sⁿ` of `EuclideanSpace ℝ ι`, for `ι` of cardinality `n + 1`: the
`0`-cell of its CW structure, onto which the boundary of the `n`-cell is collapsed. -/
def spherePole : EuclideanSpace ℝ ι :=
  sphereOnePointEquiv h ∞

theorem spherePole_mem_sphere : spherePole h ∈ sphere (0 : EuclideanSpace ℝ ι) 1 :=
  (sphereOnePointEquiv h ∞).2

/-- A point of `Sⁿ` other than the pole comes from a finite point of the one-point
compactification. -/
private theorem sphereOnePointEquiv_symm_mem_target {y : EuclideanSpace ℝ ι}
    (hy : y ∈ sphere 0 1 \ {spherePole h}) :
    (sphereOnePointEquiv h).symm ⟨y, hy.1⟩ ∈ (unitBallToOnePoint (E := Fin n → ℝ)).target := by
  rw [unitBallToOnePoint_target, mem_compl_singleton_iff]
  intro h'
  refine hy.2 ?_
  rw [Set.mem_singleton_iff, spherePole, ← h', Homeomorph.apply_symm_apply]

open scoped Classical in
/-- The characteristic map of the top cell of the unit sphere `Sⁿ` of `EuclideanSpace ℝ ι`, for
`ι` of cardinality `n + 1`: it maps the open unit cube of `Fin n → ℝ` bijectively onto the
complement of `TauCeti.spherePole h` and collapses the boundary of the cube to the pole. -/
def sphereTopCellMap : PartialEquiv (Fin n → ℝ) (EuclideanSpace ℝ ι) where
  toFun x := sphereOnePointEquiv h (unitBallToOnePoint x)
  invFun y := if hy : y ∈ sphere 0 1 then
    unitBallToOnePoint.symm ((sphereOnePointEquiv h).symm ⟨y, hy⟩) else 0
  source := ball 0 1
  target := sphere 0 1 \ {spherePole h}
  map_source' x hx := by
    refine ⟨(sphereOnePointEquiv h _).2, fun h' ↦ ?_⟩
    have : unitBallToOnePoint x = ∞ := (sphereOnePointEquiv h).injective (Subtype.ext h')
    exact (unitBallToOnePoint_apply_eq_infty_iff.1 this).not_gt (mem_ball_zero_iff.1 hx)
  map_target' y hy := by
    rw [dite_eq_left hy.1, ← unitBallToOnePoint_source]
    exact unitBallToOnePoint.map_target (sphereOnePointEquiv_symm_mem_target h hy)
  left_inv' x hx := by
    simp only [Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta, Homeomorph.symm_apply_apply]
    exact unitBallToOnePoint.left_inv (by rwa [unitBallToOnePoint_source])
  right_inv' y hy := by
    rw [dite_eq_left hy.1, unitBallToOnePoint.right_inv (sphereOnePointEquiv_symm_mem_target h hy),
      Homeomorph.apply_symm_apply]

@[simp]
theorem sphereTopCellMap_source : (sphereTopCellMap h).source = ball 0 1 :=
  (rfl)

@[simp]
theorem sphereTopCellMap_target :
    (sphereTopCellMap h).target = sphere 0 1 \ {spherePole h} :=
  (rfl)

/-- The characteristic map of the top cell of `Sⁿ` is the boundary collapse
`TauCeti.unitBallToOnePoint` followed by `onePointEquivSphereOfFinrankEq`. -/
theorem sphereTopCellMap_apply (x : Fin n → ℝ) :
    sphereTopCellMap h x =
      ↑(onePointEquivSphereOfFinrankEq (ι := ι) (V := Fin n → ℝ) (by simp [h])
        (unitBallToOnePoint x)) :=
  (rfl)

/-- On `Sⁿ`, the inverse of the characteristic map of the top cell is the inverse of
`onePointEquivSphereOfFinrankEq` followed by the inverse of `TauCeti.unitBallToOnePoint`. -/
theorem sphereTopCellMap_symm_apply {y : EuclideanSpace ℝ ι} (hy : y ∈ sphere 0 1) :
    (sphereTopCellMap h).symm y = unitBallToOnePoint.symm
      ((onePointEquivSphereOfFinrankEq (ι := ι) (V := Fin n → ℝ) (by simp [h])).symm ⟨y, hy⟩) :=
  dite_eq_left hy

theorem sphereTopCellMap_mem_sphere (x : Fin n → ℝ) :
    sphereTopCellMap h x ∈ sphere (0 : EuclideanSpace ℝ ι) 1 :=
  (sphereOnePointEquiv h _).2

/-- The characteristic map of the top cell collapses the boundary of the cube to the pole. -/
@[simp]
theorem sphereTopCellMap_apply_of_norm_eq_one {x : Fin n → ℝ} (hx : ‖x‖ = 1) :
    sphereTopCellMap h x = spherePole h := by
  rw [sphereTopCellMap_apply, unitBallToOnePoint_apply_of_one_le_norm hx.ge, spherePole,
    sphereOnePointEquiv]

/-- The characteristic map of the top cell of `Sⁿ` is continuous on the closed unit ball, as a
CW characteristic map must be. -/
theorem continuousOn_sphereTopCellMap : ContinuousOn (sphereTopCellMap h) (closedBall 0 1) :=
  (continuous_subtype_val.comp (sphereOnePointEquiv h).continuous).comp_continuousOn
    continuousOn_unitBallToOnePoint

/-- The inverse of the characteristic map of the top cell of `Sⁿ` is continuous on the open
cell `Sⁿ \ {pole}`. -/
theorem continuousOn_sphereTopCellMap_symm :
    ContinuousOn (sphereTopCellMap h).symm (sphereTopCellMap h).target := by
  rw [continuousOn_iff_continuous_domRestrict]
  -- On the target, the inverse is `unitBallToOnePoint.symm` after the inverse homeomorphism.
  refine (continuousOn_unitBallToOnePoint_symm.comp_continuous
    ((sphereOnePointEquiv h).symm.continuous.comp
      (continuous_subtype_val.subtype_mk fun y ↦ y.2.1))
    fun y ↦ sphereOnePointEquiv_symm_mem_target h y.2).congr fun y ↦ ?_
  exact (sphereTopCellMap_symm_apply h y.2.1).symm

/-- The cells of dimension `m` of the CW structure on `Sⁿ`: one if `m = 0` and one if `m = n`. -/
private abbrev SphereCell (n m : ℕ) : Type u := ULift.{u} (PLift (m = 0) ⊕ PLift (m = n))

include h in
/-- The characteristic maps of the CW structure on `Sⁿ`: the constant map to the pole and the
characteristic map of the top cell. -/
private def sphereCellMap :
    (m : ℕ) → SphereCell.{u} n m → PartialEquiv (Fin m → ℝ) (EuclideanSpace ℝ ι)
  | _, ⟨.inl _⟩ => .single 0 (spherePole h)
  | _, ⟨.inr ⟨rfl⟩⟩ => sphereTopCellMap h

private theorem isEmpty_sphereCell {m : ℕ} (hm : n + 1 ≤ m) : IsEmpty (SphereCell.{u} n m) :=
  ⟨fun i ↦ by rcases i with ⟨⟨⟨rfl⟩⟩ | ⟨⟨rfl⟩⟩⟩ <;> omega⟩

/-- The open cells of `Sⁿ`, the pole and its complement, are disjoint. -/
private theorem pairwiseDisjoint_sphereCellMap :
    (univ : Set (Σ m, SphereCell.{u} n m)).PairwiseDisjoint
      (fun i ↦ sphereCellMap h i.1 i.2 '' ball 0 1) := by
  rintro ⟨m, ⟨⟨⟨rfl⟩⟩ | ⟨⟨rfl⟩⟩⟩⟩ - ⟨m', ⟨⟨⟨rfl⟩⟩ | ⟨⟨h'⟩⟩⟩⟩ - hne
  · exact absurd rfl hne
  · subst h'
    refine disjoint_left.2 ?_
    rintro _ ⟨x, -, rfl⟩ ⟨y, hy, hxy⟩
    exact ((sphereTopCellMap h).map_source hy).2 hxy
  · refine disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, -, hxy⟩
    exact ((sphereTopCellMap h).map_source hx).2 hxy.symm
  · subst h'
    exact absurd rfl hne

/-- The boundary of every cell of `Sⁿ` lies in the closed cells of lower dimension. -/
private theorem mapsTo_sphereCellMap (m : ℕ) (i : SphereCell.{u} n m) :
    MapsTo (sphereCellMap h m i) (sphere 0 1)
      (⋃ (k < m) (j : SphereCell.{u} n k), sphereCellMap h k j '' closedBall 0 1) := by
  rcases i with ⟨⟨⟨rfl⟩⟩ | ⟨⟨rfl⟩⟩⟩
  · exact fun x hx ↦ ((sphere_eq_empty_of_subsingleton one_ne_zero).subset hx).elim
  -- The boundary of the top cell goes to the pole, the `0`-cell.
  intro x hx
  obtain _ | k := m
  · exact ((sphere_eq_empty_of_subsingleton one_ne_zero).subset hx).elim
  refine mem_iUnion₂.2 ⟨0, k.succ_pos, mem_iUnion.2 ⟨⟨.inl ⟨rfl⟩⟩, 0, by simp, ?_⟩⟩
  exact (sphereTopCellMap_apply_of_norm_eq_one h (mem_sphere_zero_iff_norm.1 hx)).symm

/-- The closed cells of `Sⁿ` cover it. -/
private theorem iUnion_sphereCellMap :
    ⋃ (m : ℕ) (j : SphereCell.{u} n m), sphereCellMap h m j '' closedBall 0 1 =
      sphere (0 : EuclideanSpace ℝ ι) 1 := by
  refine subset_antisymm (iUnion₂_subset ?_) fun y hy ↦ ?_
  · rintro m ⟨⟨⟨rfl⟩⟩ | ⟨⟨rfl⟩⟩⟩ _ ⟨x, -, rfl⟩
    · exact spherePole_mem_sphere h
    · exact sphereTopCellMap_mem_sphere h x
  by_cases hpole : y = spherePole h
  · exact mem_iUnion₂.2 ⟨0, ⟨.inl ⟨rfl⟩⟩, 0, by simp, hpole.symm⟩
  · have hy : y ∈ (sphereTopCellMap h).target := ⟨hy, hpole⟩
    exact mem_iUnion₂.2 ⟨n, ⟨.inr ⟨rfl⟩⟩, _,
      ball_subset_closedBall ((sphereTopCellMap h).map_target hy),
      (sphereTopCellMap h).right_inv hy⟩

/-- The CW structure on the unit sphere `Sⁿ` of `EuclideanSpace ℝ ι`, for `ι` of cardinality
`n + 1`: one `0`-cell, the pole `TauCeti.spherePole h`, and one `n`-cell with characteristic map
`TauCeti.sphereTopCellMap h`. -/
@[instance_reducible]
def sphereCWComplex : CWComplex (sphere (0 : EuclideanSpace ℝ ι) 1) :=
  CWComplex.mkFinite _ (SphereCell.{u} n) (sphereCellMap h)
    (Filter.eventually_atTop.2 ⟨n + 1, fun _ ↦ isEmpty_sphereCell⟩)
    (fun _ ↦ inferInstance)
    (by
      rintro m ⟨⟨⟨rfl⟩⟩ | ⟨⟨rfl⟩⟩⟩
      · ext x
        simp [sphereCellMap, Subsingleton.elim x 0]
      · rfl)
    (by
      rintro m ⟨⟨⟨rfl⟩⟩ | ⟨⟨rfl⟩⟩⟩
      · exact continuousOn_const
      · exact continuousOn_sphereTopCellMap h)
    (by
      rintro m ⟨⟨⟨rfl⟩⟩ | ⟨⟨rfl⟩⟩⟩
      · exact continuousOn_const
      · exact continuousOn_sphereTopCellMap_symm h)
    (pairwiseDisjoint_sphereCellMap h) (mapsTo_sphereCellMap h) (iUnion_sphereCellMap h)

/-- The CW structure on `Sⁿ` is finite. -/
theorem finite_sphereCWComplex :
    letI := sphereCWComplex h
    RelCWComplex.Finite (sphere (0 : EuclideanSpace ℝ ι) 1) :=
  letI := sphereCWComplex h
  { eventually_isEmpty_cell := Filter.eventually_atTop.2 ⟨n + 1, fun _ ↦ isEmpty_sphereCell⟩
    finite_cell _ := inferInstanceAs (Finite (SphereCell.{u} n _)) }

/-- The CW structure on `Sⁿ` has one cell in dimension `0` and one in dimension `n` (two `0`-cells
when `n = 0`). -/
theorem nat_card_cell_sphereCWComplex (m : ℕ) :
    letI := sphereCWComplex h
    Nat.card (cell (sphere (0 : EuclideanSpace ℝ ι) 1) m) =
      (if m = 0 then 1 else 0) + if m = n then 1 else 0 := by
  -- `CWComplex.mkFinite` takes the supplied family as its `cell` field
  -- (`CWComplex.mkFinite_cell`), so the cells of `sphereCWComplex h` in dimension `m` are
  -- `SphereCell n m` by definition.
  change Nat.card (SphereCell.{u} n m) = _
  rw [Nat.card_ulift, Nat.card_sum]
  congr 1 <;> split_ifs with h' <;> simp [h']

/-- The unit sphere of a finite-dimensional real normed space has finite CW type: it is
homeomorphic to the unit sphere of `EuclideanSpace ℝ (ULift (Fin (n + 1)))` for `n + 1` the
dimension, or empty in dimension zero. -/
instance finiteCWType_sphere {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : FiniteCWType (sphere (0 : E) 1) := by
  rcases (finrank ℝ E).eq_zero_or_pos with hE | hE
  · have : IsEmpty (sphere (0 : E) 1) := ⟨fun x ↦ by
      simpa [finrank_zero_iff_forall_zero.1 hE x] using x.2⟩
    exact FiniteCWType.of_discreteTopology _
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero hE.ne'
  have h : Fintype.card (ULift.{u} (Fin (n + 1))) = n + 1 := by simp
  let _ := sphereCWComplex h
  have := finite_sphereCWComplex h
  exact (sphereHomeomorphOfFinrankEq (F := EuclideanSpace ℝ (ULift.{u} (Fin (n + 1))))
    (by simp [hn])).finiteCWType

end TauCeti
