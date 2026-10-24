/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Bigraded.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.KnotTheory.Grid.Grading.Complex
public import TauCeti.KnotTheory.Grid.Homology.Basic
import TauCeti.LinearAlgebra.Dimension.DirectSum

/-!
# The bigrading of fully blocked grid homology

For a grid diagram with an odd number of components, the fully blocked differential lowers the
`(O-Maslov, Alexander)` bidegree of every state by `(1, 0)`. So taking the homogeneous part of
bidegree `g` of a chain sends cycles to cycles and boundaries to boundaries, and descends to a
projection of the fully blocked grid homology `GH~` (written $\widetilde{GH}$ in the literature)
onto its bidegree-`g` piece. These pieces form an internal direct sum, so `GH~` is a bigraded
vector space over `ZMod 2`. Its Poincaré series, the dimension of each piece recorded as a
`TauCeti.Bigraded.Series`, refines the dimension of `GH~`: its total dimension is the dimension
of `GH~`.

By Ozsváth--Stipsicz--Szabó, the fully blocked homology of a grid of size `n` presenting an
`ℓ`-component link is the simply blocked homology of the link tensored with `n - ℓ` copies of the
two-dimensional bigraded space `W`. So the Poincaré series is the object on which the
`⊗ W`-stabilization quotient `TauCeti.Bigraded.StableSeries` acts.

## Main definitions

* `TauCeti.OddComponentGridDiagram.bigradedFullyBlockedHomologyProjection`: the projection of
  `GH~` onto bidegree `g`.
* `TauCeti.OddComponentGridDiagram.bigradedFullyBlockedHomologyPiece`: the bidegree-`g` piece of
  `GH~`.
* `TauCeti.OddComponentGridDiagram.bigradedFullyBlockedHomologyGrading`: the bundled internal
  grading of `GH~`.
* `TauCeti.OddComponentGridDiagram.fullyBlockedHomologySeries`: the Poincaré series of `GH~`.

## Main results

* `TauCeti.OddComponentGridDiagram.mem_bigradedFullyBlockedHomologyPiece_iff_exists`: a class is
  homogeneous of bidegree `g` exactly when it is the class of a cycle of bidegree `g`.
* `TauCeti.OddComponentGridDiagram.isInternal_bigradedFullyBlockedHomologyPiece`: `GH~` is the
  internal direct sum of its homogeneous pieces.
* `TauCeti.OddComponentGridDiagram.totalDim_fullyBlockedHomologySeries`: the total dimension of
  the Poincaré series is the dimension of `GH~`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3--4.4, for the bigrading
of the fully blocked complex, and Chapter 5 for the factor `W` in bidegrees `(0, 0)` and
`(-1, -1)`.
-/

public section

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

local notation "F" => ZMod 2

/-! ### Homogeneous parts of cycles and boundaries -/

/-- The homogeneous part of a fully blocked cycle is a cycle. -/
theorem bigradedChainInclusion_bigradedChainProjection_mem_fullyBlockedCycles (g : ℤ × ℤ)
    {z : GridChain F n} (hz : z ∈ G.1.fullyBlockedCycles) :
    G.bigradedChainInclusion F g (G.bigradedChainProjection F g z) ∈ G.1.fullyBlockedCycles := by
  rw [GridDiagram.mem_fullyBlockedCycles] at hz ⊢
  rw [fullyBlockedDifferential_bigradedChainInclusion_bigradedChainProjection, hz, map_zero,
    map_zero]

/-- The homogeneous part of a fully blocked boundary is a boundary. -/
theorem bigradedChainInclusion_bigradedChainProjection_mem_fullyBlockedBoundaries (g : ℤ × ℤ)
    {b : GridChain F n} (hb : b ∈ G.1.fullyBlockedBoundaries) :
    G.bigradedChainInclusion F g (G.bigradedChainProjection F g b) ∈
      G.1.fullyBlockedBoundaries := by
  obtain ⟨c, rfl⟩ := (G.1.mem_fullyBlockedBoundaries b).mp hb
  refine (G.1.mem_fullyBlockedBoundaries _).mpr
    ⟨G.bigradedChainInclusion F (g + (1, 0)) (G.bigradedChainProjection F (g + (1, 0)) c), ?_⟩
  rw [fullyBlockedDifferential_bigradedChainInclusion_bigradedChainProjection,
    add_sub_cancel_right]

/-! ### The homogeneous projections of fully blocked homology -/

/-- The projection of fully blocked grid homology onto bidegree `g`: the class of a cycle goes to
the class of its homogeneous part of bidegree `g`. -/
noncomputable def bigradedFullyBlockedHomologyProjection (g : ℤ × ℤ) :
    G.1.fullyBlockedHomology →ₗ[F] G.1.fullyBlockedHomology :=
  G.1.fullyBlockedBoundariesInCycles.mapQ G.1.fullyBlockedBoundariesInCycles
    ((G.bigradedChainInclusion F g ∘ₗ G.bigradedChainProjection F g).restrict fun _ hz =>
      G.bigradedChainInclusion_bigradedChainProjection_mem_fullyBlockedCycles g hz)
    fun z hz => by
      rw [Submodule.mem_comap, GridDiagram.mem_fullyBlockedBoundariesInCycles,
        LinearMap.coe_restrict_apply]
      exact G.bigradedChainInclusion_bigradedChainProjection_mem_fullyBlockedBoundaries g
        ((GridDiagram.mem_fullyBlockedBoundariesInCycles _ z).mp hz)

/-- The projection onto bidegree `g` sends the class of a cycle to the class of its homogeneous
part of bidegree `g`. -/
@[simp]
theorem bigradedFullyBlockedHomologyProjection_mk (g : ℤ × ℤ) (z : G.1.fullyBlockedCycles) :
    G.bigradedFullyBlockedHomologyProjection g (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨G.bigradedChainInclusion F g (G.bigradedChainProjection F g z),
        G.bigradedChainInclusion_bigradedChainProjection_mem_fullyBlockedCycles g z.2⟩ := by
  rw [bigradedFullyBlockedHomologyProjection, Submodule.mapQ_apply]
  rfl

/-- The projection onto bidegree `g` is idempotent. -/
@[simp]
theorem bigradedFullyBlockedHomologyProjection_apply_self (g : ℤ × ℤ)
    (y : G.1.fullyBlockedHomology) :
    G.bigradedFullyBlockedHomologyProjection g (G.bigradedFullyBlockedHomologyProjection g y) =
      G.bigradedFullyBlockedHomologyProjection g y := by
  induction y using Submodule.Quotient.induction_on with
  | H z => simp

/-- Projections onto two different bidegrees are orthogonal. -/
theorem bigradedFullyBlockedHomologyProjection_apply_of_ne {g h : ℤ × ℤ} (hgh : g ≠ h)
    (y : G.1.fullyBlockedHomology) :
    G.bigradedFullyBlockedHomologyProjection g (G.bigradedFullyBlockedHomologyProjection h y) =
      0 := by
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    simp only [bigradedFullyBlockedHomologyProjection_mk,
      bigradedChainProjection_bigradedChainInclusion_of_ne _ _ hgh, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.zero_mem _)

/-- A homology class is the sum of its homogeneous projections over the occupied bidegrees. -/
theorem sum_bigradedFullyBlockedHomologyProjection (y : G.1.fullyBlockedHomology) :
    ∑ g ∈ G.bidegreeSupport, G.bigradedFullyBlockedHomologyProjection g y = y := by
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    simp only [bigradedFullyBlockedHomologyProjection_mk]
    refine (map_sum G.1.fullyBlockedBoundariesInCycles.mkQ _ _).symm.trans ?_
    rw [Submodule.mkQ_apply]
    congr 1
    ext x
    simp [Finsupp.finsetSum_apply, bigradedChainInclusion_apply]

/-! ### The homogeneous pieces -/

/-- The bidegree-`g` piece of fully blocked grid homology: the image of the projection onto
bidegree `g`. Its elements are the classes of cycles of bidegree `g`
(`mem_bigradedFullyBlockedHomologyPiece_iff_exists`). -/
noncomputable def bigradedFullyBlockedHomologyPiece (g : ℤ × ℤ) :
    Submodule F G.1.fullyBlockedHomology :=
  LinearMap.range (G.bigradedFullyBlockedHomologyProjection g)

/-- A class lies in the bidegree-`g` piece exactly when the projection onto bidegree `g`
fixes it. -/
theorem mem_bigradedFullyBlockedHomologyPiece_iff {g : ℤ × ℤ} {y : G.1.fullyBlockedHomology} :
    y ∈ G.bigradedFullyBlockedHomologyPiece g ↔
      G.bigradedFullyBlockedHomologyProjection g y = y := by
  refine ⟨?_, fun h => ⟨y, h⟩⟩
  rintro ⟨y, rfl⟩
  exact G.bigradedFullyBlockedHomologyProjection_apply_self g y

/-- The projection onto bidegree `g` lands in the bidegree-`g` piece. -/
theorem bigradedFullyBlockedHomologyProjection_mem (g : ℤ × ℤ) (y : G.1.fullyBlockedHomology) :
    G.bigradedFullyBlockedHomologyProjection g y ∈ G.bigradedFullyBlockedHomologyPiece g :=
  ⟨y, rfl⟩

/-- A class is homogeneous of bidegree `g` exactly when it is the class of a cycle of bidegree
`g`. -/
theorem mem_bigradedFullyBlockedHomologyPiece_iff_exists {g : ℤ × ℤ}
    {y : G.1.fullyBlockedHomology} :
    y ∈ G.bigradedFullyBlockedHomologyPiece g ↔
      ∃ z : G.1.fullyBlockedCycles,
        (z : GridChain F n) ∈ LinearMap.range (G.bigradedChainInclusion F g) ∧
          Submodule.Quotient.mk z = y := by
  constructor
  · rintro ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | H z => exact ⟨_, ⟨_, rfl⟩, (G.bigradedFullyBlockedHomologyProjection_mk g z).symm⟩
  · rintro ⟨z, ⟨c, hc⟩, rfl⟩
    rw [mem_bigradedFullyBlockedHomologyPiece_iff, bigradedFullyBlockedHomologyProjection_mk]
    congr 1
    ext1
    simp only [← hc, bigradedChainProjection_bigradedChainInclusion]

/-- The projection onto bidegree `g` kills the pieces of every other bidegree. -/
theorem bigradedFullyBlockedHomologyProjection_eq_zero_of_mem {g h : ℤ × ℤ} (hgh : g ≠ h)
    {y : G.1.fullyBlockedHomology} (hy : y ∈ G.bigradedFullyBlockedHomologyPiece h) :
    G.bigradedFullyBlockedHomologyProjection g y = 0 := by
  obtain ⟨y, rfl⟩ := hy
  exact G.bigradedFullyBlockedHomologyProjection_apply_of_ne hgh y

/-- Only the bidegrees occupied by grid states carry homology. -/
theorem bigradedFullyBlockedHomologyPiece_eq_bot {g : ℤ × ℤ} (hg : g ∉ G.bidegreeSupport) :
    G.bigradedFullyBlockedHomologyPiece g = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, rfl⟩
  rw [Submodule.mem_bot]
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    have hz : G.bigradedChainInclusion F g (G.bigradedChainProjection F g z) = 0 := by
      ext x
      rw [bigradedChainInclusion_apply, Finsupp.zero_apply]
      exact dite_eq_right_iff.mpr fun hx =>
        (hg ((G.mem_bidegreeSupport_iff g).mpr ⟨x, hx⟩)).elim
    rw [bigradedFullyBlockedHomologyProjection_mk, GridDiagram.fullyBlockedHomology_mk_eq_zero_iff]
    simp only [hz, Submodule.zero_mem]

/-- **Fully blocked grid homology is bigraded**: it is the internal direct sum of its
homogeneous pieces. -/
theorem isInternal_bigradedFullyBlockedHomologyPiece :
    DirectSum.IsInternal G.bigradedFullyBlockedHomologyPiece := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (fun g => ?_) ?_
  · rw [Submodule.disjoint_def]
    intro y hy hy'
    have hle : (⨆ (h) (_ : h ≠ g), G.bigradedFullyBlockedHomologyPiece h) ≤
        LinearMap.ker (G.bigradedFullyBlockedHomologyProjection g) :=
      iSup₂_le fun h hne _ hy =>
        G.bigradedFullyBlockedHomologyProjection_eq_zero_of_mem (Ne.symm hne) hy
    rw [← (mem_bigradedFullyBlockedHomologyPiece_iff G).mp hy]
    exact LinearMap.mem_ker.mp (hle hy')
  · rw [eq_top_iff]
    intro y _
    rw [← G.sum_bigradedFullyBlockedHomologyProjection y]
    exact Submodule.sum_mem _ fun g _ => Submodule.mem_iSup_of_mem g
      (G.bigradedFullyBlockedHomologyProjection_mem g y)

/-- The internal `(O-Maslov, Alexander)` grading of fully blocked grid homology. -/
noncomputable def bigradedFullyBlockedHomologyGrading :
    InternalGrading F G.1.fullyBlockedHomology (ℤ × ℤ) :=
  ⟨G.bigradedFullyBlockedHomologyPiece, G.isInternal_bigradedFullyBlockedHomologyPiece⟩

/-- The pieces of the bundled grading are the homogeneous pieces. -/
@[simp]
theorem bigradedFullyBlockedHomologyGrading_piece (g : ℤ × ℤ) :
    G.bigradedFullyBlockedHomologyGrading.piece g = G.bigradedFullyBlockedHomologyPiece g :=
  (rfl)

/-! ### The Poincaré series -/

/-- The bigraded Poincaré series of fully blocked grid homology: its coefficient in bidegree `g`
is the dimension of the bidegree-`g` piece. -/
noncomputable def fullyBlockedHomologySeries : Bigraded.Series :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.onFinset G.bidegreeSupport
    (fun g => Module.finrank F (G.bigradedFullyBlockedHomologyPiece g)) fun g hg => by
      by_contra h
      rw [G.bigradedFullyBlockedHomologyPiece_eq_bot h, finrank_bot] at hg
      exact hg rfl

/-- The coefficient of the Poincaré series in bidegree `g` is the dimension of the bidegree-`g`
piece of fully blocked homology. -/
@[simp]
theorem coeff_fullyBlockedHomologySeries (g : ℤ × ℤ) :
    G.fullyBlockedHomologySeries.coeff g =
      Module.finrank F (G.bigradedFullyBlockedHomologyPiece g) :=
  (rfl)

/-- The dimension of fully blocked homology is the sum of the dimensions of its pieces. -/
theorem sum_finrank_bigradedFullyBlockedHomologyPiece :
    ∑ g ∈ G.bidegreeSupport, Module.finrank F (G.bigradedFullyBlockedHomologyPiece g) =
      Module.finrank F G.1.fullyBlockedHomology := by
  have hsupp : {g | G.bigradedFullyBlockedHomologyPiece g ≠ ⊥} ⊆ G.bidegreeSupport :=
    fun _ hg => Classical.byContradiction fun h => hg (G.bigradedFullyBlockedHomologyPiece_eq_bot h)
  rw [← finsum_finrank_eq_finrank_of_isInternal G.isInternal_bigradedFullyBlockedHomologyPiece
    (G.bidegreeSupport.finite_toSet.subset hsupp)]
  refine (finsum_eq_sum_of_support_subset _ fun g hg => ?_).symm
  by_contra h
  rw [Function.mem_support, G.bigradedFullyBlockedHomologyPiece_eq_bot h, finrank_bot] at hg
  exact hg rfl

/-- The total dimension of the Poincaré series is the dimension of fully blocked homology. -/
@[simp]
theorem totalDim_fullyBlockedHomologySeries :
    Bigraded.totalDim G.fullyBlockedHomologySeries = Module.finrank F G.1.fullyBlockedHomology := by
  rw [Bigraded.totalDim_apply, fullyBlockedHomologySeries, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.onFinset_sum _ fun _ => rfl, sum_finrank_bigradedFullyBlockedHomologyPiece]

end TauCeti.OddComponentGridDiagram
