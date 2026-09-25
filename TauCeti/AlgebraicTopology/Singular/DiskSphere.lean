/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.AlgebraicTopology.Disk

/-!
# The degree-zero relative homology of a disk and its boundary

The degree-zero relative homology of a positive-dimensional disk vanishes relative to its
boundary.  For the one-dimensional disk, both boundary points determine the same zeroth-homology
class of the disk; in higher dimensions the boundary itself is path-connected.  The lower bound is
sharp: for `n = 0`, the disk is a point and its boundary is empty.
-/

public section

noncomputable section
open CategoryTheory Limits
universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

private lemma diskBoundary_singularHomologyMap_zero_epi {n : ℕ} (hn : 1 ≤ n) :
    Epi (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map
      (TopCat.diskBoundaryInclusion (n := n) :
        (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}))) := by
  let i : (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}) :=
    TopCat.diskBoundaryInclusion n
  have hne : Nonempty (TopCat.diskBoundary n) := by
    -- Unfolding `TopCat.diskBoundary` exposes its metric-sphere carrier.
    change Nonempty (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    let i : Fin n := ⟨0, Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)⟩
    let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
    have hx : x ∈ Metric.sphere 0 1 := by simp [x]
    exact ⟨⟨x, hx⟩⟩
  let x : (TopCat.diskBoundary n : TopCat.{w}) := Classical.choice hne
  let hsplit : IsSplitEpi
      (TopCat.singularHomology₀ε (TopCat.diskBoundary n : TopCat.{w}) R) := by
    refine IsSplitEpi.mk' { section_ := TauCeti.singularHomology₀Section R x, id := ?_ }
    exact TauCeti.singularHomology₀Section_singularHomology₀ε R x
  let hε : Epi (TopCat.singularHomology₀ε (TopCat.diskBoundary n : TopCat.{w}) R) := by
    infer_instance
  let hp : IsIso (TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R) := by
    let _ : ContractibleSpace (TopCat.disk n : TopCat.{w}) :=
      TauCeti.TopCat.contractibleSpace_disk n
    infer_instance
  let hεcomp : Epi
      (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i ≫
        TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R) := by
    rw [TauCeti.singularHomologyMap_singularHomology₀ε R i]
    exact hε
  exact (CategoryTheory.epi_comp_iff_of_isIso
    (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i)
    (TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R)).mp hεcomp

/-- The inclusion from the boundary of a disk of dimension at least two is an isomorphism on
zeroth singular homology. -/
lemma diskBoundary_singularHomologyMap_zero_isIso {n : ℕ} (hn : 2 ≤ n) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map
      (TopCat.diskBoundaryInclusion (n := n) :
        (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}))) := by
  let i : (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}) :=
    TopCat.diskBoundaryInclusion n
  let hp : IsIso (TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R) := by
    let _ : ContractibleSpace (TopCat.disk n : TopCat.{w}) :=
      TauCeti.TopCat.contractibleSpace_disk n
    infer_instance
  let hq : IsIso (TopCat.singularHomology₀ε (TopCat.diskBoundary n : TopCat.{w}) R) := by
    let _ : PathConnectedSpace (TopCat.diskBoundary n : TopCat.{w}) :=
      TauCeti.TopCat.diskBoundary_isPathConnected hn
    infer_instance
  let hcomp : IsIso
      (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i ≫
        TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R) := by
    rw [TauCeti.singularHomologyMap_singularHomology₀ε R i]
    exact hq
  exact IsIso.of_isIso_comp_right
    (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i)
    (TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R)

/-- The degree-zero relative homology of a positive-dimensional disk and its boundary vanishes. -/
lemma isZero_singularHomology_diskBoundaryPair_zero {n : ℕ} (hn : 1 ≤ n) :
    IsZero ((diskBoundaryPair n).singularHomology R 0) := by
  let P : TopPair.{w} := diskBoundaryPair n
  -- The singular homology functor is the composite of `TopCat.toSSet` and the simplicial
  -- homology functor; this records that composite on the boundary inclusion.
  have hmapBridge :
      SSet.homologyMap
          (TopCat.toSSet.map
            (TopCat.diskBoundaryInclusion (n := n) :
              (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}))) R 0 =
        ((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map
          (TopCat.diskBoundaryInclusion (n := n) :
            (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w})) := rfl
  have hmap :
      Epi (SSet.homologyMap
        (TopCat.toSSet.map
          (TopCat.diskBoundaryInclusion (n := n) :
            (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}))) R 0) := by
    rw [hmapBridge]
    exact diskBoundary_singularHomologyMap_zero_epi (R := R) hn
  let S : ShortComplex C :=
    ShortComplex.mk
      (SSet.homologyMap (TopCat.toSSet.map P.map) R 0)
      (P.singularHomologyπ R 0) (P.homologyMap_comp_singularHomologyπ R 0)
  have hPmap : P.map = TopCat.diskBoundaryInclusion n := by
    simpa only [P] using (diskBoundaryPair_map n)
  have hEpiF : Epi S.f := by
    dsimp [S]
    rw [hPmap]
    exact hmap
  have hEpiG : Epi S.g := by
    simpa only [S, P, TopPair.toSSetPair_obj_right] using
      (inferInstance : Epi (P.singularHomologyπ R 0))
  -- `S.zero` is the short-complex relation `S.f ≫ S.g = 0`; epi of `S.f` forces
  -- `S.g = 0`, and epi of `S.g` then makes the target zero.
  have hgzero : S.g = 0 := zero_of_epi_comp S.f S.zero
  have hzero : IsZero S.X₃ := by
    have hz : (0 : S.X₂ ⟶ S.X₃) = S.g := hgzero.symm
    have hepiZero : Epi (0 : S.X₂ ⟶ S.X₃) := by
      rw [hz]
      exact hEpiG
    exact IsZero.of_epi_zero S.X₂ S.X₃
  simpa only [S] using hzero

end TopPair
