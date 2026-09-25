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

This file constructs the standard pair `(D^n, ∂D^n)` and proves the degree-zero
relative-homology convention `H₀(D^n, ∂D^n) = 0` for `n ≥ 2`.  The proof uses
path-connectedness of the disk and its boundary and then applies the long exact
sequence of a pair.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits
universe w v u

namespace TopPair

/-- The standard pair `(D^n, ∂D^n)`. -/
def diskBoundaryPair (n : ℕ) : TopPair.{w} :=
  TopPair.of (TopCat.diskBoundaryInclusion n) (by
    let hT2 : T2Space (TopCat.disk n) := by
      change T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
      infer_instance
    exact
      (((ConcreteCategory.hom (TopCat.diskBoundaryInclusion n)).continuous_toFun).isClosedEmbedding
        ((TopCat.mono_iff_injective _).mp
          (inferInstance : Mono (TopCat.diskBoundaryInclusion n)))).isEmbedding)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

private lemma disk_isPathConnected (n : ℕ) : PathConnectedSpace (TopCat.disk n) := by
  let hcontractible : ContractibleSpace (TopCat.disk n) :=
    TauCeti.TopCat.contractibleSpace_disk n
  infer_instance

private lemma diskBoundary_isPathConnected {n : ℕ} (hn : 2 ≤ n) :
    PathConnectedSpace (TopCat.diskBoundary n) := by
  change PathConnectedSpace (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
  let _ : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere
        (E := EuclideanSpace ℝ (Fin n))
        (by
          rw [← Module.finrank_eq_rank]
          norm_num [finrank_euclideanSpace_fin]
          omega)
        0 (by norm_num))
  exact Homeomorph.ulift.symm.pathConnectedSpace

private lemma diskBoundary_singularHomologyMap_zero_isIso {n : ℕ} (hn : 2 ≤ n) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map
      (TopCat.diskBoundaryInclusion (n := n) :
        (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}))) := by
  let hboundaryConnected : PathConnectedSpace (TopCat.diskBoundary n : TopCat.{w}) :=
    diskBoundary_isPathConnected hn
  let hdiskConnected : PathConnectedSpace (TopCat.disk n : TopCat.{w}) :=
    disk_isPathConnected n
  let i : (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}) :=
    TopCat.diskBoundaryInclusion n
  let hp : IsIso (TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R) := by
    infer_instance
  let hq : IsIso (TopCat.singularHomology₀ε (TopCat.diskBoundary n : TopCat.{w}) R) := by
    infer_instance
  have hnat :
      ((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i ≫
          TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R =
        TopCat.singularHomology₀ε (TopCat.diskBoundary n : TopCat.{w}) R :=
    TauCeti.singularHomologyMap_singularHomology₀ε R i
  let hcomp : IsIso
      (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i ≫
        TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R) := by
    rw [hnat]
    exact hq
  exact IsIso.of_isIso_comp_right
    (((AlgebraicTopology.singularHomologyFunctor C 0).obj R).map i)
    (TopCat.singularHomology₀ε (TopCat.disk n : TopCat.{w}) R)

/-- The degree-zero relative homology of a disk and its boundary vanishes for `n ≥ 2`. -/
lemma isZero_singularHomology_diskBoundaryPair_zero {n : ℕ} (hn : 2 ≤ n) :
    IsZero ((diskBoundaryPair n).singularHomology R 0) := by
  let P : TopPair.{w} := diskBoundaryPair n
  have hfun := diskBoundary_singularHomologyMap_zero_isIso (R := R) hn
  let i : (TopCat.diskBoundary n : TopCat.{w}) ⟶ (TopCat.disk n : TopCat.{w}) :=
    TopCat.diskBoundaryInclusion n
  have hmap :
      IsIso (SSet.homologyMap (TopCat.toSSet.map i) R 0) := by
    change IsIso
      (SSet.homologyMap (TopCat.toSSet.map
        (TopCat.diskBoundaryInclusion n :
          (TopCat.diskBoundary n : TopCat.{w}) ⟶
            (TopCat.disk n : TopCat.{w}))) R 0)
    exact hfun
  have hzero :
      SSet.homologyMap (TopCat.toSSet.map i) R 0 ≫
        P.singularHomologyπ R 0 = 0 := by
    change
      SSet.homologyMap (TopCat.toSSet.map
        (TopCat.diskBoundaryInclusion n :
          (TopCat.diskBoundary n : TopCat.{w}) ⟶
            (TopCat.disk n : TopCat.{w}))) R 0 ≫
        P.singularHomologyπ R 0 = 0
    exact P.homologyMap_comp_singularHomologyπ R 0
  let S : ShortComplex C :=
    ShortComplex.mk
      (SSet.homologyMap (TopCat.toSSet.map P.map) R 0)
      (P.singularHomologyπ R 0) (by exact hzero)
  have hS : S.Exact := by
    simpa [S] using (P.singularHomology_exact_space R 0)
  have hEpi : Epi S.g := by
    simpa [S] using (inferInstance : Epi (P.singularHomologyπ R 0))
  have hmapP : IsIso (SSet.homologyMap (TopCat.toSSet.map P.map) R 0) := by
    change IsIso (SSet.homologyMap (TopCat.toSSet.map i) R 0)
    exact hmap
  have hmapPI : IsIso (SSet.homologyMap (TopCat.toSSet.map P.map) R 0) := hmapP
  have hEpiF : Epi S.f := by
    dsimp [S]
    exact CategoryTheory.IsIso.epi_of_iso _
  exact CokernelCofork.IsColimit.isZero_of_epi hS.gIsCokernel

end TopPair
