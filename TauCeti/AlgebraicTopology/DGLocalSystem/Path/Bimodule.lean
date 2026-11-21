/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule
public import TauCeti.Topology.PathSpace.Moore.Between.Basic

/-!
# The chain bimodule of Moore paths between two basepoints

For two points `b` and `b'` of a space `B`, the Moore loops at `b` act on the Moore paths from `b`
to `b'` by concatenation in front, and those at `b'` by concatenation behind; the two actions are
strictly associative and unital, and commute (`TauCeti.MoorePathBetween`).  So the normalized
cubical chains `C_*(P_{b→b'} B; R)` form a differential graded
`(C_*(Ω_b B; R), C_*(Ω_{b'} B; R))`-bimodule.  The derived tensor product with this bimodule
carries DG local systems at `b` to DG local systems at `b'`, which is how a DG local system
changes basepoint.

The chains are the module
`TauCeti.cubicalChainModule (MoorePathBetween B b b') (MooreLoopSpace B b') R` of
`TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Action`, whose left action is that of
`TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule`.

## Main definitions

* `TauCeti.pathChainPoint`: the `0`-chain of a single Moore path.

## Main results

* `TauCeti.pathChain_isDGBimodule`: the chains `C_*(P_{b→b'} B; R)` form a DG
  `(C_*(Ω_b B), C_*(Ω_{b'} B))`-bimodule, bundled as `TauCeti.pathChainBimodule`.
* `TauCeti.cubicalChainModuleLinearMap_moorePathBetweenMap_smul`,
  `TauCeti.cubicalChainModuleLinearMap_moorePathBetweenMap_op_smul`: pushing path chains forward
  along a continuous map `f` is semilinear for both actions, through `C_*(Ωf)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public section

namespace TauCeti

variable (B : Type*) [TopologicalSpace B] (b b' : B) (R : Type*) [CommRing R]

/-- **The chains of the Moore paths from `b` to `b'` form a differential graded
`(C_*(Ω_b B), C_*(Ω_{b'} B))`-bimodule**: the loops at `b` act by concatenation in front, those
at `b'` by concatenation behind, the chains of dimension `n` lie in cohomological degree `-n`, and
the boundary is the differential. -/
theorem pathChain_isDGBimodule :
    IsDGBimodule (loopChain_isDGAlgebra B b R) (loopChain_isDGAlgebra B b' R)
      (cubicalChainModuleGrading (MoorePathBetween B b b') (MooreLoopSpace B b') R)
      (cubicalChainModuleDifferential (MoorePathBetween B b b') (MooreLoopSpace B b') R) :=
  cubicalChainModule_isDGBimodule (MooreLoopSpace B b) (MoorePathBetween B b b')
    (MooreLoopSpace B b') R

/-- **The chains of Moore paths from `b` to `b'`**, as an object of the category of DG
`(C_*(Ω_b B), C_*(Ω_{b'} B))`-bimodules. -/
noncomputable abbrev pathChainBimodule :
    DGBimoduleCat (loopChain_isDGAlgebra B b R) (loopChain_isDGAlgebra B b' R) :=
  DGBimoduleCat.of (pathChain_isDGBimodule B b b' R)

section Point

variable {B b b' R}

variable (R) in
/-- The `0`-chain of a path. -/
noncomputable def pathChainPoint (δ : MoorePathBetween B b b') :
    cubicalChainModule (MoorePathBetween B b b') (MooreLoopSpace B b') R :=
  cubicalChainModuleLof _ _ R 0 (NormalizedCubicalChain.ofCube _ R (SingularCube.point δ))

/-- The `0`-chain of a path is the class of the constant `0`-cube at the path. -/
theorem pathChainPoint_def (δ : MoorePathBetween B b b') :
    pathChainPoint R δ =
      cubicalChainModuleLof (MoorePathBetween B b b') (MooreLoopSpace B b') R 0
        (NormalizedCubicalChain.ofCube (MoorePathBetween B b b') R (SingularCube.point δ)) :=
  (rfl)

/-- The `0`-chain of a path has degree `0`. -/
theorem pathChainPoint_mem (δ : MoorePathBetween B b b') :
    pathChainPoint R δ ∈
      cubicalChainModuleGrading (MoorePathBetween B b b') (MooreLoopSpace B b') R 0 :=
  mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨0, _, by simp, rfl⟩)

/-- The `0`-chain of a path is a cycle. -/
@[simp]
theorem cubicalChainModuleDifferential_pathChainPoint (δ : MoorePathBetween B b b') :
    cubicalChainModuleDifferential _ _ R (pathChainPoint R δ) = 0 :=
  cubicalChainModuleDifferential_lof_zero _

end Point

section Map

open MulOpposite

variable {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B'] {R : Type*} [CommRing R]
  (f : C(B', B)) {a b : B'}

/-- Pushing path chains forward along `f` is semilinear for the loops acting in front, through
`C_*(Ωf)`. -/
theorem cubicalChainModuleLinearMap_moorePathBetweenMap_smul (α : loopChainAlgebra B' a R)
    (x : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    cubicalChainModuleLinearMap (G' := MooreLoopSpace B (f b)) R (MoorePathBetween.map f)
        (α • x) =
      loopChainMap R f rfl α • cubicalChainModuleLinearMap R (MoorePathBetween.map f) x := by
  induction α using DirectSum.induction_on with
  | zero => rw [zero_smul, map_zero, map_zero, zero_smul]
  | add α α' hα hα' => rw [add_smul, map_add, hα, hα', map_add, add_smul]
  | of p y =>
    rw [← DirectSum.lof_eq_of R, loopChainMap_lof, cubicalChainModuleLinearMap_smul_map _
      (MooreLoopSpace.map f rfl).toContinuousMap (MoorePathBetween.map_smul f),
      cubicalChainSumMap_lof]

/-- Pushing path chains forward along `f` is semilinear for the loops acting behind, through
`C_*(Ωf)`. -/
theorem cubicalChainModuleLinearMap_moorePathBetweenMap_op_smul (α : loopChainAlgebra B' b R)
    (x : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    cubicalChainModuleLinearMap (G' := MooreLoopSpace B (f b)) R (MoorePathBetween.map f)
        (op α • x) =
      op (loopChainMap R f rfl α) • cubicalChainModuleLinearMap R (MoorePathBetween.map f) x := by
  induction α using DirectSum.induction_on with
  | zero => rw [op_zero, zero_smul, map_zero, map_zero, op_zero, zero_smul]
  | add α α' hα hα' =>
    rw [op_add, add_smul, map_add, hα, hα', map_add, op_add, add_smul]
  | of p y =>
    rw [← DirectSum.lof_eq_of R, loopChainMap_lof, cubicalChainModuleLinearMap_op_smul_map _
      (MooreLoopSpace.map f rfl).toContinuousMap (fun ω γ ↦ MoorePathBetween.map_op_smul f ω γ),
      cubicalChainSumMap_lof]

end Map

end TauCeti
