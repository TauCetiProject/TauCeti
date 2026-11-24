/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
public import TauCeti.Topology.Homotopy.MappingPath.PathFibration
public import TauCeti.Topology.Homotopy.Path
public import TauCeti.Topology.PathComponent
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# Spaces whose loop space has the homology of a point

Let `X` be a path-connected space and `x` a point of `X`. If the loop space `Ω X x` has the
homology of a point with coefficients in a ring `R` in degrees at most `k`, then so does `X`
(`TauCeti.isIso_singularHomologyMap_of_isIso_loopSpace`). In particular `X` then has no homology
in the positive degrees at most `k` (`TauCeti.isZero_singularHomology_of_isIso_loopSpace`). Without
the connectedness hypothesis the conclusion holds for the path component of `x`, which has the
same loop space (`TauCeti.isIso_singularHomologyMap_pathComponent_of_isIso_loopSpace`). The
same holds for the Moore loop space
(`TauCeti.isIso_singularHomologyMap_of_isIso_mooreLoopSpace`,
`TauCeti.isIso_singularHomologyMap_pathComponent_of_isIso_mooreLoopSpace`).

The proof is the spectral sequence argument for the path fibration `Ω X x → P → X`, with total
space the paths ending at `x`, done through the comparison theorem for Serre fibrations
(`TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point`) rather than through the
second page. The projection to the starting point is a Hurewicz fibration
(`TauCeti.MappingPathFiber.isHurewiczFibration_proj`). Its fibre over `b` is homotopy equivalent
to `Ω X x` once a path from `b` to `x` is chosen
(`TauCeti.MappingPathFiber.projFiberHomotopyEquivLoopSpace`), which is possible for every `b`
because `X` is path connected. So every fibre has the homology of a point, the projection is a
homology isomorphism, and the total space is contractible. No simple connectivity of `X` is
needed.

Applied to the loop space `Ω Q x` of a space `Q` and its constant loop, whose path component is
the space `Ω₀Q` of contractible based loops, this shows that if the double loop space `Ω²Q` has
the homology of a point in degrees at most `k`, so does `Ω₀Q`. With coefficients in `𝔽₂` this is
the step in the proof of Theorem 5.15 of Barraud–Damian–Humilière–Oancea that passes from mod-two
acyclicity of `Ω²Q` to that of `Ω₀Q`, to which the mod-two vanishing theorem for the homotopy
groups of a simply connected space then applies.

## Main results

* `TauCeti.isIso_singularHomologyMap_of_isIso_loopSpace`: if `Ω X x` has the homology of a point
  in degrees at most `k` and `X` is path connected, then `X` has the homology of a point in
  degree `k`.
* `TauCeti.isZero_singularHomology_of_isIso_loopSpace`: the corresponding vanishing of the
  homology of `X` in positive degrees.
* `TauCeti.isIso_singularHomologyMap_pathComponent_of_isIso_loopSpace`: the same for the path
  component of `x` in an arbitrary space.
* `TauCeti.isIso_singularHomologyMap_of_isIso_mooreLoopSpace`,
  `TauCeti.isIso_singularHomologyMap_pathComponent_of_isIso_mooreLoopSpace`: the same with the
  Moore loop space.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter IV.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, proof of Theorem 5.15.
-/

public section

open CategoryTheory Limits AlgebraicTopology
open scoped Topology.Homotopy

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] (R : Type u) [Ring R]

/-- The fibre over `b` of the path fibration `P → X`, the paths from `b` to `x`, is homotopy
equivalent to the loop space `Ω X x` once a path from `b` to `x` is chosen. So the fibre has the
homology of a point in every degree in which `Ω X x` has. -/
private theorem isIso_singularHomologyMap_mappingPathFiber_fiber (x b : X) (α : Path b x) (q : ℕ)
    (h : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map
      (TopCat.isTerminalPUnit.from (TopCat.of (Ω X x))))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map
      (TopCat.isTerminalPUnit.from ((TopCat.ofHom
        (MappingPathFiber.proj (ContinuousMap.id X) x)).fiber b))) := by
  let e := MappingPathFiber.projFiberHomotopyEquivLoopSpace (ContinuousMap.id X) x b α
  -- The fibre of the projection over `b` is, by definition, the subtype of the paths from `b`.
  let f : (TopCat.ofHom (MappingPathFiber.proj (ContinuousMap.id X) x)).fiber b ⟶
      TopCat.of (Ω X x) := TopCat.ofHom e.toFun
  exact (isIso_singularHomologyMap_isTerminalPUnit_from_iff (ModuleCat.of R R) f q h).2
    (e.isWeakHomotopyEquivalence.isIso_singularHomologyMap (ModuleCat.of R R) q)

/-- **A path-connected space whose loop space has the homology of a point has the homology of a
point.** If `X` is path connected and, for every `q ≤ k`, the map from the loop space `Ω X x` to a
point induces an isomorphism on `Hq(-; R)`, then so does the map from `X` to a point in
degree `k`. The proof applies the comparison theorem to the path fibration `Ω X x → P → X`, whose
total space is contractible. -/
theorem isIso_singularHomologyMap_of_isIso_loopSpace [PathConnectedSpace X] (x : X) (k : ℕ)
    (h : ∀ q ≤ k, IsIso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (TopCat.isTerminalPUnit.from (TopCat.of (Ω X x))))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
      (TopCat.isTerminalPUnit.from (TopCat.of X))) := by
  let H := (singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)
  -- The path fibration: the paths ending at `x`, projected to their starting points.
  let p : TopCat.of (MappingPathFiber (ContinuousMap.id X) x) ⟶ TopCat.of X :=
    TopCat.ofHom (MappingPathFiber.proj (ContinuousMap.id X) x)
  have hp : TopCat.serreFibrations p :=
    (MappingPathFiber.isHurewiczFibration_proj.{u} (ContinuousMap.id X) x).mem_serreFibrations
  have hpk : IsIso (H.map p) := TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point hp R k
    fun b q hq ↦ isIso_singularHomologyMap_mappingPathFiber_fiber R x b
      (PathConnectedSpace.somePath b x) q (h q hq)
  -- The total space is contractible, so its map to a point is a homology isomorphism.
  have hE : IsIso (H.map (p ≫ TopCat.isTerminalPUnit.from (TopCat.of X))) := by
    rw [TopCat.isTerminalPUnit.hom_ext (p ≫ TopCat.isTerminalPUnit.from _)
      (TopCat.isTerminalPUnit.from _)]
    infer_instance
  rw [H.map_comp] at hE
  exact IsIso.of_isIso_comp_left (H.map p) _

/-- **A path-connected space whose loop space has the homology of a point has no positive-degree
homology.** If `X` is path connected and the map from `Ω X x` to a point induces isomorphisms on
`Hq(-; R)` for every `q ≤ k`, then `Hₖ(X; R) = 0` for `k ≠ 0`. -/
theorem isZero_singularHomology_of_isIso_loopSpace [PathConnectedSpace X] (x : X) {k : ℕ}
    (hk : k ≠ 0)
    (h : ∀ q ≤ k, IsIso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (TopCat.isTerminalPUnit.from (TopCat.of (Ω X x))))) :
    IsZero ((((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R))).obj
      (TopCat.of X)) :=
  have := isIso_singularHomologyMap_of_isIso_loopSpace R x k h
  (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{u} R) k
    (ModuleCat.of R R) (TopCat.of PUnit.{u + 1}) hk).of_iso
      (asIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
        (TopCat.isTerminalPUnit.from (TopCat.of X))))

/-- **The path component of a point whose loop space has the homology of a point has the homology
of a point.** For an arbitrary space `X`, if the map from `Ω X x` to a point induces isomorphisms on
`Hq(-; R)` for every `q ≤ k`, then so does the map from the path component of `x`, with the
subspace topology, in degree `k`. The path component has the same loop space at `x`
(`Path.subtypeValHomeomorph`). For `X = Ω Q x` and `x` the constant loop, the path component is
the space `Ω₀Q` of contractible loops, and the hypothesis is on the double loop space `Ω²Q`. -/
theorem isIso_singularHomologyMap_pathComponent_of_isIso_loopSpace (x : X) (k : ℕ)
    (h : ∀ q ≤ k, IsIso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (TopCat.isTerminalPUnit.from (TopCat.of (Ω X x))))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
      (TopCat.isTerminalPUnit.from (TopCat.of (pathComponent x)))) := by
  refine isIso_singularHomologyMap_of_isIso_loopSpace R (pathComponentSelf x) k fun q hq ↦ ?_
  -- The loops at `x` in its path component are the loops of `X` at `x`.
  let e : TopCat.of (Ω (pathComponent x) (pathComponentSelf x)) ≅ TopCat.of (Ω X x) :=
    TopCat.isoOfHomeo (Path.subtypeValHomeomorph subset_rfl)
  exact (isIso_singularHomologyMap_isTerminalPUnit_from_iff (ModuleCat.of R R) e.hom q
    (h q hq)).2 inferInstance

/-- The loop space `Ω X x` has the homology of a point in every degree in which the Moore loop
space has, since the two are homotopy equivalent (`TauCeti.MooreLoopSpace.homotopyEquivPath`). -/
private theorem isIso_singularHomologyMap_loopSpace_of_isIso_mooreLoopSpace (x : X) (q : ℕ)
    (h : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (TopCat.isTerminalPUnit.from (TopCat.of (MooreLoopSpace X x))))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (TopCat.isTerminalPUnit.from (TopCat.of (Ω X x)))) :=
  let e := (MooreLoopSpace.homotopyEquivPath x).symm
  (isIso_singularHomologyMap_isTerminalPUnit_from_iff (ModuleCat.of R R)
    (TopCat.ofHom e.toFun) q h).2
      (e.isWeakHomotopyEquivalence.isIso_singularHomologyMap (ModuleCat.of R R) q)

/-- **A path-connected space whose Moore loop space has the homology of a point has the homology
of a point.** This is `TauCeti.isIso_singularHomologyMap_of_isIso_loopSpace` for the Moore loop
space `MooreLoopSpace X x`, which is homotopy equivalent to `Ω X x`
(`TauCeti.MooreLoopSpace.homotopyEquivPath`). -/
theorem isIso_singularHomologyMap_of_isIso_mooreLoopSpace [PathConnectedSpace X] (x : X) (k : ℕ)
    (h : ∀ q ≤ k, IsIso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (TopCat.isTerminalPUnit.from (TopCat.of (MooreLoopSpace X x))))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
      (TopCat.isTerminalPUnit.from (TopCat.of X))) :=
  isIso_singularHomologyMap_of_isIso_loopSpace R x k fun q hq ↦
    isIso_singularHomologyMap_loopSpace_of_isIso_mooreLoopSpace R x q (h q hq)

/-- **The path component of a point whose Moore loop space has the homology of a point has the
homology of a point.** This is `TauCeti.isIso_singularHomologyMap_pathComponent_of_isIso_loopSpace`
for the Moore loop space `MooreLoopSpace X x`. For `X = MooreLoopSpace Q x` and its unit `1`, the
path component is the space of contractible Moore loops, and the hypothesis is on the double Moore
loop space. -/
theorem isIso_singularHomologyMap_pathComponent_of_isIso_mooreLoopSpace (x : X) (k : ℕ)
    (h : ∀ q ≤ k, IsIso (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).map (TopCat.isTerminalPUnit.from (TopCat.of (MooreLoopSpace X x))))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
      (TopCat.isTerminalPUnit.from (TopCat.of (pathComponent x)))) :=
  isIso_singularHomologyMap_pathComponent_of_isIso_loopSpace R x k fun q hq ↦
    isIso_singularHomologyMap_loopSpace_of_isIso_mooreLoopSpace R x q (h q hq)

end TauCeti
