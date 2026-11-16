/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
public import TauCeti.Topology.Homotopy.MappingPath.PathFibration
import TauCeti.AlgebraicTopology.Singular.Contractible

/-!
# Serre fibrations with acyclic fibres and the path fibration

A path-connected space `F` has the `R`-homology of a point through degree `k` whenever
`H_q(F; R) = 0` for `1 ≤ q ≤ k`. Combined with the Serre-fibration homology comparison theorem
(`TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point`), this yields homology
isomorphisms for Serre fibrations with `R`-acyclic fibres and acyclicity transfer from a loop space
`Ω X x` to its base `X` via the fixed-end path fibration.

## Main results

* `TauCeti.TopCat.isIso_singularHomologyMap_to_point_of_subsingleton`: the map from a
  path-connected space `X` to a point induces an isomorphism on `H_k(-; R)` whenever `k = 0` or
  `H_k(X; R) = 0`.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_subsingleton_fiber`: a Serre fibration with
  path-connected fibres that are `R`-acyclic through degree `k` induces an isomorphism on
  `H_k(-; R)`.
* `TauCeti.TopCat.isIso_singularHomologyMap_of_homotopyEquiv_fiber`: the same when every fibre is
  homotopy equivalent to a path-connected `R`-acyclic model fibre `F`.
* `TauCeti.subsingleton_singularHomology_of_loopSpace`: if `X` and `Ω X x` are path-connected and
  `H_q(Ω X x; R) = 0` for `1 ≤ q ≤ k + 1`, then `H_{k + 1}(X; R) = 0`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.3, path-loop fibrations.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti

namespace TopCat

/-- For a path-connected space `X` and a ring `R`, the map `X ⟶ PUnit` induces an isomorphism on
`H_k(-; R)` whenever `k = 0` or `H_k(X; R) = 0`. -/
theorem isIso_singularHomologyMap_to_point_of_subsingleton (X : _root_.TopCat.{u})
    [PathConnectedSpace X] (R : Type u) [Ring R] (k : ℕ)
    (hX : k ≠ 0 →
      Subsingleton (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).obj X)) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
      (_root_.TopCat.isTerminalPUnit.from X)) := by
  cases k with
  | zero =>
    exact IsIso.of_isIso_fac_right (singularHomologyMap_singularHomology₀ε (ModuleCat.of R R)
      (_root_.TopCat.isTerminalPUnit.from X))
  | succ m =>
    exact (ModuleCat.isZero_iff_subsingleton.mpr (hX m.succ_ne_zero)).isIso
      (isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of R R)
        (_root_.TopCat.of PUnit) m.succ_ne_zero) _

/-- If `X` is homotopy equivalent to a path-connected space `F` with `H_k(F; R) = 0` (or `k = 0`),
then `X ⟶ PUnit` induces an isomorphism on `H_k(-; R)`. -/
theorem isIso_singularHomologyMap_to_point_of_homotopyEquiv {X F : Type u} [TopologicalSpace X]
    [TopologicalSpace F] [PathConnectedSpace F] (e : ContinuousMap.HomotopyEquiv X F)
    (R : Type u) [Ring R] (k : ℕ)
    (hF : k ≠ 0 →
      Subsingleton (((singularHomologyFunctor (ModuleCat.{u} R) k).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of F))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
      (_root_.TopCat.isTerminalPUnit.from (_root_.TopCat.of X))) := by
  have he : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
      (_root_.TopCat.ofHom e.toFun)) :=
    e.singularHomologyIso_hom (ModuleCat.of R R) k ▸
      (e.singularHomologyIso (ModuleCat.of R R) k).isIso_hom
  have := isIso_singularHomologyMap_to_point_of_subsingleton (_root_.TopCat.of F) R k hF
  rw [← _root_.TopCat.isTerminalPUnit.hom_ext
      (_root_.TopCat.ofHom e.toFun ≫ _root_.TopCat.isTerminalPUnit.from (_root_.TopCat.of F))
      (_root_.TopCat.isTerminalPUnit.from (_root_.TopCat.of X)), Functor.map_comp]
  exact IsIso.comp_isIso

/-- **A Serre fibration with `R`-acyclic path-connected fibres induces an isomorphism on
`H_k(-; R)`.** -/
theorem isIso_singularHomologyMap_of_subsingleton_fiber {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) (R : Type u) [Ring R] (k : ℕ)
    (hpc : ∀ b : B, PathConnectedSpace (p.fiber b))
    (hfib : ∀ b : B, ∀ q, 1 ≤ q → q ≤ k →
      Subsingleton (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (p.fiber b))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map p) :=
  isIso_singularHomologyMap_of_isIso_fiber_to_point hp R k fun b q hq ↦
    have := hpc b
    isIso_singularHomologyMap_to_point_of_subsingleton (p.fiber b) R q fun hq0 ↦
      hfib b q (Nat.pos_of_ne_zero hq0) hq

/-- **A Serre fibration whose fibres are homotopy equivalent to a path-connected `R`-acyclic model
fibre `F` induces an isomorphism on `H_k(-; R)`.** -/
theorem isIso_singularHomologyMap_of_homotopyEquiv_fiber {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) {F : Type u} [TopologicalSpace F] [PathConnectedSpace F]
    (hhe : ∀ b : B, Nonempty (ContinuousMap.HomotopyEquiv (p.fiber b) F))
    (R : Type u) [Ring R] (k : ℕ)
    (hF : ∀ q, 1 ≤ q → q ≤ k →
      Subsingleton (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of F))) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map p) :=
  isIso_singularHomologyMap_of_isIso_fiber_to_point hp R k fun b q hq ↦
    let ⟨e⟩ := hhe b
    isIso_singularHomologyMap_to_point_of_homotopyEquiv e R q fun hq0 ↦
      hF q (Nat.pos_of_ne_zero hq0) hq

end TopCat

/-- **Path-fibration acyclicity transfer**: if `X` and its loop space `Ω X x` are path-connected
and `H_q(Ω X x; R) = 0` for `1 ≤ q ≤ k + 1`, then `H_{k + 1}(X; R) = 0`. -/
theorem subsingleton_singularHomology_of_loopSpace {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) [PathConnectedSpace (Ω X x)] (R : Type u) [Ring R] (k : ℕ)
    (hΩ : ∀ q, 1 ≤ q → q ≤ k + 1 →
      Subsingleton (((singularChains R).obj (TopCat.of (Ω X x))).homology q)) :
    Subsingleton (((singularChains R).obj (TopCat.of X)).homology (k + 1)) := by
  let p : TopCat.of (MappingPathFiber (ContinuousMap.id X) x) ⟶ TopCat.of X :=
    TopCat.ofHom (MappingPathFiber.proj (ContinuousMap.id X) x)
  have : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
      (ModuleCat.of R R)).map p) :=
    TopCat.isIso_singularHomologyMap_of_homotopyEquiv_fiber
      (MappingPathFiber.isHurewiczFibration_proj.{0} (ContinuousMap.id X) x).mem_serreFibrations
      (fun b ↦ ⟨MappingPathFiber.projFiberHomotopyEquivLoopSpace (ContinuousMap.id X) x b
        (PathConnectedSpace.somePath b x)⟩)
      R (k + 1) hΩ
  have := ModuleCat.subsingleton_singularHomology_of_contractibleSpace (ModuleCat.of R R)
    (TopCat.of (MappingPathFiber (ContinuousMap.id X) x)) k
  exact (asIso (((singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
    (ModuleCat.of R R)).map p)).toLinearEquiv.toEquiv.symm.subsingleton

end TauCeti
