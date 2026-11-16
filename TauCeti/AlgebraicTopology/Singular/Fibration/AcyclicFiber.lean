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

Let `R` be a ring. A path-connected space `F` has the `R`-homology of a point in degrees at most `k`
if and only if `H_q(F; R)` vanishes for `1 ≤ q ≤ k`
(`TauCeti.TopCat.isIso_singularHomologyMap_to_point_of_subsingleton`). Combined with the homology
comparison theorem for Serre fibrations
(`TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point`), this gives:

* If `p : E ⟶ B` is a Serre fibration whose fibres are path-connected with vanishing `R`-homology
  in degrees `1 ≤ q ≤ k`, then `p` induces an isomorphism `H_k(E; R) ≅ H_k(B; R)`
  (`TauCeti.TopCat.isIso_singularHomologyMap_of_subsingleton_fiber`).
* More generally, if every fibre of `p` is homotopy equivalent to a fixed path-connected space `F`
  with `H_q(F; R) = 0` for `1 ≤ q ≤ k`, then `p` induces an isomorphism
  `H_k(E; R) ≅ H_k(B; R)` (`TauCeti.TopCat.isIso_singularHomologyMap_of_homotopyEquiv_fiber`).
* Applied to the fixed-end path fibration `MappingPathFiber (ContinuousMap.id X) x ⟶ X` over a
  path-connected space `X`, whose total space is contractible and whose fibres are homotopy
  equivalent to the loop space `Ω X x`, vanishing of `H_q(Ω X x; R)` for `1 ≤ q ≤ k + 1` (with
  `Ω X x` path-connected) implies vanishing of `H_{k + 1}(X; R)`
  (`TauCeti.subsingleton_singularHomology_of_loopSpace`).

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
    exact IsIso.of_isIso_fac_right
      (singularHomologyMap_singularHomology₀ε (ModuleCat.of R R)
        (_root_.TopCat.isTerminalPUnit.from X))
  | succ m =>
    have : Subsingleton
        (((singularHomologyFunctor (ModuleCat.{u} R) (m + 1)).obj (ModuleCat.of R R)).obj X) :=
      hX m.succ_ne_zero
    exact (ModuleCat.isZero_iff_subsingleton.mpr this).isIso
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
  have hfac :
      _root_.TopCat.ofHom e.toFun ≫ _root_.TopCat.isTerminalPUnit.from (_root_.TopCat.of F) =
        _root_.TopCat.isTerminalPUnit.from (_root_.TopCat.of X) :=
    _root_.TopCat.isTerminalPUnit.hom_ext _ _
  have he : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).map
      (_root_.TopCat.ofHom e.toFun)) :=
    e.singularHomologyIso_hom (ModuleCat.of R R) k ▸
      (e.singularHomologyIso (ModuleCat.of R R) k).isIso_hom
  have hpt := isIso_singularHomologyMap_to_point_of_subsingleton (_root_.TopCat.of F) R k hF
  rw [← hfac, Functor.map_comp]
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
  have hp : TopCat.serreFibrations p :=
    (MappingPathFiber.isHurewiczFibration_proj.{0} (ContinuousMap.id X) x).mem_serreFibrations
  have hiso : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
      (ModuleCat.of R R)).map p) :=
    TopCat.isIso_singularHomologyMap_of_homotopyEquiv_fiber hp
      (fun b ↦ ⟨MappingPathFiber.projFiberHomotopyEquivLoopSpace (ContinuousMap.id X) x b
        (PathConnectedSpace.somePath b x)⟩)
      R (k + 1) hΩ
  have : Subsingleton (((singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
      (ModuleCat.of R R)).obj (TopCat.of (MappingPathFiber (ContinuousMap.id X) x))) :=
    ModuleCat.subsingleton_singularHomology_of_contractibleSpace (ModuleCat.of R R) _ k
  exact (asIso (((singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
    (ModuleCat.of R R)).map p)).toLinearEquiv.toEquiv.symm.subsingleton

end TauCeti
