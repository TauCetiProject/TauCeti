/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SerreClass.PowerTorsion
public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
public import TauCeti.CategoryTheory.ObjectProperty.KilledBy
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent
public import TauCeti.Topology.Homotopy.MappingPath.PathFibration
public import TauCeti.Topology.PathComponent
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# The homology of a space modulo a Serre class, from that of its loop space

Let `Y` be a path-connected space with trivial fundamental group at `y`, let `P` be a Serre class of
`R`-modules, and let `Q ≤ P` be a property containing zero and closed under isomorphisms and
direct sums, such as the modules killed by a fixed integer inside the Serre class of modules killed
by some power of it. If the homology of the loop space `Ω Y y` lies in `Q` in the positive degrees
up to `k`, then the homology of `Y` in the positive degree `k` lies in `P`
(`TauCeti.prop_singularHomology_of_prop_loopSpace`). This is the comparison theorem modulo a Serre
class (`TauCeti.TopCat.prop_singularHomology_of_contractibleSpace`) for the based path fibration of
`Y`: its total space, the paths ending at `y`, is contractible, and its fibres are homotopy
equivalent to `Ω Y y`, which is path connected because `π₁(Y, y)` is trivial.

The application is to the space `Ω₀X` of contractible loops of a pointed space `(X, x)`, the path
component of the constant loop in `Ω X x`. Its loop space is the double loop space
`Ω (Ω X x) (Path.refl x)` (`Path.subtypeHomeomorphOfPathComponentSubset`), and its fundamental
group is `π₂(X, x)`. So when `π₂(X, x)` is trivial, a property of the homology of the double loop
space modulo `Q` passes to the homology of `Ω₀X` modulo `P`
(`TauCeti.prop_singularHomology_pathComponent_refl_of_prop_doubleLoopSpace`). For the integers and
a natural number `d`: if `d` kills the integral homology of `Ω²X` in the positive degrees up to
`k`, then some power of `d` kills `Hₖ(Ω₀X; ℤ)`
(`TauCeti.exists_pow_smul_eq_zero_singularHomology_pathComponent_refl`).

This is the spectral-sequence step in the proof of the second part of Proposition 5.11 of
Barraud–Damian–Humilière–Oancea. There, if the reduced homology of `Ω²Q`, which is the kernel of
`i_{Q*}`, were killed by `d`, the Leray–Serre spectral sequence of the path-loop fibration
`Ω²Q → P Ω₀Q → Ω₀Q` would make every `Hₗ(Ω₀Q; ℤ)` killed by a power of `d`. Here the comparison
theorem modulo a Serre class replaces the spectral sequence.

## Main results

* `TauCeti.prop_singularHomology_of_prop_loopSpace`: for a path-connected space with trivial
  fundamental group, homology of the loop space in `Q` gives homology of the space in `P`.
* `TauCeti.prop_singularHomology_pathComponent_refl_of_prop_doubleLoopSpace`: if `π₂(X, x)` is
  trivial, homology of `Ω²X` in `Q` gives homology of the contractible loops `Ω₀X` in `P`.
* `TauCeti.exists_pow_smul_eq_zero_singularHomology_pathComponent_refl`: if `π₂(X, x)` is trivial
  and `d` kills the integral homology of `Ω²X` in the positive degrees up to `k`, then some power
  of `d` kills `Hₖ(Ω₀X; ℤ)`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Chapter I.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, proof of Proposition 5.11.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti

section General

variable {R : Type u} [Ring R] (P Q : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
  [Q.IsClosedUnderIsomorphisms] [Q.ContainsZero]
  [∀ J : Type u, Q.IsClosedUnderColimitsOfShape (Discrete J)]

/-- **The homology of a simply connected space modulo a Serre class, from its loop space.** Let `P`
be a Serre class of `R`-modules and `Q ≤ P` a property containing zero and closed under
isomorphisms and direct sums. Let `Y` be a path-connected space with trivial fundamental group at
`y`. If the `R`-homology of the loop space `Ω Y y` lies in `Q` in the positive degrees `q ≤ k`, then
the `R`-homology of `Y` in the positive degree `k` lies in `P`. -/
theorem prop_singularHomology_of_prop_loopSpace (hQP : Q ≤ P) {Y : Type u} [TopologicalSpace Y]
    [PathConnectedSpace Y] (y : Y) (hY : Subsingleton (π_ 1 Y y)) {k : ℕ} (hk : k ≠ 0)
    (hΩ : ∀ q, q ≠ 0 → q ≤ k → Q (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (TopCat.of (Ω Y y)))) :
    P (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of Y)) := by
  -- The based path fibration `P → Y`, sending a path ending at `y` to its starting point.
  let p : TopCat.of (MappingPathFiber (ContinuousMap.id Y) y) ⟶ TopCat.of Y :=
    TopCat.ofHom (MappingPathFiber.proj _ y)
  have hp : TauCeti.TopCat.serreFibrations p :=
    (MappingPathFiber.isHurewiczFibration_proj.{u} _ _).mem_serreFibrations
  have : PathConnectedSpace (Ω Y y) := (pathConnectedSpace_loopSpace_iff_subsingleton_pi1 y).2 hY
  -- Every fibre is homotopy equivalent to the loop space.
  let e (b : Y) : ContinuousMap.HomotopyEquiv (p.fiber b) (Ω Y y) :=
    MappingPathFiber.projFiberHomotopyEquivLoopSpace _ y b (PathConnectedSpace.somePath _ _)
  exact TauCeti.TopCat.prop_singularHomology_of_contractibleSpace P Q hQP hp hk
    (fun b ↦ (e b).symm.pathConnectedSpace)
    fun b q hq hqk ↦ Q.prop_of_iso ((e b).singularHomologyIso _ q).symm (hΩ q hq hqk)

/-- **The homology of the contractible loops modulo a Serre class, from the double loop space.**
Let `P` be a Serre class of `R`-modules and `Q ≤ P` a property containing zero and closed under
isomorphisms and direct sums. Let `(X, x)` be a pointed space with `π₂(X, x)` trivial. If the
`R`-homology of the double loop space `Ω (Ω X x) (Path.refl x)` lies in `Q` in the positive degrees
`q ≤ k`, then the `R`-homology in the positive degree `k` of the contractible loops `Ω₀X`, the path
component of the constant loop in `Ω X x`, lies in `P`. -/
theorem prop_singularHomology_pathComponent_refl_of_prop_doubleLoopSpace (hQP : Q ≤ P)
    {X : Type u} [TopologicalSpace X] (x : X) (hX : Subsingleton (π_ 2 X x)) {k : ℕ} (hk : k ≠ 0)
    (hΩ : ∀ q, q ≠ 0 → q ≤ k → Q (((singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).obj (TopCat.of (Ω (Ω X x) (Path.refl x))))) :
    P (((singularHomologyFunctor (ModuleCat.{u} R) k).obj (ModuleCat.of R R)).obj
      (TopCat.of (pathComponent (Path.refl x)))) := by
  let y : pathComponent (Path.refl x) := ⟨Path.refl x, mem_pathComponent_self _⟩
  have hS : pathComponent (y : Ω X x) ⊆ pathComponent (Path.refl x) := subset_rfl
  have : PathConnectedSpace (pathComponent (Path.refl x)) :=
    isPathConnected_iff_pathConnectedSpace.1 isPathConnected_pathComponent
  -- The loop space of the path component is the double loop space.
  let e : Ω (pathComponent (Path.refl x)) y ≃ₜ Ω (Ω X x) (Path.refl x) :=
    Path.subtypeHomeomorphOfPathComponentSubset hS
  -- Its fundamental group is `π₁(Ω X x) ≅ π₂(X, x)`.
  have hY : Subsingleton (π_ 1 (pathComponent (Path.refl x)) y) := by
    have := (subsingleton_homotopyGroup_loopSpace_iff x 1).2 hX
    exact (HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset (N := Fin 1) hS
      rfl).1.subsingleton
  exact prop_singularHomology_of_prop_loopSpace P Q hQP y hY hk fun q hq hqk ↦
    Q.prop_of_iso (e.toHomotopyEquiv.singularHomologyIso _ q).symm (hΩ q hq hqk)

end General

/-- **A power of `d` kills the homology of the contractible loops.** Let `(X, x)` be a pointed space
with `π₂(X, x)` trivial, and `d` a natural number which kills the integral homology of the double
loop space `Ω (Ω X x) (Path.refl x)` in every positive degree `q ≤ k`. Then some power of `d` kills
the integral homology in the positive degree `k` of the contractible loops `Ω₀X`, the path component
of the constant loop in `Ω X x`. -/
theorem exists_pow_smul_eq_zero_singularHomology_pathComponent_refl {X : Type} [TopologicalSpace X]
    (x : X) (hX : Subsingleton (π_ 2 X x)) (d : ℕ) {k : ℕ} (hk : k ≠ 0)
    (hΩ : ∀ q, q ≠ 0 → q ≤ k → ∀ z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Ω (Ω X x) (Path.refl x))), (d : ℤ) • z = 0) :
    ∃ n : ℕ, ∀ z : ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (pathComponent (Path.refl x))), ((d : ℤ) ^ n) • z = 0 := by
  -- Apply the general theorem to the Serre class of `ℤ`-modules killed by some power of `d`, and
  -- the modules killed by `d ^ 1`.
  refine (AddCommGrpCat.prop_inverseImage_isKilledBySomePower_iff d _).1 <|
    prop_singularHomology_pathComponent_refl_of_prop_doubleLoopSpace _ _
      (AddCommGrpCat.isKilledBy_pow_le_inverseImage_isKilledBySomePower d 1) x hX hk
      fun q hq hqk ↦ (ModuleCat.prop_isKilledBy_iff _ _).2 fun z ↦ ?_
  rw [pow_one, ← natCast_zsmul]
  exact hΩ q hq hqk z

end TauCeti
