/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology
public import TauCeti.Geometry.Manifold.ModelTransport.Finrank
import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.CodimensionOne
import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Topology.Instances.Shrink

/-!
# The first homotopy groups of a closed simply connected three-manifold

For a closed simply connected topological three-manifold, Poincaré duality gives
`H₂(M; ℤ) = 0`. Hurewicz in degree two then shows that the manifold is 2-connected.
Hurewicz in degree three identifies `π₃(M, x)` with the infinite cyclic top homology.

The integer coordinate uses local homology at a fixed reference point. Keeping this point
fixed lets a based class move along a path without changing its coordinate.

## References

* A. Hatcher, *Algebraic Topology*, Theorems 3.26, 3.30 and 4.32.
-/

public section

noncomputable section

open AlgebraicTopology Module

universe u

namespace TauCeti

variable {M : Type u} {E : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [SimplyConnectedSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M]

/-- A closed simply connected three-manifold is 2-connected at every basepoint. -/
theorem subsingleton_homotopyGroup_threeManifold_of_lt (hd : finrank ℝ E = 3) (x : M)
    {k : ℕ} (hk : k < 3) : Subsingleton (HomotopyGroup (Fin k) M x) := by
  by_cases h : k < 2
  · exact subsingleton_homotopyGroup_of_lt_two x h
  obtain rfl : k = 2 := by omega
  -- Apply Poincaré duality on a small homeomorphic copy of the manifold.
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  let : ChartedSpace (Fin 3 → ℝ) M :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [hd])
  have : Small.{0} M := ChartedSpace.small_of_lindelof (Fin 3 → ℝ) M
  let e := Shrink.homeomorph.{0} M
  let : ChartedSpace (Fin 3 → ℝ) (Shrink.{0} M) := e.chartedSpace
  have : SimplyConnectedSpace (Shrink.{0} M) := e.symm.toHomotopyEquiv.simplyConnectedSpace
  have := subsingleton_homotopyGroup_of_lt_two (e x) (by decide : 1 < 2)
  have := subsingleton_homotopyGroup_of_isZero_singularHomologyFunctor_ulift_of_le (e x)
    (k := 2) fun n hn ↦ by
      obtain rfl : n = 0 := by omega
      exact isZero_singularHomology_codim_one_of_simplyConnectedSpace (M := Shrink.{0} M)
        (E := Fin 3 → ℝ) (by simp) (ModuleCat.of ℤ (ULift.{0} ℤ))
  exact (HomotopyGroup.homeomorphEquiv (N := Fin 2) e x).subsingleton

/-- The integer coordinate on integral third homology, obtained by restricting to local homology
at the reference point `z` and using its chart. -/
def singularHomologyThreeManifoldAddEquiv (hd : finrank ℝ E = 3) (z : M) :
    (((singularHomologyFunctor (ModuleCat.{u} ℤ) 3).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) ≃+ ℤ :=
  haveI : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  letI : ChartedSpace (ULift.{u} (Fin 3) → ℝ) M :=
    ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [hd])
  let top := singularHomologyIsoOfSimplyConnectedSpace (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))
    (E := ULift.{u} (Fin 3) → ℝ) (n := 2) (by simp) z
  ((TopCat.of M).singularHomologyUliftAddEquiv ℤ 3).trans
    (top.toLinearEquiv.toAddEquiv.trans AddEquiv.ulift)

/-- The third homotopy group of a closed simply connected three-manifold is infinite cyclic.
The integer of a based class at `x` is its Hurewicz image in top homology, read in the local
homology coordinate at the reference point `z`. Its sign depends on the coordinate. -/
def homotopyGroupThreeManifoldAddEquiv (hd : finrank ℝ E = 3) (z x : M) :
    Additive (HomotopyGroup (Fin 3) M x) ≃+ ℤ :=
  (HomotopyGroup.hurewiczUliftAddEquiv (n := 1)
    (fun _ ↦ subsingleton_homotopyGroup_threeManifold_of_lt hd x)).trans
    (singularHomologyThreeManifoldAddEquiv hd z)

/-- The integer coordinate is the local coordinate at `z` of the Hurewicz image evaluated at one. -/
theorem homotopyGroupThreeManifoldAddEquiv_apply (hd : finrank ℝ E = 3) (z x : M)
    (a : Additive (HomotopyGroup (Fin 3) M x)) :
    homotopyGroupThreeManifoldAddEquiv hd z x a =
      singularHomologyThreeManifoldAddEquiv hd z
        ((HomotopyGroup.hurewiczHom (ModuleCat.of ℤ (ULift.{u} ℤ)) 2 a).hom 1) := by
  simp only [homotopyGroupThreeManifoldAddEquiv, AddEquiv.trans_apply,
    HomotopyGroup.hurewiczUliftAddEquiv_apply]

end TauCeti
