/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.ConnectedMap
public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Loop
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# Moore loop maps of `n`-connected maps and the homology of double loop spaces

A based map `f : X → Y`, `f x = y`, induces the continuous monoid homomorphism
`Ωᴹf = TauCeti.MooreLoopSpace.map f hf` of Moore loop spaces. Normalizing Moore loops to the unit
interval (`TauCeti.MooreLoopSpace.homotopyEquivPath`) is a homotopy equivalence which carries
`Ωᴹf` to the fixed-interval loop map `ContinuousMap.loopMap`
(`TauCeti.MooreLoopSpace.homotopyEquivPath_comp_map`, in
`TauCeti.Topology.PathSpace.Moore.Comparison.Basic`), so the two loop maps have the same
connectivity. Hence, as for fixed-interval loops, Moore loop maps lower connectivity by one
(`TauCeti.MooreLoopSpace.isNConnected_map`, `ContinuousMap.IsNConnected.mooreLoopSpaceMap`), and
the double Moore loop map of an `(n + 2)`-connected map is `n`-connected
(`ContinuousMap.IsNConnected.mooreLoopSpaceMap_map`).

Through the comparison of `n`-connected maps with singular homology, the double Moore loop map
`ΩᴹΩᴹf` of an `(n + 2)`-connected map induces isomorphisms `H_m(ΩᴹΩᴹX; R) ≅ H_m(ΩᴹΩᴹY; R)` for
`m < n` and a surjection for `m = n`, for every coefficient ring `R`
(`ContinuousMap.IsNConnected.isIso_singularHomologyMap_mooreLoopSpaceMap_map`,
`ContinuousMap.IsNConnected.epi_singularHomologyMap_mooreLoopSpaceMap_map`). For instance, for a
fibration `F → E → B` over an `n`-connected base the fibre inclusion is `n`-connected, so the
double loop spaces of the fibre and of the total space have the same homology below degree
`n - 2`.

## Main results

* `TauCeti.MooreLoopSpace.isNConnected_map`: the Moore loop map is `n`-connected when `f` induces
  injections on `π_(k+1)` at `x` for `k < n` and surjections for `k ≤ n`.
* `ContinuousMap.IsNConnected.mooreLoopSpaceMap`,
  `ContinuousMap.IsNConnected.mooreLoopSpaceMap_map`: the Moore loop map of an
  `(n + 1)`-connected map, and the double Moore loop map of an `(n + 2)`-connected map, are
  `n`-connected.
* `ContinuousMap.IsNConnected.isIso_singularHomologyMap_mooreLoopSpaceMap_map`,
  `ContinuousMap.IsNConnected.epi_singularHomologyMap_mooreLoopSpaceMap_map`: the homology of
  the double Moore loop spaces in the corresponding range.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1 and Proposition 4.21.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup

namespace TauCeti.MooreLoopSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- **Moore loop maps lower connectivity by one.** If a based map `f : X → Y`, `f x = y`, induces
injections `π_(k+1)(X, x) → π_(k+1)(Y, y)` for `k < n` and surjections for `k ≤ n`, then the
Moore loop map `MooreLoopSpace X x → MooreLoopSpace Y y` is `n`-connected. -/
theorem isNConnected_map (f : C(X, Y)) (hf : f x = y) {n : ℕ}
    (hinj : ∀ k < n, Function.Injective (HomotopyGroup.map (N := Fin (k + 1)) f hf))
    (hsurj : ∀ k ≤ n, Function.Surjective (HomotopyGroup.map (N := Fin (k + 1)) f hf)) :
    (map f hf).toContinuousMap.IsNConnected n :=
  ((homotopyEquivPath x).isWeakHomotopyEquivalence.isNConnected_iff_of_comp_eq
    (homotopyEquivPath y).isWeakHomotopyEquivalence (homotopyEquivPath_comp_map f hf)).1
      (f.isNConnected_loopMap hf hinj hsurj)

end TauCeti.MooreLoopSpace

namespace ContinuousMap.IsNConnected

open TauCeti

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y} {f : C(X, Y)}
  {n : ℕ}

/-- **The Moore loop map of an `(n + 1)`-connected map is `n`-connected.** -/
theorem mooreLoopSpaceMap (hf : f.IsNConnected (n + 1)) (hx : f x = y) :
    (MooreLoopSpace.map f hx).toContinuousMap.IsNConnected n := by
  subst hx
  exact MooreLoopSpace.isNConnected_map f rfl (fun k hk ↦ hf.injective (k + 1) (by omega) x)
    (fun k hk ↦ hf.surjective (k + 1) (by omega) x)

/-- **The double Moore loop map of an `(n + 2)`-connected map is `n`-connected.** -/
theorem mooreLoopSpaceMap_map (hf : f.IsNConnected (n + 2)) (hx : f x = y) :
    (MooreLoopSpace.map (MooreLoopSpace.map f hx).toContinuousMap
      (MooreLoopSpace.map f hx).map_one).toContinuousMap.IsNConnected n :=
  (hf.mooreLoopSpaceMap hx).mooreLoopSpaceMap _

end

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y} {f : C(X, Y)}
  {n : ℕ} (R : Type u) [Ring R]

/-- **Double Moore loop spaces have the same homology in a range.** If `f` is
`(n + 2)`-connected, the double Moore loop map induces isomorphisms on singular homology with
coefficients in `R` in every degree `m < n`. -/
theorem isIso_singularHomologyMap_mooreLoopSpaceMap_map (hf : f.IsNConnected (n + 2))
    (hx : f x = y) {m : ℕ} (hm : m < n) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (MooreLoopSpace.map (MooreLoopSpace.map f hx).toContinuousMap
        (MooreLoopSpace.map f hx).map_one).toContinuousMap)) :=
  (hf.mooreLoopSpaceMap_map hx).isIso_singularHomologyMap R hm

/-- If `f` is `(n + 2)`-connected, the double Moore loop map induces a surjection on singular
homology with coefficients in `R` in degree `n` and below. -/
theorem epi_singularHomologyMap_mooreLoopSpaceMap_map (hf : f.IsNConnected (n + 2))
    (hx : f x = y) {m : ℕ} (hm : m ≤ n) :
    Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (TopCat.ofHom (MooreLoopSpace.map (MooreLoopSpace.map f hx).toContinuousMap
        (MooreLoopSpace.map f hx).map_one).toContinuousMap)) :=
  (hf.mooreLoopSpaceMap_map hx).epi_singularHomologyMap R hm

end ContinuousMap.IsNConnected
