/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.SerreFibration.Exact
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# Connectivity of the total space of a Serre fibration

Let `p : E → B` be a Serre fibration (`TauCeti.TopCat.serreFibrations`) and `F = p⁻¹(b)` a fibre.
The exact homotopy sequence `π_k(F) → π_k(E) → π_k(B)` bounds the homotopy of the total space by
that of the base and of the fibre: if `π_k(B, b)` and `π_k(F, e)` are trivial, then so is
`π_k(E, e)` (`TauCeti.TopCat.subsingleton_homotopyGroup_of_mem_serreFibrations`). In degree zero
this says that `E` is path-connected when `B` and `F` are
(`TauCeti.TopCat.pathConnectedSpace_of_mem_serreFibrations`): a path in the base from the image of a
point to `b` lifts to a path ending in `F`.

So the total space of a fibration whose base and one fibre are `n`-connected is `n`-connected, at
every base point of `E` (`TauCeti.TopCat.forall_subsingleton_homotopyGroup_of_mem_serreFibrations`),
and simply connected when the base and one fibre are
(`TauCeti.TopCat.simplyConnectedSpace_of_mem_serreFibrations`). The hypotheses are on a single
fibre: over a path-connected base every point of `E` is joined to it.

The projection of a fibre bundle is a Serre fibration (`TauCeti.TopCat.mem_serreFibrations_proj`)
whose fibres are homeomorphic to the model fibre. Hence the total space of a fibre bundle is
`n`-connected when its base and its model fibre are
(`FiberBundle.forall_subsingleton_homotopyGroup_totalSpace`), and simply connected when they are
(`FiberBundle.simplyConnectedSpace_totalSpace`). For instance a sphere bundle with fibre `Sⁿ`,
`n ≥ 2`, over a simply connected base has a simply connected total space, since `Sⁿ` is simply
connected (`TauCeti.simplyConnectedSpace_sphere_euclideanSpace`); this is how Barraud, Damian,
Humilière and Oancea see that the sphere bundles of their Proposition 6.23 are simply connected,
so that orientation local systems over them are trivial.

## Main results

* `TauCeti.TopCat.subsingleton_homotopyGroup_of_mem_serreFibrations`: `π_k(E, e)` is trivial when
  `π_k(B, b)` and `π_k(p⁻¹(b), e)` are.
* `TauCeti.TopCat.pathConnectedSpace_of_mem_serreFibrations`: the total space is path-connected
  when the base and one fibre are.
* `TauCeti.TopCat.forall_subsingleton_homotopyGroup_of_mem_serreFibrations`: the total space is
  `n`-connected when the base and one fibre are.
* `TauCeti.TopCat.simplyConnectedSpace_of_mem_serreFibrations`: the total space is simply
  connected when the base and one fibre are.
* `FiberBundle.forall_subsingleton_homotopyGroup_totalSpace`,
  `FiberBundle.simplyConnectedSpace_totalSpace`: the same for the total space of a fibre bundle,
  with hypotheses on the base and the model fibre.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23.
-/

public section

open CategoryTheory Bundle
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B}

/-- **The total space is path-connected when the base and one fibre are.** For a Serre fibration
`p : E → B` over a path-connected base, if the fibre over `b` is path-connected, then so is `E`:
a path from the projection of a point of `E` to `b` lifts to a path from that point into the
fibre over `b`. -/
theorem pathConnectedSpace_of_mem_serreFibrations (hp : serreFibrations p) (b : B)
    [PathConnectedSpace B] [PathConnectedSpace (p.fiber b)] : PathConnectedSpace E := by
  obtain ⟨⟨y, hy⟩⟩ := (inferInstance : Nonempty (p.fiber b))
  obtain rfl : p y = b := Set.mem_singleton_iff.1 hy
  refine ⟨⟨y⟩, fun x z ↦ ?_⟩
  exact (joined_of_mem_serreFibrations hp (PathConnectedSpace.joined (p x) (p y))).trans
    (joined_of_mem_serreFibrations hp (PathConnectedSpace.joined (p z) (p y))).symm

/-- **The homotopy of the total space is bounded by that of the base and of a fibre.** Let
`p : E → B` be a Serre fibration and `e` a point of the fibre over `b`. If `π_k(B, b)` and
`π_k(p⁻¹(b), e)` are trivial, then so is `π_k(E, e)`. In degree zero this is path-connectedness;
in positive degrees it is exactness of `π_k(p⁻¹(b)) → π_k(E) → π_k(B)` at `π_k(E)`. -/
theorem subsingleton_homotopyGroup_of_mem_serreFibrations (hp : serreFibrations p) {b : B}
    (e : p.fiber b) {k : ℕ} (hB : Subsingleton (π_ k B b))
    (hF : Subsingleton (π_ k (p.fiber b) e)) : Subsingleton (π_ k E e.1) := by
  cases k with
  | zero =>
    have : PathConnectedSpace B := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero b).2 hB
    have : PathConnectedSpace (p.fiber b) :=
      (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero e).2 hF
    have := pathConnectedSpace_of_mem_serreFibrations hp b
    exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero e.1).1 this
  | succ k =>
    -- Since `π_(k+1)(F, e)` is trivial, `p` is injective on `π_(k+1)(E, e)`.
    exact (injective_homotopyGroupMap_of_subsingleton (N := Fin (k + 1)) hp (e := e)).subsingleton

/-- **The total space of a fibration with `n`-connected base and fibre is `n`-connected.** Let
`p : E → B` be a Serre fibration and `e` a point of the fibre over `b`. If `π_k(B, b)` and
`π_k(p⁻¹(b), e)` are trivial for every `k ≤ n`, then `π_k(E, x)` is trivial for every `k ≤ n` and
every point `x` of `E`, not only for the points of the fibre over `b`: `E` is path-connected, and
homotopy groups at points joined by a path are in bijection. -/
theorem forall_subsingleton_homotopyGroup_of_mem_serreFibrations (hp : serreFibrations p)
    {b : B} (e : p.fiber b) {n : ℕ} (hB : ∀ k ≤ n, Subsingleton (π_ k B b))
    (hF : ∀ k ≤ n, Subsingleton (π_ k (p.fiber b) e)) :
    ∀ k ≤ n, ∀ x : E, Subsingleton (π_ k E x) := by
  intro k hk x
  have : PathConnectedSpace E := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero e.1).2
    (subsingleton_homotopyGroup_of_mem_serreFibrations hp e (hB 0 n.zero_le) (hF 0 n.zero_le))
  have := subsingleton_homotopyGroup_of_mem_serreFibrations hp e (hB k hk) (hF k hk)
  -- Transport the trivial group `π_k(E, e)` along a path from `e` to `x`.
  exact (homotopyGroupEquivOfPath (N := Fin k)
    (PathConnectedSpace.somePath e.1 x)).symm.subsingleton

/-- **The total space is simply connected when the base and one fibre are.** For a Serre fibration
`p : E → B` over a simply connected base whose fibre over `b` is simply connected, the total space
`E` is simply connected. -/
theorem simplyConnectedSpace_of_mem_serreFibrations (hp : serreFibrations p) (b : B)
    [SimplyConnectedSpace B] [SimplyConnectedSpace (p.fiber b)] : SimplyConnectedSpace E := by
  have := pathConnectedSpace_of_mem_serreFibrations hp b
  obtain ⟨e⟩ := (inferInstance : Nonempty (p.fiber b))
  -- The fundamental group of `E` at `e` is `π₁(E, e)`, which is trivial by exactness.
  have h₁ : Subsingleton (π_ 1 E e.1) := subsingleton_homotopyGroup_of_mem_serreFibrations hp e
    (HomotopyGroup.pi1EquivFundamentalGroup.subsingleton)
    (HomotopyGroup.pi1EquivFundamentalGroup.subsingleton)
  have : Subsingleton (_root_.FundamentalGroup E e.1) :=
    HomotopyGroup.pi1EquivFundamentalGroup.symm.subsingleton
  exact simplyConnectedSpace_of_subsingleton_fundamentalGroup e.1

end TauCeti.TopCat

namespace FiberBundle

variable {B : Type u} {F : Type*} [TopologicalSpace B] [TopologicalSpace F] {E : B → Type u}
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable (F E) in
/-- The fibre over `b` of the projection of a fibre bundle, as a fibre of a morphism of `TopCat`,
is homeomorphic to the model fibre `F`, through the trivialization at `b`. -/
private noncomputable def projFiberHomeomorph (b : B) :
    (_root_.TopCat.ofHom ⟨TotalSpace.proj, continuous_proj F E⟩ :
      _root_.TopCat.of (TotalSpace F E) ⟶ _root_.TopCat.of B).fiber b ≃ₜ F :=
  (trivializationAt F E b).preimageSingletonHomeomorph (mem_baseSet_trivializationAt F E b)

/-- **The total space of a fibre bundle with `n`-connected base and fibre is `n`-connected.** If
`π_k(B, b)` is trivial for every `k ≤ n`, and the homotopy groups `π_k` of the model fibre `F` are
trivial at every point for every `k ≤ n`, then the homotopy groups `π_k` of the total space are
trivial at every point for every `k ≤ n`. -/
theorem forall_subsingleton_homotopyGroup_totalSpace (b : B) {n : ℕ}
    (hB : ∀ k ≤ n, Subsingleton (π_ k B b)) (hF : ∀ k ≤ n, ∀ y : F, Subsingleton (π_ k F y)) :
    ∀ k ≤ n, ∀ x : TotalSpace F E, Subsingleton (π_ k (TotalSpace F E) x) := by
  intro k hk x
  -- A point of the fibre over `b`: the model fibre is nonempty, since it contains the image of `x`.
  let e := (projFiberHomeomorph F E b).symm (projFiberHomeomorph F E x.proj ⟨x, rfl⟩)
  refine TauCeti.TopCat.forall_subsingleton_homotopyGroup_of_mem_serreFibrations
    (TauCeti.TopCat.mem_serreFibrations_proj F E) e hB (fun j hj ↦ ?_) k hk x
  have := hF j hj (projFiberHomeomorph F E b e)
  exact (HomotopyGroup.homeomorphEquiv (projFiberHomeomorph F E b) e).subsingleton

variable (F E) in
/-- **The total space of a fibre bundle with simply connected base and fibre is simply
connected.** For instance, for `n ≥ 2` the total space of a fibre bundle with fibre the sphere
`Sⁿ` over a simply connected base is simply connected. -/
theorem simplyConnectedSpace_totalSpace [SimplyConnectedSpace B] [SimplyConnectedSpace F] :
    SimplyConnectedSpace (TotalSpace F E) := by
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  have : SimplyConnectedSpace ((_root_.TopCat.ofHom ⟨TotalSpace.proj, continuous_proj F E⟩ :
      _root_.TopCat.of (TotalSpace F E) ⟶ _root_.TopCat.of B).fiber b) :=
    (projFiberHomeomorph F E b).toHomotopyEquiv.simplyConnectedSpace
  exact TauCeti.TopCat.simplyConnectedSpace_of_mem_serreFibrations
    (TauCeti.TopCat.mem_serreFibrations_proj F E) b

end FiberBundle
