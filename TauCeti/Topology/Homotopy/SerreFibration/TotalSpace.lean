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
`π_k(E, e)` (`TauCeti.TopCat.subsingleton_homotopyGroup_of_mem_serreFibrations`), for homotopy
groups indexed by any finite type. In degree zero this says that `E` is path-connected when `B` and
`F` are (`TauCeti.TopCat.pathConnectedSpace_of_mem_serreFibrations`, in
`TauCeti.Topology.Homotopy.SerreFibration.Basic`).

So the total space of a fibration whose base and one fibre are `n`-connected is `n`-connected, at
every base point of `E` (`TauCeti.TopCat.forall_subsingleton_homotopyGroup_of_mem_serreFibrations`),
and simply connected when the base and one fibre are
(`TauCeti.TopCat.simplyConnectedSpace_of_mem_serreFibrations`). The hypotheses are on a single
fibre: over a path-connected base every point of `E` is joined to it.

A locally trivial map `p : E → B` with fibre `F` is a Serre fibration
(`TauCeti.hasHomotopyLiftingProperty_cube_of_exists_trivialization`) whose fibres are homeomorphic
to `F`. Lifting `E` and `B` to a common universe, the same bounds hold for `p` with hypotheses on
the base and on `F`, with `E`, `B` and `F` in arbitrary universes
(`TauCeti.subsingleton_homotopyGroup_of_exists_trivialization` and its consequences). In particular
the total space of a fibre bundle is path-connected, `n`-connected or simply connected when its base
and its model fibre are. For instance a sphere bundle with fibre `Sⁿ`, `n ≥ 2`, over a simply
connected base has a simply connected total space, since `Sⁿ` is simply connected
(`TauCeti.simplyConnectedSpace_sphere_euclideanSpace`); this is how Barraud, Damian, Humilière and
Oancea see that the sphere bundles of their Proposition 6.23 are simply connected, so that
orientation local systems over them are trivial.

## Main results

* `TauCeti.TopCat.subsingleton_homotopyGroup_of_mem_serreFibrations`: `π_N(E, e)` is trivial when
  `π_N(B, b)` and `π_N(p⁻¹(b), e)` are.
* `TauCeti.TopCat.forall_subsingleton_homotopyGroup_of_mem_serreFibrations`: the total space is
  `n`-connected when the base and one fibre are.
* `TauCeti.TopCat.simplyConnectedSpace_of_mem_serreFibrations`: the total space is simply
  connected when the base and one fibre are.
* `TauCeti.subsingleton_homotopyGroup_of_exists_trivialization`,
  `TauCeti.pathConnectedSpace_of_exists_trivialization`,
  `TauCeti.forall_subsingleton_homotopyGroup_of_exists_trivialization`,
  `TauCeti.simplyConnectedSpace_of_exists_trivialization`: the same for a locally trivial map, with
  hypotheses on the base and the model fibre.
* `FiberBundle.subsingleton_homotopyGroup_totalSpace`, `FiberBundle.pathConnectedSpace_totalSpace`,
  `FiberBundle.forall_subsingleton_homotopyGroup_totalSpace`,
  `FiberBundle.simplyConnectedSpace_totalSpace`: the same for the total space of a fibre bundle.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23.
-/

public section

open CategoryTheory Bundle
open scoped Topology Topology.Homotopy

universe u v

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B}

/-- **The homotopy of the total space is bounded by that of the base and of a fibre.** Let
`p : E → B` be a Serre fibration and `e` a point of the fibre over `b`. If `π_N(B, b)` and
`π_N(p⁻¹(b), e)` are trivial, for a finite index type `N`, then so is `π_N(E, e)`. For empty `N`
this is path-connectedness; otherwise it is exactness of `π_N(p⁻¹(b)) → π_N(E) → π_N(B)` at
`π_N(E)`. -/
theorem subsingleton_homotopyGroup_of_mem_serreFibrations (hp : serreFibrations p) {b : B}
    (e : p.fiber b) {N : Type*} [Finite N] (hB : Subsingleton (HomotopyGroup N B b))
    (hF : Subsingleton (HomotopyGroup N (p.fiber b) e)) : Subsingleton (HomotopyGroup N E e.1) := by
  cases isEmpty_or_nonempty N with
  | inl _ =>
    -- With no cube directions, `π_N` is `π_0`.
    let c := Equiv.equivOfIsEmpty N (Fin 0)
    have : PathConnectedSpace B := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero b).2
      (HomotopyGroup.congrEquiv c).symm.subsingleton
    have : PathConnectedSpace (p.fiber b) :=
      (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero e).2
        (HomotopyGroup.congrEquiv c).symm.subsingleton
    have := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero e.1).1
      (pathConnectedSpace_of_mem_serreFibrations hp b)
    exact (HomotopyGroup.congrEquiv c).subsingleton
  | inr _ =>
    -- Since `π_N(F, e)` is trivial, `p` is injective on `π_N(E, e)`.
    exact (injective_homotopyGroupMap_of_subsingleton (N := N) hp (e := e)).subsingleton

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

namespace TauCeti

variable {E : Type u} {B : Type v} {F : Type*} [TopologicalSpace E] [TopologicalSpace B]
  [TopologicalSpace F] {p : E → B}

/-- A locally trivial map `p : E → B`, as a morphism of `TopCat` between the lifts of `E` and `B`
to a common universe. -/
private noncomputable def uliftHom (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) :
    _root_.TopCat.of (ULift.{v} E) ⟶ _root_.TopCat.of (ULift.{u} B) :=
  _root_.TopCat.ofHom ⟨ULift.up ∘ p ∘ ULift.down, continuous_uliftUp.comp
    ((continuous_of_forall_exists_trivialization h).comp continuous_uliftDown)⟩

/-- The lift of a locally trivial map to a common universe is a Serre fibration. -/
private theorem mem_serreFibrations_uliftHom (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) :
    TopCat.serreFibrations (uliftHom h) :=
  TopCat.mem_serreFibrations_iff_cube.2 fun n ↦
    ((Homeomorph.ulift.symm.hasHomotopyLiftingProperty _).comp
      (hasHomotopyLiftingProperty_cube_of_exists_trivialization h (Fin n))
      (continuous_of_forall_exists_trivialization h)).comp
      (Homeomorph.ulift.hasHomotopyLiftingProperty _) Homeomorph.ulift.continuous

/-- The fibre of the lift `uliftHom h` over a point `b` of the base set of a trivialization is
homeomorphic to the model fibre `F`. -/
private noncomputable def uliftHomFiberHomeomorph
    (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) {b : B} {e : Trivialization F p}
    (hb : b ∈ e.baseSet) : (uliftHom h).fiber (ULift.up b) ≃ₜ F :=
  (Homeomorph.ulift.subtype fun _ ↦ ULift.up_inj).trans (e.preimageSingletonHomeomorph hb)

/-- **The homotopy of the total space of a locally trivial map is bounded by that of the base and
of the fibre.** Let `p : E → B` be a map for which every point of the base lies in the base set of
a trivialization with fibre `F`, and let `x` be a point of `E`. If `π_N(B, p x)` is trivial and
`π_N(F, y)` is trivial at every point `y`, for a finite index type `N`, then `π_N(E, x)` is
trivial. -/
theorem subsingleton_homotopyGroup_of_exists_trivialization
    (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) (x : E) {N : Type*} [Finite N]
    (hB : Subsingleton (HomotopyGroup N B (p x)))
    (hF : ∀ y : F, Subsingleton (HomotopyGroup N F y)) :
    Subsingleton (HomotopyGroup N E x) := by
  obtain ⟨e, he⟩ := h (p x)
  -- Read `p` as a Serre fibration between the lifts of `E` and `B` to a common universe.
  let φ := uliftHomFiberHomeomorph h he
  let x' : (uliftHom h).fiber (ULift.up (p x)) := ⟨ULift.up x, rfl⟩
  have := hF (φ x')
  have := (HomotopyGroup.homeomorphEquiv (N := N) φ x').subsingleton
  have := @Equiv.subsingleton _ _
    (HomotopyGroup.homeomorphEquiv (N := N) (Homeomorph.ulift.{u} (X := B)) (ULift.up (p x))) hB
  have := TopCat.subsingleton_homotopyGroup_of_mem_serreFibrations
    (mem_serreFibrations_uliftHom h) x' ‹_› ‹_›
  exact (HomotopyGroup.homeomorphEquiv (N := N) (Homeomorph.ulift.{v} (X := E))
    (ULift.up x)).symm.subsingleton

/-- **The total space of a locally trivial map is path-connected when the base and the fibre
are.** -/
theorem pathConnectedSpace_of_exists_trivialization
    (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) [PathConnectedSpace B]
    [PathConnectedSpace F] : PathConnectedSpace E := by
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  obtain ⟨y⟩ := (inferInstance : Nonempty F)
  obtain ⟨e, hb⟩ := h b
  let x : E := ((e.preimageSingletonHomeomorph hb).symm y).1
  exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero x).2
    (subsingleton_homotopyGroup_of_exists_trivialization h x
      ((pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (p x)).1 ‹_›)
      fun y ↦ (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero y).1 ‹_›)

/-- **The total space of a locally trivial map with `n`-connected base and fibre is
`n`-connected.** Let `p : E → B` be a map for which every point of the base lies in the base set
of a trivialization with fibre `F`. If `π_k(B, b)` is trivial for every `k ≤ n`, and the homotopy
groups `π_k` of `F` are trivial at every point for every `k ≤ n`, then the homotopy groups `π_k`
of `E` are trivial at every point for every `k ≤ n`. -/
theorem forall_subsingleton_homotopyGroup_of_exists_trivialization
    (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) (b : B) {n : ℕ}
    (hB : ∀ k ≤ n, Subsingleton (π_ k B b)) (hF : ∀ k ≤ n, ∀ y : F, Subsingleton (π_ k F y)) :
    ∀ k ≤ n, ∀ x : E, Subsingleton (π_ k E x) := by
  intro k hk x
  have : PathConnectedSpace B :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero b).2 (hB 0 n.zero_le)
  have := hB k hk
  -- Transport the trivial group `π_k(B, b)` along a path from `p x` to `b`.
  exact subsingleton_homotopyGroup_of_exists_trivialization h x
    (homotopyGroupEquivOfPath (N := Fin k) (PathConnectedSpace.somePath (p x) b)).subsingleton
    (hF k hk)

/-- **The total space of a locally trivial map is simply connected when the base and the fibre
are.** -/
theorem simplyConnectedSpace_of_exists_trivialization
    (h : ∀ b, ∃ e : Trivialization F p, b ∈ e.baseSet) [SimplyConnectedSpace B]
    [SimplyConnectedSpace F] : SimplyConnectedSpace E := by
  have := pathConnectedSpace_of_exists_trivialization h
  obtain ⟨x⟩ := (inferInstance : Nonempty E)
  -- The fundamental group of `E` at `x` is `π₁(E, x)`, which is trivial.
  have h₁ : Subsingleton (π_ 1 E x) := subsingleton_homotopyGroup_of_exists_trivialization h x
    (HomotopyGroup.pi1EquivFundamentalGroup.subsingleton)
    fun _ ↦ HomotopyGroup.pi1EquivFundamentalGroup.subsingleton
  have : Subsingleton (_root_.FundamentalGroup E x) :=
    HomotopyGroup.pi1EquivFundamentalGroup.symm.subsingleton
  exact simplyConnectedSpace_of_subsingleton_fundamentalGroup x

end TauCeti

namespace FiberBundle

variable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- **The homotopy of the total space of a fibre bundle is bounded by that of the base and of the
fibre.** If `π_N(B, x.proj)` is trivial and `π_N(F, y)` is trivial at every point `y`, for a finite
index type `N`, then `π_N(TotalSpace F E, x)` is trivial. -/
theorem subsingleton_homotopyGroup_totalSpace (x : TotalSpace F E) {N : Type*} [Finite N]
    (hB : Subsingleton (HomotopyGroup N B x.proj))
    (hF : ∀ y : F, Subsingleton (HomotopyGroup N F y)) :
    Subsingleton (HomotopyGroup N (TotalSpace F E) x) :=
  TauCeti.subsingleton_homotopyGroup_of_exists_trivialization
    (exists_trivialization_mem_baseSet F E) x hB hF

/-- **The total space of a fibre bundle with path-connected base and fibre is path-connected.** -/
instance pathConnectedSpace_totalSpace [PathConnectedSpace B] [PathConnectedSpace F] :
    PathConnectedSpace (TotalSpace F E) :=
  TauCeti.pathConnectedSpace_of_exists_trivialization (exists_trivialization_mem_baseSet F E)

/-- **The total space of a fibre bundle with `n`-connected base and fibre is `n`-connected.** If
`π_k(B, b)` is trivial for every `k ≤ n`, and the homotopy groups `π_k` of the model fibre `F` are
trivial at every point for every `k ≤ n`, then the homotopy groups `π_k` of the total space are
trivial at every point for every `k ≤ n`. -/
theorem forall_subsingleton_homotopyGroup_totalSpace (b : B) {n : ℕ}
    (hB : ∀ k ≤ n, Subsingleton (π_ k B b)) (hF : ∀ k ≤ n, ∀ y : F, Subsingleton (π_ k F y)) :
    ∀ k ≤ n, ∀ x : TotalSpace F E, Subsingleton (π_ k (TotalSpace F E) x) :=
  TauCeti.forall_subsingleton_homotopyGroup_of_exists_trivialization
    (exists_trivialization_mem_baseSet F E) b hB hF

/-- **The total space of a fibre bundle with simply connected base and fibre is simply
connected.** For instance, for `n ≥ 2` the total space of a fibre bundle with fibre the sphere
`Sⁿ` over a simply connected base is simply connected. -/
instance simplyConnectedSpace_totalSpace [SimplyConnectedSpace B] [SimplyConnectedSpace F] :
    SimplyConnectedSpace (TotalSpace F E) :=
  TauCeti.simplyConnectedSpace_of_exists_trivialization (exists_trivialization_mem_baseSet F E)

end FiberBundle
