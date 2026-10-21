/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Exact
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Compression
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# The pair of a CW complex and its skeleton is highly connected

Let `C` be a relative CW complex with base `D` in a Hausdorff space, and write
`Xⁿ = skeletonLT C (n + 1)` for its `n`-skeleton. This file proves Hatcher's Corollary 4.12: the
pair `(C, Xⁿ)` is `n`-connected. That is, the relative homotopy set `π_{k+1}(C, Xⁿ, a)` is trivial
for `k + 1 ≤ n` and every `a ∈ Xⁿ` (`TauCeti.subsingleton_relHomotopyGroup_skeletonLT`), and so the
inclusion `Xⁿ ↪ C` induces a surjection `π_k(Xⁿ, a) → π_k(C, a)` for `k ≤ n`
(`TauCeti.surjective_homotopyGroupMap_skeletonLT`) and an injection for `k < n`
(`TauCeti.injective_homotopyGroupMap_skeletonLT`). In degree zero these say that every point of `C`
is joined by a path to a point of `Xⁿ`, and that for `n ≥ 1` two points of `Xⁿ` joined by a path
in `C` are joined by a path in `Xⁿ`.

The subspace `A` of the statements is any set equal to `Xⁿ`, together with the inclusion `A ⊆ C`
from which the pair `(C, A)` is built. Taking `A = Xⁿ` gives the statement about the skeleton.
When `C` has no cells of dimension at most `n`, the skeleton `Xⁿ` is the base `D`
(`TauCeti.skeletonLT_eq_base_of_isEmpty_cell`), and taking `A = D` gives Hatcher's statement for
a CW pair `(C, D)` all of whose cells outside `D` have dimension greater than `n`: attaching such
cells does not change `π_k` for `k < n`, and induces a surjection on `π_n`.

The input is the compression of maps of low-dimensional compacta into skeleta
(`TauCeti.exists_homotopicRel_skeletonLT_finrank`), the step of cellular approximation that
concerns a single map. A relative cube `I × Iᵏ → C` is a map of pairs
`(I × Iᵏ, ∂(I × Iᵏ)) → (C, Xⁿ)` out of a compactum of dimension `k + 1 ≤ n`, so it is homotopic,
relative to the boundary of the cube, to a map into `Xⁿ`; by the compression criterion
(`TauCeti.RelHomotopyGroup.subsingleton_iff`) its class is trivial. The absolute statements
follow from the exact homotopy sequence of the pair `(C, Xⁿ)`.

## Main results

* `TauCeti.subsingleton_relHomotopyGroup_skeletonLT`: `π_{k+1}(C, Xⁿ, a)` is trivial for `k < n`.
* `TauCeti.exists_joined_skeletonLT`, `TauCeti.joined_skeletonLT_iff`: every point of `C`
  is joined to `Xⁿ`, and for `n ≥ 1` points of `Xⁿ` joined in `C` are joined in `Xⁿ`.
* `TauCeti.surjective_homotopyGroupMap_skeletonLT`: `π_k(Xⁿ, a) → π_k(C, a)` is surjective for
  `k ≤ n`.
* `TauCeti.injective_homotopyGroupMap_skeletonLT`: `π_k(Xⁿ, a) → π_k(C, a)` is injective for
  `k < n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollary 4.12.
-/

public section

noncomputable section

universe u v

open Metric Set Topology Topology.RelCWComplex Module
open scoped unitInterval Topology.Homotopy

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {n : ℕ} {A : Set X}

/-- **The pair `(C, Xⁿ)` is `n`-connected** (Hatcher, Corollary 4.12). If `A` is the `n`-skeleton
`skeletonLT C (n + 1)` of a relative CW complex `C`, then the relative homotopy set
`π_{k+1}(C, A, a)` is trivial for every `a ∈ A`, where `k = Nat.card N < n`. -/
theorem subsingleton_relHomotopyGroup_skeletonLT {N : Type v} [Finite N] (hN : Nat.card N < n)
    (hA : (skeletonLT C (n + 1) : Set X) = A) (hAC : A ⊆ C) (a : A) :
    Subsingleton (RelHomotopyGroup N ⟨TopPair.ofInclusion (X := TopCat.of X) hAC, a⟩) := by
  have := Fintype.ofFinite N
  refine RelHomotopyGroup.subsingleton_iff.2 fun p ↦ ?_
  -- Read the relative cube on the closed unit ball of `Option N → ℝ`, of dimension `k + 1 ≤ n`,
  -- and compress it into the skeleton relative to the points it already sends there.
  let e : I × (I^N) ≃ₜ closedBall (0 : Option N → ℝ) 1 :=
    (piOptionEquivProdHomeomorph fun _ ↦ I).symm.trans (cubeHomeomorphClosedBall (Option N))
  have hdim : finrank ℝ (Option N → ℝ) ≤ n := by
    rw [finrank_fintype_fun_eq_card, Fintype.card_option, ← Nat.card_eq_fintype_card]
    omega
  let f : C(closedBall (0 : Option N → ℝ) 1, C) :=
    (p.1 : C(I × (I^N), C)).comp (e.symm : C(closedBall (0 : Option N → ℝ) 1, I × (I^N)))
  obtain ⟨g, ⟨H⟩, hg⟩ := exists_homotopicRel_skeletonLT_finrank (C := C)
    (isCompact_closedBall (0 : Option N → ℝ) 1) hdim f
  have hfe (y : I × (I^N)) : f (e y) = p.1 y := congrArg p.1 (e.symm_apply_apply y)
  -- The boundary of the cube is sent into `A`, so the homotopy is relative to it.
  have hbd {y : I × (I^N)} (hy : y ∈ Cube.prodBoundary N) :
      ((f (e y) : C) : X) ∈ skeletonLT C (n + 1) := by
    obtain ⟨b, hb⟩ := RelGenLoop.mapsTo_prodBoundary p.2 hy
    rw [hfe, ← SetLike.mem_coe, hA, ← hb]
    exact b.2
  refine ⟨g.comp (e : C(I × (I^N), closedBall (0 : Option N → ℝ) 1)),
    ⟨{ toHomotopy := (H.toHomotopy.compContinuousMap
          (e : C(I × (I^N), closedBall (0 : Option N → ℝ) 1))).cast
          (ContinuousMap.ext fun y ↦ hfe y) rfl
       prop' t y hy := ?_ }⟩, fun y ↦ ⟨⟨_, hA ▸ hg (e y)⟩, rfl⟩⟩
  exact (H.prop t (e y) (hbd hy)).trans (hfe y)

/-- **The inclusion of the `n`-skeleton is surjective on `π_k` for `k ≤ n`** (Hatcher,
Corollary 4.12). If `A` is the `n`-skeleton `skeletonLT C (n + 1)` of a relative CW complex `C`,
then the inclusion `A ↪ C` induces a surjection `π_k(A, a) → π_k(C, a)`, where
`k = Nat.card N ≤ n`. -/
theorem surjective_homotopyGroupMap_skeletonLT {N : Type v} [Finite N] (hN : Nat.card N ≤ n)
    (hA : (skeletonLT C (n + 1) : Set X) = A) (hAC : A ⊆ C) (a : A) :
    Function.Surjective
      (HomotopyGroup.map (N := N) (x := a) (ContinuousMap.inclusion hAC) rfl) := by
  classical
  rcases isEmpty_or_nonempty N with hN₀ | ⟨⟨i⟩⟩
  · -- In degree zero, homotopy classes are path components.
    intro c
    induction c using Quotient.inductionOn with | h γ => ?_
    obtain ⟨b, hb⟩ := exists_joined_skeletonLT hA hAC (γ 0)
    refine ⟨⟦(genLoopHomeoOfIsEmpty N a).symm b⟧,
      (homotopyGroupEquivZerothHomotopyOfIsEmpty N _).injective ?_⟩
    rw [HomotopyGroup.map_mk, homotopyGroupEquivZerothHomotopyOfIsEmpty_mk,
      homotopyGroupEquivZerothHomotopyOfIsEmpty_mk, GenLoop.map_apply]
    exact ZerothHomotopy.sound hb.somePath
  · -- Split off a direction `i` and use exactness of the pair at `π_k(C, a)`.
    let e := Equiv.optionSubtypeNe i
    have hcard : Nat.card {j // j ≠ i} < n := by
      have := Nat.card_congr e
      rw [Finite.card_option] at this
      omega
    have := subsingleton_relHomotopyGroup_skeletonLT hcard hA hAC a
    intro c
    obtain ⟨b, hb⟩ := (RelHomotopyGroup.mem_range_homotopyGroupMap_iff
      (X := ⟨TopPair.ofInclusion (X := TopCat.of X) hAC, a⟩)
      (a := (HomotopyGroup.congrEquiv e).symm c)).2 (Subsingleton.elim _ _)
    exact ⟨HomotopyGroup.congrEquiv e b,
      (HomotopyGroup.map_congrEquiv _ _ e b).trans ((Equiv.eq_symm_apply _).1 hb)⟩

/-- **The inclusion of the `n`-skeleton is injective on `π_k` for `k < n`** (Hatcher,
Corollary 4.12). If `A` is the `n`-skeleton `skeletonLT C (n + 1)` of a relative CW complex `C`,
then the inclusion `A ↪ C` induces an injection `π_k(A, a) → π_k(C, a)`, where
`k = Nat.card N < n`. -/
theorem injective_homotopyGroupMap_skeletonLT {N : Type v} [Finite N] (hN : Nat.card N < n)
    (hA : (skeletonLT C (n + 1) : Set X) = A) (hAC : A ⊆ C) (a : A) :
    Function.Injective
      (HomotopyGroup.map (N := N) (x := a) (ContinuousMap.inclusion hAC) rfl) := by
  classical
  rcases isEmpty_or_nonempty N with hN₀ | hN₀
  · -- In degree zero, homotopy classes are path components.
    intro c d hcd
    induction c using Quotient.inductionOn with | h γ => ?_
    induction d using Quotient.inductionOn with | h δ => ?_
    apply (homotopyGroupEquivZerothHomotopyOfIsEmpty N a).injective
    have := congrArg (homotopyGroupEquivZerothHomotopyOfIsEmpty N _) hcd
    rw [HomotopyGroup.map_mk, HomotopyGroup.map_mk, homotopyGroupEquivZerothHomotopyOfIsEmpty_mk,
      homotopyGroupEquivZerothHomotopyOfIsEmpty_mk, GenLoop.map_apply, GenLoop.map_apply] at this
    rw [homotopyGroupEquivZerothHomotopyOfIsEmpty_mk,
      homotopyGroupEquivZerothHomotopyOfIsEmpty_mk]
    exact ZerothHomotopy.sound
      ((joined_skeletonLT_iff (by omega) hA hAC).1 (Quotient.exact this)).somePath
  · -- In positive degrees the induced map is a homomorphism, and by exactness of the pair at
    -- `π_k(A, a)` its kernel consists of boundaries, which are trivial.
    have := subsingleton_relHomotopyGroup_skeletonLT hN hA hAC a
    refine (injective_iff_map_eq_one
      (HomotopyGroup.mapHom (N := N) (x := a) (ContinuousMap.inclusion hAC) rfl)).2 fun c hc ↦ ?_
    rw [HomotopyGroup.mapHom_apply, ← HomotopyGroup.mk_const_eq_one] at hc
    obtain ⟨r, hr⟩ := (RelHomotopyGroup.mem_range_boundary_iff
      (X := ⟨TopPair.ofInclusion (X := TopCat.of X) hAC, a⟩)).2 hc
    rw [← hr, Subsingleton.elim r default, RelHomotopyGroup.boundary_default,
      HomotopyGroup.mk_const_eq_one]
    -- Both sides are the identity of `π_k(A, a)`, once read on the subspace of the pair and once
    -- on `A`; these are the same group.
    rfl

end TauCeti
