/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

import TauCeti.Analysis.Calculus.GroupAction.FaceKernel
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Geometry.Manifold.GroupAction.Straightening
import TauCeti.Topology.OpenPartialHomeomorph.CornerFace

/-!
# Faces detect the ineffective kernel of a finite smooth action

Let a finite group `G` act by `C^n` maps, `1 ≤ n`, on a manifold `M` without boundary, modelled
on a real Banach space, and let `x` be a common fixed point. Let `ρ : ι → M → ℝ` be finitely many
locally invariant functions, `C¹` at `x`, whose differentials at `x` are linearly independent for
the labels active at `x`, that is, those with `ρ i x = 0`. For a set `s` of labels, the face
`{y | (∀ i, 0 ≤ ρ i y) ∧ ∀ i ∈ s, ρ i y = 0}` is a corner of the domain cut out by the
inequalities `0 ≤ ρ i`.

If `x` lies on this face, an element of `G` acts as the identity near `x` exactly when it acts as
the identity on the face near `x` (`TauCeti.eventually_nhdsWithin_face_smul_eq_iff`). So the
germ kernel of the action at `x`, the subgroup of elements acting as the identity near `x`, is
also the germ kernel of the action on every face through `x`, including faces of codimension
greater than one and at corners where further labels are active. No faithfulness is assumed:
the statement concerns the actual group elements, including those acting trivially everywhere.

Preserving each `ρ i` individually is essential. A reflection fixing a hypersurface pointwise is
not the identity near it; it does not preserve a defining function of that hypersurface, it
negates it.

The proof combines three local results. Smooth Bochner linearization and equivariant
straightening of the active defining functions give a chart at `x` in which `G` acts linearly and
these functions are linear coordinates (`TauCeti.exists_equivariant_straightened_chart`). So near
`x` the face is the image of a convex cone in the kernel of its normal coordinates
(`OpenPartialHomeomorph.tendsto_symm_nhdsWithin_face`), with nonempty interior there
(`TauCeti.uniqueDiffOn_ker_setOf_nonneg`). Finally, an element of finite order preserving linear
normal coordinates and fixing such a cone near the origin is the identity near the origin
(`OpenPartialHomeomorph.eventually_smul_eq_iff_on_ker`).

## Main results

* `TauCeti.eventually_nhdsWithin_face_smul_eq_iff`: an element acts as the identity near `x`
  exactly when it acts as the identity on a face through `x` near `x`.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46
  (1945), 372–381.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Chapter 1.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M]
  [Group G] [Finite G] [MulAction G M] [Finite ι]

/-- **Faces detect the germ kernel.** Let a finite group act by `C^n` maps, `1 ≤ n`, fixing `x`,
and let the functions `ρ i` be locally invariant and `C¹` at `x`, with linearly independent
differentials at `x` for the labels active at `x`. If `x` lies on the face of a set `s` of labels,
then an element `g` acts as the identity on this face near `x` exactly when it acts as the
identity near `x`. -/
theorem eventually_nhdsWithin_face_smul_eq_iff
    (hsmooth : ∀ g : G, ContMDiff I I n fun y : M ↦ g • y) (hn : 1 ≤ n)
    {x : M} (hx : ∀ g : G, g • x = x) {ρ : ι → M → ℝ}
    (hρ : ∀ i, ContMDiffAt I 𝓘(ℝ) 1 (ρ i) x)
    (hinv : ∀ i (g : G), ∀ᶠ y in 𝓝 x, ρ i (g • y) = ρ i y)
    (hlin : LinearIndependent ℝ fun i : {i // ρ i x = 0} ↦ mvfderiv I (ρ i) x)
    {s : Set ι} (hxD : ∀ i, 0 ≤ ρ i x) (hxs : ∀ i ∈ s, ρ i x = 0) (g : G) :
    (∀ᶠ y in 𝓝[{y | (∀ i, 0 ≤ ρ i y) ∧ ∀ i ∈ s, ρ i y = 0}] x, g • y = y) ↔
      ∀ᶠ y in 𝓝 x, g • y = y := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Fintype.card G : ℝ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let : ContinuousConstSMul G M := ⟨fun g ↦ (hsmooth g).continuous⟩
  refine ⟨fun hg ↦ ?_, fun h ↦ nhdsWithin_le_nhds h⟩
  obtain ⟨σ, χ, q, hxχ, hχx, -, -, hχ, hq, hqσ, hqχ⟩ :=
    exists_equivariant_straightened_chart (ρ := fun a : {i // ρ i x = 0} ↦ ρ a) hsmooth hn hx
      (fun a ↦ a.property) (fun a ↦ hρ a) (fun a ↦ hinv a) hlin
  let A := {i // ρ i x = 0}
  have h0χ : (0 : E) ∈ χ.target := hχx ▸ χ.map_source hxχ
  have hρχ (v : E) (hv : v ∈ χ.target) (a : A) : ρ a (χ.symm v) = q v a := by
    rw [← hqχ _ (χ.map_target hv), χ.right_inv hv]
  -- In the chart the action is linear, and the labels in `s` give its normal coordinates `qs`.
  have hL (g : G) : HasStrictFDerivAt (χ ∘ (g • ·) ∘ χ.symm) (σ g : E →L[ℝ] E) 0 := by
    refine (σ g).hasStrictFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [χ.open_target.mem_nhds h0χ] with w hw
    simp [(hχ g _ (χ.map_target hw)).2, χ.right_inv hw]
  let t : Set A := {a | (a : ι) ∈ s}
  let qs := ContinuousLinearMap.pi fun a : t ↦ (ContinuousLinearMap.proj (a : A)).comp q
  have hqs : qs ∘ χ ∘ (g • ·) ∘ χ.symm =ᶠ[𝓝 0] qs := by
    filter_upwards [χ.open_target.mem_nhds h0χ] with w hw
    funext a
    simpa only [qs, Function.comp_apply, (hχ g _ (χ.map_target hw)).2, χ.right_inv hw,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using congrFun (DFunLike.congr_fun (hqσ g) w) (a : A)
  -- Near `0` the face is the cone of `ker qs` cut out by the remaining active coordinates.
  let S : Set qs.ker := {v | ∀ a, 0 ≤ q v a}
  have hS : UniqueDiffWithinAt ℝ S 0 := uniqueDiffOn_ker_setOf_nonneg hq t 0 fun _ ↦ by simp
  refine (χ.eventually_smul_eq_iff_on_ker hxχ hχx hx qs hS hL g hqs).mpr ?_
  -- Pull the face germ condition back along the chart inverse restricted to the cone.
  exact (χ.tendsto_symm_nhdsWithin_face hxχ hχx (fun i ↦ (hρ i).continuousAt) hxD hxs
    hρχ).eventually hg

end TauCeti
