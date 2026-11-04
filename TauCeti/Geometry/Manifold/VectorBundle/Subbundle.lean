/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Topology.VectorBundle.Subbundle
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Notation
import TauCeti.Geometry.Manifold.ContMDiff.LeftInverse

/-!
# Subbundles spanned by smooth local frames

Let `E` be a `C^n` vector bundle over a manifold `B` with model fibre `F`, and let `V` assign to
every point `x` a subspace `V x` of the fibre `E x`. A continuous local frame `X` of `V` on an open
set `U` gives the local trivialization `TauCeti.IsSubbundleFrameOn.trivialization` of `V`, which
sends a vector of `V y` to its coordinates in the basis `X · y`; with the subspace topology, these
trivializations make `V` a topological vector bundle. This file shows that when the sections
`X i` are `C^n`, the coordinate changes between such trivializations are `C^n`. This is the
compatibility condition for the trivializations of `C^n` local frames to form a `C^n` vector
bundle structure on `V`, a `C^n` subbundle of `E`;
`TauCeti.IsContMDiffDistribution.contMDiffVectorBundle` assembles it for the distributions of a
manifold.

Read in a trivialization of `E` near a point `y₀`, a `C^n` frame `X` becomes a `C^n` family of
injective operators `A_X y : 𝕜ᵏ →L[𝕜] F`, namely `c ↦ ∑ i, c i • X i y`
(`TauCeti.IsSubbundleFrameOn.contMDiffAt_trivOperator`). Such a family has `C^n` left inverses
near `y₀` (`ContMDiffAt.exists_contMDiffAt_leftInverse`), and the coordinate change from the frame
`X` to a second frame `Y` is `L_Y y ∘ A_X y` for a left inverse `L_Y y` of `A_Y y`.

## Main results

* `TauCeti.IsSubbundleFrameOn.contMDiffAt_trivOperator`: `C^n` sections of `E`, read in a
  trivialization of `E`, form a `C^n` family of operators.
* `TauCeti.IsSubbundleFrameOn.contMDiffOn_coordChangeL`: the coordinate changes between the
  trivializations of two `C^n` local frames of `V` are `C^n` on the intersection of their domains.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32
  (the local frame criterion for smooth subbundles).
-/

public section

noncomputable section

open Set Filter Function Bundle Topology Module
open scoped Manifold ContDiff

namespace TauCeti.IsSubbundleFrameOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F E IB]
  {ι : Type*} [Fintype ι] {V : Π x, Submodule 𝕜 (E x)}

/-- A family of sections `X i` of `E` that are `C^n` at `y`, read in the trivialization of `E` at
any point `y₀` whose base set contains `y`, is an operator `c ↦ ∑ i, c i • X i` depending `C^n`
on the base point at `y`. -/
theorem contMDiffAt_trivOperator {X : ι → Π x, E x} {y₀ y : B}
    (hX : ∀ i, CMDiffAt n (T% (X i)) y) (hy : y ∈ (trivializationAt F E y₀).baseSet) :
    ContMDiffAt IB 𝓘(𝕜, (ι → 𝕜) →L[𝕜] F) n (trivOperator 𝕜 F X y₀) y := by
  have h (i : ι) := ((trivializationAt F E y₀).contMDiffAt_section_iff hy).mp (hX i)
  rw [funext (trivOperator_eq_sum (𝕜 := 𝕜) (F := F) (X := X) y₀)]
  exact contMDiffAt_finsetSum fun i _ ↦ ((ContinuousLinearMap.smulRightL 𝕜 (ι → 𝕜) F
    (ContinuousLinearMap.proj i)).contDiff.contDiffAt).comp_contMDiffAt (h i)

variable [IsRCLikeNormedField 𝕜]

/-- **Coordinate changes between `C^n` local frames are `C^n`.** If `X` and `Y` are local frames
of `V` on open sets `U` and `U'` whose sections are `C^n`, then the coordinate change from the
trivialization of `X` to that of `Y` is a `C^n` family of operators on `U ∩ U'`. -/
theorem contMDiffOn_coordChangeL {X Y : ι → Π x, E x} {U U' : Set B}
    (hX : IsSubbundleFrameOn F V X U) (hU : IsOpen U) (hXn : ∀ i, CMDiff[U] n (T% (X i)))
    (hY : IsSubbundleFrameOn F V Y U') (hU' : IsOpen U') (hYn : ∀ i, CMDiff[U'] n (T% (Y i))) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    ContMDiffOn IB 𝓘(𝕜, (ι → 𝕜) →L[𝕜] ι → 𝕜) n
      (fun y ↦ ((hX.trivialization hU).coordChangeL 𝕜 (hY.trivialization hU') y :
        (ι → 𝕜) →L[𝕜] ι → 𝕜)) (U ∩ U') := by
  let := subbundleTopology F (F' := ι → 𝕜) V
  have : CompleteSpace 𝕜 := by
    let := IsRCLikeNormedField.rclike 𝕜
    infer_instance
  intro y₀ hy₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hy₀e := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) y₀
  have hAX := contMDiffAt_trivOperator (y₀ := y₀)
    (fun i ↦ (hXn i).contMDiffAt (hU.mem_nhds hy₀.1)) hy₀e
  have hAY := contMDiffAt_trivOperator (y₀ := y₀)
    (fun i ↦ (hYn i).contMDiffAt (hU'.mem_nhds hy₀.2)) hy₀e
  -- Coordinates in `Y` are recovered from the vector read in the trivialization of `E` by a
  -- `C^n` left inverse of the frame operator of `Y`.
  obtain ⟨L, hL, hLinv⟩ := hAY.exists_contMDiffAt_leftInverse
    (.of_injective_of_finiteDimensional_domain (hY.injective_trivOperator hy₀.2))
  refine (hL.clm_comp hAX).congr_of_eventuallyEq ?_
  filter_upwards [hLinv, (hU.inter hU').mem_nhds hy₀,
    (trivializationAt F E y₀).open_baseSet.mem_nhds hy₀e] with y hyL hy hye
  ext1 c
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    (hX.trivialization hU).coordChangeL_apply' (R := 𝕜) (hY.trivialization hU')
      (by simpa only [trivialization_baseSet] using hy),
    trivialization_symm_apply hX hU (q := (y, c)) hy.1]
  rw [trivialization_apply hY hU' (p := TotalSpace.mk' (ι → 𝕜) (E := fun x ↦ V x) y _) hy.2]
  -- The coordinates `d` of the vector in `Y` and its coordinates `c` in `X` describe the same
  -- vector of `E y`, so the frame operators of `Y` and of `X` send them to the same point.
  set d := (hY.basis hy.2).equivFun ((hX.basis hy.1).equivFun.symm c)
  have hd : ∑ i, d i • Y i y = ∑ i, c i • X i y := by
    rw [← coe_basis_equivFun_symm hY hy.2, ← coe_basis_equivFun_symm hX hy.1,
      LinearEquiv.symm_apply_apply]
  rw [← hyL d, trivOperator_apply hye, trivOperator_apply hye, hd]

end TauCeti.IsSubbundleFrameOn
