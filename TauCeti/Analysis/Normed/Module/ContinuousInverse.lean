/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# Continuous left inverses of injective operators

Mathlib's `ContinuousLinearMap.HasLeftInverse` records that a continuous linear map has a left
inverse which is itself continuous and linear. This file adds two facts about it.

* Over `ℝ` or `ℂ`, an injective continuous linear map out of a finite-dimensional space has a
  continuous left inverse, whatever the locally convex codomain: its range is finite-dimensional,
  hence has a closed complement by the Hahn–Banach theorem.
* Having a continuous left inverse is stable in families. If `A x` depends continuously on `x`
  and `A x₀` has a continuous left inverse, then so does `A x` for `x` near `x₀`, and the left
  inverses can be chosen to depend continuously on `x` at `x₀`. If `P` is a left inverse of
  `A x₀`, then `P ∘ A x` is invertible near `x₀`, and `(P ∘ A x)⁻¹ ∘ P` is a left inverse of
  `A x`.

The second fact is what makes coordinates with respect to a moving family of linearly
independent vectors depend continuously on the base point, as in the local trivializations of a
subbundle spanned by local frames.

## Main results

* `ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional_domain`: an injective
  continuous linear map out of a finite-dimensional space over `ℝ` or `ℂ` has a continuous left
  inverse.
* `ContinuousAt.exists_continuousAt_leftInverse`: continuously varying left inverses of a
  continuous family of operators whose member at `x₀` has a continuous left inverse.
-/

public section

noncomputable section

open Filter Function Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

namespace ContinuousLinearMap.HasLeftInverse

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [Module 𝕜 G] [IsTopologicalAddGroup G]
  [ContinuousSMul 𝕜 G]
  {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F] [T2Space F]

/-- Over `ℝ` or `ℂ`, an injective continuous linear map out of a finite-dimensional space into a
locally convex (polynormable) space has a continuous left inverse. Its range is
finite-dimensional, so it has a closed complement, and the inverse of `f` on its range is
continuous. -/
theorem of_injective_of_finiteDimensional_domain [IsRCLikeNormedField 𝕜] [PolynormableSpace 𝕜 F]
    [FiniteDimensional 𝕜 G] {f : G →L[𝕜] F} (hf : Injective f) : f.HasLeftInverse := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  -- A continuous projection `p` onto the range, followed by the inverse of `f` on its range.
  obtain ⟨p, hp⟩ :=
    Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range f.toLinearMap)
  let g := (LinearEquiv.ofInjective f.toLinearMap hf).symm
  refine ⟨(LinearMap.toContinuousLinearMap g.toLinearMap).comp p, fun v ↦ ?_⟩
  have hv : p (f v) = LinearEquiv.ofInjective f.toLinearMap hf v :=
    hp ⟨f v, LinearMap.mem_range_self f.toLinearMap v⟩
  simp [g, hv]

end ContinuousLinearMap.HasLeftInverse

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {X : Type*} [TopologicalSpace X]

/-- **Left inverses vary continuously.** Let `A x` be a continuous linear map depending
continuously on `x` at `x₀`, into a normed space from a Banach space. If `A x₀` has a continuous
left inverse, then there are continuous linear maps `L x`, depending continuously on `x` at `x₀`,
such that `L x` is a left inverse of `A x` for all `x` near `x₀`. -/
theorem ContinuousAt.exists_continuousAt_leftInverse {A : X → G →L[𝕜] F} {x₀ : X}
    (hA : ContinuousAt A x₀) (h : (A x₀).HasLeftInverse) :
    ∃ L : X → F →L[𝕜] G, ContinuousAt L x₀ ∧ ∀ᶠ x in 𝓝 x₀, LeftInverse (L x) (A x) := by
  obtain ⟨P, hP⟩ := h
  -- The compression `P ∘ A x` is the identity at `x₀`, hence invertible near `x₀`.
  have hQ : ContinuousAt (fun x ↦ P ∘L A x) x₀ := (continuousAt_const (y := P)).clm_comp hA
  have hQ₀ : P ∘L A x₀ = ((1 : (G →L[𝕜] G)ˣ) : G →L[𝕜] G) := ContinuousLinearMap.ext hP
  refine ⟨fun x ↦ Ring.inverse (P ∘L A x) ∘L P,
    ContinuousAt.clm_comp ((NormedRing.inverse_continuousAt 1).comp_of_eq hQ hQ₀)
      continuousAt_const, ?_⟩
  filter_upwards [hQ.preimage_mem_nhds (hQ₀ ▸ Units.nhds 1)] with x hx v
  have := congrArg (fun T : G →L[𝕜] G ↦ T v) (Ring.inverse_mul_cancel _ hx)
  simpa using this
