/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import TauCeti.Analysis.Fredholm.SmallPerturbation

import TauCeti.Analysis.Fredholm.Basic

/-!
# Continuous families of Fredholm operators

The Fredholm index is locally constant in a continuous family of Fredholm operators. Consequently,
it is constant when the parameter space is preconnected, and in particular at the endpoints of a
path of Fredholm operators, so it descends to the set of path components
`ZerothHomotopy {T : E →L[K] F // T.IsFredholm}` (`ZerothHomotopy.fredholmIndex`). Between
finite-dimensional spaces over a path-connected complete nontrivially normed field, every operator
is Fredholm and scalar interpolation makes the Fredholm locus path connected
(`ContinuousLinearMap.instPathConnectedSpaceIsFredholmOfFiniteDimensional`).

This is the continuous-family form of stability under small perturbations: a family can change index
only by leaving the Fredholm locus.

The proofs use the operator-norm neighborhood on which
`ContinuousLinearMap.IsFredholm.eventually_isFredholm_and_index_eq` makes the index constant,
together with Mathlib's general API for locally constant functions on preconnected spaces.

## Main declarations

* `Continuous.isLocallyConstant_index`: the index of a continuous Fredholm family is
  locally constant.
* `ContinuousOn.index_eq_of_isPreconnected`: two parameters in the same preconnected set
  give operators of equal index.
* `Continuous.index_eq_of_preconnectedSpace`: a continuous Fredholm family over a
  preconnected space has constant index.
* `Path.index_eq`: the endpoints of a continuous Fredholm path have equal index.
* `ContinuousLinearMap.index_eq_of_segment`: two operators joined by a Fredholm affine segment
  have equal index.
* `ZerothHomotopy.fredholmIndex`: the Fredholm index descended to the path components of the
  Fredholm locus.
* `ContinuousLinearMap.instPathConnectedSpaceIsFredholmOfFiniteDimensional`: in finite dimensions
  over a path-connected complete nontrivially normed field, the Fredholm locus is path connected.

The index convention and its perturbation stability follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace TauCeti

variable {K E F X : Type*}
variable [NontriviallyNormedField K] [CompleteSpace K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F]
variable [TopologicalSpace X]

/-- The Fredholm index of a continuous family of Fredholm operators is locally constant on the
parameter space. -/
theorem _root_.Continuous.isLocallyConstant_index {A : X → E →L[K] F}
    (hA : Continuous A) (hFredholm : ∀ x, ContinuousLinearMap.IsFredholm (A x)) :
    IsLocallyConstant fun x ↦ ContinuousLinearMap.index (A x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [hA.continuousAt (hFredholm x).eventually_isFredholm_and_index_eq] with y hy
  exact hy.2

/-- Along a continuous family of Fredholm operators, parameters in the same preconnected set give
operators with equal index. -/
theorem _root_.ContinuousOn.index_eq_of_isPreconnected {A : X → E →L[K] F} {s : Set X}
    (hA : ContinuousOn A s) (hFredholm : ∀ x ∈ s, ContinuousLinearMap.IsFredholm (A x))
    (hs : IsPreconnected s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ContinuousLinearMap.index (A x) = ContinuousLinearMap.index (A y) := by
  let := Subtype.preconnectedSpace hs
  exact (Continuous.isLocallyConstant_index hA.domRestrict
    (fun x ↦ hFredholm x x.property)).apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

/-- A continuous family of Fredholm operators over a preconnected parameter space has constant
index. -/
theorem _root_.Continuous.index_eq_of_preconnectedSpace [PreconnectedSpace X]
    {A : X → E →L[K] F} (hA : Continuous A)
    (hFredholm : ∀ x, ContinuousLinearMap.IsFredholm (A x)) (x y : X) :
    ContinuousLinearMap.index (A x) = ContinuousLinearMap.index (A y) :=
  (Continuous.isLocallyConstant_index hA hFredholm).apply_eq_of_preconnectedSpace x y

/-- The endpoints of a continuous path of Fredholm operators have the same index. -/
theorem _root_.Path.index_eq {T S : E →L[K] F} (A : Path T S)
    (hFredholm : ∀ t, ContinuousLinearMap.IsFredholm (A t)) :
    ContinuousLinearMap.index T = ContinuousLinearMap.index S := by
  simpa only [A.source, A.target] using
    Continuous.index_eq_of_preconnectedSpace A.continuous hFredholm 0 1

/-- Two operators have equal index if every operator on the affine segment between them is
Fredholm. The operator space only needs a continuous real module structure to form the segment. -/
theorem _root_.ContinuousLinearMap.index_eq_of_segment
    [Module ℝ (E →L[K] F)] [ContinuousSMul ℝ (E →L[K] F)]
    (T S : E →L[K] F) : (∀ t : unitInterval,
      ContinuousLinearMap.IsFredholm ((1 - (t : ℝ)) • T + (t : ℝ) • S)) →
      ContinuousLinearMap.index T = ContinuousLinearMap.index S := by
  intro hFredholm
  apply Path.index_eq (Path.segment T S)
  simpa only [Path.segment_apply, AffineMap.lineMap_apply_module] using hFredholm

end TauCeti

section ZerothHomotopy

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The Fredholm index descended to the path components of the Fredholm locus. -/
noncomputable def ZerothHomotopy.fredholmIndex :
    ZerothHomotopy {T : E →L[𝕜] F // T.IsFredholm} → ℤ :=
  ZerothHomotopy.lift (fun T ↦ T.val.index) fun _ _ γ ↦
    (γ.map continuous_subtypeVal).index_eq fun t ↦ (γ t).property

/-- On the path component of a Fredholm operator `T`, `ZerothHomotopy.fredholmIndex` evaluates to
`T.val.index`. -/
@[simp]
theorem ZerothHomotopy.fredholmIndex_mk (T : {T : E →L[𝕜] F // T.IsFredholm}) :
    ZerothHomotopy.fredholmIndex (.mk T) = T.val.index :=
  ZerothHomotopy.lift_mk _ _ T

end ZerothHomotopy

/-- Between finite-dimensional topological vector spaces over a path-connected complete
nontrivially normed field (with Hausdorff target), every continuous linear map is Fredholm and
interpolating along a scalar path from `0` to `1` in `𝕜` makes the Fredholm locus path connected. -/
noncomputable instance ContinuousLinearMap.instPathConnectedSpaceIsFredholmOfFiniteDimensional
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [PathConnectedSpace 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F] :
    PathConnectedSpace {T : E →L[𝕜] F // T.IsFredholm} :=
  PathConnectedSpace.mk ⟨⟨0, isFredholm_of_finiteDimensional 0⟩⟩ fun S T ↦ by
    let γ : Path S.val T.val :=
      ((PathConnectedSpace.somePath (0 : 𝕜) 1).map
        (f := fun c : 𝕜 ↦ S.val + c • (T.val - S.val))
        (continuous_const.add (continuous_id.smul continuous_const))).cast (by simp) (by simp)
    exact (joinedIn_iff_joined (F := {U : E →L[𝕜] F | U.IsFredholm}) S.property T.property).mp
      ⟨γ, fun _ ↦ isFredholm_of_finiteDimensional _⟩

end
