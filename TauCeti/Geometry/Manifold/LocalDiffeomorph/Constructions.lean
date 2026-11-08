/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Constructions of partial diffeomorphisms

Two basic ways of producing a `PartialDiffeomorph`: lowering the regularity of a given one, and
reading a continuous linear equivalence as one at any regularity. Mathlib's
`ContinuousLinearEquiv.toDiffeomorph` gives the latter at regularity `∞` only, so it does not cover
the analytic regularity `ω`. It also records that the coordinate axes of a partial diffeomorphism
into a real Euclidean space, centred at a point, pull back to curves through that point.

## Main definitions

* `PartialDiffeomorph.ofLE`: a `C^n` partial diffeomorphism as a `C^m` one, for `m ≤ n`.
* `ContinuousLinearEquiv.toPartialDiffeomorph`: a continuous linear equivalence as a `C^n` partial
  diffeomorphism defined everywhere, for any `n`.

## Main results

* `PartialDiffeomorph.exists_curve_single_axis`: pulling a coordinate axis back through a
  partial diffeomorphism into `EuclideanSpace ℝ ι` gives a curve through the centre point, smooth
  near `0`.
-/

public section

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {m n : WithTop ℕ∞}

namespace PartialDiffeomorph

/-- A `C^n` partial diffeomorphism as a `C^m` one, for `m ≤ n`. -/
def ofLE (Φ : PartialDiffeomorph I J M N n) (hmn : m ≤ n) : PartialDiffeomorph I J M N m where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn.of_le hmn
  contMDiffOn_invFun := Φ.symm.contMDiffOn.of_le hmn

/-- Lowering the regularity keeps the underlying partial equivalence. -/
@[simp]
theorem ofLE_toPartialEquiv (Φ : PartialDiffeomorph I J M N n) (hmn : m ≤ n) :
    (Φ.ofLE hmn).toPartialEquiv = Φ.toPartialEquiv :=
  (rfl)

section Axis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pulling a coordinate axis of a `C^∞` partial diffeomorphism `ψ` into `EuclideanSpace ℝ ι`
with `ψ x = 0` back through the inverse chart gives a curve through `x`, smooth near the parameter
`0`, which at every parameter near `0` lies in the chart source and maps to the point of the axis
with that coordinate. -/
theorem exists_curve_single_axis {x : M}
    (ψ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ ι) M (EuclideanSpace ℝ ι) ∞)
    (hxψ : x ∈ ψ.source) (hψx : ψ x = 0) (i : ι) :
    ∃ γ : ℝ → M, (∀ᶠ t in 𝓝 0, ContMDiffAt 𝓘(ℝ) I ∞ γ t) ∧ γ 0 = x ∧
      ∀ᶠ t in 𝓝 0, γ t ∈ ψ.source ∧ ψ (γ t) = EuclideanSpace.single i t := by
  have haxis : ContDiff ℝ ∞ fun t : ℝ ↦ EuclideanSpace.single i t := by
    rw [contDiff_piLp]
    intro j
    simp only [PiLp.single_apply]
    split_ifs <;> fun_prop
  have haxis0 : EuclideanSpace.single i (0 : ℝ) = (0 : EuclideanSpace ℝ ι) := by simp
  have hzero : (0 : EuclideanSpace ℝ ι) ∈ ψ.target := by
    simpa only [hψx] using ψ.map_source hxψ
  -- Openness of the chart target makes the inverse-chart curve valid near zero.
  have hTarget : ∀ᶠ t in 𝓝 (0 : ℝ), EuclideanSpace.single i t ∈ ψ.target := by
    apply haxis.continuous.continuousAt
    simpa only [haxis0] using ψ.open_target.mem_nhds hzero
  refine ⟨fun t ↦ ψ.toOpenPartialHomeomorph.symm (EuclideanSpace.single i t),
    hTarget.mono fun t ht ↦ ?_, ?_, hTarget.mono fun t ht ↦ ⟨ψ.map_target ht, ψ.right_inv ht⟩⟩
  · -- The inverse chart is smooth on its open target.
    exact (ψ.contMDiffOn_invFun.contMDiffAt (ψ.open_target.mem_nhds ht)).comp t
      haxis.contMDiff.contMDiffAt
  · simp only [haxis0]
    rw [← hψx]
    exact ψ.left_inv hxψ

end Axis

end PartialDiffeomorph

namespace ContinuousLinearEquiv

/-- A continuous linear equivalence as a `C^n` partial diffeomorphism defined everywhere, for any
regularity `n`, including the analytic regularity `ω` not reached by
`ContinuousLinearEquiv.toDiffeomorph`. -/
def toPartialDiffeomorph (A : E ≃L[𝕜] F) : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n where
  toPartialEquiv := A.toEquiv.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := A.contDiff.contMDiff.contMDiffOn
  contMDiffOn_invFun := A.symm.contDiff.contMDiff.contMDiffOn

/-- The partial equivalence underlying `ContinuousLinearEquiv.toPartialDiffeomorph` is the
underlying equivalence, on the whole space. -/
@[simp]
theorem toPartialDiffeomorph_toPartialEquiv (A : E ≃L[𝕜] F) :
    (A.toPartialDiffeomorph (n := n)).toPartialEquiv = A.toEquiv.toPartialEquiv :=
  (rfl)

end ContinuousLinearEquiv
