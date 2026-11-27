/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.EigenvalueFunction
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
import TauCeti.Topology.Algebra.Module.Alternating.HermitianForm.Trace

/-!
# The trace identity on a Hermitian manifold

Let `X` be a complex manifold of complex dimension `n = m + 1` with a Hermitian metric `κ`, and
let `α` be a real two-form that has type (1,1) at a point `x`. Then at `x`

`n α ∧ κ ^ (n - 1) = (∑ⱼ λⱼ[α]) κ ^ n`

(`TauCeti.SmoothTwoForm.Compatible.nsmul_wedge_wedgePow_apply`), where `λ[α] = λ_κ[α](x)` is the
eigenvalue vector of `α` relative to `κ` (`TauCeti.relEigenvalueFunction`), so that
`∑ⱼ λⱼ[α] = tr_κ α`. This is the pointwise identity `n·α ∧ ω^{n−1} = (tr_ω α)·ω^n` on a
manifold whose metric varies from point to point.

The proof takes an `h_x`-orthonormal family `b` (it exists since `λ_κ[κ] = e`), in which the trace
is `∑ⱼ α(bⱼ, i bⱼ)` (`TauCeti.SmoothTwoForm.Compatible.sum_relEigenvalueFunction_eq_sum_re`), and
applies the linear-algebra identity
`ContinuousAlternatingMap.nsmul_pairedWedge_wedgePow_eq_sum_smul` on the tangent space at `x`.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.nsmul_wedge_wedgePow_apply`: the trace identity at a point.

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
-/

public section

open Complex Module
open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti.SmoothTwoForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
  {κ : SmoothTwoForm 𝓘(ℝ, E) X} {α : RoughForm 𝓘(ℝ, E) X ℝ 2} {x : X}

/-- **The trace identity on a Hermitian manifold**: on a complex manifold of dimension `m + 1` with
a Hermitian metric `κ`, a real two-form `α` of type (1,1) at `x` satisfies
`(m + 1) α ∧ κ ^ m = (∑ⱼ λⱼ[α]) κ ^ (m + 1)` at `x`, for `λ[α] = λ_κ[α](x)`. -/
theorem Compatible.nsmul_wedge_wedgePow_apply
    (hκ : κ.Compatible (SmoothAlmostComplexStructure.ofComplexManifold E X)) {m : ℕ}
    (hm : finrank ℂ E = m + 1) (hα : ∀ u v : E, α x ![I • u, I • v] = α x ![u, v]) :
    (m + 1) • RoughForm.wedge (SmoothForm.wedgePow κ m).val α x =
      (∑ j, relEigenvalueFunction E κ α 0 x j) • (SmoothForm.wedgePow κ (m + 1)).val x := by
  -- An `h_x`-orthonormal family, from `λ_κ[κ] = e`.
  obtain ⟨b, hb⟩ :=
    (isRelEigenvalueVector_def _ _ _).1 ((hκ.isRelEigenvalueVector_self_iff x).2 rfl)
  have hb₁ (i j : Fin (finrank ℂ E)) :
      twoFormHermitianForm E κ.val x (b i) (b j) = if i = j then 1 else 0 := (hb i j).1
  let e := finCongr hm
  have htr : ∑ j, relEigenvalueFunction E κ α 0 x j = ∑ i : Fin (m + 1),
      α x ![b (e.symm i), I • b (e.symm i)] := by
    rw [hκ.sum_relEigenvalueFunction_eq_sum_re (φ := 0) hα contMDiffAt_const b hb₁,
      ← e.symm.sum_comp]
    simp [ddbarHermitianForm_zero, twoFormHermitianForm_def]
  rw [htr, RoughForm.wedge_def, RoughForm.wedgeWith_apply', SmoothForm.wedgePow_apply,
    SmoothForm.wedgePow_apply]
  exact ContinuousAlternatingMap.nsmul_pairedWedge_wedgePow_eq_sum_smul hm
    (hκ.invariant.apply_I_smul_I_smul x) (fun i j ↦ by
      simpa [e, twoFormHermitianForm_eq_hermitianForm] using hb₁ (e.symm i) (e.symm j)) (α x)

end TauCeti.SmoothTwoForm
