/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.YangMills.GaugeIdentities
public import TauCeti.Geometry.Lie.Subgroup.Unitary.TangentSpace
import TauCeti.Analysis.Calculus.TangentCone.Basic

/-!
# Gauge transformations with values in a closed subgroup of `U(n)`

The identities of `TauCeti.Analysis.PDE.YangMills.GaugeIdentities` are stated for one-forms and
gauge transformations with values in a normed algebra. For a structure group `G`, a closed
subgroup of the unitary group `U(n)` with Lie algebra `𝔤 = ClosedSubgroup.matrixLieAlgebra G`, a
connection is a `𝔤`-valued one-form and a gauge transformation is a `G`-valued map. This file
shows that the operations of the gauge calculus stay in `𝔤`: for a `G`-valued map `O`, the
right Maurer–Cartan form `O;x = (∂O) O⁻¹` is `𝔤`-valued, and the gauge transform
`O·A = Ad(O) A - O;x` of a `𝔤`-valued one-form `A` is `𝔤`-valued.

The derivative `∂ᵥO(x)` is the velocity of the curve `t ↦ O (x + t v)` in `G`, so it lies in the
tangent cone of `G` at `O x`, which is `O(x) 𝔤 = 𝔤 O(x)` by
`ClosedSubgroup.tangentConeAt_eq_matrixTangentSpace`. Hence `∂ᵥO(x) O(x)⁻¹ ∈ 𝔤`. Only the values of
`O` near `x` need to lie in `G`, and no differentiability is assumed: where `O` is not
differentiable, `fderiv` is `0`.

Derivatives of matrix-valued maps are taken for the operator norm `Matrix.Norms.Operator`, whose
topology is that of the matrices, so the statements do not depend on this choice.

## Main results

* `TauCeti.ringInverse_coe_unitaryGroup`: the ring inverse of a unitary matrix is its conjugate
  transpose.
* `TauCeti.fderiv_apply_mem_matrixTangentSpace`: the derivative of a `G`-valued map at `x` lies in
  the tangent space of `G` at its value.
* `TauCeti.rightMaurerCartan_mem_matrixLieAlgebra`: `O;x` is `𝔤`-valued.
* `TauCeti.gaugeAction_mem_matrixLieAlgebra`: `O·A` is `𝔤`-valued.

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436
  (2022), arXiv:1709.08599, Section 1.
-/

public section

noncomputable section

open Filter
open scoped Matrix.Norms.Operator Ring Topology

namespace TauCeti

variable {n 𝕜 E : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)}

/-- The ring inverse of a unitary matrix is its conjugate transpose. -/
@[simp]
theorem ringInverse_coe_unitaryGroup (g : Matrix.unitaryGroup n 𝕜) :
    (g : Matrix n n 𝕜)⁻¹ʳ = star (g : Matrix n n 𝕜) :=
  Ring.inverse_unit (Unitary.toUnits g)

/-- **The derivative of a `G`-valued map lies in the tangent space.** If `O` takes values in `G`
near `x`, then every directional derivative `∂ᵥO(x)` lies in the tangent space `g 𝔤` of `G` at
`g = O x`. -/
theorem fderiv_apply_mem_matrixTangentSpace {O : E → Matrix n n 𝕜} {x : E} {g : G}
    (hO : ∀ᶠ y in 𝓝 x, O y ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
    (hOx : O x = g) (v : E) : fderiv ℝ O x v ∈ G.matrixTangentSpace g := by
  by_cases hd : ¬DifferentiableAt ℝ O x
  · rw [fderiv_zero_of_not_differentiableAt hd]
    exact zero_mem _
  rw [not_not] at hd
  -- `∂ᵥO(x)` is the velocity at `t = 0` of the curve `t ↦ O (x + t v)`, which stays in `G`.
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd' : HasFDerivAt O (fderiv ℝ O x) (x + (0 : ℝ) • v) := by
    simpa using hd.hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ ↦ O (x + t • v)) (fderiv ℝ O x v) 0 :=
    hd'.comp_hasDerivAt (0 : ℝ) hline
  have htend : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝 0) (𝓝 x) := by
    simpa using hline.continuousAt.tendsto
  have h := hγ.mem_tangentConeAt (htend.eventually hO)
  rw [zero_smul, add_zero, hOx, ClosedSubgroup.tangentConeAt_eq_matrixTangentSpace] at h
  exact h

/-- **The Maurer–Cartan form of a `G`-valued map is `𝔤`-valued.** If `O` takes values in `G` near
`x`, then `O;x v = ∂ᵥO(x) O(x)⁻¹` lies in the Lie algebra of `G`. -/
theorem rightMaurerCartan_mem_matrixLieAlgebra {O : E → Matrix n n 𝕜} {x : E}
    (hO : ∀ᶠ y in 𝓝 x, O y ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
    (v : E) : rightMaurerCartan ℝ O x v ∈ G.matrixLieAlgebra := by
  obtain ⟨g, hg, hgx⟩ := hO.self_of_nhds
  have h := fderiv_apply_mem_matrixTangentSpace (g := ⟨g, hg⟩) hO hgx.symm v
  rw [ClosedSubgroup.mem_matrixTangentSpace_iff_mul_star] at h
  rwa [rightMaurerCartan_apply, ← hgx, ringInverse_coe_unitaryGroup]

/-- **The gauge action preserves `𝔤`-valued one-forms.** If `O` takes values in `G` near `x` and
the one-form `A` takes values in the Lie algebra of `G` at `x`, then
so does `O·A = Ad(O) A - O;x` at `x`. -/
-- The codomain of `A` carries the topology of the operator norm, as `gaugeAction` requires; the
-- plain `E →L[ℝ] Matrix n n 𝕜` would elaborate with the product topology of the matrices, which
-- is equal to it but not reducibly so.
theorem gaugeAction_mem_matrixLieAlgebra {O : E → Matrix n n 𝕜} {x : E}
    (hO : ∀ᶠ y in 𝓝 x, O y ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
    {A : E → @ContinuousLinearMap ℝ ℝ _ _ (RingHom.id ℝ) E _ _ (Matrix n n 𝕜)
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ _ _}
    (hA : ∀ v, A x v ∈ G.matrixLieAlgebra) (v : E) :
    gaugeAction ℝ O A x v ∈ G.matrixLieAlgebra := by
  obtain ⟨g, hg, hgx⟩ := hO.self_of_nhds
  rw [gaugeAction_apply]
  refine sub_mem ?_ (rightMaurerCartan_mem_matrixLieAlgebra hO v)
  rw [← hgx, ringInverse_coe_unitaryGroup]
  exact ClosedSubgroup.mul_mul_star_mem_matrixLieAlgebra hg (hA v)

end TauCeti
