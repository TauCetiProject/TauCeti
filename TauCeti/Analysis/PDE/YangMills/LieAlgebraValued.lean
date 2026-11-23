/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.YangMills.GaugeIdentities
public import TauCeti.Geometry.Lie.Subgroup.Unitary.TangentSpace
import TauCeti.Algebra.Star.Unitary

/-!
# Gauge transformations with values in a closed subgroup of `U(n)`

The identities of `TauCeti.Analysis.PDE.YangMills.GaugeIdentities` are stated for one-forms and
gauge transformations with values in a normed algebra. For a structure group `G`, a closed
subgroup of the unitary group `U(n)` with Lie algebra `𝔤 = ClosedSubgroup.matrixLieAlgebra G`, a
connection is a `𝔤`-valued one-form and a gauge transformation is a `G`-valued map. This file
shows that the operations of the gauge calculus stay in `𝔤`: for a `G`-valued map `O`, the
right Maurer–Cartan form `O;x = (∂O) O⁻¹` is `𝔤`-valued, and the gauge transform
`O·A = Ad(O) A - O;x` of a `𝔤`-valued one-form `A` is `𝔤`-valued.

The derivative `∂ᵥO(x)` lies in the tangent space `O(x) 𝔤 = 𝔤 O(x)` of `G` at `O x`
(`ClosedSubgroup.fderiv_apply_mem_matrixTangentSpace`), and the ring inverse of the unitary
`O(x)` is `star O(x)` (`Unitary.ringInverse_coe`). Hence `∂ᵥO(x) O(x)⁻¹ ∈ 𝔤`. Only the values of
`O` near `x` need to lie in `G`, and no differentiability is assumed: where `O` is not
differentiable, `fderiv` is `0`.

Derivatives of matrix-valued maps are taken for the operator norm `Matrix.Norms.Operator`, whose
topology is that of the matrices, so the statements do not depend on this choice.

## Main results

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

/-- **The Maurer–Cartan form of a `G`-valued map is `𝔤`-valued.** If `O` takes values in `G` near
`x`, then `O;x v = ∂ᵥO(x) O(x)⁻¹` lies in the Lie algebra of `G`. -/
theorem rightMaurerCartan_mem_matrixLieAlgebra {O : E → Matrix n n 𝕜} {x : E}
    (hO : ∀ᶠ y in 𝓝 x, O y ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
    (v : E) : rightMaurerCartan ℝ O x v ∈ G.matrixLieAlgebra := by
  obtain ⟨g, hg, hgx⟩ := hO.self_of_nhds
  have h := ClosedSubgroup.fderiv_apply_mem_matrixTangentSpace (g := ⟨g, hg⟩) hO hgx.symm v
  rw [ClosedSubgroup.mem_matrixTangentSpace_iff_mul_star] at h
  rwa [rightMaurerCartan_apply, ← hgx, Unitary.ringInverse_coe]

/-- **The gauge action preserves `𝔤`-valued one-forms.** If `O` takes values in `G` near `x` and
the one-form `A` takes a value in the Lie algebra of `G` at `x` in the direction `v`, then
so does `O·A = Ad(O) A - O;x`. -/
-- The codomain of `A` carries the topology of the operator norm, as `gaugeAction` requires; the
-- plain `E →L[ℝ] Matrix n n 𝕜` would elaborate with the product topology of the matrices, which
-- is equal to it but not reducibly so.
theorem gaugeAction_mem_matrixLieAlgebra {O : E → Matrix n n 𝕜} {x : E}
    (hO : ∀ᶠ y in 𝓝 x, O y ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
    {A : E → @ContinuousLinearMap ℝ ℝ _ _ (RingHom.id ℝ) E _ _ (Matrix n n 𝕜)
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ _ _}
    {v : E} (hA : A x v ∈ G.matrixLieAlgebra) :
    gaugeAction ℝ O A x v ∈ G.matrixLieAlgebra := by
  obtain ⟨g, hg, hgx⟩ := hO.self_of_nhds
  rw [gaugeAction_apply]
  refine sub_mem ?_ (rightMaurerCartan_mem_matrixLieAlgebra hO v)
  rw [← hgx, Unitary.ringInverse_coe]
  exact ClosedSubgroup.mul_mul_star_mem_matrixLieAlgebra hg hA

end TauCeti
