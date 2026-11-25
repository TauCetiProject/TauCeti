/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.TangentCone.Seq
import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.Normed.Algebra.MatrixExponential

/-!
# The tangent spaces of a closed subgroup of the unitary group

By the closed-subgroup theorem, a closed subgroup `G` of the unitary group
`U(n) = Matrix.unitaryGroup n 𝕜` (over `ℝ` or `ℂ`) is a compact embedded submanifold of the real
vector space of `n × n` matrices. This file describes its tangent space at each `g ∈ G` as a real
subspace of the matrices: it is `g 𝔤 = 𝔤 g`, where `𝔤 = ClosedSubgroup.matrixLieAlgebra G` is the
Lie algebra of `G`.

The tangent space is taken to be the tangent cone `tangentConeAt ℝ G g` of `G` at `g`, the set
of all limits of rescaled secants `cₖ • (gₖ - g)` with `gₖ ∈ G` tending to `g`. This notion
depends only on `G` as a set of matrices, not on a chosen manifold structure, and a map that is
differentiable at `g` has its derivative on this cone determined by its values on `G`. So, for
instance, the derivative at `g` of a retraction of a neighbourhood of `G` onto `G` is the
identity on `g 𝔤`.

The inclusion `g 𝔤 ⊆ tangentConeAt ℝ G g` holds because `t ↦ g exp (t X)` is a curve in `G` with
velocity `g X` at `t = 0`. For the converse, left multiplication by `g⁻¹` reduces to `g = 1`. There,
a local logarithm, the inverse of `exp` near `0` given by the inverse function theorem, has
derivative the identity at `1`, and so carries the tangent cone of `G` at `1` into the tangent
cone at `0` of `{Y : exp Y ∈ G}`. That cone lies in `𝔤` by the limit criterion
`ClosedSubgroup.mem_matrixLieAlgebra_of_tendsto`. Finally `Ad(g) 𝔤 = 𝔤` gives `g 𝔤 = 𝔤 g`.

## Main definitions

* `ClosedSubgroup.matrixTangentSpace`: the subspace `g 𝔤` of the matrices, for `g ∈ G`.

## Main results

* `ClosedSubgroup.mem_matrixTangentSpace_iff`: `V ∈ g 𝔤` exactly when `g⁻¹ V ∈ 𝔤`.
* `ClosedSubgroup.matrixTangentSpace_eq_map_mulRight`: `g 𝔤 = 𝔤 g`.
* `ClosedSubgroup.mem_posTangentConeAt_of_mem_matrixTangentSpace`: `g 𝔤` lies in the positive
  tangent cone of `G` at `g`.
* `ClosedSubgroup.tangentConeAt_eq_matrixTangentSpace`: the tangent cone of `G` at `g` is `g 𝔤`.
* `ClosedSubgroup.fderiv_apply_mem_matrixTangentSpace`: the derivative at `x` of a map with values
  in `G` near `x` lies in the tangent space of `G` at its value.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts in
  Mathematics 222, Springer (2015), Sections 3.3 and 3.7.
-/

public section

noncomputable section

open Filter NormedSpace Set
open scoped Matrix Topology

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ClosedSubgroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
  {G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)}

variable (G) in
/-- The tangent space `g 𝔤 = {g X : X ∈ 𝔤}` at `g ∈ G` of a closed subgroup `G` of `U(n)`, as a
real subspace of the matrices. By `ClosedSubgroup.tangentConeAt_eq_matrixTangentSpace` it is the
tangent cone of `G` at `g`, and by `ClosedSubgroup.matrixTangentSpace_eq_map_mulRight` it is also
`𝔤 g`. -/
def matrixTangentSpace (g : G) : Submodule ℝ (Matrix n n 𝕜) :=
  G.matrixLieAlgebra.toSubmodule.map (LinearMap.mulLeft ℝ (g : Matrix n n 𝕜))

/-- `g X` lies in the tangent space at `g` for every `X` in the Lie algebra. -/
theorem mul_mem_matrixTangentSpace (g : G) {X : Matrix n n 𝕜} (hX : X ∈ G.matrixLieAlgebra) :
    (g : Matrix n n 𝕜) * X ∈ G.matrixTangentSpace g :=
  ⟨X, hX, rfl⟩

/-- A matrix `V` lies in the tangent space `g 𝔤` exactly when `g⁻¹ V ∈ 𝔤`; for a unitary `g` the
inverse is `star g`. -/
@[simp]
theorem mem_matrixTangentSpace_iff {g : G} {V : Matrix n n 𝕜} :
    V ∈ G.matrixTangentSpace g ↔ star (g : Matrix n n 𝕜) * V ∈ G.matrixLieAlgebra := by
  constructor
  · rintro ⟨X, hX, rfl⟩
    simpa [← mul_assoc] using hX
  · intro hV
    exact ⟨_, hV, by simp [← mul_assoc]⟩

/-- A matrix `V` lies in the tangent space at `g` exactly when `V g⁻¹ ∈ 𝔤`; for a unitary `g` the
inverse is `star g`. -/
theorem mem_matrixTangentSpace_iff_mul_star {g : G} {V : Matrix n n 𝕜} :
    V ∈ G.matrixTangentSpace g ↔ V * star (g : Matrix n n 𝕜) ∈ G.matrixLieAlgebra := by
  rw [mem_matrixTangentSpace_iff]
  -- The two conditions differ by `Ad(g)` and `Ad(g⁻¹)`, which preserve the Lie algebra.
  constructor
  · intro h
    simpa [← mul_assoc] using mul_mul_star_mem_matrixLieAlgebra g.property h
  · intro h
    simpa [mul_assoc] using mul_mul_star_mem_matrixLieAlgebra (inv_mem g.property) h

/-- **`g 𝔤 = 𝔤 g`.** The tangent space at `g` is also the image of the Lie algebra under right
multiplication by `g`. -/
theorem matrixTangentSpace_eq_map_mulRight (g : G) :
    G.matrixTangentSpace g =
      G.matrixLieAlgebra.toSubmodule.map (LinearMap.mulRight ℝ (g : Matrix n n 𝕜)) := by
  ext V
  rw [mem_matrixTangentSpace_iff_mul_star]
  constructor
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩
  · rintro ⟨X, hX, rfl⟩
    simpa [mul_assoc] using hX

/-- The tangent space at the identity is the Lie algebra. -/
@[simp]
theorem matrixTangentSpace_one : G.matrixTangentSpace 1 = G.matrixLieAlgebra.toSubmodule := by
  ext V
  simp [mem_matrixTangentSpace_iff]

section TangentCone

open scoped Matrix.Norms.Operator

/-- If `exp Y` lies in `G`, so does `exp (-Y)`. -/
private theorem exists_eq_exp_neg {Y : Matrix n n 𝕜} (hY : ∃ g ∈ G, (g : Matrix n n 𝕜) = exp Y) :
    ∃ g ∈ G, (g : Matrix n n 𝕜) = exp (-Y) := by
  obtain ⟨g, hg, hgY⟩ := hY
  refine ⟨g⁻¹, inv_mem hg, ?_⟩
  have h : exp (-Y) * (g : Matrix n n 𝕜) = 1 := by rw [hgY, Matrix.exp_neg_mul_exp]
  rw [Matrix.UnitaryGroup.inv_val]
  exact (left_inv_eq_right_inv h (Unitary.mul_star_self_of_mem g.property)).symm

/-- The tangent cone at `0` of `{Y : exp Y ∈ G}` lies in the Lie algebra. -/
private theorem tangentConeAt_setOf_exp_subset :
    tangentConeAt ℝ {Y : Matrix n n 𝕜 | ∃ g ∈ G, (g : Matrix n n 𝕜) = exp Y} 0 ⊆
      G.matrixLieAlgebra := by
  intro V hV
  obtain ⟨c, d, hc, hd, hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hV
  have hc0 := eventually_ne_of_tendsto_norm_atTop hc 0
  -- Rescale by `|cₖ|⁻¹ → 0`: then `|cₖ|⁻¹ • (cₖ • dₖ) = ± dₖ`, whose exponential lies in `G`.
  refine mem_matrixLieAlgebra_of_tendsto (t := fun k ↦ |c k|⁻¹) (Xn := fun k ↦ c k • d k) ?_ ?_
    hcd ?_
  · filter_upwards [hc0] with k hk
    positivity
  · exact tendsto_inv_atTop_zero.comp (by simpa only [Real.norm_eq_abs] using hc)
  · filter_upwards [hd, hc0] with k hk hck
    rw [zero_add] at hk
    rw [smul_smul]
    rcases hck.lt_or_gt with h | h
    · rw [abs_of_neg h, inv_neg, neg_mul, inv_mul_cancel₀ h.ne, neg_one_smul]
      exact exists_eq_exp_neg hk
    · rwa [abs_of_pos h, inv_mul_cancel₀ h.ne', one_smul]

/-- The tangent cone of `G` at `1` lies in the Lie algebra. -/
private theorem tangentConeAt_one_subset :
    tangentConeAt ℝ (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) 1 ⊆
      G.matrixLieAlgebra := by
  -- A local logarithm `L`: the local inverse of `exp` at `0`, which has derivative the identity.
  -- The scoped operator norm induces the native topology and module structure of the matrices,
  -- so the facts below, stated for the latter, are accepted up to definitional unfolding.
  have hexp : HasStrictFDerivAt (exp : Matrix n n 𝕜 → Matrix n n 𝕜)
      ((ContinuousLinearEquiv.refl ℝ (Matrix n n 𝕜) : Matrix n n 𝕜 →L[ℝ] Matrix n n 𝕜)) 0 :=
    hasStrictFDerivAt_exp_zero
  have hU : {M | exp (hexp.localInverse _ _ _ M) = M} ∈ 𝓝 (1 : Matrix n n 𝕜) := by
    have h := hexp.eventually_right_inverse
    rw [exp_zero] at h
    exact h
  have hlog :
      HasFDerivAt (hexp.localInverse _ _ _) (ContinuousLinearMap.id ℝ (Matrix n n 𝕜)) 1 := by
    have h := hexp.to_localInverse.hasFDerivAt
    rw [exp_zero] at h
    exact h
  have hlog1 : hexp.localInverse _ _ _ (1 : Matrix n n 𝕜) = 0 := by
    have h := hexp.localInverse_apply_image
    rw [exp_zero] at h
    exact h
  intro V hV
  rw [← tangentConeAt_inter_nhds hU] at hV
  have h : V ∈ tangentConeAt ℝ (hexp.localInverse _ _ _ ''
      ((((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) ∩
        {M | exp (hexp.localInverse _ _ _ M) = M})) (hexp.localInverse _ _ _ 1) :=
    hlog.hasFDerivWithinAt.mapsTo_tangent_cone hV
  rw [hlog1] at h
  refine tangentConeAt_setOf_exp_subset (tangentConeAt_mono ?_ h)
  rintro _ ⟨M, ⟨⟨g, hg, rfl⟩, hM⟩, rfl⟩
  exact ⟨g, hg, hM.symm⟩

/-- Every vector `g X`, `X ∈ 𝔤`, of the tangent space at `g` is a velocity of a curve in `G`
starting at `g`, so it lies in the positive tangent cone of `G` at `g`. -/
theorem mem_posTangentConeAt_of_mem_matrixTangentSpace {g : G} {V : Matrix n n 𝕜}
    (hV : V ∈ G.matrixTangentSpace g) :
    V ∈ posTangentConeAt (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
      (g : Matrix n n 𝕜) := by
  obtain ⟨X, hX, rfl⟩ := Submodule.mem_map.mp hV
  -- The curve `t ↦ g exp (t X)` stays in `G` and has velocity `g X` at `t = 0`.
  have hγ := (hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul (g : Matrix n n 𝕜)
  simp only [zero_smul, exp_zero, one_mul] at hγ
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), (g : Matrix n n 𝕜) * exp (t • X) ∈
      ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G := by
    refine Eventually.of_forall fun t ↦ ?_
    obtain ⟨h, hh, hht⟩ := mem_matrixLieAlgebra_iff.mp ((LieSubalgebra.mem_toSubmodule _).mp hX) t
    exact ⟨g * h, mul_mem g.property hh, by simp [hht]⟩
  have h : (g : Matrix n n 𝕜) * X ∈ posTangentConeAt
      (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
      ((g : Matrix n n 𝕜) * exp ((0 : ℝ) • X)) :=
    hγ.hasDerivWithinAt.mem_posTangentConeAt hmem.frequently
  simpa using h

/-- **The tangent space of a closed subgroup of `U(n)`.** The tangent cone of `G` at `g ∈ G`, as a
set of matrices, is the subspace `g 𝔤`. -/
theorem tangentConeAt_eq_matrixTangentSpace (g : G) :
    tangentConeAt ℝ (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G) (g : Matrix n n 𝕜) =
      G.matrixTangentSpace g := by
  refine Subset.antisymm (fun V hV ↦ ?_) (fun V hV ↦ ?_)
  · rw [SetLike.mem_coe, mem_matrixTangentSpace_iff]
    -- Left multiplication by `g⁻¹ = star g` maps `G` into itself and `g` to `1`. It is the
    -- continuous linear map `ContinuousLinearMap.mul ℝ _ (star g)` for the scoped operator norm,
    -- whose topology and module structure are those of the matrices up to definitional unfolding.
    have h : star (g : Matrix n n 𝕜) * V ∈ tangentConeAt ℝ
        ((star (g : Matrix n n 𝕜) * ·) '' (((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G))
        (star (g : Matrix n n 𝕜) * g) :=
      ((ContinuousLinearMap.mul ℝ (Matrix n n 𝕜)) (star (g : Matrix n n 𝕜))).hasFDerivAt
        |>.hasFDerivWithinAt.mapsTo_tangent_cone hV
    rw [Matrix.UnitaryGroup.star_mul_self] at h
    refine tangentConeAt_one_subset (tangentConeAt_mono ?_ h)
    rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨g⁻¹ * h, mul_mem (inv_mem g.property) hh, by simp⟩
  · exact tangentConeAt_mono_field (mem_posTangentConeAt_of_mem_matrixTangentSpace hV)

/-- **The derivative of a `G`-valued map lies in the tangent space.** If `O` takes values in `G`
near `x`, then every directional derivative `∂ᵥO(x)` lies in the tangent space `g 𝔤` of `G` at
`g = O x`. No differentiability is assumed: where `O` is not differentiable, `fderiv` is `0`. -/
theorem fderiv_apply_mem_matrixTangentSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : E → Matrix n n 𝕜} {x : E} {g : G}
    (hO : ∀ᶠ y in 𝓝 x, O y ∈ ((↑) : Matrix.unitaryGroup n 𝕜 → Matrix n n 𝕜) '' G)
    (hOx : O x = g) (v : E) : fderiv ℝ O x v ∈ G.matrixTangentSpace g := by
  by_cases hd : DifferentiableAt ℝ O x
  · rw [← SetLike.mem_coe, ← tangentConeAt_eq_matrixTangentSpace, ← hOx]
    refine tangentConeAt_mono (image_preimage_subset O _) ?_
    exact hd.hasFDerivAt.hasFDerivWithinAt.mapsTo_tangent_cone
      (by rw [tangentConeAt_of_mem_nhds (show O ⁻¹' _ ∈ 𝓝 x from hO)]; trivial)
  · rw [fderiv_zero_of_not_differentiableAt hd]
    exact zero_mem _

end TangentCone

end ClosedSubgroup
