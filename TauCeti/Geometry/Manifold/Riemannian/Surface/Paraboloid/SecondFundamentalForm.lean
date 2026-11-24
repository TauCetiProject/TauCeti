/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Paraboloid.Basic
public import TauCeti.Analysis.InnerProductSpace.SecondFundamentalForm

/-!
# The Cartesian second fundamental form of the paraboloid

The upward normal `N=(-2x₀,-2x₁,1)` has squared length `1+4‖x‖²`. The graph Hessian is
`2⟪u,v⟫ e₂`, hence its normal projection is `2⟪u,v⟫/(1+4‖x‖²) N`.
These formulas hold also at the vertex.
-/

public noncomputable section

open scoped ContDiff InnerProductSpace

namespace TauCeti.Manifold.Paraboloid

local notation "V₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The upward, unnormalized normal to the Cartesian graph. -/
def normal (x : V₂) : E₃ :=
  (-2 * x 0) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
    (-2 * x 1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
    EuclideanSpace.basisFun (Fin 3) ℝ 2

/-- The three Cartesian coordinates of the upward graph normal. -/
theorem normal_def (x : V₂) : normal x =
    (-2 * x 0) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      (-2 * x 1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
      EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  rfl

/-- The normal has squared length `1+4‖x‖²`, and is therefore never zero. -/
theorem inner_normal_self (x : V₂) : inner ℝ (normal x) (normal x) = 1 + 4 * ‖x‖ ^ 2 := by
  simp only [normal, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  norm_num
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  ring

/-- The normal is orthogonal to every graph tangent. -/
theorem inner_normal_fderiv (x w : V₂) :
    inner ℝ (normal x) (fderiv ℝ paraboloidGraph x w) = 0 := by
  simp only [normal, inner_add_left, real_inner_smul_left, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left, fderiv_paraboloidGraph_apply_zero,
    fderiv_paraboloidGraph_apply_one, fderiv_paraboloidGraph_apply_two]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  ring

/-- The upward normal belongs to the native orthogonal complement of the differential. -/
theorem normal_mem_orthogonal (x : V₂) : normal x ∈ (fderiv ℝ paraboloidGraph x).rangeᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨w, rfl⟩
  rw [real_inner_comm]
  exact inner_normal_fderiv x w

/-- The Cartesian graph Hessian is the constant height Hessian `2⟪u,v⟫ e₂`. -/
theorem fderiv_fderiv_graph (x w z : V₂) :
    fderiv ℝ (fderiv ℝ paraboloidGraph) x w z =
      (2 * inner ℝ w z) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  have hf : ContDiffAt ℝ 2 paraboloidGraph x := contDiff_paraboloidGraph.contDiffAt
  have hi := (hasFDerivAt_id (𝕜 := ℝ) x).inner ℝ (hasFDerivAt_const z x)
  have hi₂ := (hi.const_mul 2).smul_const (EuclideanSpace.basisFun (Fin 3) ℝ 2)
  have hz := hi₂.const_add (LinearIsometry.piLpExtendByZero 2 ℝ ℝ
    (Fin.castLEEmb (by decide : 2 ≤ 3)) z)
  have hd := hz.congr_of_eventuallyEq (f₁ := fun y ↦ fderiv ℝ paraboloidGraph y z)
    (.of_forall fun y ↦ fderiv_paraboloidGraph_apply y z)
  have ha := hf.hasFDerivAt_fderiv_apply (by norm_num) z
  have h := congrArg (fun L ↦ L w) (ha.fderiv.symm.trans hd.fderiv)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, zero_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, inner_zero_right, zero_add] at h
  exact h

/-- Pairing with the graph normal recovers the ordinary height Hessian. -/
theorem inner_normal_secondFundamentalForm (x w z : V₂) :
    inner ℝ (normal x) (TauCeti.secondFundamentalForm ℝ paraboloidGraph x w z) =
      2 * inner ℝ w z := by
  rw [TauCeti.inner_secondFundamentalForm_apply_of_mem_orthogonal
    (normal_mem_orthogonal x), fderiv_fderiv_graph]
  simp only [normal, inner_add_left, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  norm_num

/-- The upward normal spans the whole graph normal space at every Cartesian point. -/
theorem orthogonal_range_fderiv_eq_span_normal (x : V₂) :
    (fderiv ℝ paraboloidGraph x).rangeᗮ = Submodule.span ℝ {normal x} := by
  have hn : normal x ≠ 0 := by
    intro h
    have hi := inner_normal_self x
    rw [h, inner_zero_left] at hi
    nlinarith [sq_nonneg ‖x‖]
  symm
  apply Submodule.eq_of_le_of_finrank_eq
    (Submodule.span_le.mpr (by simpa using normal_mem_orthogonal x))
  have hdim := (fderiv ℝ paraboloidGraph x).range.finrank_add_finrank_orthogonal
  have hrank := LinearMap.finrank_range_of_inj (fderiv_paraboloidGraph_injective x)
  rw [finrank_span_singleton hn]
  norm_num at hdim hrank
  omega

/-- The actual orthogonal-projected Hessian of the graph, valid also at the vertex. -/
theorem secondFundamentalForm_graph (x w z : V₂) :
    TauCeti.secondFundamentalForm ℝ paraboloidGraph x w z =
      (2 * inner ℝ w z / (1 + 4 * ‖x‖ ^ 2)) • normal x := by
  have hm := TauCeti.secondFundamentalForm_apply_mem_orthogonal (𝕜 := ℝ) paraboloidGraph x w z
  rw [orthogonal_range_fderiv_eq_span_normal] at hm
  have hp := Submodule.starProjection_eq_self_iff.mpr hm
  rw [Submodule.starProjection_singleton, ← real_inner_self_eq_norm_sq,
    inner_normal_self, inner_normal_secondFundamentalForm] at hp
  exact hp.symm

end TauCeti.Manifold.Paraboloid
