/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Linearization
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Morse.Index
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The height function on the unit sphere is a Morse function

The height function `x ↦ ⟪x, v⟫` on the unit sphere of an `(n + 1)`-dimensional real inner product
space, for a unit vector `v`, is the standard first example of a Morse function: it is smooth, its
only critical points are the north pole `v` and the south pole `-v`, and these are nondegenerate,
of Morse index `n` and `0` respectively. Morse homology reads the homology of the sphere off this
function, one generator in degree `0` and one in degree `n`, so it is the first test case for a
Morse complex.

The manifold structure on the sphere is Mathlib's, charted by stereographic projection. In the
chart centred at the north pole `v`, which projects from `-v`, the height function is the explicit
rational function `stereographicHeight w = (4 - ‖w‖ ^ 2) / (‖w‖ ^ 2 + 4)` of the chart coordinate
`w`. Its Hessian at the origin is minus the inner product, which is what makes `v` a nondegenerate
critical point of index `n`. The chart centred at `-v` sees the negative of the same function, so
the south pole is a nondegenerate critical point of index `0`. The critical points are located
through the manifold derivative: the differential of the height function at `x` is the inner
product with `v` restricted to the tangent space `(ℝ ∙ x)ᗮ`, which vanishes exactly when `v` is a
multiple of `x`.

## Main declarations

* `TauCeti.stereographicHeight`: the height function in the stereographic chart at the north pole,
  with `TauCeti.isNondegenerateCriticalPoint_stereographicHeight_zero` and
  `TauCeti.morseIndex_stereographicHeight_zero` computing its Morse data at the origin.
* `TauCeti.sphereHeight`: the height function on the unit sphere in the direction of a unit vector.
* `TauCeti.sphereHeight_comp_extChartAt_symm`: in the preferred chart at the north pole it is
  `stereographicHeight`.
* `TauCeti.mvfderiv_sphereHeight_eq_zero_iff` and `TauCeti.mfderiv_sphereHeight_eq_zero_iff`: its
  critical points are the two poles.
* `TauCeti.sphereHeight_lt_self` and `TauCeti.sphereHeight_neg_lt`: the north pole is its strict
  global maximum and the south pole its strict global minimum.
* `TauCeti.isMorse_sphereHeight`: the height function is a Morse function.
* `TauCeti.manifoldMorseIndex_sphereHeight_self` and
  `TauCeti.manifoldMorseIndex_sphereHeight_neg`: the north pole has index `n` and the south pole
  has index `0`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Function Metric Module Set
open scoped ContDiff Gradient InnerProductSpace Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

/-! ### The height function in the stereographic chart -/

section Model

variable {F : Type*} [NormedAddCommGroup F]

/-- The height function of the unit sphere, read in the stereographic chart centred at the north
pole: the point with chart coordinate `w` has height `(4 - ‖w‖ ^ 2) / (‖w‖ ^ 2 + 4)`. -/
def stereographicHeight (w : F) : ℝ :=
  (4 - ‖w‖ ^ 2) / (‖w‖ ^ 2 + 4)

@[simp]
theorem stereographicHeight_apply (w : F) :
    stereographicHeight w = (4 - ‖w‖ ^ 2) / (‖w‖ ^ 2 + 4) :=
  (rfl)

variable [InnerProductSpace ℝ F]

/-- The chart height function is smooth. -/
theorem contDiff_stereographicHeight {n : WithTop ℕ∞} :
    ContDiff ℝ n (stereographicHeight (F := F)) :=
  ContDiff.div (contDiff_const.sub (contDiff_norm_sq ℝ)) ((contDiff_norm_sq ℝ).add contDiff_const)
    fun _ ↦ by positivity

/-- The derivative of the chart height function. -/
theorem hasFDerivAt_stereographicHeight (w : F) :
    HasFDerivAt stereographicHeight ((-16 / (‖w‖ ^ 2 + 4) ^ 2) • innerSL ℝ w) w := by
  have hq : HasFDerivAt (fun x : F ↦ ‖x‖ ^ 2) (2 • innerSL ℝ w) w :=
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h4 : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  have hg : HasDerivAt (fun s : ℝ ↦ (4 - s) / (s + 4)) (-8 / (‖w‖ ^ 2 + 4) ^ 2) (‖w‖ ^ 2) := by
    refine (((hasDerivAt_id (‖w‖ ^ 2)).const_sub 4).div ((hasDerivAt_id (‖w‖ ^ 2)).add_const 4)
      h4).congr_deriv ?_
    simp only [id]
    ring
  refine (hg.comp_hasFDerivAt w hq).congr_fderiv ?_
  ext y
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, two_smul, add_apply]
  ring

/-- The Fréchet derivative of the chart height function at `w` is `-16 / (‖w‖ ^ 2 + 4) ^ 2` times
the inner product with `w`. -/
theorem fderiv_stereographicHeight (w : F) :
    fderiv ℝ stereographicHeight w = (-16 / (‖w‖ ^ 2 + 4) ^ 2) • innerSL ℝ w :=
  (hasFDerivAt_stereographicHeight w).fderiv

variable [CompleteSpace F]

/-- The gradient of the chart height function. -/
theorem hasGradientAt_stereographicHeight (w : F) :
    HasGradientAt stereographicHeight ((-16 / (‖w‖ ^ 2 + 4) ^ 2) • w) w := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hasFDerivAt_stereographicHeight w).congr_fderiv ?_
  ext y
  simp

/-- The gradient of the chart height function at `w` is `-16 / (‖w‖ ^ 2 + 4) ^ 2` times `w`. -/
theorem gradient_stereographicHeight (w : F) :
    ∇ stereographicHeight w = (-16 / (‖w‖ ^ 2 + 4) ^ 2) • w :=
  (hasGradientAt_stereographicHeight w).gradient

/-- The origin is a critical point of the chart height function. -/
@[simp]
theorem gradient_stereographicHeight_zero : ∇ stereographicHeight (0 : F) = 0 := by
  simp [gradient_stereographicHeight]

/-- The Hessian of the chart height function at the origin is minus the identity. -/
theorem hasFDerivAt_gradient_stereographicHeight_zero :
    HasFDerivAt (∇ stereographicHeight) (-ContinuousLinearMap.id ℝ F) (0 : F) := by
  have hfun : ∇ stereographicHeight = fun w : F ↦ (-16 * ((‖w‖ ^ 2 + 4) ^ 2)⁻¹) • w :=
    funext fun w ↦ by rw [gradient_stereographicHeight, div_eq_mul_inv]
  have hd : DifferentiableAt ℝ (fun w : F ↦ (‖w‖ ^ 2 + 4) ^ 2) 0 :=
    ((((contDiff_norm_sq ℝ (E := F) (n := 1)).differentiable one_ne_zero) 0).add_const 4).pow 2
  have hc : DifferentiableAt ℝ (fun w : F ↦ -16 * ((‖w‖ ^ 2 + 4) ^ 2)⁻¹) 0 :=
    (hd.inv (by norm_num)).const_mul (-16)
  rw [hfun]
  refine (hc.hasFDerivAt.smul (hasFDerivAt_id (𝕜 := ℝ) (0 : F))).congr_fderiv ?_
  ext y
  norm_num

/-- The Hessian operator of the chart height function at the origin is minus the identity. -/
theorem hessianOperator_stereographicHeight_zero :
    hessianOperator stereographicHeight (0 : F) = -ContinuousLinearMap.id ℝ F :=
  (ContDiffAt.hasFDerivAt_gradient contDiff_stereographicHeight.contDiffAt).unique
    hasFDerivAt_gradient_stereographicHeight_zero

/-- The Hessian quadratic form of the chart height function at the origin is minus the squared
norm. -/
theorem hessianQuadraticForm_stereographicHeight_zero (w : F) :
    hessianQuadraticForm stereographicHeight 0 w = -‖w‖ ^ 2 := by
  rw [hessianQuadraticForm_apply, ← inner_hessianOperator_left,
    hessianOperator_stereographicHeight_zero]
  simp

/-- The origin is a nondegenerate critical point of the chart height function. -/
theorem isNondegenerateCriticalPoint_stereographicHeight_zero :
    IsNondegenerateCriticalPoint stereographicHeight (0 : F) := by
  rw [isNondegenerateCriticalPoint_iff_gradient, hessianOperator_stereographicHeight_zero]
  refine ⟨contDiff_stereographicHeight.contDiffAt, gradient_stereographicHeight_zero, ?_⟩
  have h : -ContinuousLinearMap.id ℝ F = (ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F) := by
    ext y
    simp
  rw [h]
  exact ContinuousLinearMap.isInvertible_equiv

omit [CompleteSpace F] in
/-- The Morse index of the chart height function at the origin is the dimension of the chart
space. -/
theorem morseIndex_stereographicHeight_zero [FiniteDimensional ℝ F] :
    morseIndex stereographicHeight (0 : F) = finrank ℝ F := by
  have := FiniteDimensional.complete ℝ F
  have h := isNondegenerateCriticalPoint_stereographicHeight_zero (F := F)
  rw [← h.neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank]
  intro w hw
  rw [neg_apply, hessianQuadraticForm_stereographicHeight_zero, neg_neg]
  positivity

end Model

/-! ### The height function on the sphere -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The **height function** on the unit sphere in the direction of the unit vector `v`: the inner
product with `v`. It is the standard Morse function on the sphere, with the poles `v` and `-v` as
its only critical points. -/
def sphereHeight (v x : sphere (0 : E) 1) : ℝ :=
  ⟪(x : E), (v : E)⟫

@[simp]
theorem sphereHeight_apply (v x : sphere (0 : E) 1) : sphereHeight v x = ⟪(x : E), (v : E)⟫ :=
  (rfl)

/-- The height function is the inner product with `v` composed with the inclusion of the sphere. -/
theorem sphereHeight_eq_innerSL_comp (v : sphere (0 : E) 1) :
    sphereHeight v = innerSL ℝ (v : E) ∘ ((↑) : sphere (0 : E) 1 → E) := by
  funext x
  simp [real_inner_comm]

/-- Reversing the direction negates the height function. -/
@[simp]
theorem sphereHeight_neg (v : sphere (0 : E) 1) : sphereHeight (-v) = -sphereHeight v := by
  funext x
  simp

/-- The height function is smooth. -/
theorem contMDiff_sphereHeight {m : WithTop ℕ∞} (v : sphere (0 : E) 1) :
    ContMDiff (𝓡 n) 𝓘(ℝ) m (sphereHeight v) := by
  rw [sphereHeight_eq_innerSL_comp]
  exact (innerSL ℝ (v : E)).contMDiff.comp contMDiff_coe_sphere

/-- The critical points of the height function are exactly the north and south poles. -/
@[simp]
theorem mvfderiv_sphereHeight_eq_zero_iff (v x : sphere (0 : E) 1) :
    mvfderiv (𝓡 n) (sphereHeight v) x = 0 ↔ x = v ∨ x = -v := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hcoe : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    (contMDiff_coe_sphere (m := 1) (n := n) x).mdifferentiableAt one_ne_zero
  -- The differential is the inner product with `v` composed with the differential of the
  -- inclusion, whose range is `(ℝ ∙ x)ᗮ`; it vanishes exactly when `v ∈ (ℝ ∙ x)ᗮᗮ = ℝ ∙ x`.
  rw [sphereHeight_eq_innerSL_comp,
    mvfderiv_comp x (((innerSL ℝ (v : E)).contMDiffAt (n := 1)).mdifferentiableAt one_ne_zero)
      hcoe, mvfderiv_eq_fderiv,
    ContinuousLinearMap.fderiv, eq_comm (a := x) (b := v), eq_comm (a := x) (b := -v),
    neg_eq_iff_eq_neg, ← coe_mem_span_singleton_iff one_ne_zero (x := v) (p := x),
    ← Submodule.orthogonal_orthogonal (ℝ ∙ (x : E)), ← range_mvfderiv_subtypeVal (n := n) x,
    Submodule.mem_orthogonal']
  simp only [mvfderiv, ContinuousLinearMap.comp_assoc, LinearMap.mem_range,
    ContinuousLinearMap.coe_coe, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro h u
    simpa using congrArg (fun L ↦ L u) h
  · intro h
    ext u
    simpa using h u

/-- The critical points of the height function, stated with `mfderiv`, are the two poles. -/
theorem mfderiv_sphereHeight_eq_zero_iff (v x : sphere (0 : E) 1) :
    mfderiv (𝓡 n) 𝓘(ℝ) (sphereHeight v) x = 0 ↔ x = v ∨ x = -v := by
  rw [← mvfderiv_eq_zero_iff, mvfderiv_sphereHeight_eq_zero_iff]

/-- The north pole is the strict global maximum of the height function. -/
theorem sphereHeight_lt_self {v x : sphere (0 : E) 1} (hx : x ≠ v) :
    sphereHeight v x < sphereHeight v v := by
  have hvn : ‖(v : E)‖ = 1 := norm_eq_of_mem_sphere v
  simpa [real_inner_self_eq_norm_sq, hvn] using
    (inner_lt_one_iff_real_of_norm_eq_one (norm_eq_of_mem_sphere x) hvn).2
      (Subtype.coe_injective.ne hx)

/-- The south pole is the strict global minimum of the height function. -/
theorem sphereHeight_neg_lt {v x : sphere (0 : E) 1} (hx : x ≠ -v) :
    sphereHeight v (-v) < sphereHeight v x := by
  simpa only [sphereHeight_neg, Pi.neg_apply, neg_lt_neg_iff] using
    sphereHeight_lt_self (v := -v) hx

/-- In the chart centred at the north pole `v`, the height function in the direction `v` is
`stereographicHeight`. -/
theorem sphereHeight_comp_chartAt_symm (v : sphere (0 : E) 1) :
    sphereHeight v ∘ (chartAt (EuclideanSpace ℝ (Fin n)) v).symm = stereographicHeight := by
  funext w
  simp only [comp_apply, sphereHeight_apply, stereographicHeight_apply, chartAt_sphere,
    stereographic'_symm_apply]
  set u : E := ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere (-v))).repr.symm w : E) with hu
  have hperp : ⟪u, (v : E)⟫ = 0 := by
    have := (Submodule.mem_orthogonal_singleton_iff_inner_left).1
      ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
        (ne_zero_of_mem_unit_sphere (-v))).repr.symm w).2
    rw [hu]
    simpa [coe_neg_sphere, inner_neg_right] using this
  have hnorm : ‖u‖ = ‖w‖ := by
    rw [hu, Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  have hv : ⟪(v : E), (v : E)⟫ = 1 := by
    simp [norm_eq_of_mem_sphere]
  have h4 : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  simp only [coe_neg_sphere, inner_add_left, inner_smul_left, inner_neg_left, hperp, hv, hnorm,
    RCLike.conj_to_real]
  field_simp
  ring

/-- In the preferred extended chart at the north pole `v`, the height function in the direction
`v` is `stereographicHeight`. -/
theorem sphereHeight_comp_extChartAt_symm (v : sphere (0 : E) 1) :
    sphereHeight v ∘ (extChartAt (𝓡 n) v).symm = stereographicHeight := by
  rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, comp_id, sphereHeight_comp_chartAt_symm]

/-- The north pole is a nondegenerate critical point of the height function. -/
theorem isManifoldNondegenerateCriticalPoint_sphereHeight_self (v : sphere (0 : E) 1) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) (sphereHeight v) v := by
  rw [isManifoldNondegenerateCriticalPoint_iff, sphereHeight_comp_extChartAt_symm,
    extChartAt_sphere_apply_self]
  exact isNondegenerateCriticalPoint_stereographicHeight_zero

/-- The south pole is a nondegenerate critical point of the height function. -/
theorem isManifoldNondegenerateCriticalPoint_sphereHeight_neg (v : sphere (0 : E) 1) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) (sphereHeight v) (-v) := by
  have h := (isManifoldNondegenerateCriticalPoint_sphereHeight_self (n := n) (-v)).neg
  rwa [sphereHeight_neg, neg_neg] at h

/-- **The height function on the sphere is a Morse function.** -/
theorem isMorse_sphereHeight (v : sphere (0 : E) 1) : IsMorse (𝓡 n) (sphereHeight v) := by
  refine isMorse_iff.2 ⟨contMDiff_sphereHeight v, fun x hx ↦ ?_⟩
  have hx' : mvfderiv (𝓡 n) (sphereHeight v) x = 0 := by
    rw [((contMDiff_sphereHeight (m := 1) v x).mdifferentiableAt one_ne_zero).mvfderiv,
      ModelWithCorners.range_eq_univ, fderivWithin_univ]
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp]
    -- The two sides differ only in presenting the domain as a tangent space rather than as
    -- `EuclideanSpace ℝ (Fin n)`.
    exact hx
  rcases (mvfderiv_sphereHeight_eq_zero_iff v x).1 hx' with rfl | rfl
  · exact isManifoldNondegenerateCriticalPoint_sphereHeight_self x
  · exact isManifoldNondegenerateCriticalPoint_sphereHeight_neg _

/-- The Morse index of the height function at the north pole is `n`. -/
@[simp]
theorem manifoldMorseIndex_sphereHeight_self (v : sphere (0 : E) 1) :
    manifoldMorseIndex (𝓡 n) (sphereHeight v) v = n := by
  rw [manifoldMorseIndex_def, sphereHeight_comp_extChartAt_symm, extChartAt_sphere_apply_self,
    morseIndex_stereographicHeight_zero, finrank_euclideanSpace_fin]

/-- The Morse index of the height function at the south pole is `0`. -/
@[simp]
theorem manifoldMorseIndex_sphereHeight_neg (v : sphere (0 : E) 1) :
    manifoldMorseIndex (𝓡 n) (sphereHeight v) (-v) = 0 := by
  have h := (isManifoldNondegenerateCriticalPoint_sphereHeight_self (n := n)
    (-v)).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  rw [manifoldMorseIndex_sphereHeight_self, sphereHeight_neg, neg_neg,
    finrank_euclideanSpace_fin] at h
  omega

end Sphere

end TauCeti

end
