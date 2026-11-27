/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.GlobalParametric
public import TauCeti.Analysis.Fredholm.LevelSet.Parametric

/-!
# Checks for universal zero sets and the parameter projection

A parametrized equation `s (x, p) = 0`, for an unknown `x` and a parameter `p`, has a universal
zero set `{(x, p) | s (x, p) = 0}` and a projection from it to the parameter space. At a solution
where the total derivative `D₁.coprod D₂` is onto, the regular-level-set chart turns this
projection into the local map `TauCeti.levelSetParameterMap`, whose derivative at the chart origin
is the linear parameter projection `ContinuousLinearMap.parameterProj D₁ D₂`
(`TauCeti.fderiv_levelSetParameterMap`). A parameter is regular
(`TauCeti.IsRegularParameter`) when the fixed-parameter derivative `D₁` is onto at every solution
over it, and the regular parameters form a residual set when `s` is sufficiently smooth, the
fixed-parameter derivative is Fredholm, and the total derivative is onto at every solution
(`TauCeti.mem_residual_setOf_isRegularParameter`).

This file computes these objects for three equations `s : ℝ × ℝ → ℝ`.

* **`s (x, p) = x - p`.** The zero set is the diagonal `x = p`. The total derivative is
  `(ξ, π) ↦ ξ - π`, with `D₁ = 1`, so the projection has derivative `1` along the diagonal: it is
  bijective, of index `0` with zero kernel, and every parameter is regular.
* **`s (x, p) = p`.** The zero set is the axis `p = 0`, and the total derivative `(ξ, π) ↦ π` is
  onto, but `D₁ = 0`. The projection is constant on the zero set: its derivative has kernel and
  cokernel of dimension `1`, hence index `0`, and it is not onto. Accordingly `p` is regular
  exactly when `p ≠ 0`, where there are no solutions at all, and these parameters form a residual
  set, as the parametric transversality theorem predicts.
* **`s (x, p) = 0`.** The total derivative vanishes, so it is not onto, and the zero set is the
  whole plane: its tangent space has dimension `2`, while the index of the total derivative, the
  dimension of the zero set of a regular equation, is `1`. No parameter is regular, so the set of
  regular parameters is empty and not residual: the surjectivity of the total derivative cannot
  be dropped from the parametric transversality theorem.

The index of an operator between finite-dimensional spaces is the difference of their dimensions
(`ContinuousLinearMap.index_eq_of_finiteDimensional`), so for the two equations `x - p` and `p`,
whose total derivative is onto, the derivative of the projection has index `0`; these two cases
differ in kernel and cokernel. For `0`, the total derivative is not onto, so the regular-level-set
chart and its projection are not available.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.3 (universal zero sets and the parameter
  projection).
-/

public section

open Function Module Set ContinuousLinearMap

namespace TauCeti.ParameterProjectionExample

/-! ### The equation `x - p = 0` -/

/-- The universal zero set of `s (x, p) = x - p` is the diagonal `x = p`. -/
theorem setOf_fst_sub_snd_eq_zero : {z : ℝ × ℝ | z.1 - z.2 = 0} = {z | z.1 = z.2} := by
  ext z
  simp [sub_eq_zero]

/-- The total derivative of `s (x, p) = x - p` is `(ξ, π) ↦ ξ - π`: its fixed-parameter part is
`1` and its parameter part is `-1`. -/
theorem hasStrictFDerivAt_fst_sub_snd (z : ℝ × ℝ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ ↦ z.1 - z.2)
      ((1 : ℝ →L[ℝ] ℝ).coprod (-1 : ℝ →L[ℝ] ℝ)) z := by
  have h : (fun z : ℝ × ℝ ↦ z.1 - z.2) = ⇑((1 : ℝ →L[ℝ] ℝ).coprod (-1 : ℝ →L[ℝ] ℝ)) := by
    funext z
    simp [sub_eq_add_neg]
  rw [h]
  exact ((1 : ℝ →L[ℝ] ℝ).coprod (-1 : ℝ →L[ℝ] ℝ)).hasStrictFDerivAt

/-- The total derivative of `s (x, p) = x - p` is onto. -/
theorem surjective_one_coprod_neg_one : Surjective ((1 : ℝ →L[ℝ] ℝ).coprod (-1 : ℝ →L[ℝ] ℝ)) :=
  fun y ↦ ⟨(y, 0), by simp⟩

/-- The local projection to the parameter from the universal zero set of `x - p`, in the
regular-level-set chart at the solution `(a, a)`. -/
noncomputable abbrev diagonalParameterMap (a : ℝ) :
    ((1 : ℝ →L[ℝ] ℝ).coprod (-1 : ℝ →L[ℝ] ℝ)).ker → ℝ :=
  levelSetParameterMap (hasStrictFDerivAt_fst_sub_snd (a, a)) surjective_one_coprod_neg_one
    (Submodule.ClosedComplemented.of_finiteDimensional _) (sub_self a)

/-- The tangent line `(1, 1)` of the diagonal lies in the kernel of the total derivative of
`x - p`. -/
theorem one_one_mem_ker :
    ((1 : ℝ), (1 : ℝ)) ∈ ((1 : ℝ →L[ℝ] ℝ).coprod (-1 : ℝ →L[ℝ] ℝ)).ker := by
  simp

/-- **The projection from the diagonal has derivative `1`**: at every solution `(a, a)` of
`x - p = 0`, the derivative of the local parameter map sends the tangent vector `(1, 1)` of the
diagonal to `1`. -/
theorem fderiv_diagonalParameterMap_apply (a : ℝ) :
    fderiv ℝ (diagonalParameterMap a) 0 ⟨(1, 1), one_one_mem_ker⟩ = 1 := by
  rw [fderiv_levelSetParameterMap, parameterProj_apply]

/-- The derivative of the projection from the diagonal is bijective. -/
theorem bijective_fderiv_diagonalParameterMap (a : ℝ) :
    Bijective (fderiv ℝ (diagonalParameterMap a) 0) := by
  rw [fderiv_levelSetParameterMap]
  refine ⟨fun v w h ↦ ?_, parameterProj_surjective_of_surjective _ _ fun y ↦ ⟨y, rfl⟩⟩
  obtain ⟨⟨x, p⟩, hv⟩ := v
  obtain ⟨⟨y, q⟩, hw⟩ := w
  simp only [parameterProj_apply] at h
  simp only [LinearMap.mem_ker, coe_coe, coprod_apply, neg_apply,
    one_apply_eq_self] at hv hw
  ext <;> simp only <;> linarith

/-- The derivative of the projection from the diagonal has zero kernel. -/
theorem finrank_ker_fderiv_diagonalParameterMap (a : ℝ) :
    finrank ℝ (fderiv ℝ (diagonalParameterMap a) 0).ker = 0 := by
  rw [LinearMap.ker_eq_bot_of_injective (bijective_fderiv_diagonalParameterMap a).injective]
  exact finrank_bot ℝ _

/-- The derivative of the projection from the diagonal has index `0`. -/
theorem index_fderiv_diagonalParameterMap (a : ℝ) :
    (fderiv ℝ (diagonalParameterMap a) 0).index = 0 :=
  index_eq_zero_of_bijective _ (bijective_fderiv_diagonalParameterMap a)

/-- Every parameter of `x - p = 0` is regular. -/
theorem isRegularParameter_fst_sub_snd (p : ℝ) :
    IsRegularParameter (fun z : ℝ × ℝ ↦ z.1 - z.2) 0 p := isRegularParameter_iff.2 fun x _ ↦ by
  rw [(hasStrictFDerivAt_fst_sub_snd (x, p)).hasFDerivAt.fderiv, coprod_comp_inl]
  exact fun y ↦ ⟨y, rfl⟩

/-! ### The equation `p = 0` -/

/-- The universal zero set of `s (x, p) = p` is the axis `p = 0`. -/
theorem setOf_snd_eq_zero : {z : ℝ × ℝ | z.2 = 0} = range fun x : ℝ ↦ (x, (0 : ℝ)) := by
  ext ⟨x, p⟩
  simp [eq_comm]

/-- The total derivative of `s (x, p) = p` is `(ξ, π) ↦ π`: its fixed-parameter part is `0` and
its parameter part is `1`. -/
theorem hasStrictFDerivAt_snd (z : ℝ × ℝ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ ↦ z.2) ((0 : ℝ →L[ℝ] ℝ).coprod (1 : ℝ →L[ℝ] ℝ)) z := by
  have h : (fun z : ℝ × ℝ ↦ z.2) = ⇑((0 : ℝ →L[ℝ] ℝ).coprod (1 : ℝ →L[ℝ] ℝ)) := by
    funext z
    simp
  rw [h]
  exact ((0 : ℝ →L[ℝ] ℝ).coprod (1 : ℝ →L[ℝ] ℝ)).hasStrictFDerivAt

/-- The total derivative of `s (x, p) = p` is onto. -/
theorem surjective_zero_coprod_one : Surjective ((0 : ℝ →L[ℝ] ℝ).coprod (1 : ℝ →L[ℝ] ℝ)) :=
  fun y ↦ ⟨(0, y), by simp⟩

/-- The local projection to the parameter from the universal zero set of `p`, in the
regular-level-set chart at the solution `(a, 0)`. -/
noncomputable abbrev axisParameterMap (a : ℝ) : ((0 : ℝ →L[ℝ] ℝ).coprod (1 : ℝ →L[ℝ] ℝ)).ker → ℝ :=
  levelSetParameterMap (hasStrictFDerivAt_snd (a, 0)) surjective_zero_coprod_one
    (Submodule.ClosedComplemented.of_finiteDimensional _) rfl

/-- The zero map `ℝ → ℝ` is not onto. -/
private theorem not_surjective_zero : ¬ Surjective (0 : ℝ →L[ℝ] ℝ) := fun h ↦ by
  obtain ⟨x, hx⟩ := h 1
  simp at hx

/-- **The projection from the axis is not onto at the derivative level**: at every solution
`(a, 0)` of `p = 0`, the derivative of the local parameter map is not onto, although the total
derivative is. -/
theorem not_surjective_fderiv_axisParameterMap (a : ℝ) :
    ¬ Surjective (fderiv ℝ (axisParameterMap a) 0) := by
  rw [surjective_fderiv_levelSetParameterMap_iff]
  exact not_surjective_zero

/-- The derivative of the projection from the axis has a kernel of dimension `1`, the tangent line
of the axis. -/
theorem finrank_ker_fderiv_axisParameterMap (a : ℝ) :
    finrank ℝ (fderiv ℝ (axisParameterMap a) 0).ker = 1 := by
  rw [fderiv_levelSetParameterMap, finrank_ker_parameterProj, toLinearMap_zero,
    LinearMap.ker_zero]
  simp

/-- The derivative of the projection from the axis has a cokernel of dimension `1`. -/
theorem finrank_quotient_range_fderiv_axisParameterMap (a : ℝ) :
    finrank ℝ (ℝ ⧸ (fderiv ℝ (axisParameterMap a) 0).range) = 1 := by
  rw [fderiv_levelSetParameterMap,
    finrank_quotient_range_parameterProj _ _ surjective_zero_coprod_one, toLinearMap_zero,
    LinearMap.range_zero, (Submodule.quotEquivOfEqBot _ rfl).finrank_eq]
  simp

/-- The derivative of the projection from the axis has index `0`, although it is not onto. -/
theorem index_fderiv_axisParameterMap (a : ℝ) :
    (fderiv ℝ (axisParameterMap a) 0).index = 0 := by
  rw [index_fderiv_levelSetParameterMap, index_zero]
  simp

/-- A parameter of `p = 0` is regular exactly when it is nonzero: over `0` every point is a
solution, with fixed-parameter derivative `0`, and over a nonzero parameter there is no
solution. -/
theorem isRegularParameter_snd_iff {p : ℝ} :
    IsRegularParameter (fun z : ℝ × ℝ ↦ z.2) 0 p ↔ p ≠ 0 := by
  refine ⟨fun h hp ↦ ?_, fun hp ↦ isRegularParameter_iff.2 fun x hx ↦ absurd hx hp⟩
  subst hp
  have h0 := isRegularParameter_iff.1 h 0 rfl
  rw [(hasStrictFDerivAt_snd (0, 0)).hasFDerivAt.fderiv, coprod_comp_inl] at h0
  exact not_surjective_zero h0

/-- The regular parameters of `p = 0` are the nonzero reals. -/
theorem setOf_isRegularParameter_snd :
    {p | IsRegularParameter (fun z : ℝ × ℝ ↦ z.2) 0 p} = {0}ᶜ := by
  ext p
  simp [isRegularParameter_snd_iff]

/-- The parametric transversality theorem applies to `p = 0`: the total derivative is onto, and
the fixed-parameter derivative `0 : ℝ → ℝ` is Fredholm of index `0`. Its conclusion, that the
regular parameters form a residual set, is the residual set `{0}ᶜ`. -/
theorem mem_residual_setOf_isRegularParameter_snd :
    {p | IsRegularParameter (fun z : ℝ × ℝ ↦ z.2) 0 p} ∈ residual ℝ := by
  refine mem_residual_setOf_isRegularParameter (n := 1) (fun z _ ↦ contDiffAt_snd)
    (fun _ _ ↦ isFredholm_of_finiteDimensional _) (fun z _ ↦ ?_) (fun _ _ ↦ ?_)
  · rw [(hasStrictFDerivAt_snd z).hasFDerivAt.fderiv]
    exact surjective_zero_coprod_one
  · rw [index_eq_of_finiteDimensional]
    simp

/-! ### The equation `0 = 0` -/

/-- The total derivative of `s (x, p) = 0` is not onto. -/
theorem not_surjective_fderiv_zero (z : ℝ × ℝ) :
    ¬ Surjective (fderiv ℝ (fun _ : ℝ × ℝ ↦ (0 : ℝ)) z) := fun h ↦ by
  obtain ⟨v, hv⟩ := h 1
  simp at hv

/-- The kernel of the total derivative of `s (x, p) = 0` has dimension `2`: it is the tangent
space of the zero set, which is the whole plane. -/
theorem finrank_ker_fderiv_zero (z : ℝ × ℝ) :
    finrank ℝ (fderiv ℝ (fun _ : ℝ × ℝ ↦ (0 : ℝ)) z).ker = 2 := by
  rw [fderiv_const_apply, toLinearMap_zero, LinearMap.ker_zero]
  simp

/-- The index of the total derivative of `s (x, p) = 0`, the expected dimension of its zero set,
is `1`, while the zero set has dimension `2` (`finrank_ker_fderiv_zero`). -/
theorem index_fderiv_zero (z : ℝ × ℝ) :
    (fderiv ℝ (fun _ : ℝ × ℝ ↦ (0 : ℝ)) z).index = 1 := by
  rw [index_eq_of_finiteDimensional]
  simp

/-- No parameter of `s (x, p) = 0` is regular: every `x` is a solution, with fixed-parameter
derivative `0`. -/
theorem not_isRegularParameter_zero (p : ℝ) :
    ¬ IsRegularParameter (fun _ : ℝ × ℝ ↦ (0 : ℝ)) 0 p := fun h ↦ by
  have h0 := isRegularParameter_iff.1 h 0 rfl
  rw [fderiv_const_apply, zero_comp] at h0
  exact not_surjective_zero h0

/-- **The total derivative must be onto in the parametric transversality theorem.** The equation
`s (x, p) = 0` is smooth, and its fixed-parameter derivative `0 : ℝ → ℝ` is Fredholm of index `0`,
as for `s (x, p) = p`, but its total derivative is not onto (`not_surjective_fderiv_zero`). The
conclusion of `TauCeti.mem_residual_setOf_isRegularParameter` fails for it: the set of regular
parameters is empty, so it is not residual. -/
theorem setOf_isRegularParameter_zero_notMem_residual :
    {p | IsRegularParameter (fun _ : ℝ × ℝ ↦ (0 : ℝ)) 0 p} ∉ residual ℝ := fun h ↦ by
  obtain ⟨p, hp⟩ := (dense_of_mem_residual h).nonempty
  exact not_isRegularParameter_zero p hp

end TauCeti.ParameterProjectionExample
