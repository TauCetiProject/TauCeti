/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.SecondDerivative
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.Morse.Index

/-!
# The critical Hessian on a manifold

The Hessian of a real function `f` at a critical point `x` of a manifold is a symmetric bilinear
form on the tangent space `TangentSpace I x`. Here it is defined as the second derivative of the
coordinate expression of `f` in the preferred extended chart at `x`; the tangent space at `x` is
the model vector space, so this is a continuous bilinear map on `TangentSpace I x`.

Away from critical points this second derivative depends on the chart (on a Riemannian manifold,
on the connection), because the second-order chain rule carries a first-order term. At a critical
point that term vanishes. The central result of this file is that, on a boundaryless manifold,
the critical Hessian of a `C²` function is then the pull-back of the Hessian computed in *any*
chart of the `C²` maximal atlas along the manifold derivative of that chart. In particular
nondegeneracy and the Morse index of a critical point may be computed in any such chart, and the
Morse index is the negative index of inertia of the critical Hessian.

## Main declarations

* `TauCeti.criticalHessian`: the Hessian at a point, as a bilinear form on its tangent space.
* `TauCeti.criticalHessian_apply_eq_of_mem_maximalAtlas`: at a critical point the critical Hessian
  is the Hessian in an arbitrary chart of the maximal atlas, composed with the chart derivative.
* `TauCeti.criticalHessian_apply_swap`: the critical Hessian of a `C²` function is symmetric.
* `TauCeti.isManifoldNondegenerateCriticalPoint_iff_criticalHessian`: an intrinsic
  characterization of nondegenerate critical points.
* `TauCeti.isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas` and
  `TauCeti.manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas`: nondegeneracy and the Morse index
  in an arbitrary chart.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_eq_zero_iff` and
  `TauCeti.IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_eq_finrank_iff`: definiteness
  tests for the extreme indices.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f g : M → ℝ} {x : M}

/-- The **critical Hessian** of a real function `f` at a point `x` of a manifold: the second
derivative at `extChartAt I x x` of the coordinate expression of `f` in the preferred extended
chart, as a bilinear form on the tangent space at `x`.

Like `TauCeti.manifoldMorseIndex`, the definition makes sense at every point and carries no
regularity hypotheses. At a critical point of a `C²` function on a manifold without boundary it is
intrinsic: `TauCeti.criticalHessian_apply_eq_of_mem_maximalAtlas` computes it in an arbitrary chart
there. At a noncritical point it depends on the preferred chart, and on a manifold with boundary
or corners it may also depend on the chart inverse outside `range I`. -/
def criticalHessian (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)

/-- The critical Hessian is the second derivative of the preferred coordinate expression. -/
theorem criticalHessian_def :
    criticalHessian I f x = fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x) :=
  (rfl)

/-- The diagonal of the critical Hessian is the Hessian quadratic form of the preferred coordinate
expression. -/
theorem criticalHessian_apply_self (v : TangentSpace I x) :
    criticalHessian I f x v v =
      hessianQuadraticForm (f ∘ (extChartAt I x).symm) (extChartAt I x x) v :=
  (hessianQuadraticForm_apply (f ∘ (extChartAt I x).symm) (extChartAt I x x) v).symm

/-- The quadratic form of the critical Hessian is the Hessian quadratic form of the preferred
coordinate expression. -/
theorem toQuadraticMap_toBilinForm_criticalHessian :
    (criticalHessian I f x).toBilinForm.toQuadraticMap =
      hessianQuadraticForm (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
  QuadraticMap.ext criticalHessian_apply_self

/-- The Morse index is the negative index of inertia of the critical Hessian. -/
theorem manifoldMorseIndex_eq_sigNeg_criticalHessian :
    manifoldMorseIndex I f x = sigNeg (criticalHessian I f x).toBilinForm.toQuadraticMap := by
  rw [manifoldMorseIndex_def, morseIndex_def, toQuadraticMap_toBilinForm_criticalHessian]
  -- The two sides differ only in reading the model space `E` as `TangentSpace I x`.
  rfl

/-- The critical Hessian depends only on the germ of the function. -/
theorem criticalHessian_congr_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    criticalHessian I f x = criticalHessian I g x := by
  have hchart : (extChartAt I x).symm (extChartAt I x x) = x := by simp
  have hfg' : f ∘ (extChartAt I x).symm =ᶠ[𝓝 (extChartAt I x x)] g ∘ (extChartAt I x).symm :=
    (hchart ▸ hfg).comp_tendsto (continuousAt_extChartAt_symm (I := I) x)
  rw [criticalHessian_def, criticalHessian_def, hfg'.fderiv.fderiv_eq]

/-- Negating the function negates the critical Hessian. -/
@[simp]
theorem criticalHessian_neg : criticalHessian I (-f) x = -criticalHessian I f x := by
  have hfun : (-f) ∘ (extChartAt I x).symm = -(f ∘ (extChartAt I x).symm) := rfl
  have hfd : fderiv ℝ (-(f ∘ (extChartAt I x).symm)) = -fderiv ℝ (f ∘ (extChartAt I x).symm) :=
    funext fun _ ↦ fderiv_neg
  rw [criticalHessian_def, criticalHessian_def, hfun, hfd, fderiv_neg]
  -- The two sides differ only in reading the model space `E` as `TangentSpace I x`.
  rfl

/-- On a normed space with its self-model, the critical Hessian is the second derivative. -/
@[simp]
theorem criticalHessian_modelSpace {g : E → ℝ} {v : E} :
    criticalHessian 𝓘(ℝ, E) g v = fderiv ℝ (fderiv ℝ g) v := by
  simp only [criticalHessian_def, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Function.comp_id, id_eq]
  -- The two sides differ only in reading `E` as the tangent space `TangentSpace 𝓘(ℝ, E) v`.
  rfl

/-- At a nondegenerate critical point the critical Hessian is invertible as a map to the dual of
the tangent space. -/
theorem IsManifoldNondegenerateCriticalPoint.isInvertible_criticalHessian
    (h : IsManifoldNondegenerateCriticalPoint I f x) : (criticalHessian I f x).IsInvertible :=
  ((isManifoldNondegenerateCriticalPoint_iff I).mp h).isInvertible

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- At a nondegenerate critical point the Morse index vanishes exactly when the critical Hessian is
positive definite. -/
theorem IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_eq_zero_iff
    (h : IsManifoldNondegenerateCriticalPoint I f x) :
    manifoldMorseIndex I f x = 0 ↔ ∀ v ≠ 0, 0 < criticalHessian I f x v v := by
  rw [manifoldMorseIndex_def, ← ((isManifoldNondegenerateCriticalPoint_iff I).mp
    h).hessianQuadraticForm_posDef_iff_morseIndex_eq_zero]
  simp only [QuadraticMap.PosDef, hessianQuadraticForm_apply]
  -- The two sides differ only in reading the model space `E` as `TangentSpace I x`.
  rfl

/-- At a nondegenerate critical point the Morse index is the dimension exactly when the critical
Hessian is negative definite. -/
theorem IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_eq_finrank_iff
    (h : IsManifoldNondegenerateCriticalPoint I f x) :
    manifoldMorseIndex I f x = Module.finrank ℝ E ↔ ∀ v ≠ 0, criticalHessian I f x v v < 0 := by
  rw [manifoldMorseIndex_def, ← ((isManifoldNondegenerateCriticalPoint_iff I).mp
    h).neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank]
  simp only [QuadraticMap.PosDef, neg_apply, hessianQuadraticForm_apply, neg_pos]
  -- The two sides differ only in reading the model space `E` as `TangentSpace I x`.
  rfl

end FiniteDimensional

/-! ### Boundaryless manifolds: symmetry and chart independence -/

section Boundaryless

variable [I.Boundaryless]

/-- The critical Hessian of a function which is `C²` at `x` is symmetric. -/
theorem criticalHessian_apply_swap (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (v w : TangentSpace I x) :
    criticalHessian I f x v w = criticalHessian I f x w v :=
  hf.contDiffAt_comp_extChartAt_symm.isSymmSndFDerivAt (by simp) v w

/-- A nondegenerate critical point on a boundaryless manifold is a point where the function is
`C²`, its differential vanishes, and its critical Hessian is invertible. -/
theorem isManifoldNondegenerateCriticalPoint_iff_criticalHessian :
    IsManifoldNondegenerateCriticalPoint I f x ↔
      ContMDiffAt I 𝓘(ℝ) 2 f x ∧ mvfderiv I f x = 0 ∧ (criticalHessian I f x).IsInvertible := by
  have hsmooth :=
    contMDiffAt_iff_contDiffAt_comp_extChartAt_symm (I := I) (f := f) (x := x) (n := 2)
  rw [isManifoldNondegenerateCriticalPoint_iff]
  refine ⟨fun h ↦ ?_, fun ⟨hf, hcrit, hinv⟩ ↦ ?_⟩
  · have hf := hsmooth.2 h.contDiffAt
    refine ⟨hf, ?_, h.isInvertible⟩
    rw [(hf.mdifferentiableAt two_ne_zero).mvfderiv_eq_fderiv_comp_extChartAt_symm]
    exact h.fderiv_eq_zero
  · refine ⟨hsmooth.1 hf, ?_, hinv⟩
    rwa [← (hf.mdifferentiableAt two_ne_zero).mvfderiv_eq_fderiv_comp_extChartAt_symm]

/-- A function with a nondegenerate critical point on a boundaryless manifold is `C²` there. -/
theorem IsManifoldNondegenerateCriticalPoint.contMDiffAt
    (h : IsManifoldNondegenerateCriticalPoint I f x) : ContMDiffAt I 𝓘(ℝ) 2 f x :=
  (isManifoldNondegenerateCriticalPoint_iff_criticalHessian.mp h).1

/-- The differential of a function vanishes at a nondegenerate critical point. -/
theorem IsManifoldNondegenerateCriticalPoint.mvfderiv_eq_zero
    (h : IsManifoldNondegenerateCriticalPoint I f x) : mvfderiv I f x = 0 :=
  (isManifoldNondegenerateCriticalPoint_iff_criticalHessian.mp h).2.1

section Chart

variable {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 2 M)
  (hx : x ∈ e.source)
include he hx

/-- The transition from the preferred chart at `x` to a chart `e` of the maximal atlas is `C²` at
the chart image of `x`, with the invertible manifold derivative of `e` as its derivative there,
and every preferred coordinate expression factors through it near that point. The coordinate
expression in `e` of a function which is `C²` at `x` is `C²` at the image of that point. -/
private theorem exists_transition :
    ∃ φ : E → E, φ (extChartAt I x x) = e.extend I x ∧ ContDiffAt ℝ 2 φ (extChartAt I x x) ∧
      fderiv ℝ φ (extChartAt I x x) = mvfderiv I (e.extend I) x ∧
      (fderiv ℝ φ (extChartAt I x x)).IsInvertible ∧
      (∀ f : M → ℝ, f ∘ (extChartAt I x).symm =ᶠ[𝓝 (extChartAt I x x)]
        (f ∘ (e.extend I).symm) ∘ φ) ∧
      ∀ f : M → ℝ, ContMDiffAt I 𝓘(ℝ) 2 f x →
        ContDiffAt ℝ 2 (f ∘ (e.extend I).symm) (φ (extChartAt I x x)) := by
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he
  have hext := e.contMDiffAt_extend he hx
  have hD := ((hext.mdifferentiableAt two_ne_zero).mvfderiv_eq_fderiv_comp_extChartAt_symm).symm
  have hinv : (mvfderiv I (e.extend I) x).IsInvertible := by
    -- `mvfderiv` is `mfderiv` followed by the identification `fromTangentSpace` of the tangent
    -- space of `E` with `E`; both factors are invertible.
    unfold mvfderiv
    exact ContinuousLinearMap.IsInvertible.comp ⟨NormedSpace.fromTangentSpace (e.extend I x), rfl⟩
      (isInvertible_mfderiv_extend he1 hx)
  have hφx : (e.extend I ∘ (extChartAt I x).symm) (extChartAt I x x) = e.extend I x := by simp
  refine ⟨e.extend I ∘ (extChartAt I x).symm, hφx,
    contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.mp hext, hD, hD ▸ hinv, fun f ↦ ?_,
    fun f hf ↦ hφx ▸ (contMDiffAt_iff_contDiffAt_comp_extend_symm he hx).mp hf⟩
  have hmem : (extChartAt I x).symm ⁻¹' e.source ∈ 𝓝 (extChartAt I x x) :=
    (continuousAt_extChartAt_symm (I := I) x).preimage_mem_nhds
      (by simpa only [extChartAt_to_inv] using e.open_source.mem_nhds hx)
  filter_upwards [hmem] with y hy
  have hy' : (extChartAt I x).symm y ∈ (e.extend I).source := by rwa [e.extend_source]
  simp only [comp_apply, (e.extend I).left_inv hy']

/-- **The critical Hessian in an arbitrary chart.** At a critical point of a `C²` function on a
boundaryless manifold, the critical Hessian is the Hessian of the coordinate expression in any
chart `e` of the `C²` maximal atlas, evaluated on the images of the tangent vectors under the
derivative of `e`. In particular it does not depend on the choice of chart. -/
theorem criticalHessian_apply_eq_of_mem_maximalAtlas (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hcrit : mvfderiv I f x = 0) (v w : TangentSpace I x) :
    criticalHessian I f x v w =
      fderiv ℝ (fderiv ℝ (f ∘ (e.extend I).symm)) (e.extend I x)
        (mvfderiv I (e.extend I) x v) (mvfderiv I (e.extend I) x w) := by
  obtain ⟨φ, hφx, hφ, hDφ, -, hfg, hreg⟩ := exists_transition he hx
  have key := fderiv_fderiv_comp_apply_of_fderiv_eq_zero (hreg f hf) hφ
    (hφx ▸ (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
      (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hx
      (hf.mdifferentiableAt two_ne_zero)).mp hcrit) v w
  rw [← (hfg f).fderiv.fderiv_eq, hDφ, hφx] at key
  exact key

/-- **Nondegeneracy in an arbitrary chart.** On a boundaryless manifold, `x` is a nondegenerate
critical point of `f` exactly when the coordinate expression of `f` in any chart `e` of the `C²`
maximal atlas has a nondegenerate critical point at the image of `x`. -/
theorem isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas :
    IsManifoldNondegenerateCriticalPoint I f x ↔
      IsNondegenerateCriticalPoint (f ∘ (e.extend I).symm) (e.extend I x) := by
  have hsmooth := contMDiffAt_iff_contDiffAt_comp_extend_symm (f := f) he hx
  by_cases hf : ContMDiffAt I 𝓘(ℝ) 2 f x
  · obtain ⟨φ, hφx, hφ, -, hinv, hfg, hreg⟩ := exists_transition he hx
    rw [isManifoldNondegenerateCriticalPoint_iff, ← hφx,
      ← isNondegenerateCriticalPoint_comp_iff (hreg f hf) hφ hinv]
    exact ⟨fun h ↦ h.congr_of_eventuallyEq (hfg f), fun h ↦ h.congr_of_eventuallyEq (hfg f).symm⟩
  · exact iff_of_false (fun h ↦ hf h.contMDiffAt) fun h ↦ hf (hsmooth.mpr h.contDiffAt)

/-- **The Morse index in an arbitrary chart.** At a critical point of a `C²` function on a
boundaryless manifold, the Morse index is the Morse index of the coordinate expression in any chart
`e` of the `C²` maximal atlas. -/
theorem manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hcrit : mvfderiv I f x = 0) :
    manifoldMorseIndex I f x = morseIndex (f ∘ (e.extend I).symm) (e.extend I x) := by
  obtain ⟨φ, hφx, hφ, -, hinv, hfg, hreg⟩ := exists_transition he hx
  rw [manifoldMorseIndex_def, morseIndex_congr_of_eventuallyEq (hfg f),
    morseIndex_comp (hreg f hf) hφ (hφx ▸ (mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
      (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) hx
      (hf.mdifferentiableAt two_ne_zero)).mp hcrit) hinv, hφx]

end Chart

end Boundaryless

end TauCeti
