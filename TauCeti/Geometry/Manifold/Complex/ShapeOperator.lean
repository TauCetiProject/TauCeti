/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
public import TauCeti.Geometry.Manifold.Immersion.ShapeOperator
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# The second fundamental form, shape operator, and focal points of holomorphic maps

Let `M` be a manifold modelled on a complex normed space `E`, and let `i : M → F` be a map into a
complex inner product space `F`. Endowing `F` with the underlying real inner product
`re ⟪·, ·⟫_ℂ`, the manifold `M` (viewed as a real manifold modelled on `𝓘(ℝ, E)`) carries the
normal space `TauCeti.normalSubspace 𝓘(ℝ, E) i x`, the real second fundamental form
`TauCeti.manifoldSecondFundamentalForm 𝓘(ℝ, E) i x`, and the real shape operator
`TauCeti.manifoldShapeOperator 𝓘(ℝ, E) i x ν`.

When `i` is `C²` over `ℂ` at `x` (in particular, when `i` is holomorphic):

* `TauCeti.normalSubspace 𝓘(ℝ, E) i x` coincides with `(mvfderiv 𝓘(ℂ, E) i x).rangeᗮ` as a real
  subspace and is therefore stable under `I • ·` (requiring only complex differentiability at `x`
  and no finite-dimensionality of `E`);
* when `E` is finite-dimensional over `ℂ`, the real second fundamental form coincides with the
  complex second fundamental form `TauCeti.manifoldSecondFundamentalForm 𝓘(ℂ, E) i x` and is
  `ℂ`-bilinear (`B(I • v, w) = I • B(v, w) = B(v, I • w)`, `B(I • v, I • w) = -B(v, w)`);
* the shape operator `S_ν = manifoldShapeOperator 𝓘(ℝ, E) i x ν` anticommutes with `I • ·` (and
  with `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M x`), while rotating `ν` by `I`
  satisfies `S_{I • ν} = I • S_ν`;
* consequently the generalized `κ`- and `-κ`-eigenspaces of `S_ν` have equal dimension, the
  principal curvatures of `i` occur in opposite pairs `±κ`, and the generalized `0`-eigenspaces
  (in particular `ker S_ν`) are `I`-invariant;
* for a `C²` holomorphic immersion and a normal vector `ν`, the opposite points `i x - ν` and
  `i x + ν` have equal focal multiplicity at `x`, one is a nondegenerate critical center at `x` if
  and only if the other is, and the squared-distance functions from `i x - ν` and `i x + ν` have
  equal `TauCeti.manifoldMorseIndex` at `x`.

No completeness or finite-dimensionality is assumed on the ambient complex inner product space `F`.

## Main results

* `MDifferentiableAt.normalSubspace_eq_orthogonal_range_mvfderiv` and
  `MDifferentiableAt.I_smul_mem_normalSubspace_iff`: complex structure on the normal space.
* `ContMDiffAt.manifoldSecondFundamentalForm_restrictScalars_apply`,
  `ContMDiffAt.manifoldSecondFundamentalForm_I_smul_left`, and
  `ContMDiffAt.manifoldSecondFundamentalForm_I_smul_right`: complex bilinearity of the second
  fundamental form.
* `ContMDiffAt.manifoldShapeOperator_apply_I_smul`,
  `ContMDiffAt.manifoldShapeOperator_I_smul_apply`, and
  `ContMDiffAt.manifoldShapeOperator_apply_ofComplexManifold`: interaction of the shape operator
  with the complex structure.
* `ContMDiffAt.finrank_genEigenspace_manifoldShapeOperator_neg`,
  `ContMDiffAt.hasEigenvalue_manifoldShapeOperator_neg_iff`,
  `ContMDiffAt.I_smul_mem_genEigenspace_manifoldShapeOperator_zero`, and
  `ContMDiffAt.ofComplexManifold_mem_genEigenspace_manifoldShapeOperator_zero_iff`: paired
  principal curvatures and complex kernel.
* `ContMDiffAt.finrank_ker_criticalHessian_norm_sq_sub_sub_comp`,
  `ContMDiffAt.isManifoldNondegenerateCriticalPoint_norm_sq_sub_sub_comp_iff`, and
  `ContMDiffAt.manifoldMorseIndex_norm_sq_sub_sub_comp`: focal and Morse-index symmetry along
  normal lines.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §§6–7.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Chapter IX, §2–§3.
-/

public section

open Complex Function Module Module.End
open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

open SmoothAlmostComplexStructure

attribute [local instance] InnerProductSpace.complexToReal

section NormalSpace

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] {i : M → F} {x : M}

/-- For a map `i : M → F` which is complex differentiable at `x`, the real normal space
`TauCeti.normalSubspace 𝓘(ℝ, E) i x` (with respect to `re ⟪·, ·⟫_ℂ`) is the complex orthogonal
complement `(mvfderiv 𝓘(ℂ, E) i x).rangeᗮ` with scalars restricted to `ℝ`. -/
theorem _root_.MDifferentiableAt.normalSubspace_eq_orthogonal_range_mvfderiv
    (hi : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) i x) :
    normalSubspace 𝓘(ℝ, E) i x = (mvfderiv 𝓘(ℂ, E) i x).rangeᗮ.restrictScalars ℝ := by
  have hextC : ((extChartAt 𝓘(ℂ, E) x).symm : E → M) = (chartAt E x).symm := by ext; simp
  have hextC' : extChartAt 𝓘(ℂ, E) x x = chartAt E x x := by simp
  have hg : DifferentiableAt ℂ (i ∘ (chartAt E x).symm) (chartAt E x x) := by
    simpa only [hextC, hextC'] using hi.differentiableAt_comp_extChartAt_symm
  have hR : (mvfderiv 𝓘(ℝ, E) i x).range =
      (fderiv ℝ (i ∘ (chartAt E x).symm) (chartAt E x x)).range := by
    rw [← (hi.restrictScalars ℝ).fderiv_comp_chartAt_symm]
    -- `TangentSpace 𝓘(ℝ, E) x` and `E` are definitionally the same type.
    rfl
  have hC : (mvfderiv 𝓘(ℂ, E) i x).range =
      (fderiv ℂ (i ∘ (chartAt E x).symm) (chartAt E x x)).range := by
    rw [← hi.fderiv_comp_chartAt_symm]
    -- `TangentSpace 𝓘(ℂ, E) x` and `E` are definitionally the same type.
    rfl
  rw [← orthogonal_range_mvfderiv_eq_normalSubspace, hR, hC,
    hg.orthogonal_range_fderiv_restrictScalars]

/-- The real normal space of a complex-differentiable map is invariant under `I • ·`. -/
theorem _root_.MDifferentiableAt.I_smul_mem_normalSubspace_iff
    (hi : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) i x) {ν : F} :
    I • ν ∈ normalSubspace 𝓘(ℝ, E) i x ↔ ν ∈ normalSubspace 𝓘(ℝ, E) i x := by
  rw [hi.normalSubspace_eq_orthogonal_range_mvfderiv, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem]
  exact ⟨fun h ↦ by simpa [smul_smul] using Submodule.smul_mem _ (-I) h,
    fun h ↦ Submodule.smul_mem _ I h⟩

/-- For a complex-differentiable map into a normed space, injectivity of the real manifold
derivative is equivalent to injectivity of the complex manifold derivative. -/
theorem _root_.MDifferentiableAt.injective_mvfderiv_restrictScalars_iff
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] {g : M → G}
    (hg : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, G) g x) :
    Injective (mvfderiv 𝓘(ℝ, E) g x) ↔ Injective (mvfderiv 𝓘(ℂ, E) g x) := by
  have hextC : ((extChartAt 𝓘(ℂ, E) x).symm : E → M) = (chartAt E x).symm := by ext; simp
  have hextC' : extChartAt 𝓘(ℂ, E) x x = chartAt E x x := by simp
  have hd : DifferentiableAt ℂ (g ∘ (chartAt E x).symm) (chartAt E x x) := by
    simpa only [hextC, hextC'] using hg.differentiableAt_comp_extChartAt_symm
  have hR : Injective (mvfderiv 𝓘(ℝ, E) g x) ↔
      Injective (fderiv ℝ (g ∘ (chartAt E x).symm) (chartAt E x x)) := by
    rw [(hg.restrictScalars ℝ).fderiv_comp_chartAt_symm]
    -- `TangentSpace 𝓘(ℝ, E) x` and `E` are definitionally the same type.
    rfl
  have hC : Injective (mvfderiv 𝓘(ℂ, E) g x) ↔
      Injective (fderiv ℂ (g ∘ (chartAt E x).symm) (chartAt E x x)) := by
    rw [hg.fderiv_comp_chartAt_symm]
    -- `TangentSpace 𝓘(ℂ, E) x` and `E` are definitionally the same type.
    rfl
  exact hR.trans ((hd.injective_fderiv_restrictScalars_iff ℝ).trans hC.symm)

end NormalSpace

section FiniteDimensional

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M] {i : M → F} {x : M}

private theorem manifoldShapeOperator_self_apply (i : M → F) (x : M) (ν : F) (v : E) :
    tangentSpaceCastModel 𝓘(ℝ, E) x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v) =
      shapeOperator (i ∘ (chartAt E x).symm) (chartAt E x x) ν v := by
  have hext : ((extChartAt 𝓘(ℝ, E) x).symm : E → M) = (chartAt E x).symm := by ext; simp
  have hext' : extChartAt 𝓘(ℝ, E) x x = chartAt E x x := by simp
  -- On `𝓘(ℝ, E)`, `tangentSpaceCastModel 𝓘(ℝ, E) x` is the identity on `E`.
  refine (tangentSpaceCastModel_manifoldShapeOperator_apply
    (I := 𝓘(ℝ, E)) (i := i) (x := x) ν v).trans ?_
  rw [hext, hext']
  rfl

/-! ### Complex bilinearity of `manifoldSecondFundamentalForm` -/

/-- **Real vs. complex second fundamental form.** For a map `i : M → F` which is `C²` over `ℂ` at
`x`, the real second fundamental form `manifoldSecondFundamentalForm 𝓘(ℝ, E) i x` coincides with
the complex second fundamental form `manifoldSecondFundamentalForm 𝓘(ℂ, E) i x`. -/
theorem _root_.ContMDiffAt.manifoldSecondFundamentalForm_restrictScalars_apply
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (v w : E) :
    manifoldSecondFundamentalForm 𝓘(ℝ, E) i x v w =
      manifoldSecondFundamentalForm 𝓘(ℂ, E) i x v w :=
  (secondFundamentalForm_comp_chartAt_symm (𝕜 := ℝ) (g := i) (y := x) v w).symm.trans <|
    (hi.contDiffAt_comp_chartAt_symm.secondFundamentalForm_restrictScalars_apply v w).trans
      (secondFundamentalForm_comp_chartAt_symm (𝕜 := ℂ) (g := i) (y := x) v w)

/-- For a `C²` holomorphic map, `B(I • v, w) = I • B(v, w)`. -/
@[simp]
theorem _root_.ContMDiffAt.manifoldSecondFundamentalForm_I_smul_left
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (v w : E) :
    manifoldSecondFundamentalForm 𝓘(ℝ, E) i x (I • v) w =
      I • manifoldSecondFundamentalForm 𝓘(ℝ, E) i x v w := by
  rw [hi.manifoldSecondFundamentalForm_restrictScalars_apply,
    hi.manifoldSecondFundamentalForm_restrictScalars_apply]
  refine ((secondFundamentalForm_comp_chartAt_symm (𝕜 := ℂ) (g := i) (y := x) (I • v) w).symm.trans
    ?_).trans
    (congrArg (I • ·) (secondFundamentalForm_comp_chartAt_symm (𝕜 := ℂ) (g := i) (y := x) v w))
  simp

/-- For a `C²` holomorphic map, `B(v, I • w) = I • B(v, w)`. -/
@[simp]
theorem _root_.ContMDiffAt.manifoldSecondFundamentalForm_I_smul_right
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (v w : E) :
    manifoldSecondFundamentalForm 𝓘(ℝ, E) i x v (I • w) =
      I • manifoldSecondFundamentalForm 𝓘(ℝ, E) i x v w := by
  rw [hi.manifoldSecondFundamentalForm_restrictScalars_apply,
    hi.manifoldSecondFundamentalForm_restrictScalars_apply]
  refine ((secondFundamentalForm_comp_chartAt_symm (𝕜 := ℂ) (g := i) (y := x) v (I • w)).symm.trans
    ?_).trans
    (congrArg (I • ·) (secondFundamentalForm_comp_chartAt_symm (𝕜 := ℂ) (g := i) (y := x) v w))
  simp

/-- For a `C²` holomorphic map, `B(I • v, I • w) = -B(v, w)`. -/
theorem _root_.ContMDiffAt.manifoldSecondFundamentalForm_I_smul_I_smul
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (v w : E) :
    manifoldSecondFundamentalForm 𝓘(ℝ, E) i x (I • v) (I • w) =
      -manifoldSecondFundamentalForm 𝓘(ℝ, E) i x v w := by
  rw [hi.manifoldSecondFundamentalForm_I_smul_left, hi.manifoldSecondFundamentalForm_I_smul_right,
    smul_smul, I_mul_I, neg_one_smul]

/-- On a smooth complex manifold, `manifoldSecondFundamentalForm 𝓘(ℝ, E) i x` is complex linear in
the first argument with respect to `SmoothAlmostComplexStructure.ofComplexManifold E M x`. -/
@[simp]
theorem _root_.ContMDiffAt.manifoldSecondFundamentalForm_ofComplexManifold_left
    [IsManifold 𝓘(ℂ, E) ∞ M] (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x)
    (v w : TangentSpace 𝓘(ℝ, E) x) :
    manifoldSecondFundamentalForm 𝓘(ℝ, E) i x (ofComplexManifold E M x v) w =
      I • manifoldSecondFundamentalForm 𝓘(ℝ, E) i x v w := by
  let v₀ : E := v
  let w₀ : E := w
  rw [ofComplexManifold_apply (E := E) x v₀]
  exact hi.manifoldSecondFundamentalForm_I_smul_left v₀ w₀

/-- On a smooth complex manifold, `manifoldSecondFundamentalForm 𝓘(ℝ, E) i x` is complex linear in
the second argument with respect to `SmoothAlmostComplexStructure.ofComplexManifold E M x`. -/
@[simp]
theorem _root_.ContMDiffAt.manifoldSecondFundamentalForm_ofComplexManifold_right
    [IsManifold 𝓘(ℂ, E) ∞ M] (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x)
    (v w : TangentSpace 𝓘(ℝ, E) x) :
    manifoldSecondFundamentalForm 𝓘(ℝ, E) i x v (ofComplexManifold E M x w) =
      I • manifoldSecondFundamentalForm 𝓘(ℝ, E) i x v w := by
  let v₀ : E := v
  let w₀ : E := w
  rw [ofComplexManifold_apply (E := E) x w₀]
  exact hi.manifoldSecondFundamentalForm_I_smul_right v₀ w₀

/-! ### Anticommutation of `manifoldShapeOperator` with `J` and paired principal curvatures -/

/-- **The shape operator of a holomorphic map anticommutes with `I • ·`.** -/
theorem _root_.ContMDiffAt.manifoldShapeOperator_apply_I_smul
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (ν : F) (v : E) :
    tangentSpaceCastModel 𝓘(ℝ, E) x (manifoldShapeOperator 𝓘(ℝ, E) i x ν (I • v)) =
      -(I • tangentSpaceCastModel 𝓘(ℝ, E) x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v)) := by
  rw [manifoldShapeOperator_self_apply, manifoldShapeOperator_self_apply,
    hi.contDiffAt_comp_chartAt_symm.shapeOperator_apply_I_smul]

/-- **Rotating the normal vector by `I` rotates the shape operator by `I`.** -/
theorem _root_.ContMDiffAt.manifoldShapeOperator_I_smul_apply
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (ν : F) (v : E) :
    tangentSpaceCastModel 𝓘(ℝ, E) x (manifoldShapeOperator 𝓘(ℝ, E) i x (I • ν) v) =
      I • tangentSpaceCastModel 𝓘(ℝ, E) x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v) := by
  rw [manifoldShapeOperator_self_apply, manifoldShapeOperator_self_apply,
    hi.contDiffAt_comp_chartAt_symm.shapeOperator_I_smul_apply]

/-- On a smooth complex manifold, `manifoldShapeOperator 𝓘(ℝ, E) i x ν` anticommutes with
`SmoothAlmostComplexStructure.ofComplexManifold E M x`. -/
theorem _root_.ContMDiffAt.manifoldShapeOperator_apply_ofComplexManifold
    [IsManifold 𝓘(ℂ, E) ∞ M] (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (ν : F)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    manifoldShapeOperator 𝓘(ℝ, E) i x ν (ofComplexManifold E M x v) =
      -ofComplexManifold E M x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v) := by
  let v₀ : E := v
  let w₀ : E := tangentSpaceCastModel 𝓘(ℝ, E) x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v₀)
  refine (tangentSpaceCastModel 𝓘(ℝ, E) x).injective ?_
  rw [map_neg, ofComplexManifold_apply (E := E) x v₀]
  have hw : tangentSpaceCastModel 𝓘(ℝ, E) x
      (ofComplexManifold E M x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v)) = I • w₀ :=
    ofComplexManifold_apply (E := E) x w₀
  rw [hw]
  exact hi.manifoldShapeOperator_apply_I_smul ν v₀

/-- On a smooth complex manifold, `S_{I • ν} = J ∘ S_ν` for
`J = SmoothAlmostComplexStructure.ofComplexManifold E M x`. -/
theorem _root_.ContMDiffAt.manifoldShapeOperator_I_smul_apply_eq_ofComplexManifold
    [IsManifold 𝓘(ℂ, E) ∞ M] (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (ν : F)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    manifoldShapeOperator 𝓘(ℝ, E) i x (I • ν) v =
      ofComplexManifold E M x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v) := by
  let v₀ : E := v
  let w₀ : E := tangentSpaceCastModel 𝓘(ℝ, E) x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v₀)
  refine (tangentSpaceCastModel 𝓘(ℝ, E) x).injective ?_
  have hw : tangentSpaceCastModel 𝓘(ℝ, E) x
      (ofComplexManifold E M x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v)) = I • w₀ :=
    ofComplexManifold_apply (E := E) x w₀
  rw [hw]
  exact hi.manifoldShapeOperator_I_smul_apply ν v₀

/-- Multiplication by `I` on `E`, viewed as a real linear equivalence of
`TangentSpace 𝓘(ℝ, E) x`. -/
private def complexMulEquiv (x : M) : TangentSpace 𝓘(ℝ, E) x ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x :=
  (LinearEquiv.smulOfNeZero ℂ E I I_ne_zero).restrictScalars ℝ

private theorem manifoldShapeOperator_mul_add_mul_eq_zero
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (ν : F) :
    manifoldShapeOperator 𝓘(ℝ, E) i x ν * (complexMulEquiv (E := E) (M := M) x :
        Module.End ℝ (TangentSpace 𝓘(ℝ, E) x)) +
      (complexMulEquiv (E := E) (M := M) x : Module.End ℝ (TangentSpace 𝓘(ℝ, E) x)) *
        manifoldShapeOperator 𝓘(ℝ, E) i x ν = 0 := by
  ext v
  let v₀ : E := v
  rw [LinearMap.add_apply, LinearMap.zero_apply, mul_eq_comp, mul_eq_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  refine (tangentSpaceCastModel 𝓘(ℝ, E) x).injective ?_
  -- On `𝓘(ℝ, E)`, `complexMulEquiv x` is multiplication by `I` and `tangentSpaceCastModel` is `id`.
  have h1 : tangentSpaceCastModel 𝓘(ℝ, E) x
      (manifoldShapeOperator 𝓘(ℝ, E) i x ν (complexMulEquiv (E := E) (M := M) x v)) =
      tangentSpaceCastModel 𝓘(ℝ, E) x (manifoldShapeOperator 𝓘(ℝ, E) i x ν (I • v₀)) := rfl
  have h2 : tangentSpaceCastModel 𝓘(ℝ, E) x
      (complexMulEquiv (E := E) (M := M) x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v)) =
      I • tangentSpaceCastModel 𝓘(ℝ, E) x (manifoldShapeOperator 𝓘(ℝ, E) i x ν v₀) := rfl
  rw [map_add, map_zero, h1, h2, hi.manifoldShapeOperator_apply_I_smul, neg_add_cancel]

/-- **Paired principal curvatures on a complex manifold.** For a map `i : M → F` which is `C²` over
`ℂ` at `x`, the generalized `κ`- and `-κ`-eigenspaces of `manifoldShapeOperator 𝓘(ℝ, E) i x ν` have
the same real dimension. -/
theorem _root_.ContMDiffAt.finrank_genEigenspace_manifoldShapeOperator_neg
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (ν : F) (κ : ℝ) (k : ℕ∞) :
    finrank ℝ (genEigenspace (manifoldShapeOperator 𝓘(ℝ, E) i x ν) (-κ) k) =
      finrank ℝ (genEigenspace (manifoldShapeOperator 𝓘(ℝ, E) i x ν) κ k) :=
  finrank_genEigenspace_neg_of_anticommute _ (manifoldShapeOperator_mul_add_mul_eq_zero hi ν) κ k

/-- For a map `i : M → F` which is `C²` over `ℂ` at `x`, `-κ` is an eigenvalue of
`manifoldShapeOperator 𝓘(ℝ, E) i x ν` if and only if `κ` is. -/
theorem _root_.ContMDiffAt.hasEigenvalue_manifoldShapeOperator_neg_iff
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (ν : F) {κ : ℝ} :
    (manifoldShapeOperator 𝓘(ℝ, E) i x ν).HasEigenvalue (-κ) ↔
      (manifoldShapeOperator 𝓘(ℝ, E) i x ν).HasEigenvalue κ :=
  hasEigenvalue_neg_iff_of_anticommute _ (manifoldShapeOperator_mul_add_mul_eq_zero hi ν)

/-- For a map `i : M → F` which is `C²` over `ℂ` at `x`, the generalized `0`-eigenspaces of
`manifoldShapeOperator 𝓘(ℝ, E) i x ν` (in particular its kernel) are invariant under `I • ·`. -/
theorem _root_.ContMDiffAt.I_smul_mem_genEigenspace_manifoldShapeOperator_zero
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (ν : F) (k : ℕ∞) {v : E}
    (hv : v ∈ genEigenspace (manifoldShapeOperator 𝓘(ℝ, E) i x ν : Module.End ℝ E) 0 k) :
    I • v ∈ genEigenspace (manifoldShapeOperator 𝓘(ℝ, E) i x ν : Module.End ℝ E) 0 k := by
  have h := mapsTo_genEigenspace_neg_of_anticommute
    (manifoldShapeOperator_mul_add_mul_eq_zero hi ν) 0 k hv
  rwa [neg_zero] at h

/-- On a smooth complex manifold, the generalized `0`-eigenspaces of
`manifoldShapeOperator 𝓘(ℝ, E) i x ν` are preserved by
`SmoothAlmostComplexStructure.ofComplexManifold E M x`. -/
@[simp]
theorem _root_.ContMDiffAt.ofComplexManifold_mem_genEigenspace_manifoldShapeOperator_zero_iff
    [IsManifold 𝓘(ℂ, E) ∞ M] (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (ν : F) (k : ℕ∞)
    {v : TangentSpace 𝓘(ℝ, E) x} :
    ofComplexManifold E M x v ∈ genEigenspace (manifoldShapeOperator 𝓘(ℝ, E) i x ν) 0 k ↔
      v ∈ genEigenspace (manifoldShapeOperator 𝓘(ℝ, E) i x ν) 0 k := by
  have hmap {u : TangentSpace 𝓘(ℝ, E) x}
      (hu : u ∈ genEigenspace (manifoldShapeOperator 𝓘(ℝ, E) i x ν) 0 k) :
      ofComplexManifold E M x u ∈ genEigenspace (manifoldShapeOperator 𝓘(ℝ, E) i x ν) 0 k := by
    let u₀ : E := u
    rw [ofComplexManifold_apply (E := E) x u₀]
    exact hi.I_smul_mem_genEigenspace_manifoldShapeOperator_zero ν k hu
  refine ⟨fun h ↦ ?_, hmap⟩
  have h2 := hmap h
  have hsq : ofComplexManifold E M x (ofComplexManifold E M x v) = -v :=
    DFunLike.congr_fun ((ofComplexManifold E M).square_neg x) v
  rwa [hsq, Submodule.neg_mem_iff] at h2

/-! ### Symmetric focal points and Morse indices along normal lines -/

/-- **Symmetric focal multiplicities on a complex manifold.** For a `C²` holomorphic immersion
`i : M → F` and a normal vector `ν ∈ normalSubspace 𝓘(ℝ, E) i x`, the opposite points `i x - ν` and
`i x + ν` have equal focal multiplicity at `x`. -/
theorem _root_.ContMDiffAt.finrank_ker_criticalHessian_norm_sq_sub_sub_comp
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (h : Injective (mvfderiv 𝓘(ℂ, E) i x)) {ν : F}
    (hν : ν ∈ normalSubspace 𝓘(ℝ, E) i x) :
    finrank ℝ (LinearMap.ker
        (criticalHessian 𝓘(ℝ, E) (fun y ↦ ‖i y - (i x - ν)‖ ^ 2) x :
          TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)) =
      finrank ℝ (LinearMap.ker
        (criticalHessian 𝓘(ℝ, E) (fun y ↦ ‖i y - (i x + ν)‖ ^ 2) x :
          TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)) := by
  have hiR : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 2 i x := by simpa using hi.restrictScalars ℝ
  have hR : Injective (mvfderiv 𝓘(ℝ, E) i x) :=
    (hi.mdifferentiableAt two_ne_zero).injective_mvfderiv_restrictScalars_iff.mpr h
  rw [ker_criticalHessian_norm_sq_sub_comp hiR hR (by simpa [sub_sub_cancel] using hν),
    ker_criticalHessian_norm_sq_sub_comp hiR hR
      (by simpa [sub_add_cancel_left] using Submodule.neg_mem _ hν),
    sub_sub_cancel_left, add_sub_cancel_left, manifoldShapeOperator_neg, eigenspace, eigenspace,
    genEigenspace_neg]
  exact hi.finrank_genEigenspace_manifoldShapeOperator_neg ν 1 1

/-- **Symmetric nondegeneracy on a complex manifold.** Along a `C²` holomorphic immersion
`i : M → F`, `x` is a nondegenerate critical point of `y ↦ ‖i y - (i x - ν)‖²` if and only if `x`
is a nondegenerate critical point of `y ↦ ‖i y - (i x + ν)‖²`. -/
theorem _root_.ContMDiffAt.isManifoldNondegenerateCriticalPoint_norm_sq_sub_sub_comp_iff
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (h : Injective (mvfderiv 𝓘(ℂ, E) i x)) (ν : F) :
    IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) (fun y ↦ ‖i y - (i x - ν)‖ ^ 2) x ↔
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) (fun y ↦ ‖i y - (i x + ν)‖ ^ 2) x := by
  have hiR : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 2 i x := by simpa using hi.restrictScalars ℝ
  have hR : Injective (mvfderiv 𝓘(ℝ, E) i x) :=
    (hi.mdifferentiableAt two_ne_zero).injective_mvfderiv_restrictScalars_iff.mpr h
  rw [isManifoldNondegenerateCriticalPoint_norm_sq_sub_comp_iff hiR hR,
    isManifoldNondegenerateCriticalPoint_norm_sq_sub_comp_iff hiR hR, sub_sub_cancel,
    sub_add_cancel_left, Submodule.neg_mem_iff, sub_sub_cancel_left, add_sub_cancel_left,
    manifoldShapeOperator_neg, Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff,
    eigenspace, eigenspace, genEigenspace_neg, ← Module.End.hasEigenvalue_iff,
    ← Module.End.hasEigenvalue_iff, hi.hasEigenvalue_manifoldShapeOperator_neg_iff]

/-- **Symmetric Morse indices along a normal line on a complex manifold.** For a `C²` holomorphic
immersion `i : M → F` and a normal vector `ν ∈ normalSubspace 𝓘(ℝ, E) i x`, the squared-distance
functions from `i x - ν` and `i x + ν` have equal `TauCeti.manifoldMorseIndex` at `x` (degenerate
or not). -/
theorem _root_.ContMDiffAt.manifoldMorseIndex_norm_sq_sub_sub_comp
    (hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) 2 i x) (h : Injective (mvfderiv 𝓘(ℂ, E) i x)) {ν : F}
    (hν : ν ∈ normalSubspace 𝓘(ℝ, E) i x) :
    manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - (i x - ν)‖ ^ 2) x =
      manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ ‖i y - (i x + ν)‖ ^ 2) x := by
  have hiR : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 2 i x := by simpa using hi.restrictScalars ℝ
  have hR : Injective (mvfderiv 𝓘(ℝ, E) i x) :=
    (hi.mdifferentiableAt two_ne_zero).injective_mvfderiv_restrictScalars_iff.mpr h
  have ha₁ : i x - (i x - ν) ∈ normalSubspace 𝓘(ℝ, E) i x := by rwa [sub_sub_cancel]
  have ha₂ : i x - (i x + ν) ∈ normalSubspace 𝓘(ℝ, E) i x := by
    simpa [sub_add_cancel_left] using Submodule.neg_mem _ hν
  rw [manifoldMorseIndex_norm_sq_sub_comp_eq_finsum_finrank_ker hiR hR ha₁,
    manifoldMorseIndex_norm_sq_sub_comp_eq_finsum_finrank_ker hiR hR ha₂]
  refine finsum_mem_congr rfl fun t _ ↦ ?_
  have hsub₁ : i x + t • (i x - ν - i x) = i x - t • ν := by
    rw [sub_sub_cancel_left, smul_neg, sub_eq_add_neg]
  have hsub₂ : i x + t • (i x + ν - i x) = i x + t • ν := by
    rw [add_sub_cancel_left]
  rw [hsub₁, hsub₂]
  exact hi.finrank_ker_criticalHessian_norm_sq_sub_sub_comp h (Submodule.smul_mem _ t hν)

end FiniteDimensional

end TauCeti

end
