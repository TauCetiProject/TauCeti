/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Analysis.Calculus.SecondDerivative
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.Morse.Index
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.Algebra.Module.BilinearForm

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
* `TauCeti.fderiv_fderiv_comp_chartAt_symm`: on a manifold modelled on a real normed space, the
  second derivative in the preferred chart is the critical Hessian.
* `TauCeti.criticalHessian_apply_eq_of_mem_maximalAtlas`: at a critical point the critical Hessian
  is the Hessian in an arbitrary chart of the maximal atlas, composed with the chart derivative.
* `TauCeti.criticalHessian_apply_swap`: the critical Hessian of a `C²` function is symmetric.
* `TauCeti.criticalHessian_apply_eq_mvfderiv`: at a critical point, differentiating `df(Y)`
  computes the Hessian against the value of the vector field `Y`.
* `TauCeti.isManifoldNondegenerateCriticalPoint_iff_criticalHessian`: an intrinsic
  characterization of nondegenerate critical points.
* `TauCeti.isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas` and
  `TauCeti.manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas`: nondegeneracy and the Morse index
  in an arbitrary chart.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_eq_zero_iff` and
  `TauCeti.IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_eq_finrank_iff`: definiteness
  tests for the extreme indices.
* `Module.Basis.criticalHessianMatrix`: the Gram matrix of the critical Hessian in a
  tangent-space basis, with determinant, inertia, and definiteness comparisons
  (`Module.Basis.criticalHessianMatrix_posDef_iff` and
  `Module.Basis.neg_criticalHessianMatrix_posDef_iff`).
* `TauCeti.exists_negDef_subspace_finrank_eq_manifoldMorseIndex`: the Morse
  index is attained by a negative-definite tangent subspace.
* `TauCeti.exists_posDef_subspace_finrank_eq_manifoldMorseIndex_neg`: the Morse index of `-f` is
  attained by a positive-definite tangent subspace.

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

/-- On a manifold modelled on a real normed space, the second derivative in the preferred chart is
the critical Hessian. -/
theorem fderiv_fderiv_comp_chartAt_symm {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
    {u : N → ℝ} {y : N} (v w : E) :
    fderiv ℝ (fderiv ℝ (u ∘ (chartAt E y).symm)) (chartAt E y y) v w =
      criticalHessian 𝓘(ℝ, E) u y v w := by
  have hext : ((extChartAt 𝓘(ℝ, E) y).symm : E → N) = (chartAt E y).symm := by ext; simp
  have hext' : extChartAt 𝓘(ℝ, E) y y = chartAt E y y := by simp
  have h : fderiv ℝ (fderiv ℝ (u ∘ (chartAt E y).symm)) (chartAt E y y) =
      criticalHessian 𝓘(ℝ, E) u y := by
    rw [criticalHessian_def, hext, hext']
  -- `criticalHessian` is a form on `TangentSpace 𝓘(ℝ, E) y`, which is `E` by definition.
  exact congr($h v w)

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

/-- The Morse index of `-f` is the positive inertia index of the critical Hessian of `f`. -/
theorem manifoldMorseIndex_neg_eq_sigPos_criticalHessian :
    manifoldMorseIndex I (-f) x = sigPos (criticalHessian I f x).toBilinForm.toQuadraticMap := by
  have hneg : (-criticalHessian I f x).toBilinForm = -(criticalHessian I f x).toBilinForm := by
    ext v w
    simp only [ContinuousLinearMap.toBilinForm_apply, neg_apply, LinearMap.neg_apply]
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian, criticalHessian_neg, hneg,
    LinearMap.BilinMap.toQuadraticMap_neg, sigNeg_neg]

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

/-- On a finite-dimensional model space, an injective critical Hessian is invertible as a map to
the dual of the tangent space. -/
theorem criticalHessian_isInvertible_of_injective [FiniteDimensional ℝ E]
    (h : Injective (criticalHessian I f x)) : (criticalHessian I f x).IsInvertible :=
  -- `TangentSpace I x` is by definition the model space `E`, so the finite-dimensional result
  -- for the normed space `E` applies; matrix and subspace proofs go through this lemma.
  ContinuousLinearMap.isInvertible_of_injective (E := E) h

/-! ### Matrix and subspace descriptions -/

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of the critical Hessian of `f` in a basis of the tangent space. -/
noncomputable def _root_.Module.Basis.criticalHessianMatrix
    (b : Module.Basis ι ℝ (TangentSpace I x)) (f : M → ℝ) : Matrix ι ι ℝ :=
  (criticalHessian I f x).toBilinForm.toMatrix b

/-- The entries of the critical Hessian matrix are its values on basis vectors. -/
@[simp]
theorem _root_.Module.Basis.criticalHessianMatrix_apply
    (b : Module.Basis ι ℝ (TangentSpace I x)) (i j : ι) :
    b.criticalHessianMatrix f i j = criticalHessian I f x (b i) (b j) :=
  LinearMap.BilinForm.toMatrix_apply _ _ _ _

/-- The critical Hessian matrix depends only on the germ of the function. -/
theorem _root_.Module.Basis.criticalHessianMatrix_congr_of_eventuallyEq
    (b : Module.Basis ι ℝ (TangentSpace I x))
    (hfg : f =ᶠ[𝓝 x] g) : b.criticalHessianMatrix f = b.criticalHessianMatrix g := by
  rw [Module.Basis.criticalHessianMatrix, Module.Basis.criticalHessianMatrix,
    criticalHessian_congr_of_eventuallyEq hfg]

/-- Negating the function negates its critical Hessian matrix. -/
@[simp]
theorem _root_.Module.Basis.criticalHessianMatrix_neg
    (b : Module.Basis ι ℝ (TangentSpace I x)) :
    b.criticalHessianMatrix (-f) = -b.criticalHessianMatrix f := by
  ext i j
  simp only [Module.Basis.criticalHessianMatrix_apply, criticalHessian_neg, neg_apply,
    Matrix.neg_apply]

/-- Critical Hessian matrices in two tangent-space bases are related by congruence. -/
theorem _root_.Module.Basis.criticalHessianMatrix_changeBasis
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℝ (TangentSpace I x)) (c : Module.Basis κ ℝ (TangentSpace I x)) :
    Matrix.transpose (b.toMatrix c) * b.criticalHessianMatrix f * b.toMatrix c =
      c.criticalHessianMatrix f :=
  LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c (criticalHessian I f x).toBilinForm

/-- The critical Hessian is recovered from its matrix by the usual coordinate formula. -/
theorem _root_.Module.Basis.criticalHessian_eq_dotProduct_criticalHessianMatrix_mulVec
    (b : Module.Basis ι ℝ (TangentSpace I x)) (v w : TangentSpace I x) :
    criticalHessian I f x v w =
      dotProduct (b.repr v) ((b.criticalHessianMatrix f).mulVec (b.repr w)) :=
  (criticalHessian I f x).toBilinForm.apply_eq_dotProduct_toMatrix_mulVec b v w

/-- The negative inertia index of the critical Hessian matrix is the manifold Morse index. -/
theorem _root_.Module.Basis.sigNeg_toQuadraticForm_criticalHessianMatrix
    (b : Module.Basis ι ℝ (TangentSpace I x)) :
    sigNeg (b.criticalHessianMatrix f).toQuadraticForm' = manifoldMorseIndex I f x := by
  rw [Module.Basis.criticalHessianMatrix, LinearMap.BilinForm.sigNeg_toMatrix,
    manifoldMorseIndex_eq_sigNeg_criticalHessian]

/-- The critical Hessian is invertible exactly when its matrix in any basis has nonzero
determinant. -/
theorem _root_.Module.Basis.criticalHessian_isInvertible_iff_det_ne_zero
    (b : Module.Basis ι ℝ (TangentSpace I x)) :
    (criticalHessian I f x).IsInvertible ↔ (b.criticalHessianMatrix f).det ≠ 0 := by
  have : FiniteDimensional ℝ (TangentSpace I x) := b.finiteDimensional_of_finite
  rw [Module.Basis.criticalHessianMatrix, ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  refine ⟨fun h ↦ LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    ((criticalHessian I f x).separatingLeft_toBilinForm_iff_injective.mpr h.injective),
    fun h ↦ ?_⟩
  -- `b` is also a basis of the model space `E`, which is `TangentSpace I x` by definition.
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  exact criticalHessian_isInvertible_of_injective
    ((criticalHessian I f x).separatingLeft_toBilinForm_iff_injective.mp h.1)

end Matrix

section Subspace

variable [FiniteDimensional ℝ E]

/-- Restricting the critical Hessian to a tangent subspace cannot increase its negative inertia
index. -/
theorem _root_.Submodule.sigNeg_restrict_criticalHessian_le_manifoldMorseIndex
    (W : Submodule ℝ (TangentSpace I x)) :
    sigNeg ((criticalHessian I f x).toBilinForm.toQuadraticMap.restrict W) ≤
      manifoldMorseIndex I f x := by
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian]
  exact QuadraticForm.sigNeg_restrict_le _ _

/-- A tangent subspace on which the critical Hessian is negative definite has dimension at most
the Morse index. -/
theorem finrank_le_manifoldMorseIndex_of_negDef_criticalHessian
    {W : Submodule ℝ (TangentSpace I x)}
    (hW : ((-(criticalHessian I f x).toBilinForm.toQuadraticMap).restrict W).PosDef) :
    Module.finrank ℝ W ≤ manifoldMorseIndex I f x := by
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian]
  exact le_sigNeg_of_negDef _ hW

/-- There is a negative-definite tangent subspace whose dimension is the Morse index. -/
theorem exists_negDef_subspace_finrank_eq_manifoldMorseIndex :
    ∃ W : Submodule ℝ (TangentSpace I x),
      Module.finrank ℝ W = manifoldMorseIndex I f x ∧
        ((-(criticalHessian I f x).toBilinForm.toQuadraticMap).restrict W).PosDef := by
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian]
  exact exists_finrank_eq_sigNeg_and_negDef _

/-- A tangent subspace on which the critical Hessian is positive definite has dimension at most
the Morse index of `-f`. -/
theorem finrank_le_manifoldMorseIndex_neg_of_posDef_criticalHessian
    {W : Submodule ℝ (TangentSpace I x)}
    (hW : ((criticalHessian I f x).toBilinForm.toQuadraticMap.restrict W).PosDef) :
    Module.finrank ℝ W ≤ manifoldMorseIndex I (-f) x := by
  rw [manifoldMorseIndex_neg_eq_sigPos_criticalHessian]
  exact le_sigPos_of_posDef _ hW

/-- There is a positive-definite tangent subspace whose dimension is the Morse index of `-f`. -/
theorem exists_posDef_subspace_finrank_eq_manifoldMorseIndex_neg :
    ∃ W : Submodule ℝ (TangentSpace I x),
      Module.finrank ℝ W = manifoldMorseIndex I (-f) x ∧
        ((criticalHessian I f x).toBilinForm.toQuadraticMap.restrict W).PosDef := by
  rw [manifoldMorseIndex_neg_eq_sigPos_criticalHessian]
  exact exists_finrank_eq_sigPos_and_posDef _

/-- At a nondegenerate critical point, a tangent subspace on which the critical Hessian is positive
definite has dimension at most the complementary index. -/
theorem IsManifoldNondegenerateCriticalPoint.finrank_add_manifoldMorseIndex_le_of_posDef_restrict
    (h : IsManifoldNondegenerateCriticalPoint I f x)
    {W : Submodule ℝ (TangentSpace I x)}
    (hW : ((criticalHessian I f x).toBilinForm.toQuadraticMap.restrict W).PosDef) :
    Module.finrank ℝ W + manifoldMorseIndex I f x ≤ Module.finrank ℝ E := by
  rw [← h.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank]
  exact Nat.add_le_add_right (finrank_le_manifoldMorseIndex_neg_of_posDef_criticalHessian hW) _

/-- At a nondegenerate critical point there is a positive-definite tangent subspace of dimension
the dimension of the manifold minus the Morse index. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_posDef_subspace_finrank_add_index_eq
    (h : IsManifoldNondegenerateCriticalPoint I f x) :
    ∃ W : Submodule ℝ (TangentSpace I x),
      Module.finrank ℝ W + manifoldMorseIndex I f x = Module.finrank ℝ E ∧
        ((criticalHessian I f x).toBilinForm.toQuadraticMap.restrict W).PosDef := by
  obtain ⟨W, hWrank, hW⟩ := exists_posDef_subspace_finrank_eq_manifoldMorseIndex_neg (I := I)
    (f := f) (x := x)
  exact ⟨W, hWrank ▸ h.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank, hW⟩

end Subspace

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

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of the critical Hessian of a `C²` function is symmetric. -/
theorem _root_.Module.Basis.criticalHessianMatrix_isSymm
    (b : Module.Basis ι ℝ (TangentSpace I x))
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) : (b.criticalHessianMatrix f).IsSymm := by
  rw [Module.Basis.criticalHessianMatrix,
    (criticalHessian I f x).toBilinForm.isSymm_toMatrix_iff_isSymm b]
  exact ⟨criticalHessian_apply_swap hf⟩

/-- The matrix of the critical Hessian of a `C²` function is positive definite exactly when the
critical Hessian is positive definite. -/
theorem _root_.Module.Basis.criticalHessianMatrix_posDef_iff
    (b : Module.Basis ι ℝ (TangentSpace I x))
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    (b.criticalHessianMatrix f).PosDef ↔ ∀ v ≠ 0, 0 < criticalHessian I f x v v := by
  simp only [Matrix.posDef_iff_dotProduct_mulVec, star_trivial, Matrix.isHermitian_iff_isSymm,
    b.criticalHessianMatrix_isSymm hf, true_and]
  refine ⟨fun h v hv ↦ ?_, fun h c hc ↦ ?_⟩
  · rw [b.criticalHessian_eq_dotProduct_criticalHessianMatrix_mulVec]
    exact h ((not_congr Finsupp.coe_eq_zero).mpr (b.repr.map_ne_zero_iff.mpr hv))
  · have hpos := h _ (b.equivFun.symm.map_ne_zero_iff.mpr hc)
    rwa [b.criticalHessian_eq_dotProduct_criticalHessianMatrix_mulVec, ← b.equivFun_apply,
      b.equivFun.apply_symm_apply] at hpos

/-- The negated matrix of the critical Hessian of a `C²` function is positive definite exactly when
the critical Hessian is negative definite. -/
theorem _root_.Module.Basis.neg_criticalHessianMatrix_posDef_iff
    (b : Module.Basis ι ℝ (TangentSpace I x))
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    (-b.criticalHessianMatrix f).PosDef ↔ ∀ v ≠ 0, criticalHessian I f x v v < 0 := by
  have hf' : ContMDiffAt I 𝓘(ℝ) 2 (-f) x := contDiff_neg.contMDiff.contMDiffAt.comp x hf
  rw [← b.criticalHessianMatrix_neg, b.criticalHessianMatrix_posDef_iff hf']
  simp only [criticalHessian_neg, neg_apply, neg_pos]

/-- In a tangent-space basis, nondegeneracy of a critical point is equivalent to `C²` regularity,
vanishing differential, and a nonzero determinant of the critical Hessian matrix. -/
theorem _root_.Module.Basis.isManifoldNondegenerateCriticalPoint_iff_det_criticalHessianMatrix
    (b : Module.Basis ι ℝ (TangentSpace I x)) :
    IsManifoldNondegenerateCriticalPoint I f x ↔
      ContMDiffAt I 𝓘(ℝ) 2 f x ∧ mvfderiv I f x = 0 ∧ (b.criticalHessianMatrix f).det ≠ 0 := by
  rw [isManifoldNondegenerateCriticalPoint_iff_criticalHessian,
    b.criticalHessian_isInvertible_iff_det_ne_zero]

end Matrix

/-- A function with a nondegenerate critical point on a boundaryless manifold is `C²` there. -/
theorem IsManifoldNondegenerateCriticalPoint.contMDiffAt
    (h : IsManifoldNondegenerateCriticalPoint I f x) : ContMDiffAt I 𝓘(ℝ) 2 f x :=
  (isManifoldNondegenerateCriticalPoint_iff_criticalHessian.mp h).1

/-- The differential of a function vanishes at a nondegenerate critical point. -/
theorem IsManifoldNondegenerateCriticalPoint.mvfderiv_eq_zero
    (h : IsManifoldNondegenerateCriticalPoint I f x) : mvfderiv I f x = 0 :=
  (isManifoldNondegenerateCriticalPoint_iff_criticalHessian.mp h).2.1

/-- At a critical point, differentiating `df(Y)` in a tangent direction computes the critical
Hessian against `Y x`. The derivative of the vector field contributes nothing because `df = 0`.
In particular this expression depends only on the value of `Y` at the point. -/
theorem criticalHessian_apply_eq_mvfderiv [IsManifold I 2 M]
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hcrit : mvfderiv I f x = 0)
    {Y : (y : M) → TangentSpace I y}
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (v : TangentSpace I x) :
    criticalHessian I f x v (Y x) = mvfderiv I (fun y ↦ mvfderiv I f y (Y y)) x v := by
  -- In the preferred chart, the field is a differentiable map into the model vector space.
  let ψ := extChartAt I x
  let g := f ∘ ψ.symm
  let V : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I ψ.symm Y (range I)
  have hg : ContDiffAt ℝ 2 g (ψ x) := hf.contDiffAt_comp_extChartAt_symm
  have hDg : DifferentiableAt ℝ (fderiv ℝ g) (ψ x) :=
    (hg.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt one_ne_zero
  have hV : DifferentiableAt ℝ V (ψ x) := by
    have h := MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_extChartAt_symm
      (hY.mdifferentiableWithinAt (s := univ))
    have h' : DifferentiableWithinAt ℝ V univ (ψ x) := by
      simpa only [V, preimage_univ, univ_inter,
        ModelWithCorners.Boundaryless.range_eq_univ] using h
    exact h'.differentiableAt univ_mem
  -- The first-order chain rule identifies the coordinate directional derivative with `df(Y)`.
  have heq : (fun z ↦ fderiv ℝ g z (V z)) =ᶠ[𝓝 (ψ x)]
      (fun y ↦ mvfderiv I f y (Y y)) ∘ ψ.symm := by
    simpa only [g, V, ψ, ModelWithCorners.Boundaryless.range_eq_univ, nhdsWithin_univ,
      fderivWithin_univ] using
      eventuallyEq_fderivWithin_chart_apply_mpullbackWithin (U := Y) hf (by norm_num)
  -- Differentiating once more leaves only `D²g`: the term involving `DV` is multiplied by `Dg=0`.
  have hmd : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I f y (Y y)) x :=
    ((hf.contMDiffAt_mvfderiv_apply (m := 1) (by norm_num)).mdifferentiableAt one_ne_zero).comp x hY
  have hzero : fderiv ℝ g (ψ x) = 0 := by
    rwa [← (hf.mdifferentiableAt two_ne_zero).mvfderiv_eq_fderiv_comp_extChartAt_symm]
  rw [criticalHessian_def, hmd.mvfderiv_eq_fderiv_comp_extChartAt_symm, ← heq.fderiv_eq,
    fderiv_clm_apply hDg hV]
  have hVx : V (ψ x) = Y x := VectorField.mpullbackWithin_extChartAt_symm_self Y x
  simp only [hzero, ContinuousLinearMap.zero_comp, zero_add, hVx]
  exact (ContinuousLinearMap.flip_apply (fderiv ℝ (fderiv ℝ g) (ψ x)) v (Y x)).symm

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

omit hx in
/-- A nondegenerate critical point of the coordinate expression in the target of a chart of the
`C²` maximal atlas gives a nondegenerate critical point at its inverse image. -/
theorem isManifoldNondegenerateCriticalPoint_symm_of_mem_maximalAtlas
    {v : E} (hv : v ∈ (e.extend I).target)
    (h : IsNondegenerateCriticalPoint (f ∘ (e.extend I).symm) v) :
    IsManifoldNondegenerateCriticalPoint I f ((e.extend I).symm v) := by
  have hs : (e.extend I).symm v ∈ e.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (e.extend I).map_target hv
  apply (isManifoldNondegenerateCriticalPoint_iff_of_mem_maximalAtlas he hs).mpr
  simpa only [(e.extend I).right_inv hv] using h

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

omit hx in
/-- At a nondegenerate critical point in a chart's target, the coordinate Morse index equals
the manifold Morse index at its inverse image. -/
theorem manifoldMorseIndex_symm_eq_morseIndex_of_mem_maximalAtlas
    {v : E} (hv : v ∈ (e.extend I).target)
    (h : IsNondegenerateCriticalPoint (f ∘ (e.extend I).symm) v) :
    manifoldMorseIndex I f ((e.extend I).symm v) =
      morseIndex (f ∘ (e.extend I).symm) v := by
  have hs : (e.extend I).symm v ∈ e.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (e.extend I).map_target hv
  have hnd := isManifoldNondegenerateCriticalPoint_symm_of_mem_maximalAtlas he hv h
  rw [manifoldMorseIndex_eq_morseIndex_of_mem_maximalAtlas he hs hnd.contMDiffAt
    hnd.mvfderiv_eq_zero, (e.extend I).right_inv hv]

end Chart

end Boundaryless

end TauCeti
