/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondBianchi
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# The covariant derivative of the curvature tensor

Let `∇` be a smooth connection on a finite-rank vector bundle `V` with curvature tensor `R`, and
let `∇ᵀ` be a connection on the tangent bundle. The covariant derivative of the curvature is

`(∇_X R)(Y, Z) σ = ∇_X (R(Y, Z) σ) - R(∇ᵀ_X Y, Z) σ - R(Y, ∇ᵀ_X Z) σ - R(Y, Z) (∇_X σ)`.

Its value at a point depends only on the values of `X`, `Y`, `Z` and `σ` there, so it is a
pointwise tensor, `CovariantDerivative.derivCurvatureTensor`, linear in three tangent vectors and
one bundle vector. On the tangent bundle with `∇ = ∇ᵀ` this is the classical tensor `∇R` of an
affine connection, whose vanishing defines local symmetry, and which enters the contracted Bianchi
identity and the normal-coordinate expansion of a Riemannian metric.

The construction uses globally smooth extensions of fibre vectors and the tensoriality criterion
`TauCeti.Manifold.eq_of_contMDiff_tensorial`. Its characteristic equation
`derivCurvatureTensor_apply` evaluates it on any smooth fields and section. In this form the second
Bianchi identity `covariantDerivative_curvatureOperator_cyclic_eq_zero` becomes the pointwise
identity `derivCurvatureTensor_cyclic_eq_zero`.

## Main definitions and results

* `CovariantDerivative.derivCurvatureTensor`: the covariant derivative `∇R` of the curvature
  tensor, with `derivCurvatureTensor cov covT x v u w s = (∇_v R)(u, w) s`.
* `CovariantDerivative.derivCurvatureTensor_apply` and
  `CovariantDerivative.derivCurvatureTensor_apply_eq_curvatureOperator`: its value on smooth
  fields and sections.
* `CovariantDerivative.derivCurvatureTensor_antisymm`: `∇R` is antisymmetric in its two curvature
  arguments.
* `CovariantDerivative.derivCurvatureTensor_cyclic_eq_zero`: the **second Bianchi identity**
  `(∇_u R)(v, w) + (∇_v R)(w, u) + (∇_w R)(u, v) = 0`, for a torsion-free `∇ᵀ`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7,
  Proposition 7.5 (the differential Bianchi identity, with `∇R` as a tensor field).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- The expression `(∇_v R)(Y, Z) σ` on sections, at the point `x`;
`CovariantDerivative.derivCurvatureTensor` is the tensor it induces. -/
private def derivCurvatureAux (Y Z : Π y : M, TangentSpace I y) (σ : Π y : M, V y) (x : M)
    (v : TangentSpace I x) : V x :=
  cov (fun y ↦ cov.curvatureTensor y (Y y) (Z y) (σ y)) x v -
    cov.curvatureTensor x (covT Y x v) (Z x) (σ x) -
      cov.curvatureTensor x (Y x) (covT Z x v) (σ x) -
        cov.curvatureTensor x (Y x) (Z x) (cov σ x v)

variable {cov covT} {Y Y' Z : Π y : M, TangentSpace I y} {σ σ' : Π y : M, V y} {x : M}

/-- On smooth inputs, the section `y ↦ R(Y y, Z y) (σ y)` is differentiable. -/
private theorem mdifferentiable_curvatureTensor_apply (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) :
    MDiff (T% (fun y ↦ cov.curvatureTensor y (Y y) (Z y) (σ y))) := by
  have h (y : M) : cov.curvatureTensor y (Y y) (Z y) (σ y) = curvatureOperator cov Y Z σ y :=
    curvatureTensor_apply cov y hY hZ hσ
  simp only [h]
  exact (contMDiff_curvatureOperator cov hY hZ hσ).mdifferentiable (by simp)

private theorem derivCurvatureAux_antisymm (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hσ : CMDiff ∞ (T% σ)) :
    derivCurvatureAux cov covT Y Z σ x = -derivCurvatureAux cov covT Z Y σ x := by
  funext v
  have h : (fun y ↦ cov.curvatureTensor y (Y y) (Z y) (σ y)) =
      -fun y ↦ cov.curvatureTensor y (Z y) (Y y) (σ y) := by
    funext y
    simp only [curvatureTensor_antisymm cov y (Y y), LinearMap.neg_apply, Pi.neg_apply]
  simp only [derivCurvatureAux]
  rw [h, cov.isCovariantDerivativeOnUniv.neg (mdifferentiable_curvatureTensor_apply hZ hY hσ x)]
  simp only [derivCurvatureAux, Pi.neg_apply, curvatureTensor_antisymm cov x (Y x),
    curvatureTensor_antisymm cov x (covT Y x v), neg_apply, LinearMap.neg_apply]
  abel

private theorem derivCurvatureAux_congr_of_eventuallyEq_first (hY : CMDiff ∞ (T% Y))
    (hY' : CMDiff ∞ (T% Y')) (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ))
    (hYY' : ∀ᶠ y in nhds x, Y y = Y' y) :
    derivCurvatureAux cov covT Y Z σ x = derivCurvatureAux cov covT Y' Z σ x := by
  funext v
  have hR : ∀ᶠ y in nhds x, cov.curvatureTensor y (Y y) (Z y) (σ y) =
      cov.curvatureTensor y (Y' y) (Z y) (σ y) := hYY'.mono fun y hy ↦ by rw [hy]
  simp only [derivCurvatureAux]
  rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      (mdifferentiable_curvatureTensor_apply hY hZ hσ x)
      (mdifferentiable_curvatureTensor_apply hY' hZ hσ x) Filter.univ_mem hR,
    covT.isCovariantDerivativeOn.congr_of_eventuallyEq (hY.mdifferentiableAt (by simp))
      (hY'.mdifferentiableAt (by simp)) Filter.univ_mem hYY', hYY'.self_of_nhds]

private theorem derivCurvatureAux_add_first (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) :
    derivCurvatureAux cov covT (Y + Y') Z σ x =
      derivCurvatureAux cov covT Y Z σ x + derivCurvatureAux cov covT Y' Z σ x := by
  funext v
  have h : (fun y ↦ cov.curvatureTensor y ((Y + Y') y) (Z y) (σ y)) =
      (fun y ↦ cov.curvatureTensor y (Y y) (Z y) (σ y)) +
        fun y ↦ cov.curvatureTensor y (Y' y) (Z y) (σ y) := by
    funext y
    simp
  simp only [derivCurvatureAux]
  rw [h, cov.isCovariantDerivativeOnUniv.add (mdifferentiable_curvatureTensor_apply hY hZ hσ x)
      (mdifferentiable_curvatureTensor_apply hY' hZ hσ x),
    covT.isCovariantDerivativeOnUniv.add (hY.mdifferentiableAt (by simp))
      (hY'.mdifferentiableAt (by simp))]
  simp only [derivCurvatureAux, Pi.add_apply, add_apply, map_add, LinearMap.add_apply]
  abel

private theorem derivCurvatureAux_smul_first {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) :
    derivCurvatureAux cov covT (f • Y) Z σ x = f x • derivCurvatureAux cov covT Y Z σ x := by
  funext v
  have h : (fun y ↦ cov.curvatureTensor y ((f • Y) y) (Z y) (σ y)) =
      f • fun y ↦ cov.curvatureTensor y (Y y) (Z y) (σ y) := by
    funext y
    simp
  simp only [derivCurvatureAux]
  rw [h, cov.isCovariantDerivativeOnUniv.leibniz
      (mdifferentiable_curvatureTensor_apply hY hZ hσ x) (hf.mdifferentiableAt (by simp)),
    covT.isCovariantDerivativeOnUniv.leibniz (hY.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
  simp only [derivCurvatureAux, Pi.smul_apply, Pi.smul_apply', add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply]
  module

private theorem derivCurvatureAux_congr_of_eventuallyEq_section (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) (hσ' : CMDiff ∞ (T% σ'))
    (hσσ' : ∀ᶠ y in nhds x, σ y = σ' y) :
    derivCurvatureAux cov covT Y Z σ x = derivCurvatureAux cov covT Y Z σ' x := by
  funext v
  have hR : ∀ᶠ y in nhds x, cov.curvatureTensor y (Y y) (Z y) (σ y) =
      cov.curvatureTensor y (Y y) (Z y) (σ' y) := hσσ'.mono fun y hy ↦ by rw [hy]
  simp only [derivCurvatureAux]
  rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      (mdifferentiable_curvatureTensor_apply hY hZ hσ x)
      (mdifferentiable_curvatureTensor_apply hY hZ hσ' x) Filter.univ_mem hR,
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq (hσ.mdifferentiableAt (by simp))
      (hσ'.mdifferentiableAt (by simp)) Filter.univ_mem hσσ', hσσ'.self_of_nhds]

private theorem derivCurvatureAux_add_section (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hσ : CMDiff ∞ (T% σ)) (hσ' : CMDiff ∞ (T% σ')) :
    derivCurvatureAux cov covT Y Z (σ + σ') x =
      derivCurvatureAux cov covT Y Z σ x + derivCurvatureAux cov covT Y Z σ' x := by
  funext v
  have h : (fun y ↦ cov.curvatureTensor y (Y y) (Z y) ((σ + σ') y)) =
      (fun y ↦ cov.curvatureTensor y (Y y) (Z y) (σ y)) +
        fun y ↦ cov.curvatureTensor y (Y y) (Z y) (σ' y) := by
    funext y
    simp
  simp only [derivCurvatureAux]
  rw [h, cov.isCovariantDerivativeOnUniv.add (mdifferentiable_curvatureTensor_apply hY hZ hσ x)
      (mdifferentiable_curvatureTensor_apply hY hZ hσ' x),
    cov.isCovariantDerivativeOnUniv.add (hσ.mdifferentiableAt (by simp))
      (hσ'.mdifferentiableAt (by simp))]
  simp only [derivCurvatureAux, Pi.add_apply, add_apply, map_add]
  abel

private theorem derivCurvatureAux_smul_section {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) :
    derivCurvatureAux cov covT Y Z (f • σ) x = f x • derivCurvatureAux cov covT Y Z σ x := by
  funext v
  have h : (fun y ↦ cov.curvatureTensor y (Y y) (Z y) ((f • σ) y)) =
      f • fun y ↦ cov.curvatureTensor y (Y y) (Z y) (σ y) := by
    funext y
    simp
  simp only [derivCurvatureAux]
  rw [h, cov.isCovariantDerivativeOnUniv.leibniz
      (mdifferentiable_curvatureTensor_apply hY hZ hσ x) (hf.mdifferentiableAt (by simp)),
    cov.isCovariantDerivativeOnUniv.leibniz (hσ.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
  simp only [derivCurvatureAux, Pi.smul_apply, Pi.smul_apply', add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul]
  module

/-- On smooth inputs, `(∇_v R)(Y, Z) σ` at `x` depends only on `Y x`, `Z x` and `σ x`. -/
private theorem derivCurvatureAux_congr {Z' : Π y : M, TangentSpace I y}
    (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y')) (hZ : CMDiff ∞ (T% Z))
    (hZ' : CMDiff ∞ (T% Z')) (hσ : CMDiff ∞ (T% σ)) (hσ' : CMDiff ∞ (T% σ'))
    (hYY' : Y x = Y' x) (hZZ' : Z x = Z' x) (hσσ' : σ x = σ' x) :
    derivCurvatureAux cov covT Y Z σ x = derivCurvatureAux cov covT Y' Z' σ' x := by
  -- Tensoriality in the first argument, for any smooth second argument; the second argument
  -- follows by antisymmetry.
  have hfirst {A A' B : Π y : M, TangentSpace I y} (hA : CMDiff ∞ (T% A))
      (hA' : CMDiff ∞ (T% A')) (hB : CMDiff ∞ (T% B)) (hAA' : A x = A' x) :
      derivCurvatureAux cov covT A B σ x = derivCurvatureAux cov covT A' B σ x :=
    TauCeti.Manifold.eq_of_contMDiff_tensorial (G := E) (W := TangentSpace I)
      (fun C ↦ derivCurvatureAux cov covT C B σ x) x
      (fun hC hC' hCC' ↦ derivCurvatureAux_congr_of_eventuallyEq_first hC hC' hB hσ hCC')
      (fun hC hC' ↦ derivCurvatureAux_add_first hC hC' hB hσ)
      (fun hf hC ↦ derivCurvatureAux_smul_first hf hC hB hσ) hA hA' hAA'
  calc derivCurvatureAux cov covT Y Z σ x
      = derivCurvatureAux cov covT Y' Z σ x := hfirst hY hY' hZ hYY'
    _ = derivCurvatureAux cov covT Y' Z' σ x := by
      rw [derivCurvatureAux_antisymm hY' hZ hσ, derivCurvatureAux_antisymm hY' hZ' hσ,
        hfirst hZ hZ' hY' hZZ']
    _ = derivCurvatureAux cov covT Y' Z' σ' x :=
      TauCeti.Manifold.eq_of_contMDiff_tensorial (G := F) (W := V)
        (fun τ ↦ derivCurvatureAux cov covT Y' Z' τ x) x
        (fun hτ hτ' hττ' ↦ derivCurvatureAux_congr_of_eventuallyEq_section hY' hZ' hτ hτ' hττ')
        (fun hτ hτ' ↦ derivCurvatureAux_add_section hY' hZ' hτ hτ')
        (fun hf hτ ↦ derivCurvatureAux_smul_section hf hY' hZ' hτ) hσ hσ' hσσ'

variable (cov covT)

/-- The value of `∇R` on fibre vectors, computed on chosen smooth extensions. -/
private def derivCurvatureValue (x : M) (v u w : TangentSpace I x) (s : V x) : V x :=
  derivCurvatureAux cov covT
    (Classical.choose (exists_contMDiff_section_eq I E u))
    (Classical.choose (exists_contMDiff_section_eq I E w))
    (Classical.choose (exists_contMDiff_section_eq I F s)) x v

private theorem derivCurvatureValue_eq (x : M) (v : TangentSpace I x)
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) :
    derivCurvatureValue cov covT x v (Y x) (Z x) (σ x) = derivCurvatureAux cov covT Y Z σ x v :=
  congrFun (derivCurvatureAux_congr
    (Classical.choose_spec (exists_contMDiff_section_eq I E (Y x))).1 hY
    (Classical.choose_spec (exists_contMDiff_section_eq I E (Z x))).1 hZ
    (Classical.choose_spec (exists_contMDiff_section_eq I F (σ x))).1 hσ
    (Classical.choose_spec (exists_contMDiff_section_eq I E (Y x))).2
    (Classical.choose_spec (exists_contMDiff_section_eq I E (Z x))).2
    (Classical.choose_spec (exists_contMDiff_section_eq I F (σ x))).2) v

private theorem derivCurvatureValue_add_dir (x : M) (v v' u w : TangentSpace I x) (s : V x) :
    derivCurvatureValue cov covT x (v + v') u w s =
      derivCurvatureValue cov covT x v u w s + derivCurvatureValue cov covT x v' u w s := by
  simp only [derivCurvatureValue, derivCurvatureAux, map_add, LinearMap.add_apply]
  abel

private theorem derivCurvatureValue_smul_dir (x : M) (c : ℝ) (v u w : TangentSpace I x)
    (s : V x) :
    derivCurvatureValue cov covT x (c • v) u w s = c • derivCurvatureValue cov covT x v u w s := by
  simp only [derivCurvatureValue, derivCurvatureAux, map_smul, LinearMap.smul_apply, smul_sub]

private theorem derivCurvatureValue_add_first (x : M) (v u u' w : TangentSpace I x) (s : V x) :
    derivCurvatureValue cov covT x v (u + u') w s =
      derivCurvatureValue cov covT x v u w s + derivCurvatureValue cov covT x v u' w s := by
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y', hY', rfl⟩ := exists_contMDiff_section_eq I E u'
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F s
  have h := derivCurvatureValue_eq cov covT x v (hY.add_section hY') hZ hσ
  rw [Pi.add_apply] at h
  rw [h, derivCurvatureAux_add_first hY hY' hZ hσ, Pi.add_apply,
    derivCurvatureValue_eq cov covT x v hY hZ hσ, derivCurvatureValue_eq cov covT x v hY' hZ hσ]

private theorem derivCurvatureValue_smul_first (x : M) (c : ℝ) (v u w : TangentSpace I x)
    (s : V x) :
    derivCurvatureValue cov covT x v (c • u) w s = c • derivCurvatureValue cov covT x v u w s := by
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F s
  have h := derivCurvatureValue_eq cov covT x v
    ((contMDiff_const (c := c)).smul_section hY) hZ hσ
  rw [Pi.smul_apply'] at h
  rw [h, derivCurvatureAux_smul_first contMDiff_const hY hZ hσ, Pi.smul_apply,
    derivCurvatureValue_eq cov covT x v hY hZ hσ]

private theorem derivCurvatureValue_antisymm (x : M) (v u w : TangentSpace I x) (s : V x) :
    derivCurvatureValue cov covT x v u w s = -derivCurvatureValue cov covT x v w u s := by
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F s
  rw [derivCurvatureValue_eq cov covT x v hY hZ hσ, derivCurvatureValue_eq cov covT x v hZ hY hσ,
    derivCurvatureAux_antisymm hY hZ hσ, Pi.neg_apply]

private theorem derivCurvatureValue_add_section (x : M) (v u w : TangentSpace I x) (s s' : V x) :
    derivCurvatureValue cov covT x v u w (s + s') =
      derivCurvatureValue cov covT x v u w s + derivCurvatureValue cov covT x v u w s' := by
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F s
  obtain ⟨σ', hσ', rfl⟩ := exists_contMDiff_section_eq I F s'
  have h := derivCurvatureValue_eq cov covT x v hY hZ (hσ.add_section hσ')
  rw [Pi.add_apply] at h
  rw [h, derivCurvatureAux_add_section hY hZ hσ hσ', Pi.add_apply,
    derivCurvatureValue_eq cov covT x v hY hZ hσ, derivCurvatureValue_eq cov covT x v hY hZ hσ']

private theorem derivCurvatureValue_smul_section (x : M) (c : ℝ) (v u w : TangentSpace I x)
    (s : V x) :
    derivCurvatureValue cov covT x v u w (c • s) = c • derivCurvatureValue cov covT x v u w s := by
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F s
  have h := derivCurvatureValue_eq cov covT x v hY hZ
    ((contMDiff_const (c := c)).smul_section hσ)
  rw [Pi.smul_apply'] at h
  rw [h, derivCurvatureAux_smul_section contMDiff_const hY hZ hσ, Pi.smul_apply,
    derivCurvatureValue_eq cov covT x v hY hZ hσ]

/-- The value of `∇R` at a fixed direction and first curvature argument, as a bilinear map in the
second curvature argument and the bundle vector. -/
private def derivCurvatureBilin (x : M) (v u : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] V x →ₗ[ℝ] V x :=
  LinearMap.mk₂ ℝ (fun w s ↦ derivCurvatureValue cov covT x v u w s)
    (fun w w' s ↦ by
      rw [derivCurvatureValue_antisymm, derivCurvatureValue_add_first, neg_add,
        ← derivCurvatureValue_antisymm, ← derivCurvatureValue_antisymm])
    (fun c w s ↦ by
      rw [derivCurvatureValue_antisymm, derivCurvatureValue_smul_first, ← smul_neg,
        ← derivCurvatureValue_antisymm])
    (fun w s s' ↦ derivCurvatureValue_add_section cov covT x v u w s s')
    (fun c w s ↦ derivCurvatureValue_smul_section cov covT x c v u w s)

/-- The **covariant derivative of the curvature tensor** of a smooth connection `∇` on `V`, taken
with `∇` on `V` and a connection `∇ᵀ` on the tangent bundle: the tensor with
`derivCurvatureTensor cov covT x v u w s = (∇_v R)(u, w) s`, where on smooth fields and sections

`(∇_X R)(Y, Z) σ = ∇_X (R(Y, Z) σ) - R(∇ᵀ_X Y, Z) σ - R(Y, ∇ᵀ_X Z) σ - R(Y, Z) (∇_X σ)`,

by `CovariantDerivative.derivCurvatureTensor_apply`. On the tangent bundle, with `∇ = ∇ᵀ`, this
is the tensor `∇R` of an affine connection. -/
def derivCurvatureTensor (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] V x →ₗ[ℝ] V x :=
  LinearMap.mk₂ ℝ (derivCurvatureBilin cov covT x)
    (fun v v' u ↦ LinearMap.ext₂ fun w s ↦ derivCurvatureValue_add_dir cov covT x v v' u w s)
    (fun c v u ↦ LinearMap.ext₂ fun w s ↦ derivCurvatureValue_smul_dir cov covT x c v u w s)
    (fun v u u' ↦ LinearMap.ext₂ fun w s ↦ derivCurvatureValue_add_first cov covT x v u u' w s)
    (fun c v u ↦ LinearMap.ext₂ fun w s ↦ derivCurvatureValue_smul_first cov covT x c v u w s)

/-- The covariant derivative of the curvature tensor on smooth fields and a smooth section:
`(∇_v R)(Y, Z) σ = ∇_v (R(Y, Z) σ) - R(∇ᵀ_v Y, Z) σ - R(Y, ∇ᵀ_v Z) σ - R(Y, Z) (∇_v σ)`. -/
theorem derivCurvatureTensor_apply (x : M) (v : TangentSpace I x)
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) :
    cov.derivCurvatureTensor covT x v (Y x) (Z x) (σ x) =
      cov (curvatureOperator cov Y Z σ) x v -
        cov.curvatureTensor x (covT Y x v) (Z x) (σ x) -
          cov.curvatureTensor x (Y x) (covT Z x v) (σ x) -
            cov.curvatureTensor x (Y x) (Z x) (cov σ x v) := by
  have h : curvatureOperator cov Y Z σ = fun y ↦ cov.curvatureTensor y (Y y) (Z y) (σ y) :=
    funext fun y ↦ (curvatureTensor_apply cov y hY hZ hσ).symm
  rw [h]
  exact derivCurvatureValue_eq cov covT x v hY hZ hσ

/-- For a smooth connection `∇ᵀ` on the tangent bundle, the covariant derivative of the curvature
tensor along a smooth vector field `X` is given entirely by curvature operators:
`(∇_X R)(Y, Z) σ = ∇_X (R(Y, Z) σ) - R(∇ᵀ_X Y, Z) σ - R(Y, ∇ᵀ_X Z) σ - R(Y, Z) (∇_X σ)`. -/
theorem derivCurvatureTensor_apply_eq_curvatureOperator [ContMDiffCovariantDerivative covT ∞]
    {X : Π y : M, TangentSpace I y} (x : M) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) :
    cov.derivCurvatureTensor covT x (X x) (Y x) (Z x) (σ x) =
      cov (curvatureOperator cov Y Z σ) x (X x) -
        curvatureOperator cov (fun y ↦ covT Y y (X y)) Z σ x -
          curvatureOperator cov Y (fun y ↦ covT Z y (X y)) σ x -
            curvatureOperator cov Y Z (fun y ↦ cov σ y (X y)) x := by
  rw [derivCurvatureTensor_apply cov covT x (X x) hY hZ hσ,
    ← curvatureTensor_apply cov x (covT.contMDiff_apply hX hY) hZ hσ,
    ← curvatureTensor_apply cov x hY (covT.contMDiff_apply hX hZ) hσ,
    ← curvatureTensor_apply cov x hY hZ (cov.contMDiff_apply hX hσ)]

/-- The covariant derivative of the curvature tensor is antisymmetric in its two curvature
arguments: `(∇_v R)(u, w) = -(∇_v R)(w, u)`. -/
theorem derivCurvatureTensor_antisymm (x : M) (v u w : TangentSpace I x) :
    cov.derivCurvatureTensor covT x v u w = -cov.derivCurvatureTensor covT x v w u := by
  ext s
  exact derivCurvatureValue_antisymm cov covT x v u w s

/-- The covariant derivative of the curvature tensor vanishes when its two curvature arguments
coincide. -/
@[simp]
theorem derivCurvatureTensor_self (x : M) (v u : TangentSpace I x) :
    cov.derivCurvatureTensor covT x v u u = 0 := by
  have h := derivCurvatureTensor_antisymm cov covT x v u u
  rwa [eq_neg_iff_add_eq_zero, ← two_smul ℝ, smul_eq_zero, or_iff_right two_ne_zero] at h

/-- **The second Bianchi identity**, pointwise: for a smooth connection `∇` on `V` and a smooth
torsion-free connection `∇ᵀ` on the tangent bundle,
`(∇_u R)(v, w) + (∇_v R)(w, u) + (∇_w R)(u, v) = 0`. -/
theorem derivCurvatureTensor_cyclic_eq_zero [ContMDiffCovariantDerivative covT ∞]
    (ht : covT.torsion = 0) (x : M) (u v w : TangentSpace I x) :
    cov.derivCurvatureTensor covT x u v w + cov.derivCurvatureTensor covT x v w u +
      cov.derivCurvatureTensor covT x w u v = 0 := by
  ext s
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F s
  simp only [LinearMap.add_apply, LinearMap.zero_apply,
    derivCurvatureTensor_apply_eq_curvatureOperator cov covT x hX hY hZ hσ,
    derivCurvatureTensor_apply_eq_curvatureOperator cov covT x hY hZ hX hσ,
    derivCurvatureTensor_apply_eq_curvatureOperator cov covT x hZ hX hY hσ]
  exact covariantDerivative_curvatureOperator_cyclic_eq_zero cov covT
    ((isTorsionFree_iff_torsion_eq_zero covT).2 ht) hX hY hZ hσ x

end CovariantDerivative
