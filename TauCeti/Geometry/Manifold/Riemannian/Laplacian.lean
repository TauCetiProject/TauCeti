/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.VectorSpace
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Divergence, Hessian, and Laplace–Beltrami operators

This file introduces the pointwise Riemannian divergence as the trace of the Levi–Civita
covariant derivative, the scalar Hessian obtained by pairing that derivative of the gradient,
and the Laplace–Beltrami operator with the convention `Δ = div ∘ grad`.  The orthonormal-basis
trace formula makes the relationship between the Laplacian and the Hessian explicit. On a
finite-dimensional inner-product space, the operator agrees with Mathlib's flat Laplacian.

-/

noncomputable section
public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- The Riemannian divergence of a vector field, defined as the trace of its
Levi–Civita covariant derivative. -/
noncomputable def divergence (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (X : (x : M) → TangentSpace I x) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x)
    (CovariantDerivative.leviCivitaConnection I M X x).toLinearMap

theorem divergence_def (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (X : (x : M) → TangentSpace I x) (x : M) :
    divergence I X x =
      LinearMap.trace ℝ (TangentSpace I x)
        (CovariantDerivative.leviCivitaConnection I M X x).toLinearMap := by
  rw [divergence]

/-- The scalar Hessian of `f`, pairing the covariant derivative of its gradient with a second
tangent vector. -/
noncomputable def hessian (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w : TangentSpace I x) : ℝ :=
  inner ℝ (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x v) w

theorem hessian_def (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    hessian I f x v w =
      inner ℝ (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x v) w := by
  rw [hessian]

section HessianSymmetry

variable {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The Hessian of a smooth function is symmetric for the Levi–Civita connection. The proof
compares the two metric product rules for the gradient and uses vanishing torsion. -/
theorem hessian_symm [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) (v w : TangentSpace I x) :
    hessian I f x v w = hessian I f x w v := by
  let V : (y : M) → TangentSpace I y := FiberBundle.extend E v
  let W : (y : M) → TangentSpace I y := FiberBundle.extend E w
  have hV : MDiffAt (T% V) x := FiberBundle.mdifferentiableAt_extend I E v
  have hW : MDiffAt (T% W) x := FiberBundle.mdifferentiableAt_extend I E w
  let _ : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hG : ContMDiff I I.tangent ∞
      (fun y ↦ (⟨y, mgradient I f y⟩ : TangentBundle I M)) :=
    contMDiff_mgradient hf
  have hG' : MDiffAt (T% (mgradient I f)) x := hG.mdifferentiableAt (by simp)
  -- Metric compatibility rewrites the two derivatives of the gradient pairing.
  have hinnerW :=
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
      V hG' hW
  have hinnerV :=
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
      W hG' hV
  have hinnerW' : (fun y ↦ inner ℝ (mgradient I f y) (W y)) =
      (fun y ↦ mvfderiv I f y (W y)) := by
    funext y
    exact inner_mgradient (I := I) (f := f) (x := y) (W y)
  have hinnerV' : (fun y ↦ inner ℝ (mgradient I f y) (V y)) =
      (fun y ↦ mvfderiv I f y (V y)) := by
    funext y
    exact inner_mgradient (I := I) (f := f) (x := y) (V y)
  have hinnerW2 := hinnerW
  have hinnerV2 := hinnerV
  rw [hinnerW'] at hinnerW2
  rw [hinnerV'] at hinnerV2
  clear hinnerW hinnerV
  have hmin : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by simp
  let _ : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) hmin
  -- The mixed-derivative identity and torsion-freeness identify the remaining bracket term.
  have hbracket := mvfderiv_mlieBracket (I := I) (𝕜 := ℝ) (F := ℝ)
    hf.contMDiffAt (by simp) hV hW
  have hzero :
      (CovariantDerivative.leviCivitaConnection I M).torsion x (V x) (W x) = 0 := by
    rw [CovariantDerivative.torsion_leviCivitaConnection_eq_zero I]
    simp
  have htw := CovariantDerivative.torsion_apply
    (CovariantDerivative.leviCivitaConnection I M) hV hW
  rw [hzero] at htw
  have htw' :
      CovariantDerivative.leviCivitaConnection I M W x (V x) -
          CovariantDerivative.leviCivitaConnection I M V x (W x) =
        VectorField.mlieBracket I V W x := by
    exact sub_eq_zero.mp htw.symm
  have hinnerW3 :
      mvfderiv I (fun y ↦ mvfderiv I f y (W y)) x (V x) =
        inner ℝ (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x (V x))
          (W x) + inner ℝ (mgradient I f x)
            (CovariantDerivative.leviCivitaConnection I M W x (V x)) := by
    simpa only [Function.comp_apply] using hinnerW2
  have hinnerV3 :
      mvfderiv I (fun y ↦ mvfderiv I f y (V y)) x (W x) =
        inner ℝ (CovariantDerivative.leviCivitaConnection I M (mgradient I f) x (W x))
          (V x) + inner ℝ (mgradient I f x)
            (CovariantDerivative.leviCivitaConnection I M V x (W x)) := by
    simpa only [Function.comp_apply] using hinnerV2
  have hgradbracket : inner ℝ (mgradient I f x) (VectorField.mlieBracket I V W x) =
      mvfderiv I f x (VectorField.mlieBracket I V W x) :=
    inner_mgradient (I := I) (f := f) (x := x) _
  dsimp [V, W] at hinnerW3 hinnerV3 htw' hbracket
  simp only [FiberBundle.extend_apply_self] at hinnerW3 hinnerV3 htw' hbracket
  rw [← hgradbracket] at hbracket
  dsimp [hessian]
  -- The two metric-compatibility equations now differ only by the torsion equation.
  have htw_inner := congrArg (fun z ↦ inner ℝ (mgradient I f x) z) htw'
  simp only [inner_sub_right] at htw_inner
  linarith [hinnerW3, hinnerV3, hbracket, htw_inner]

end HessianSymmetry

/-- The Laplace–Beltrami operator, with the sign convention `Δ = div ∘ grad`. -/
noncomputable def laplaceBeltrami (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) : ℝ :=
  divergence I (mgradient I f) x

theorem laplaceBeltrami_def (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) :
    laplaceBeltrami I f x = divergence I (mgradient I f) x := by
  rw [laplaceBeltrami]

section OperatorLaws

variable (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The divergence of the zero vector field is zero. -/
@[simp]
theorem divergence_zero (x : M) : divergence I 0 x = 0 := by
  simp [divergence]

/-- Divergence is additive at a point where both vector fields are differentiable. -/
theorem divergence_add (X Y : (x : M) → TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M)) x) :
    divergence I (X + Y) x = divergence I X x + divergence I Y x := by
  simp only [divergence,
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.add hX hY,
    ContinuousLinearMap.toLinearMap_add, map_add]

/-- Divergence commutes with a real constant at a differentiability point of the field. -/
theorem divergence_smul (c : ℝ) (X : (x : M) → TangentSpace I x) (x : M)
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x) :
    divergence I (c • X) x = c * divergence I X x := by
  simp [divergence,
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.smul_const c hX,
    ContinuousLinearMap.toLinearMap_smul]

/-- The Hessian of a constant function is zero. -/
@[simp]
theorem hessian_const (c : ℝ) (x : M) (v w : TangentSpace I x) :
    hessian I (fun _ : M ↦ c) x v w = 0 := by
  simp [hessian]

/-- The Hessian of the zero function is zero. -/
@[simp]
theorem hessian_zero (x : M) (v w : TangentSpace I x) :
    hessian I (0 : M → ℝ) x v w = 0 :=
  hessian_const I 0 x v w

/-- The Hessian is additive on twice continuously differentiable functions. -/
theorem hessian_add {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) (v w : TangentSpace I x) :
    hessian I (f + g) x v w = hessian I f x v w + hessian I g x v w := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  simp only [hessian, mgradient_add (hf.mdifferentiable (by simp))
      (hg.mdifferentiable (by simp)),
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      ((contMDiff_mgradient (n := 1)
      (by simpa only [one_add_one_eq_two] using hf)).mdifferentiableAt (by simp))
      ((contMDiff_mgradient (n := 1)
      (by simpa only [one_add_one_eq_two] using hg)).mdifferentiableAt
        (by simp)),
    add_apply, inner_add_left]

/-- The Hessian commutes with multiplication of a `C²` function by a real constant. -/
theorem hessian_smul (c : ℝ) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (x : M) (v w : TangentSpace I x) :
    hessian I (c • f) x v w = c * hessian I f x v w := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  simp only [hessian, mgradient_smul c (hf.mdifferentiable (by simp)),
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.smul_const c
      ((contMDiff_mgradient (n := 1)
      (by simpa only [one_add_one_eq_two] using hf)).mdifferentiableAt
        (by simp)),
    smul_apply, real_inner_smul_left]

/-- The Laplace–Beltrami operator vanishes on constants. -/
@[simp]
theorem laplaceBeltrami_const (c : ℝ) (x : M) :
    laplaceBeltrami I (fun _ : M ↦ c) x = 0 := by
  simp [laplaceBeltrami]

/-- The Laplace–Beltrami operator vanishes on the zero function. -/
@[simp]
theorem laplaceBeltrami_zero (x : M) : laplaceBeltrami I (0 : M → ℝ) x = 0 :=
  laplaceBeltrami_const I 0 x

/-- The Laplace–Beltrami operator is additive on `C²` functions. -/
theorem laplaceBeltrami_add {f g : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) :
    laplaceBeltrami I (f + g) x = laplaceBeltrami I f x + laplaceBeltrami I g x := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  simp only [laplaceBeltrami,
    mgradient_add (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp))]
  exact divergence_add I _ _ x
    ((contMDiff_mgradient (n := 1)
      (by simpa only [one_add_one_eq_two] using hf)).mdifferentiableAt (by simp))
    ((contMDiff_mgradient (n := 1)
      (by simpa only [one_add_one_eq_two] using hg)).mdifferentiableAt (by simp))

/-- The Laplace–Beltrami operator commutes with real scalar multiplication on `C²` functions. -/
theorem laplaceBeltrami_smul (c : ℝ) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f) (x : M) :
    laplaceBeltrami I (c • f) x = c * laplaceBeltrami I f x := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  simp only [laplaceBeltrami, mgradient_smul c (hf.mdifferentiable (by simp))]
  exact divergence_smul I c _ x
    ((contMDiff_mgradient (n := 1)
      (by simpa only [one_add_one_eq_two] using hf)).mdifferentiableAt (by simp))

end OperatorLaws

/-- In any orthonormal basis, the divergence is the sum of the diagonal inner products of the
covariant derivative of the vector field. -/
theorem divergence_eq_sum_inner (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {ι : Type*} [Fintype ι] (X : (x : M) → TangentSpace I x) (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    divergence I X x = ∑ i, inner ℝ
      (CovariantDerivative.leviCivitaConnection I M X x (b i)) (b i) := by
  rw [divergence, LinearMap.trace_eq_sum_inner _ b]
  simp only [real_inner_comm]
  rfl

@[simp] theorem hessian_add_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v₁ v₂ w : TangentSpace I x) :
    hessian I f x (v₁ + v₂) w = hessian I f x v₁ w + hessian I f x v₂ w := by
  simp only [hessian, map_add, inner_add_left]

@[simp] theorem hessian_smul_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (r : ℝ) (v w : TangentSpace I x) :
    hessian I f x (r • v) w = r * hessian I f x v w := by
  simp only [hessian, map_smul, real_inner_smul_left]

@[simp] theorem hessian_zero_left (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (w : TangentSpace I x) :
    hessian I f x 0 w = 0 := by
  simp only [hessian, map_zero, inner_zero_left]

@[simp] theorem hessian_add_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v w₁ w₂ : TangentSpace I x) :
    hessian I f x v (w₁ + w₂) = hessian I f x v w₁ + hessian I f x v w₂ := by
  simp only [hessian, inner_add_right]

@[simp] theorem hessian_smul_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (r : ℝ) (v w : TangentSpace I x) :
    hessian I f x v (r • w) = r * hessian I f x v w := by
  simp only [hessian, real_inner_smul_right]

@[simp] theorem hessian_zero_right (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    hessian I f x v 0 = 0 := by
  simp only [hessian, inner_zero_right]

/-- The Laplace–Beltrami operator is the trace of the scalar Hessian in every orthonormal basis. -/
theorem laplaceBeltrami_eq_sum_hessian (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 2 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    {ι : Type*} [Fintype ι] (f : M → ℝ) (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    laplaceBeltrami I f x = ∑ i, hessian I f x (b i) (b i) := by
  rw [laplaceBeltrami, divergence, LinearMap.trace_eq_sum_inner _ b]
  simp only [hessian, real_inner_comm]
  rfl

/-! ### The flat model -/

open scoped Gradient Laplacian

/-- On a finite-dimensional real inner-product space with its standard metric, the Riemannian
Hessian is the second Fréchet derivative. -/
theorem hessian_eq_iteratedFDeriv_model_space
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f : F → ℝ} {x : F} (hgrad : DifferentiableAt ℝ (∇ f) x)
    (v w : TangentSpace (modelWithCornersSelf ℝ F) x) :
    hessian (modelWithCornersSelf ℝ F) f x v w =
      iteratedFDeriv ℝ 2 f x
        ![NormedSpace.fromTangentSpace x v, NormedSpace.fromTangentSpace x w] := by
  rw [hessian]
  have hm : mgradient (modelWithCornersSelf ℝ F) f = ∇ f :=
    funext fun y ↦ mgradient_eq_gradient f y
  have hmgrad : DifferentiableAt ℝ (mgradient (modelWithCornersSelf ℝ F) f) x := by
    rw [hm]
    exact hgrad
  have hconnection := leviCivitaConnection_eq_fderiv_model_space hmgrad
    (NormedSpace.fromTangentSpace x v)
  have hconnection' :
      NormedSpace.fromTangentSpace x
          (CovariantDerivative.leviCivitaConnection (modelWithCornersSelf ℝ F) F
            (mgradient (modelWithCornersSelf ℝ F) f) x v) =
        fderiv ℝ (mgradient (modelWithCornersSelf ℝ F) f) x
          (NormedSpace.fromTangentSpace x v) := by
    simpa only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.symm_apply_apply] using
      hconnection
  calc
    inner ℝ
        (CovariantDerivative.leviCivitaConnection (modelWithCornersSelf ℝ F) F
          (mgradient (modelWithCornersSelf ℝ F) f) x v) w =
        inner ℝ
          (NormedSpace.fromTangentSpace x
            (CovariantDerivative.leviCivitaConnection (modelWithCornersSelf ℝ F) F
              (mgradient (modelWithCornersSelf ℝ F) f) x v))
          (NormedSpace.fromTangentSpace x w) :=
      inner_tangentSpace_vectorSpace _ _
    _ = inner ℝ
        (fderiv ℝ (mgradient (modelWithCornersSelf ℝ F) f) x
          (NormedSpace.fromTangentSpace x v))
        (NormedSpace.fromTangentSpace x w) := by rw [hconnection']
    _ = inner ℝ (fderiv ℝ (∇ f) x (NormedSpace.fromTangentSpace x v))
        (NormedSpace.fromTangentSpace x w) := by rw [hm]
    _ = _ := by
      rw [← InnerProductSpace.toDual_apply_apply]
      calc
        ((InnerProductSpace.toDual ℝ F)
            (fderiv ℝ (∇ f) x (NormedSpace.fromTangentSpace x v)))
            (NormedSpace.fromTangentSpace x w) =
            fderiv ℝ ((InnerProductSpace.toDual ℝ F) ∘ ∇ f) x
              (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) := by
                rw [(InnerProductSpace.toDual ℝ F).comp_fderiv]
                rfl
        _ = fderiv ℝ (fderiv ℝ f) x (NormedSpace.fromTangentSpace x v)
            (NormedSpace.fromTangentSpace x w) := by rw [toDual_comp_gradient]
        _ = _ := (iteratedFDeriv_two_apply f x
          ![NormedSpace.fromTangentSpace x v, NormedSpace.fromTangentSpace x w]).symm

/-- The Laplace–Beltrami operator of the standard Riemannian metric is Mathlib's flat Laplacian.
This fixes the sign convention as `Δ = div ∘ grad`. -/
theorem laplaceBeltrami_eq_laplacian
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f : F → ℝ} {x : F} (hgrad : DifferentiableAt ℝ (∇ f) x) :
    laplaceBeltrami (modelWithCornersSelf ℝ F) f x = Δ f x := by
  let e : TangentSpace (modelWithCornersSelf ℝ F) x ≃ₗᵢ[ℝ] F :=
    (NormedSpace.fromTangentSpace x).toLinearEquiv.isometryOfInner
      inner_tangentSpace_vectorSpace
  let b := (stdOrthonormalBasis ℝ F).map e.symm
  rw [laplaceBeltrami_eq_sum_hessian (modelWithCornersSelf ℝ F) f x b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ F)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have he (u : F) : NormedSpace.fromTangentSpace x (e.symm u) = u := e.apply_symm_apply u
  simpa only [b, OrthonormalBasis.map_apply, he] using
    hessian_eq_iteratedFDeriv_model_space hgrad (b i) (b i)

end TauCeti.Manifold
