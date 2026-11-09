/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bianchi
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Algebraic symmetries of the covariant curvature derivative

Covariant differentiation preserves the algebraic first Bianchi identity of a torsion-free
connection. Thus, for each fixed direction `d`, the tensor `(∇_d R)(u, v)w` has vanishing cyclic
sum in `u, v, w`. This is distinct from the differential second Bianchi identity, whose cyclic
sum includes the direction of differentiation.

On a real metric vector bundle, `(∇_d R)(u, v)` is skew-adjoint whenever the bundle connection
is metric-compatible. The auxiliary connection differentiating the two tangent slots need not
be metric-compatible or torsion-free. On the tangent bundle these identities, together with
antisymmetry in the two curvature slots, give the algebraic symmetries needed to manipulate
the curvature derivative in normal-coordinate expansions. For a metric-compatible connection on a
metric bundle,
`CovariantDerivative.IsMetricCompatible.inner_derivCurvatureTensor` expresses the metric lowering
of `∇R` as the derivative of the metric-lowered curvature; on the tangent bundle with a
torsion-free connection this gives pair interchange
`CovariantDerivative.IsMetricCompatible.inner_derivCurvatureTensor_swap_pairs`.

The proofs differentiate the existing first Bianchi and metric-curvature identities using
`CovariantDerivative.derivCurvatureTensor_apply` and the metric product rule.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7
  (curvature symmetries and their covariant derivatives).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- The differentiated algebraic first Bianchi identity: the cyclic sum of `∇R` over its three
curvature arguments vanishes for a torsion-free connection. The differentiation direction is
held fixed, unlike in the second Bianchi identity. No metric is needed. -/
theorem derivCurvatureTensor_cyclic_last_eq_zero
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] (ht : cov.torsion = 0)
    (x : M) (d u v w : TangentSpace I x) :
    cov.derivCurvatureTensor cov x d u v w + cov.derivCurvatureTensor cov x d v w u +
      cov.derivCurvatureTensor cov x d w u v = 0 := by
  obtain ⟨U, hU, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨V, hV, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  obtain ⟨W, hW, rfl⟩ := exists_contMDiff_section_eq I E ∞ w
  have hR : cov.curvatureOperator U V W + cov.curvatureOperator V W U +
      cov.curvatureOperator W U V = 0 := by
    ext y
    exact cov.curvatureOperator_cyclic_eq_zero
      ((isTorsionFree_iff_torsion_eq_zero cov).2 ht) hU hV hW y
  have h₁ := (cov.contMDiff_curvatureOperator hU hV hW).mdifferentiableAt (by simp) (x := x)
  have h₂ := (cov.contMDiff_curvatureOperator hV hW hU).mdifferentiableAt (by simp) (x := x)
  have h₃ := (cov.contMDiff_curvatureOperator hW hU hV).mdifferentiableAt (by simp) (x := x)
  have hd := congrArg (fun σ ↦ cov σ x d) hR
  rw [cov.isCovariantDerivativeOnUniv.add (mdifferentiableAt_add_section h₁ h₂) h₃,
    cov.isCovariantDerivativeOnUniv.add h₁ h₂] at hd
  simp only [add_apply, cov.zero, Pi.zero_apply, zero_apply] at hd
  have hU' := cov.curvatureTensor_cyclic_eq_zero ht x (cov U x d) (V x) (W x)
  have hV' := cov.curvatureTensor_cyclic_eq_zero ht x (U x) (cov V x d) (W x)
  have hW' := cov.curvatureTensor_cyclic_eq_zero ht x (U x) (V x) (cov W x d)
  rw [derivCurvatureTensor_apply cov cov x d hU hV hW,
    derivCurvatureTensor_apply cov cov x d hV hW hU,
    derivCurvatureTensor_apply cov cov x d hW hU hV]
  have hzero := congrArg₂ (fun a b : TangentSpace I x ↦ a - b) hd
    (congrArg₂ (fun a b : TangentSpace I x ↦ a + b)
      (congrArg₂ (fun a b : TangentSpace I x ↦ a + b) hU' hV') hW')
  simp only [add_zero, sub_zero] at hzero
  convert hzero using 1
  abel

section Metric

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 2 F V]
  {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]

/-- The covariant derivative of the curvature of a metric connection is skew-adjoint in its
bundle arguments. The connection on the tangent slots is arbitrary. In particular, for a metric
connection on the tangent bundle this is last-pair antisymmetry of the metric-lowered `∇R`. -/
theorem IsMetricCompatible.inner_derivCurvatureTensor_eq_neg (hcov : cov.IsMetricCompatible)
    (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (d u v : TangentSpace I x) (s t : V x) :
    inner ℝ (cov.derivCurvatureTensor covT x d u v s) t =
      -inner ℝ s (cov.derivCurvatureTensor covT x d u v t) := by
  obtain ⟨D, _, rfl⟩ := exists_contMDiff_section_eq I E ∞ d
  obtain ⟨U, hU, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨W, hW, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F ∞ s
  obtain ⟨τ, hτ, rfl⟩ := exists_contMDiff_section_eq I F ∞ t
  have hfun : (fun y ↦ inner ℝ (cov.curvatureOperator U W σ y) (τ y)) =
      fun y ↦ -inner ℝ (σ y) (cov.curvatureOperator U W τ y) := by
    funext y
    rw [← curvatureTensor_apply cov y hU hW hσ, ← curvatureTensor_apply cov y hU hW hτ]
    exact hcov.inner_curvatureTensor_eq_neg y _ _ _ _
  have hd := congrArg (fun f ↦ mvfderiv I f x (D x)) hfun
  rw [hcov.mvfderiv_inner_eq D
      ((cov.contMDiff_curvatureOperator hU hW hσ).mdifferentiableAt (by simp))
      (hτ.mdifferentiableAt (by simp)),
    mvfderiv_fun_neg, neg_apply,
    hcov.mvfderiv_inner_eq D (hσ.mdifferentiableAt (by simp))
      ((cov.contMDiff_curvatureOperator hU hW hτ).mdifferentiableAt (by simp))] at hd
  dsimp only at hd
  rw [← curvatureTensor_apply cov x hU hW hσ,
    ← curvatureTensor_apply cov x hU hW hτ] at hd
  rw [derivCurvatureTensor_apply cov covT x (D x) hU hW hσ,
    derivCurvatureTensor_apply cov covT x (D x) hU hW hτ]
  simp only [inner_sub_left, inner_sub_right, hcov.inner_curvatureTensor_eq_neg] at hd ⊢
  linarith

/-- For a metric-compatible connection, pairing `(∇_v R)(Y, Z) σ` with a section `U` gives
the covariant derivative of the metric-lowered curvature `⟪R(Y, Z) σ, U⟫`. The connection `covT`
differentiating the two tangent slots is arbitrary. -/
theorem IsMetricCompatible.inner_derivCurvatureTensor (hcov : cov.IsMetricCompatible)
    (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) (v : TangentSpace I x) {Y Z : Π y : M, TangentSpace I y} {σ U : Π y : M, V y}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ))
    (hU : CMDiff ∞ (T% U)) :
    inner ℝ (cov.derivCurvatureTensor covT x v (Y x) (Z x) (σ x)) (U x) =
      mvfderiv I (fun y ↦ inner ℝ (cov.curvatureTensor y (Y y) (Z y) (σ y)) (U y)) x v -
        inner ℝ (cov.curvatureTensor x (covT Y x v) (Z x) (σ x)) (U x) -
          inner ℝ (cov.curvatureTensor x (Y x) (covT Z x v) (σ x)) (U x) -
            inner ℝ (cov.curvatureTensor x (Y x) (Z x) (cov σ x v)) (U x) -
              inner ℝ (cov.curvatureTensor x (Y x) (Z x) (σ x)) (cov U x v) := by
  have hfun : (fun y ↦ inner ℝ (cov.curvatureTensor y (Y y) (Z y) (σ y)) (U y)) =
      fun y ↦ inner ℝ (cov.curvatureOperator Y Z σ y) (U y) := by
    funext y
    rw [curvatureTensor_apply cov y hY hZ hσ]
  have hd : mvfderiv I (fun y ↦ inner ℝ (cov.curvatureOperator Y Z σ y) (U y)) x v =
      inner ℝ (cov (cov.curvatureOperator Y Z σ) x v) (U x) +
        inner ℝ (cov.curvatureOperator Y Z σ x) (cov U x v) := by
    simpa only [FiberBundle.extend_apply_self] using
      hcov.mvfderiv_inner_eq (FiberBundle.extend E v)
        ((cov.contMDiff_curvatureOperator hY hZ hσ).mdifferentiableAt (by simp) (x := x))
        (hU.mdifferentiableAt (by simp))
  rw [derivCurvatureTensor_apply cov covT x v hY hZ hσ, hfun, hd,
    ← curvatureTensor_apply cov x hY hZ hσ]
  simp only [inner_sub_left]
  ring

end Metric

section TangentMetric

open scoped InnerProductSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- Pair interchange for the metric-lowered covariant derivative of curvature:
`(∇_d Rm)(u, v, w, z) = (∇_d Rm)(w, z, u, v)`. -/
theorem IsMetricCompatible.inner_derivCurvatureTensor_swap_pairs
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (d u v w z : TangentSpace I x) :
    inner ℝ (cov.derivCurvatureTensor cov x d u v w) z =
      inner ℝ (cov.derivCurvatureTensor cov x d w z u) v := by
  obtain ⟨U, hU, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ u
  obtain ⟨V, hV, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  obtain ⟨W, hW, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ w
  obtain ⟨Z, hZ, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ z
  have hs (y : M) (a b c d : TangentSpace I y) :
      inner ℝ (cov.curvatureTensor y a b c) d = inner ℝ (cov.curvatureTensor y c d a) b :=
    hcov.inner_curvatureTensor_swap_pairs ht y a b c d
  have hfun : (fun y ↦ inner ℝ (cov.curvatureTensor y (U y) (V y) (W y)) (Z y)) =
      fun y ↦ inner ℝ (cov.curvatureTensor y (W y) (Z y) (U y)) (V y) :=
    funext fun y ↦ hs y _ _ _ _
  rw [hcov.inner_derivCurvatureTensor cov x d hU hV hW hZ,
    hcov.inner_derivCurvatureTensor cov x d hW hZ hU hV, hfun, hs x (cov U x d),
    hs x (U x) (cov V x d), hs x (U x) (V x) (cov W x d), hs x (U x) (V x) (W x) (cov Z x d)]
  ring

end TangentMetric

end CovariantDerivative
