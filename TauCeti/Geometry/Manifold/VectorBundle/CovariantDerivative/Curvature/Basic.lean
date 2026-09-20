/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Curvature of a covariant derivative

For a covariant derivative `∇` on a vector bundle, this file defines its curvature operator

`R(X, Y) σ = ∇ X (∇ Y σ) - ∇ Y (∇ X σ) - ∇ [X, Y] σ`.

We use the sign convention of Lee.  The arguments to Mathlib's `CovariantDerivative` are ordered
as `cov σ x (X x) = ∇ X σ`, so the order in the defining formula is worth making explicit.
The operator is alternating in its vector-field arguments.  For a smooth connection it takes
smooth fields and sections to a smooth section and is linear over smooth scalar functions in all
three arguments; this is the tensoriality statement behind the pointwise `(1,3)`-curvature tensor
of a connection on the tangent bundle.

## Main definitions and results

* `CovariantDerivative.curvatureOperator`: the curvature operator of a connection.
* `CovariantDerivative.curvatureOperator_antisymm`: curvature is antisymmetric in its two
  vector-field arguments.
* `CovariantDerivative.contMDiff_curvatureOperator`: a smooth connection has smooth
  curvature on smooth fields and sections.
* `CovariantDerivative.curvatureOperator_smul_first`,
  `CovariantDerivative.curvatureOperator_smul_second`, and
  `CovariantDerivative.curvatureOperator_smul_section`: curvature is linear over smooth
  functions in each argument.
* `CovariantDerivative.curvatureOperator_congr`: on finite-rank smooth bundles over
  finite-dimensional Hausdorff manifolds, curvature at a point depends only on the values of
  its three inputs there.
* `CovariantDerivative.curvatureOperator_congr_of_eventuallyEq`: curvature agrees at a point
  when its smooth inputs agree in a neighborhood of that point.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018,
  Chapter 7, pp. 196--198.
-/

public section

open Bundle FiberBundle Module NormedSpace VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

section Basic

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [fiberNorm : ∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace 𝕜 (V x)]
  [FiberBundle F V]

variable (cov : _root_.CovariantDerivative I F V)

/-- The curvature operator of a covariant derivative, with Lee's sign convention:

`R(X, Y) σ = ∇ X (∇ Y σ) - ∇ Y (∇ X σ) - ∇ [X, Y] σ`.

The output is left as an unbundled section so that the definition is available without any
regularity assumption on the connection.  Smoothness is supplied by
`contMDiff_curvatureOperator` when the connection and input sections are smooth. -/
def curvatureOperator
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) : V x :=
  cov (fun y ↦ cov σ y (Y y)) x (X x) -
    cov (fun y ↦ cov σ y (X y)) x (Y x) -
      cov σ x (mlieBracket I X Y x)

/-- The curvature operator as a section, expressed using covariant derivatives. -/
theorem curvatureOperator_def (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    curvatureOperator cov X Y σ = fun x ↦
      cov (fun y ↦ cov σ y (Y y)) x (X x) -
        cov (fun y ↦ cov σ y (X y)) x (Y x) -
          cov σ x (mlieBracket I X Y x) := (rfl)

/-- The defining formula for the curvature operator evaluated at a point. -/
theorem curvatureOperator_apply (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    curvatureOperator cov X Y σ x =
      cov (fun y ↦ cov σ y (Y y)) x (X x) -
        cov (fun y ↦ cov σ y (X y)) x (Y x) -
          cov σ x (mlieBracket I X Y x) := (rfl)

/-- Curvature is antisymmetric in its two vector-field arguments. -/
theorem curvatureOperator_antisymm (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    curvatureOperator cov X Y σ = -curvatureOperator cov Y X σ := by
  funext x
  simp only [Pi.neg_apply]
  rw [curvatureOperator_apply, curvatureOperator_apply,
    mlieBracket_swap_apply (V := X) (W := Y)]
  simp only [map_neg]
  abel

/-- Curvature vanishes when its two vector-field arguments coincide. -/
@[simp]
theorem curvatureOperator_self (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    curvatureOperator cov X X σ = 0 := by
  funext x
  rw [curvatureOperator_apply]
  simp

variable [VectorBundle 𝕜 F V]

/-- Curvature vanishes when its first vector-field argument is zero. -/
@[simp]
theorem curvatureOperator_zero_first (Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    curvatureOperator cov 0 Y σ = 0 := by
  funext x
  have hz : (fun y ↦ cov σ y ((0 : Π x : M, TangentSpace I x) y)) = 0 := by
    funext y
    simp
  rw [curvatureOperator_apply, hz, cov.zero]
  simp

/-- Curvature vanishes when its second vector-field argument is zero. -/
@[simp]
theorem curvatureOperator_zero_second (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    curvatureOperator cov X 0 σ = 0 := by
  rw [curvatureOperator_antisymm]
  simp

/-- Curvature vanishes on the zero section. -/
@[simp]
theorem curvatureOperator_zero_section (X Y : Π x : M, TangentSpace I x) :
    curvatureOperator cov X Y 0 = 0 := by
  funext x
  have hzX : (fun y ↦ cov (0 : Π x : M, V x) y (X y)) = 0 := by
    rw [cov.zero]
    rfl
  have hzY : (fun y ↦ cov (0 : Π x : M, V x) y (Y y)) = 0 := by
    rw [cov.zero]
    rfl
  rw [curvatureOperator_apply, hzX, hzY, cov.zero]
  simp

end Basic

section Smooth

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [fiberNorm : ∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)] [FiberBundle F V]

variable (cov : _root_.CovariantDerivative I F V)

variable [CompleteSpace E] [IsManifold I ∞ M] [VectorBundle ℝ F V]
  [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- The curvature operator of a smooth connection sends smooth vector fields and smooth sections
to a smooth section. -/
theorem contMDiff_curvatureOperator
    {X Y : Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hσ : CMDiff ∞ (T% σ)) :
    CMDiff ∞ (T% (curvatureOperator cov X Y σ)) := by
  have hYσ := cov.contMDiff_apply hY hσ
  have hXσ := cov.contMDiff_apply hX hσ
  let _ : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by simp)
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M :=
    IsManifold.of_le (m := (∞ : ℕ∞ω) + 1) (n := ∞) (by simp)
  have hXY : CMDiff ∞ (T% (mlieBracket I X Y)) :=
    ContDiff.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hX hY (by
      rw [minSmoothness_of_isRCLikeNormedField]
      simp)
  exact ((cov.contMDiff_apply hX hYσ).sub_section
    (cov.contMDiff_apply hY hXσ)).sub_section
      (cov.contMDiff_apply hXY hσ)

variable {cov}
  {X X' Y Y' : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x} {f : M → ℝ}

/-- Curvature is additive in its first vector-field argument. -/
@[simp]
theorem curvatureOperator_add_first
    (hX : CMDiff ∞ (T% X)) (hX' : CMDiff ∞ (T% X'))
    (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov (X + X') Y σ =
      curvatureOperator cov X Y σ + curvatureOperator cov X' Y σ := by
  funext x
  simp only [Pi.add_apply]
  have hXσ := cov.contMDiff_apply hX hσ
  have hX'σ := cov.contMDiff_apply hX' hσ
  have hXd : MDiff (T% X) := hX.mdifferentiable (by simp)
  have hX'd : MDiff (T% X') := hX'.mdifferentiable (by simp)
  have hXσd : MDiff (T% (fun y ↦ cov σ y (X y))) := hXσ.mdifferentiable (by simp)
  have hX'σd : MDiff (T% (fun y ↦ cov σ y (X' y))) := hX'σ.mdifferentiable (by simp)
  have einner : (fun y ↦ cov σ y ((X + X') y)) =
      (fun y ↦ cov σ y (X y)) + fun y ↦ cov σ y (X' y) := by
    funext y
    exact map_add (cov σ y) (X y) (X' y)
  rw [curvatureOperator_apply, curvatureOperator_apply, curvatureOperator_apply, einner,
    cov.isCovariantDerivativeOn.add (hXσd x) (hX'σd x),
    mlieBracket_add_left (hXd x) (hX'd x)]
  simp only [Pi.add_apply, map_add, add_apply]
  abel

/-- Curvature is additive in its second vector-field argument. -/
@[simp]
theorem curvatureOperator_add_second
    (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov X (Y + Y') σ =
      curvatureOperator cov X Y σ + curvatureOperator cov X Y' σ := by
  rw [curvatureOperator_antisymm cov X (Y + Y') σ,
    curvatureOperator_add_first hY hY' hσ,
    curvatureOperator_antisymm cov Y X σ, curvatureOperator_antisymm cov Y' X σ]
  module

omit [CompleteSpace E] in
/-- Curvature is additive in its section argument. -/
@[simp]
theorem curvatureOperator_add_section
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) :
    curvatureOperator cov X Y (σ + τ) =
      curvatureOperator cov X Y σ + curvatureOperator cov X Y τ := by
  funext x
  have hYσ := cov.contMDiff_apply hY hσ
  have hYτ := cov.contMDiff_apply hY hτ
  have hXσ := cov.contMDiff_apply hX hσ
  have hXτ := cov.contMDiff_apply hX hτ
  have hσd : MDiff (T% σ) := hσ.mdifferentiable (by simp)
  have hτd : MDiff (T% τ) := hτ.mdifferentiable (by simp)
  have hYσd : MDiff (T% (fun y ↦ cov σ y (Y y))) := hYσ.mdifferentiable (by simp)
  have hYτd : MDiff (T% (fun y ↦ cov τ y (Y y))) := hYτ.mdifferentiable (by simp)
  have hXσd : MDiff (T% (fun y ↦ cov σ y (X y))) := hXσ.mdifferentiable (by simp)
  have hXτd : MDiff (T% (fun y ↦ cov τ y (X y))) := hXτ.mdifferentiable (by simp)
  have hinnerY : (fun y ↦ cov (σ + τ) y (Y y)) =
      (fun y ↦ cov σ y (Y y)) + fun y ↦ cov τ y (Y y) := by
    funext y
    rw [cov.isCovariantDerivativeOn.add (hσd y) (hτd y)]
    rfl
  have hinnerX : (fun y ↦ cov (σ + τ) y (X y)) =
      (fun y ↦ cov σ y (X y)) + fun y ↦ cov τ y (X y) := by
    funext y
    rw [cov.isCovariantDerivativeOn.add (hσd y) (hτd y)]
    rfl
  simp only [Pi.add_apply]
  rw [curvatureOperator_apply, curvatureOperator_apply, curvatureOperator_apply, hinnerY,
    hinnerX, cov.isCovariantDerivativeOn.add (hYσd x) (hYτd x),
    cov.isCovariantDerivativeOn.add (hXσd x) (hXτd x),
    cov.isCovariantDerivativeOn.add (hσd x) (hτd x)]
  simp only [add_apply]
  abel

/-- Curvature changes sign when its first vector-field argument is negated. -/
@[simp]
theorem curvatureOperator_neg_first
    (hX : CMDiff ∞ (T% X)) (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov (-X) Y σ = -curvatureOperator cov X Y σ := by
  apply eq_neg_of_add_eq_zero_left
  rw [← curvatureOperator_add_first hX.neg_section hX hσ, neg_add_cancel,
    curvatureOperator_zero_first]

/-- Curvature changes sign when its second vector-field argument is negated. -/
@[simp]
theorem curvatureOperator_neg_second
    (hY : CMDiff ∞ (T% Y)) (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov X (-Y) σ = -curvatureOperator cov X Y σ := by
  apply eq_neg_of_add_eq_zero_left
  rw [← curvatureOperator_add_second hY.neg_section hY hσ, neg_add_cancel,
    curvatureOperator_zero_second]

omit [CompleteSpace E] in
/-- Curvature changes sign when its section argument is negated. -/
@[simp]
theorem curvatureOperator_neg_section
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov X Y (-σ) = -curvatureOperator cov X Y σ := by
  apply eq_neg_of_add_eq_zero_left
  rw [← curvatureOperator_add_section hX hY hσ.neg_section hσ, neg_add_cancel,
    curvatureOperator_zero_section]

/-- Curvature is linear over smooth functions in its first vector-field argument. -/
@[simp]
theorem curvatureOperator_smul_first
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hX : CMDiff ∞ (T% X))
    (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov (f • X) Y σ = f • curvatureOperator cov X Y σ := by
  funext x
  -- The pointwise `Pi` action on the right hides the applied curvature operator from `rw`.
  change curvatureOperator cov (f • X) Y σ x = f x • curvatureOperator cov X Y σ x
  have hXσ := cov.contMDiff_apply hX hσ
  have hXσd : MDiff (T% (fun y ↦ cov σ y (X y))) := hXσ.mdifferentiable (by simp)
  have hfd : MDiff f := hf.mdifferentiable (by simp)
  have hXd : MDiff (T% X) := hX.mdifferentiable (by simp)
  have eX : (f • X) x = f x • X x := rfl
  have einner : (fun y ↦ cov σ y ((f • X) y)) = f • fun y ↦ cov σ y (X y) := by
    funext y
    exact map_smul (cov σ y) (f y) (X y)
  rw [curvatureOperator_apply, curvatureOperator_apply, einner,
    cov.isCovariantDerivativeOn.leibniz (hXσd x) (hfd x),
    mlieBracket_smul_left (hfd x) (hXd x)]
  simp only [eX, map_smul, map_add, add_apply, ContinuousLinearMap.smulRight_apply]
  -- Fold the expanded vector expressions into local names: rewriting cannot target these
  -- abbreviations, while `change` recognizes their definitional equality before `abel`.
  let A := f x • cov (fun y ↦ cov σ y (Y y)) x (X x)
  let B := f x • cov (fun y ↦ cov σ y (X y)) x (Y x)
  let C := d% f x (Y x) • cov σ x (X x)
  let D := f x • cov σ x (mlieBracket I X Y x)
  rw [smul_sub, smul_sub, neg_smul]
  change A - (B + C) - (-C + D) = A - B - D
  abel

/-- Curvature is linear over smooth functions in its second vector-field argument. -/
@[simp]
theorem curvatureOperator_smul_second
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hY : CMDiff ∞ (T% Y))
    (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov X (f • Y) σ = f • curvatureOperator cov X Y σ := by
  rw [curvatureOperator_antisymm cov X (f • Y) σ,
    curvatureOperator_smul_first hf hY hσ, curvatureOperator_antisymm cov Y X σ]
  simp

/-- Curvature is linear over smooth functions in its section argument. -/
@[simp]
theorem curvatureOperator_smul_section
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hX : CMDiff ∞ (T% X))
    (hY : CMDiff ∞ (T% Y)) (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov X Y (f • σ) = f • curvatureOperator cov X Y σ := by
  funext x
  -- The pointwise `Pi` action on the right hides the applied curvature operator from `rw`.
  change curvatureOperator cov X Y (f • σ) x = f x • curvatureOperator cov X Y σ x
  let gX : M → ℝ := fun y ↦ d% f y (X y)
  let gY : M → ℝ := fun y ↦ d% f y (Y y)
  have hfd : MDiff f := hf.mdifferentiable (by simp)
  have hXd : MDiff (T% X) := hX.mdifferentiable (by simp)
  have hYd : MDiff (T% Y) := hY.mdifferentiable (by simp)
  have hσd : MDiff (T% σ) := hσ.mdifferentiable (by simp)
  have hXσ := cov.contMDiff_apply hX hσ
  have hYσ := cov.contMDiff_apply hY hσ
  have hXσd : MDiff (T% (fun y ↦ cov σ y (X y))) := hXσ.mdifferentiable (by simp)
  have hYσd : MDiff (T% (fun y ↦ cov σ y (Y y))) := hYσ.mdifferentiable (by simp)
  have hgX : ContMDiff I 𝓘(ℝ) ∞ gX := by
    exact (_root_.ContMDiff.contMDiff_mvfderiv_apply hf
      (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)).comp hX
  have hgY : ContMDiff I 𝓘(ℝ) ∞ gY := by
    exact (_root_.ContMDiff.contMDiff_mvfderiv_apply hf
      (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)).comp hY
  have hgXd : MDiff gX := hgX.mdifferentiable (by simp)
  have hgYd : MDiff gY := hgY.mdifferentiable (by simp)
  have hinnerX : (fun y ↦ cov (f • σ) y (X y)) =
      f • (fun y ↦ cov σ y (X y)) + gX • σ := by
    funext y
    have h := cov.isCovariantDerivativeOn.leibniz (hσd y) (hfd y)
    -- `h` is an equality of continuous linear maps; expose its value at `X y` through the
    -- pointwise `Pi` operations before rewriting by it.
    change cov (f • σ) y (X y) = f y • cov σ y (X y) + gX y • σ y
    rw [h]
    simp [gX, add_apply, ContinuousLinearMap.smulRight_apply]
  have hinnerY : (fun y ↦ cov (f • σ) y (Y y)) =
      f • (fun y ↦ cov σ y (Y y)) + gY • σ := by
    funext y
    have h := cov.isCovariantDerivativeOn.leibniz (hσd y) (hfd y)
    -- `h` is an equality of continuous linear maps; expose its value at `Y y` through the
    -- pointwise `Pi` operations before rewriting by it.
    change cov (f • σ) y (Y y) = f y • cov σ y (Y y) + gY y • σ y
    rw [h]
    simp [gY, add_apply, ContinuousLinearMap.smulRight_apply]
  have hfXσd : MDiff (T% (f • fun y ↦ cov σ y (X y))) :=
    (hf.smul_section hXσ).mdifferentiable (by simp)
  have hfYσd : MDiff (T% (f • fun y ↦ cov σ y (Y y))) :=
    (hf.smul_section hYσ).mdifferentiable (by simp)
  have hgXσd : MDiff (T% (gX • σ)) := (hgX.smul_section hσ).mdifferentiable (by simp)
  have hgYσd : MDiff (T% (gY • σ)) := (hgY.smul_section hσ).mdifferentiable (by simp)
  let _ : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by simp)
  -- The commutator identity below cancels the second-derivative terms.
  have hcomm := mvfderiv_mlieBracket (f := f) (V := X) (W := Y) (x := x)
    (hf.contMDiffAt) (by simp) (hXd x) (hYd x)
  rw [curvatureOperator_apply, curvatureOperator_apply, hinnerY, hinnerX,
    cov.isCovariantDerivativeOn.add (hfYσd x) (hgYσd x),
    cov.isCovariantDerivativeOn.add (hfXσd x) (hgXσd x),
    cov.isCovariantDerivativeOn.leibniz (hYσd x) (hfd x),
    cov.isCovariantDerivativeOn.leibniz (hσd x) (hgYd x),
    cov.isCovariantDerivativeOn.leibniz (hXσd x) (hfd x),
    cov.isCovariantDerivativeOn.leibniz (hσd x) (hgXd x),
    cov.isCovariantDerivativeOn.leibniz (hσd x) (hfd x)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [hcomm]
  simp only [gX, gY]
  simp only [sub_smul, smul_sub]
  -- Fold the expanded vector expressions into local names: rewriting cannot target these
  -- abbreviations, while `change` recognizes their definitional equality before `abel`.
  let A := f x • cov (fun y ↦ cov σ y (Y y)) x (X x)
  let B := f x • cov (fun y ↦ cov σ y (X y)) x (Y x)
  let D := f x • cov σ x (mlieBracket I X Y x)
  let P := d% f x (X x) • cov σ x (Y x)
  let Q := d% f x (Y x) • cov σ x (X x)
  let S := d% (fun y ↦ d% f y (Y y)) x (X x) • σ x
  let T := d% (fun y ↦ d% f y (X y)) x (Y x) • σ x
  change A + P + (Q + S) - (B + Q + (P + T)) - (D + (S - T)) = A - B - D
  abel

omit [CompleteSpace E] in
/-- Curvature at a point is unchanged when its smooth inputs agree in a neighborhood of that
point. -/
theorem curvatureOperator_congr_of_eventuallyEq
    {X X' Y Y' : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hX' : CMDiff ∞ (T% X'))
    (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (hσ : CMDiff ∞ (T% σ)) (hσ' : CMDiff ∞ (T% σ'))
    (hXX' : X =ᶠ[nhds x] X') (hYY' : Y =ᶠ[nhds x] Y')
    (hσσ' : Filter.Eventually (fun y ↦ σ y = σ' y) (nhds x)) :
    curvatureOperator cov X Y σ x = curvatureOperator cov X' Y' σ' x := by
  have hσd := hσ.mdifferentiable (by simp)
  have hσ'd := hσ'.mdifferentiable (by simp)
  have hinnerY : Filter.Eventually
      (fun y ↦ cov σ y (Y y) = cov σ' y (Y' y)) (nhds x) := by
    filter_upwards [eventually_eventually_nhds.2 hσσ', hYY'.eventuallyEq_nhds] with y hσy hYy
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      (hσd y) (hσ'd y) Filter.univ_mem hσy, hYy.eq_of_nhds]
  have hinnerX : Filter.Eventually
      (fun y ↦ cov σ y (X y) = cov σ' y (X' y)) (nhds x) := by
    filter_upwards [eventually_eventually_nhds.2 hσσ', hXX'.eventuallyEq_nhds] with y hσy hXy
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      (hσd y) (hσ'd y) Filter.univ_mem hσy, hXy.eq_of_nhds]
  have hYσ := cov.contMDiff_apply hY hσ
  have hY'σ' := cov.contMDiff_apply hY' hσ'
  have hXσ := cov.contMDiff_apply hX hσ
  have hX'σ' := cov.contMDiff_apply hX' hσ'
  have hfirst : cov (fun y ↦ cov σ y (Y y)) x (X x) =
      cov (fun y ↦ cov σ' y (Y' y)) x (X' x) := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      (hYσ.mdifferentiable (by simp) x) (hY'σ'.mdifferentiable (by simp) x)
      Filter.univ_mem hinnerY, hXX'.self_of_nhds]
  have hsecond : cov (fun y ↦ cov σ y (X y)) x (Y x) =
      cov (fun y ↦ cov σ' y (X' y)) x (Y' x) := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      (hXσ.mdifferentiable (by simp) x) (hX'σ'.mdifferentiable (by simp) x)
      Filter.univ_mem hinnerX, hYY'.self_of_nhds]
  have hthird : cov σ x (mlieBracket I X Y x) = cov σ' x (mlieBracket I X' Y' x) := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      (hσd x) (hσ'd x) Filter.univ_mem hσσ', hXX'.mlieBracket_vectorField_eq hYY']
  rw [curvatureOperator_apply, curvatureOperator_apply, hfirst, hsecond, hthird]

omit [CompleteSpace E] in
/-- On a finite-dimensional Hausdorff manifold and a finite-rank smooth vector bundle, the value
of curvature on smooth inputs depends only on their values at the given point. -/
theorem curvatureOperator_congr
    [FiniteDimensional ℝ E] [T2Space M] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle ∞ F V I]
    {X X' Y Y' : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hX' : CMDiff ∞ (T% X'))
    (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (hσ : CMDiff ∞ (T% σ)) (hσ' : CMDiff ∞ (T% σ'))
    (hXX' : X x = X' x) (hYY' : Y x = Y' x) (hσσ' : σ x = σ' x) :
    curvatureOperator cov X Y σ x = curvatureOperator cov X' Y' σ' x := by
  calc
    curvatureOperator cov X Y σ x = curvatureOperator cov X' Y σ x :=
      TauCeti.Manifold.eq_of_contMDiff_tensorial (G := E) (W := TangentSpace I)
        (fun Z ↦ curvatureOperator cov Z Y σ x) x
        (fun hZ hZ' hZZ' ↦ curvatureOperator_congr_of_eventuallyEq
          hZ hZ' hY hY hσ hσ hZZ' Filter.EventuallyEq.rfl
            (Filter.Eventually.of_forall fun _ ↦ rfl))
        (fun hZ hZ' ↦ congrFun (curvatureOperator_add_first hZ hZ' hσ) x)
        (fun hf hZ ↦ congrFun (curvatureOperator_smul_first hf hZ hσ) x)
        hX hX' hXX'
    _ = curvatureOperator cov X' Y' σ x :=
      TauCeti.Manifold.eq_of_contMDiff_tensorial (G := E) (W := TangentSpace I)
        (fun Z ↦ curvatureOperator cov X' Z σ x) x
        (fun hZ hZ' hZZ' ↦ curvatureOperator_congr_of_eventuallyEq
          hX' hX' hZ hZ' hσ hσ Filter.EventuallyEq.rfl hZZ'
            (Filter.Eventually.of_forall fun _ ↦ rfl))
        (fun hZ hZ' ↦ congrFun (curvatureOperator_add_second hZ hZ' hσ) x)
        (fun hf hZ ↦ congrFun (curvatureOperator_smul_second hf hZ hσ) x)
        hY hY' hYY'
    _ = curvatureOperator cov X' Y' σ' x :=
      TauCeti.Manifold.eq_of_contMDiff_tensorial (G := F) (W := V)
        (fun τ ↦ curvatureOperator cov X' Y' τ x) x
        (fun hτ hτ' hττ' ↦ curvatureOperator_congr_of_eventuallyEq
          hX' hX' hY' hY' hτ hτ' Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl hττ')
        (fun hτ hτ' ↦ congrFun (curvatureOperator_add_section hX' hY' hτ hτ') x)
        (fun hf hτ ↦ congrFun (curvatureOperator_smul_section hf hX' hY' hτ) x)
        hσ hσ' hσσ'

end Smooth

end CovariantDerivative
