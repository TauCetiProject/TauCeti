/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
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

* `TauCeti.curvatureOperator`: the curvature operator of a connection.
* `TauCeti.curvatureOperator_swap`: curvature is antisymmetric in its two
  vector-field arguments.
* `TauCeti.contMDiff_curvatureOperator`: a smooth connection has smooth
  curvature on smooth fields and sections.
* `TauCeti.curvatureOperator_smul_first`, `TauCeti.curvatureOperator_smul_second`, and
  `TauCeti.curvatureOperator_smul_section`: curvature is linear over smooth
  functions in each argument.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018,
  Chapter 7, pp. 196--198.
-/

public section

open Bundle FiberBundle Module NormedSpace VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

section Basic

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace 𝕜 (V x)]
  [FiberBundle F V]

variable (cov : _root_.CovariantDerivative I F V)

/-- The curvature operator of a covariant derivative, with Lee's sign convention:

`R(X, Y) σ = ∇ X (∇ Y σ) - ∇ Y (∇ X σ) - ∇ [X, Y] σ`.

The output is left as an unbundled section so that the definition is available without any
regularity assumption on the connection.  Smoothness is supplied by
`contMDiff_curvatureOperator` when the connection and input sections are smooth. -/
@[expose] def curvatureOperator
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) : V x :=
  cov (fun y ↦ cov σ y (Y y)) x (X x) -
    cov (fun y ↦ cov σ y (X y)) x (Y x) -
      cov σ x (mlieBracket I X Y x)

/-- The defining formula for the curvature operator. -/
@[simp]
theorem curvatureOperator_apply (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    curvatureOperator cov X Y σ x =
      cov (fun y ↦ cov σ y (Y y)) x (X x) -
        cov (fun y ↦ cov σ y (X y)) x (Y x) -
          cov σ x (mlieBracket I X Y x) := rfl

/-- Curvature is antisymmetric in its two vector-field arguments. -/
theorem curvatureOperator_swap (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
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
  rw [curvatureOperator_swap]
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
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)] [FiberBundle F V]

variable (cov : _root_.CovariantDerivative I F V)

variable [CompleteSpace E] [IsManifold I ∞ M] [VectorBundle ℝ F V]
  [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

omit [CompleteSpace E] in
private theorem contMDiff_cov_apply
    {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    (hX : CMDiff ∞ (T% X)) (hσ : CMDiff ∞ (T% σ)) :
    CMDiff ∞ (T% (fun x ↦ cov σ x (X x))) := by
  rw [← contMDiffOn_univ]
  exact ContMDiffOn.clm_bundle_apply
    (_root_.CovariantDerivative.ContMDiffCovariantDerivative.contMDiff.contMDiff
      hσ.contMDiffOn) hX.contMDiffOn

/-- The curvature operator of a smooth connection sends smooth vector fields and smooth sections
to a smooth section. -/
theorem contMDiff_curvatureOperator
    {X Y : Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hσ : CMDiff ∞ (T% σ)) :
    CMDiff ∞ (T% (curvatureOperator cov X Y σ)) := by
  have hYσ := contMDiff_cov_apply cov hY hσ
  have hXσ := contMDiff_cov_apply cov hX hσ
  let _ : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by simp)
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M :=
    IsManifold.of_le (m := (∞ : ℕ∞ω) + 1) (n := ∞) (by simp)
  have hXY : CMDiff ∞ (T% (mlieBracket I X Y)) :=
    ContDiff.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hX hY (by
      rw [minSmoothness_of_isRCLikeNormedField]
      simp)
  exact ((contMDiff_cov_apply cov hX hYσ).sub_section
    (contMDiff_cov_apply cov hY hXσ)).sub_section (contMDiff_cov_apply cov hXY hσ)

variable {cov}
  {X X' Y Y' : Π x : M, TangentSpace I x} {σ τ : Π x : M, V x} {f : M → ℝ}

/-- Curvature is additive in its first vector-field argument. -/
theorem curvatureOperator_add_first
    (hX : CMDiff ∞ (T% X)) (hX' : CMDiff ∞ (T% X'))
    (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov (X + X') Y σ =
      curvatureOperator cov X Y σ + curvatureOperator cov X' Y σ := by
  funext x
  simp only [Pi.add_apply]
  have hXσ := contMDiff_cov_apply cov hX hσ
  have hX'σ := contMDiff_cov_apply cov hX' hσ
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
theorem curvatureOperator_add_second
    (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov X (Y + Y') σ =
      curvatureOperator cov X Y σ + curvatureOperator cov X Y' σ := by
  rw [curvatureOperator_swap cov X (Y + Y') σ,
    curvatureOperator_add_first hY hY' hσ,
    curvatureOperator_swap cov Y X σ, curvatureOperator_swap cov Y' X σ]
  module

omit [CompleteSpace E] in
/-- Curvature is additive in its section argument. -/
theorem curvatureOperator_add_section
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ)) :
    curvatureOperator cov X Y (σ + τ) =
      curvatureOperator cov X Y σ + curvatureOperator cov X Y τ := by
  funext x
  have hYσ := contMDiff_cov_apply cov hY hσ
  have hYτ := contMDiff_cov_apply cov hY hτ
  have hXσ := contMDiff_cov_apply cov hX hσ
  have hXτ := contMDiff_cov_apply cov hX hτ
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

/-- Curvature is linear over smooth functions in its first vector-field argument. -/
theorem curvatureOperator_smul_first
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hX : CMDiff ∞ (T% X))
    (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov (f • X) Y σ = f • curvatureOperator cov X Y σ := by
  funext x
  -- The pointwise `Pi` action on the right hides the applied curvature operator from `rw`.
  change curvatureOperator cov (f • X) Y σ x = f x • curvatureOperator cov X Y σ x
  have hXσ := contMDiff_cov_apply cov hX hσ
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
theorem curvatureOperator_smul_second
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hY : CMDiff ∞ (T% Y))
    (hσ : CMDiff ∞ (T% σ)) :
    curvatureOperator cov X (f • Y) σ = f • curvatureOperator cov X Y σ := by
  rw [curvatureOperator_swap cov X (f • Y) σ,
    curvatureOperator_smul_first hf hY hσ, curvatureOperator_swap cov Y X σ]
  simp

/-- Curvature is linear over smooth functions in its section argument. -/
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
  have hXσ := contMDiff_cov_apply cov hX hσ
  have hYσ := contMDiff_cov_apply cov hY hσ
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

end Smooth

end TauCeti
