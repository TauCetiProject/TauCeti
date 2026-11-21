/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Dual
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# The canonical connection on a trivial bundle

Ordinary differentiation gives a connection on the trivial bundle `M × F`. Combining it
with a tangent connection through `CovariantDerivative.hom` gives the induced connection
on fixed-coefficient covector fields. This allows comparison of covariant differentiation
with the ordinary exterior derivative, without choosing a frame for the tangent bundle.

On the trivial line bundle, every connection is `d + ω` for the connection form `ω = ∇ 1`
(`CovariantDerivative.apply_eq_mvfderiv_add_smul_one`). On a Riemannian manifold, the connection
`d + ⟪Y, ·⟫` (`CovariantDerivative.trivialAddInner`) has connection form metric-dual to a vector
field `Y`; it is compatible with the standard fibre metric only for `Y = 0`
(`CovariantDerivative.isMetricCompatible_trivialAddInner_iff`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4
  (connections on trivial bundles and induced connections).
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The canonical connection on the trivial bundle: its covariant derivative is the ordinary
manifold derivative, with values read in the fixed coefficient space. -/
def trivial : CovariantDerivative I F (Bundle.Trivial M F) where
  toFun := mvfderiv I
  isCovariantDerivativeOnUniv := {
    add := by
      intro σ τ x hσ hτ _
      rw [Trivial.mdifferentiableAt_section_iff] at hσ hτ
      exact mvfderiv_add hσ hτ
    leibniz := by
      intro σ f x hσ hf _
      rw [Trivial.mdifferentiableAt_section_iff] at hσ
      exact mvfderiv_smul hf hσ }

/-- The canonical trivial-bundle connection evaluates as ordinary differentiation. -/
@[simp]
theorem trivial_apply (σ : M → F) (x : M) :
    trivial (I := I) F σ x = mvfderiv I σ x := (rfl)

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}

/-- The canonical connection on a real trivial bundle is `C^n` at every regularity order. -/
instance : ContMDiffCovariantDerivative (trivial (I := I) (M := M) F) n where
  contMDiff.contMDiff {σ} hσ := by
    rw [contMDiffOn_univ] at hσ ⊢
    have hf : ContMDiff I 𝓘(ℝ, F) (n + 1) σ := fun x ↦ by
      simpa only [contMDiffAt_section_iff, Trivial.fiberBundle_trivializationAt',
        Trivial.trivialization_apply] using hσ x
    exact hf.contMDiff_totalSpaceMk_mvfderiv

end CovariantDerivative

namespace CovariantDerivative

/-! ### Connections on the trivial line bundle -/

section TrivialLine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Connections on the trivial line.** Every connection on the trivial line bundle is
`d + ω` with the connection form `ω = ∇ 1`: on a section `σ` differentiable at `x`,
`∇ σ x = dσ_x + σ x ∇ 1 x`. -/
theorem apply_eq_mvfderiv_add_smul_one (cov : CovariantDerivative I ℝ (Bundle.Trivial M ℝ))
    {σ : M → ℝ} {x : M} (hσ : MDifferentiableAt I 𝓘(ℝ) σ x) :
    cov σ x = mvfderiv I σ x + σ x • cov (1 : M → ℝ) x := by
  have h := cov.isCovariantDerivativeOnUniv.leibniz (σ := (1 : M → ℝ))
    (Trivial.mdifferentiableAt_mk_const 1) hσ
  rw [Trivial.smul_one] at h
  rw [h, add_comm]
  congr 1
  ext v
  simp only [ContinuousLinearMap.smulRight_apply, Pi.one_apply, mvfderiv_apply_eq_mfderiv_apply]
  exact mul_one _

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The connection `d + ⟪Y, ·⟫` on the trivial line bundle, whose connection form is the one-form
metric-dual to the vector field `Y`: `∇ σ = dσ + σ ⟪Y, ·⟫`
(`CovariantDerivative.trivialAddInner_apply`). Every connection on the trivial line agrees with
one of these on differentiable sections (`CovariantDerivative.apply_eq_mvfderiv_add_smul_one`). -/
def trivialAddInner (Y : Π x : M, TangentSpace I x) :
    CovariantDerivative I ℝ (Bundle.Trivial M ℝ) :=
  (trivial ℝ).addOneForm fun x ↦ ContinuousLinearMap.toSpanSingleton ℝ (innerSL ℝ (Y x))

@[simp]
theorem trivialAddInner_apply (Y : Π x : M, TangentSpace I x) (σ : M → ℝ) (x : M) :
    trivialAddInner Y σ x = mvfderiv I σ x + σ x • innerSL ℝ (Y x) := by
  rw [trivialAddInner, addOneForm_apply, trivial_apply,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- For `Y = 0`, `d + ⟪Y, ·⟫` is the flat connection `d`. -/
@[simp]
theorem trivialAddInner_zero : trivialAddInner (0 : Π x : M, TangentSpace I x) = trivial ℝ := by
  ext σ x : 3
  rw [trivialAddInner_apply, trivial_apply, Pi.zero_apply, map_zero, smul_zero, add_zero]

/-- The connection form of `d + ⟪Y, ·⟫` is `⟪Y, ·⟫`. -/
theorem trivialAddInner_one (Y : Π x : M, TangentSpace I x) (x : M) :
    trivialAddInner Y (1 : M → ℝ) x = innerSL ℝ (Y x) := by
  rw [trivialAddInner_apply, Pi.one_def, mvfderiv_const, zero_add]
  simp

variable [IsManifold I ∞ M]

/-- The connection `d + ⟪Y, ·⟫` is compatible with the standard fibre metric of the trivial line
bundle exactly when `Y = 0`: on a line, the only skew-adjoint connection form is zero. -/
theorem isMetricCompatible_trivialAddInner_iff (Y : Π x : M, TangentSpace I x) :
    (trivialAddInner Y).IsMetricCompatible ↔ Y = 0 := by
  rw [isMetricCompatible_iff]
  constructor
  · intro h
    funext x
    refine ext_inner_left ℝ fun v ↦ ?_
    have hv := h (X := FiberBundle.extend E v) (FiberBundle.mdifferentiableAt_extend I E v)
      (σ := (1 : M → ℝ)) (τ := (1 : M → ℝ)) (Trivial.mdifferentiableAt_mk_const 1)
      (Trivial.mdifferentiableAt_mk_const 1)
    simp only [trivialAddInner_one, innerSL_apply_apply, FiberBundle.extend_apply_self,
      Pi.one_apply, Real.inner_apply, mul_one, one_mul] at hv
    rw [mvfderiv_const, zero_apply] at hv
    rw [Pi.zero_apply, inner_zero_right, real_inner_comm]
    linarith
  · rintro rfl x X σ τ - hσ hτ
    have hσ' := ((Trivial.mdifferentiableAt_mk_iff (b := id) (f := σ)).1 hσ).2
    have hτ' := ((Trivial.mdifferentiableAt_mk_iff (b := id) (f := τ)).1 hτ).2
    simp only [trivialAddInner_apply, Pi.zero_apply, map_zero, smul_zero, add_zero,
      Real.inner_apply]
    rw [mvfderiv_fun_mul hσ' hτ']
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring

variable [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The connection `d + ⟪Y, ·⟫` is smooth for a smooth vector field `Y`. -/
instance (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffCovariantDerivative (trivialAddInner (Y : Π x : M, TangentSpace I x)) ∞ where
  contMDiff.contMDiff {σ} hσ := by
    rw [contMDiffOn_univ] at hσ ⊢
    have hf : ContMDiff I 𝓘(ℝ) (∞ + 1) σ := (Trivial.contMDiff_mk_iff.1 hσ).2
    have hY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (innerSL ℝ (Y x))) :=
      fun x ↦ ContMDiffWithinAt.innerSL_bundle (I := I) (F := E)
        (V := fun x : M ↦ TangentSpace I x) (Y.contMDiff x)
    have h := hf.contMDiff_totalSpaceMk_mvfderiv.add_section
      ((hf.of_le (by simp)).smul_section hY)
    convert h using 3 with x
    rw [trivialAddInner_apply, Pi.add_apply, Pi.smul_apply']

end TrivialLine

end CovariantDerivative
