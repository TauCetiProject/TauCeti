/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# Torsion-free covariant derivatives

This file names the pointwise torsion-free condition for a covariant derivative on the tangent
bundle.  When the bundled torsion tensor is available, `isTorsionFree_iff_torsion_eq_zero`
identifies this condition with its vanishing. The condition is available without finite
dimensionality or completeness, shows that vector fields whose covariant derivatives vanish at a
point have vanishing Lie bracket there (`IsTorsionFree.mlieBracket_eq_zero_of_cov_eq_zero`), and
supplies the torsion hypothesis for curvature identities such as the first Bianchi identity.
`isTorsionFree_addOneForm` shows that adding a symmetric endomorphism-valued one-form to a
torsion-free connection keeps it torsion-free, as used for the conformally changed Levi-Civita
connection. The symmetrization `CovariantDerivative.symmetrize` removes torsion when the scalar
field has characteristic different from two, without changing the derivative of a section at a
zero of that section. No regularity of the connection is required.
-/

public section

open Bundle VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- A covariant derivative on the tangent bundle is torsion-free when it evaluates the Lie
bracket of differentiable vector fields as the difference of their two covariant derivatives. -/
def IsTorsionFree
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
    MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x

/-- The pointwise characterization of a torsion-free covariant derivative. -/
theorem isTorsionFree_iff
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) :
    cov.IsTorsionFree ↔ ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
      MDiffAt (T% X) x → MDiffAt (T% Y) x →
        cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x := Iff.rfl

/-- Adding a symmetric endomorphism-valued one-form to a torsion-free covariant derivative on the
tangent bundle keeps it torsion-free. -/
theorem isTorsionFree_addOneForm
    {cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)} (ht : cov.IsTorsionFree)
    {A : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] TangentSpace I x}
    (hA : ∀ (x : M) (v w : TangentSpace I x), A x v w = A x w v) :
    (cov.addOneForm A).IsTorsionFree := by
  intro X Y x hX hY
  simp only [addOneForm, add_apply]
  rw [← ht hX hY, hA x (Y x)]
  abel

/-- For a torsion-free connection, two differentiable vector fields whose covariant derivatives
vanish at `x` have vanishing Lie bracket at `x`. -/
theorem IsTorsionFree.mlieBracket_eq_zero_of_cov_eq_zero
    {cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)} (ht : cov.IsTorsionFree)
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hX0 : cov X x = 0) (hY0 : cov Y x = 0) :
    mlieBracket I X Y x = 0 := by
  rw [← (isTorsionFree_iff cov).mp ht hX hY, hY0, hX0]
  simp

section TorsionFree

variable [CompleteSpace E]
  {cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)}
  [cov.ContMDiffCovariantDerivative ∞]

omit [CompleteSpace E] in
/-- Applying a torsion-free connection to the Lie bracket of smooth vector fields gives the
difference of applying it to their two covariant derivatives. -/
theorem covariantDerivative_mlieBracket_apply_eq_sub_of_torsion_free
    (ht : cov.IsTorsionFree)
    {Y Z : Π x : M, TangentSpace I x}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) (u : TangentSpace I x) :
    cov (mlieBracket I Y Z) x u =
      cov (fun y ↦ cov Z y (Y y)) x u - cov (fun y ↦ cov Y y (Z y)) x u := by
  have hYZ := cov.contMDiff_apply hY hZ
  have hZY := cov.contMDiff_apply hZ hY
  have heq : mlieBracket I Y Z =
      (fun y ↦ cov Z y (Y y)) - fun y ↦ cov Y y (Z y) := by
    funext y
    exact ((isTorsionFree_iff cov).mp ht
      (hY.mdifferentiable (by simp) y) (hZ.mdifferentiable (by simp) y)).symm
  rw [heq, cov.isCovariantDerivativeOnUniv.sub (hYZ.mdifferentiable (by simp) x)
    (hZY.mdifferentiable (by simp) x), sub_apply]

end TorsionFree

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 E] [IsManifold I 2 M]

/-- The named torsion-free condition is equivalent to vanishing of the bundled torsion tensor. -/
theorem isTorsionFree_iff_torsion_eq_zero
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) :
    cov.IsTorsionFree ↔ cov.torsion = 0 :=
  cov.torsion_eq_zero_iff.symm

/-- The symmetrization of a tangent-bundle connection, obtained by subtracting half its torsion
from the derivative. With the argument order used by `addOneForm`, this adds half the torsion.
It is torsion-free when `2 ≠ 0`. -/
noncomputable def symmetrize
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) :
    _root_.CovariantDerivative I E (TangentSpace I : M → Type _) :=
  cov.addOneForm (fun x ↦ (2 : 𝕜)⁻¹ • cov.torsion x)

/-- The characteristic equation for the symmetrized connection. -/
theorem symmetrize_apply
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : Π x : M, TangentSpace I x) (x : M) :
    cov.symmetrize X x = cov X x + (2 : 𝕜)⁻¹ • cov.torsion x (X x) := (rfl)

/-- Symmetrization preserves the covariant derivative at a zero of the section. -/
theorem symmetrize_apply_of_eq_zero
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
    {X : Π x : M, TangentSpace I x} {x : M} (hX : X x = 0) :
    cov.symmetrize X x = cov X x := by
  simp [symmetrize_apply, hX]

/-- Symmetrizing a connection removes its torsion when the scalar field has characteristic
different from two. -/
theorem isTorsionFree_symmetrize [NeZero (2 : 𝕜)]
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) :
    cov.symmetrize.IsTorsionFree := by
  intro X Y x hX hY
  rw [symmetrize_apply, symmetrize_apply]
  simp only [add_apply, smul_apply]
  rw [cov.torsion_antisymm (Y x) (X x), smul_neg]
  have hhalf : (2 : 𝕜)⁻¹ • cov.torsion x (X x) (Y x) +
      (2 : 𝕜)⁻¹ • cov.torsion x (X x) (Y x) = cov.torsion x (X x) (Y x) := by
    rw [← add_smul, ← two_mul, mul_inv_cancel₀ (NeZero.ne (2 : 𝕜)), one_smul]
  calc
    _ = cov Y x (X x) - cov X x (Y x) -
        ((2 : 𝕜)⁻¹ • cov.torsion x (X x) (Y x) +
          (2 : 𝕜)⁻¹ • cov.torsion x (X x) (Y x)) := by abel
    _ = mlieBracket I X Y x := by
      rw [hhalf, cov.torsion_apply hX hY]
      abel

end CovariantDerivative
