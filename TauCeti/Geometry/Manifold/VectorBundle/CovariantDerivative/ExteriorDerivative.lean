/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField

/-!
# Exterior differentiation and the torsion correction

For a connection `∇` on the tangent bundle, a fixed-coefficient one-form has an induced
covariant derivative: use the Hom connection with ordinary differentiation on its target.
The ordinary exterior derivative is

`dα(u,v) = (∇_u α)(v) - (∇_v α)(u) + α(T(u,v))`.

This comparison applies at a single differentiability point, so local coframes are allowed.
It gives the scalar torsion comparison in Cartan's first structure equation. In particular,
for a torsion-free connection the exterior derivative is the antisymmetric covariant derivative;
a parallel one-form is closed. No metric or regularity of the connection is required.

The form and the induced connection use the existing alternating-map and Hom bundles.
There is no new covector carrier or exterior derivative.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 4 and 7
  (induced connections and torsion).
* The calculation combines `TauCeti.mextDeriv_apply_one` with
  `CovariantDerivative.hom_apply` and Mathlib's torsion evaluation formula.
-/

public noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  {α : (x : M) → TangentSpace I x →L[ℝ] F} {x : M}

/-- The exterior derivative of a differentiable fixed-coefficient one-form is the
antisymmetric induced covariant derivative plus its evaluation on torsion. -/
theorem mextDeriv_ofSubsingleton
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) y (α y)) x)
    (u v : TangentSpace I x) :
    TauCeti.mextDeriv (fun y ↦
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I y) F (0 : Fin 1) (α y))
        x ![u, v] =
      cov.hom (trivial F) α x u v - cov.hom (trivial F) α x v u +
        α x (cov.torsion x u v) := by
  have hU := mdifferentiableAt_extend I E u
  have hV := mdifferentiableAt_extend I E v
  have hd := TauCeti.mextDeriv_apply_one
    (TauCeti.mdifferentiableAt_ofSubsingleton_iff.mpr hα) hU hV
  have h₁ := cov.hom_apply (trivial F) hα hV u
  have h₂ := cov.hom_apply (trivial F) hα hU v
  have hT := cov.torsion_apply hU hV
  simp only [extend_apply_self, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Matrix.cons_val_zero] at hd h₁ h₂ hT
  rw [hd, h₁, h₂, hT]
  simp only [trivial_apply, map_sub]
  abel

/-- For a torsion-free tangent connection, exterior differentiation of a differentiable
one-form is exactly antisymmetrization of the induced Hom connection. -/
theorem mextDeriv_ofSubsingleton_of_torsion_eq_zero (ht : cov.torsion x = 0)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) y (α y)) x)
    (u v : TangentSpace I x) :
    TauCeti.mextDeriv (fun y ↦
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I y) F (0 : Fin 1) (α y))
        x ![u, v] =
      cov.hom (trivial F) α x u v - cov.hom (trivial F) α x v u := by
  simp [cov.mextDeriv_ofSubsingleton hα, ht]

/-- A differentiable fixed-coefficient one-form is closed at a torsion-free point exactly
when its induced covariant derivative is symmetric there. -/
theorem mextDeriv_ofSubsingleton_eq_zero_iff (ht : cov.torsion x = 0)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) y (α y)) x) :
    TauCeti.mextDeriv (fun y ↦
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I y) F (0 : Fin 1) (α y)) x = 0 ↔
      ∀ u v : TangentSpace I x,
        cov.hom (trivial F) α x u v = cov.hom (trivial F) α x v u := by
  constructor
  · intro h u v
    have huv := congrArg (fun form ↦ form ![u, v]) h
    simpa [cov.mextDeriv_ofSubsingleton_of_torsion_eq_zero ht hα, sub_eq_zero] using huv
  · intro h
    ext v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv, cov.mextDeriv_ofSubsingleton_of_torsion_eq_zero ht hα, h]
    simp

end CovariantDerivative
