/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

/-!
# Hamiltonian vector fields and gradients for compatible metrics

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M` with a Riemannian metric
`g`, and let `J` be an almost complex structure on a tangent space `T_x M` for which
`g(u, v) = σ(u, J v)`. This is the relation between a symplectic form, a compatible almost complex
structure and its metric `g_J = σ(·, J ·)`; given `g` and `σ`, such a `J` is unique, since
`σ(u, J v) = g(u, v)` for all `u` determines `J v` by nondegeneracy of `σ` at `x`. Then the
Hamiltonian vector field of every function `f`, with the convention `ι_{X_f} σ = df`, and the
gradient of `f` for `g` are related by

`J X_f(x) = ∇f(x)`, equivalently `X_f(x) = -J ∇f(x)`

(`TauCeti.SmoothTwoForm.IsNondegenerate.apply_hamiltonianVectorField_eq_mgradient`,
`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_eq_neg_apply_mgradient`). Indeed
`g(J X_f, v) = g(v, J X_f) = σ(v, J J X_f) = σ(X_f, v) = df(v)`. Only the relation at the single
point `x` is used, and neither closedness of `σ` nor smoothness of `J` is needed.

This is the identity behind the comparison of Floer theory for a small autonomous Hamiltonian with
Morse theory: the Floer equation `∂_s u + J (∂_t u - X_H(u)) = 0` for maps independent of `t`
becomes the gradient equation `∂_s u = ∇H(u)` for the metric `g_J`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford (2017),
  Section 4.1, on compatible almost complex structures and the metric `σ(·, J ·)`.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on `X_H = -J ∇H` and the gradient flow of the action.
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {σ : SmoothTwoForm I M} {x : M} {J : AlmostComplexStructure (TangentSpace I x)}

/-- **`J X_f` is the gradient of `f`.** If the metric at `x` is `g(u, v) = σ(u, J v)`, then
`J X_f(x)` is the gradient of `f` at `x`. -/
theorem apply_hamiltonianVectorField_eq_mgradient (h : σ.IsNondegenerate)
    (hJ : ∀ u v : TangentSpace I x, ⟪u, v⟫ = σ.eval₂ x u (J v)) (f : M → ℝ) :
    J (σ.hamiltonianVectorField f x) = Manifold.mgradient I f x := by
  rw [Manifold.eq_mgradient_iff]
  intro v
  -- `g(J X_f, v) = σ(v, J J X_f) = σ(v, -X_f) = σ(X_f, v) = df(v)`.
  rw [real_inner_comm, hJ, AlmostComplexStructure.apply_apply,
    SmoothBundleForm.eval₂_neg_right, SmoothBundleForm.eval₂_swap, neg_neg,
    h.eval₂_hamiltonianVectorField]

/-- **The Hamiltonian vector field is `-J` times the gradient.** If the metric at `x` is
`g(u, v) = σ(u, J v)`, then `X_f(x) = -J ∇f(x)`. -/
theorem hamiltonianVectorField_eq_neg_apply_mgradient (h : σ.IsNondegenerate)
    (hJ : ∀ u v : TangentSpace I x, ⟪u, v⟫ = σ.eval₂ x u (J v)) (f : M → ℝ) :
    σ.hamiltonianVectorField f x = -J (Manifold.mgradient I f x) := by
  rw [← h.apply_hamiltonianVectorField_eq_mgradient hJ, AlmostComplexStructure.apply_apply,
    neg_neg]

end TauCeti.SmoothTwoForm.IsNondegenerate
