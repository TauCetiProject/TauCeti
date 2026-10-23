/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Nondegenerate critical points of separated sums

A *separated sum* `φ ∘ Prod.fst + ψ ∘ Prod.snd` on a product `E × F` has block-diagonal second
derivative, so its Hessian quadratic form at `(a, b)` is the orthogonal product of the Hessians of
`φ` at `a` and of `ψ` at `b`. Consequently `(a, b)` is a nondegenerate critical point of the sum
exactly when `a` and `b` are nondegenerate critical points of the summands, and the Morse index
is additive. This is the calculus behind the product of two Morse functions on a product manifold,
whose critical points are the pairs of critical points, graded by the sum of the indices.

## Main declarations

* `TauCeti.hessianQuadraticForm_comp_fst_add_comp_snd`: the Hessian of a separated sum is the
  product of the Hessians of the summands.
* `TauCeti.isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff` and
  `TauCeti.IsNondegenerateCriticalPoint.comp_fst_add_comp_snd`: nondegenerate critical points of
  a separated sum are the pairs of nondegenerate critical points of the summands.
* `TauCeti.morseIndex_comp_fst_add_comp_snd`: the Morse index of a separated sum is the sum of
  the Morse indices of the summands.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
-/

public section

open ContinuousLinearMap

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : E → ℝ} {ψ : F → ℝ} {a : E} {b : F}

/-- The Hessian quadratic form of a separated sum at `(a, b)` is the orthogonal product of the
Hessians of the summands at `a` and `b`. -/
@[simp]
theorem hessianQuadraticForm_comp_fst_add_comp_snd (hφ : ContDiffAt ℝ 2 φ a)
    (hψ : ContDiffAt ℝ 2 ψ b) :
    hessianQuadraticForm (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) =
      (hessianQuadraticForm φ a).prod (hessianQuadraticForm ψ b) := by
  ext ⟨v, w⟩
  rw [hessianQuadraticForm_apply, fderiv_fderiv_comp_fst_add_comp_snd hφ hψ,
    QuadraticMap.prod_apply, hessianQuadraticForm_apply, hessianQuadraticForm_apply]
  simp [coprodEquivL_apply_apply]

/-- **Nondegenerate critical points of a separated sum.** For `φ` twice continuously
differentiable at `a` and `ψ` twice continuously differentiable at `b`, the separated sum
`φ ∘ Prod.fst + ψ ∘ Prod.snd` has a nondegenerate critical point at `(a, b)` exactly when `φ` has
one at `a` and `ψ` has one at `b`. -/
@[simp]
theorem isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff (hφ : ContDiffAt ℝ 2 φ a)
    (hψ : ContDiffAt ℝ 2 ψ b) :
    IsNondegenerateCriticalPoint (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) ↔
      IsNondegenerateCriticalPoint φ a ∧ IsNondegenerateCriticalPoint ψ b := by
  have hcrit := fderiv_comp_fst_add_comp_snd_eq_zero_iff (hφ.differentiableAt two_ne_zero)
    (hψ.differentiableAt two_ne_zero)
  have hsnd := fderiv_fderiv_comp_fst_add_comp_snd hφ hψ
  constructor
  · intro h
    have hinv := h.isInvertible
    rw [hsnd, isInvertible_equiv_comp, isInvertible_prodMap_iff] at hinv
    exact ⟨⟨hφ, (hcrit.1 h.fderiv_eq_zero).1, hinv.1⟩, ⟨hψ, (hcrit.1 h.fderiv_eq_zero).2, hinv.2⟩⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨(hφ.comp _ contDiffAt_fst).add (hψ.comp _ contDiffAt_snd),
      hcrit.2 ⟨h₁.fderiv_eq_zero, h₂.fderiv_eq_zero⟩, ?_⟩
    rw [hsnd, isInvertible_equiv_comp, isInvertible_prodMap_iff]
    exact ⟨h₁.isInvertible, h₂.isInvertible⟩

/-- A pair of nondegenerate critical points of `φ` and `ψ` is a nondegenerate critical point of
the separated sum `φ ∘ Prod.fst + ψ ∘ Prod.snd`. -/
theorem IsNondegenerateCriticalPoint.comp_fst_add_comp_snd (hφ : IsNondegenerateCriticalPoint φ a)
    (hψ : IsNondegenerateCriticalPoint ψ b) :
    IsNondegenerateCriticalPoint (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) :=
  (isNondegenerateCriticalPoint_comp_fst_add_comp_snd_iff hφ.contDiffAt hψ.contDiffAt).2 ⟨hφ, hψ⟩

/-- **The Morse index of a separated sum is additive**: for `φ` twice continuously differentiable
at `a` and `ψ` twice continuously differentiable at `b`, the index of `φ ∘ Prod.fst + ψ ∘ Prod.snd`
at `(a, b)` is the sum of the indices of `φ` at `a` and of `ψ` at `b`. -/
@[simp]
theorem morseIndex_comp_fst_add_comp_snd [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hφ : ContDiffAt ℝ 2 φ a) (hψ : ContDiffAt ℝ 2 ψ b) :
    morseIndex (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) = morseIndex φ a + morseIndex ψ b := by
  simp only [morseIndex_def, hessianQuadraticForm_comp_fst_add_comp_snd hφ hψ,
    QuadraticForm.sigNeg_prod]

end TauCeti

end
