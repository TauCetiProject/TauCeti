/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.LinearChange
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Linear changes of variables of quantizations

Under a linear change of coordinates `y = A x` of `ℝⁿ`, a pseudodifferential operator is again a
pseudodifferential operator, and its full symbol transforms exactly as a function on the
cotangent bundle: positions by `A⁻¹` and frequencies, which are covectors, by the transpose `Aᵀ`.
In the left (Kohn–Nirenberg) quantization this is the identity

`Op(a) (u ∘ A) = Op(b) u ∘ A`, with `b(y, η) = a(A⁻¹ y, Aᵀ η)`

(`TauCeti.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv`, for an arbitrary coefficient,
and `TauCeti.Symbol.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv`, where `b` is the symbol
`TauCeti.Symbol.compProdMap A⁻¹ Aᵀ a` of the same order). For nonlinear changes of coordinates the
transformed symbol is only determined by an asymptotic expansion whose leading term is given by
the same rule; the linear case has no lower order corrections.

The transformation of the symbol classes, classical symbols and principal symbols under
`(x, ξ) ↦ (P x, Q ξ)` is in `TauCeti.Analysis.Pseudodifferential.Symbol.LinearChange`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Section 18.1.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, §8.
-/

public section

noncomputable section

open scoped FourierTransform SchwartzMap RealInnerProductSpace
open MeasureTheory Real FourierTransform Module

namespace TauCeti

section Quantization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Linear change of coordinates of a quantization.** For a linear automorphism `A` of `E`,
quantizing `a` on the pullback `u ∘ A` is pulling back the quantization of the transformed
coefficient `b(y, η) = a(A⁻¹ y, Aᵀ η)` on `u`:

`Op(a) (u ∘ A) (x) = Op(b) u (A x)`.

Positions transform by `A⁻¹` and frequencies, being covectors, by the transpose `Aᵀ`. No growth
or smoothness assumption on `a` is needed: both sides are the same Bochner integral after the
substitution `ζ = Aᵀ ζ'` in the frequency. -/
theorem quantizeSchwartzValue_compCLMOfContinuousLinearEquiv (a : E × E → V →L[ℂ] W)
    (A : E ≃L[ℝ] E) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x =
      quantizeSchwartzValue (fun p => a (A.symm p.1, A.adjointEquiv p.2)) u (A x) := by
  set B := A.adjointEquiv
  have hd : |A.toLinearEquiv.toLinearMap.det| ≠ 0 :=
    abs_ne_zero.2 A.toLinearEquiv.isUnit_det'.ne_zero
  have hdet : B.toLinearEquiv.toLinearMap.det = A.toLinearEquiv.toLinearMap.det := by
    have hB : B.toLinearEquiv.toLinearMap = LinearMap.adjoint A.toLinearEquiv.toLinearMap := by
      ext ζ
      simpa [B] using (congrArg (fun f : E →ₗ[ℝ] E => f ζ)
        (ContinuousLinearMap.adjoint_toLinearMap (A : E →L[ℝ] E))).symm
    rw [hB, LinearMap.det_adjoint, star_trivial]
  set g : E → W := fun ζ => 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 (u ∘ A) ζ)
  have hL : quantizeSchwartzValue a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x =
      ∫ ζ, g ζ := by
    simp only [quantizeSchwartzValue_def, g, SchwartzMap.fourier_coe,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hR : quantizeSchwartzValue (fun p => a (A.symm p.1, B p.2)) u (A x) =
      |A.toLinearEquiv.toLinearMap.det| • ∫ ζ, g (B ζ) := by
    rw [quantizeSchwartzValue_def, ← integral_smul]
    congr 1
    funext ζ
    simp only [g, A.fourier_comp, B, ContinuousLinearEquiv.adjointEquiv_apply,
      ContinuousLinearEquiv.adjoint_symm_adjoint_apply, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, map_smul,
      SchwartzMap.fourier_coe]
    rw [ContinuousLinearMap.map_smul_of_tower, smul_comm |A.toLinearEquiv.toLinearMap.det|,
      smul_smul, mul_inv_cancel₀ hd, one_smul]
  rw [hL, hR, Measure.integral_comp_continuousLinearEquiv volume g B, hdet, smul_smul,
    mul_inv_cancel₀ hd, one_smul]

/-- **Linear change of coordinates of the quantization of a symbol.** For a linear automorphism
`A` of `ℝⁿ`, `Op(a) (u ∘ A) = Op(b) u ∘ A` with the symbol `b(y, η) = a(A⁻¹ y, Aᵀ η)` of the same
order. -/
theorem Symbol.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv {n : ℕ} {m : ℝ}
    (a : Symbol n V W m) (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x =
      quantizeSchwartzValue (compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
        A.adjointEquiv a).coefficient u (A x) := by
  have h : (compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) A.adjointEquiv
      a).coefficient = fun p => a.coefficient (A.symm p.1, A.adjointEquiv p.2) :=
    funext (coefficient_compProdMap _ _ a)
  rw [h]
  exact TauCeti.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv _ A u x

end Quantization

end TauCeti
