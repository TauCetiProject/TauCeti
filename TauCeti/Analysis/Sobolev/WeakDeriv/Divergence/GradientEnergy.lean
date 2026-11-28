/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Basic
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Inner
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.Analysis.Sobolev.W1p.Symmetry

/-!
# The gradient energy of a vector field: divergence and antisymmetric part

Let `u : E → E` be a vector field in `H¹`, that is, `u ∈ L²(E; E)` with a weak derivative
`U = ∇u ∈ L²`, on a finite-dimensional real inner product space `E`. In an orthonormal basis,
`tr (U²) = ∑ᵢⱼ ∂ⱼuᵢ ∂ᵢuⱼ` and `(tr U)² = ∑ᵢⱼ ∂ᵢuᵢ ∂ⱼuⱼ`. Integrating by parts twice exchanges
the two derivatives in each term, so the two integrals agree:

`∫ tr ((∇u)²) = ∫ (div u)²`.

Since `‖A - A†‖_HS² = 2 ‖A‖_HS² - 2 tr (A²)` for every operator `A`, the gradient energy splits
into the energy of the antisymmetric part `∇u - (∇u)†` (the vorticity) and of the divergence:

`‖∇u‖²_{L²} = ½ ‖∇u - (∇u)†‖²_{L²} + ‖div u‖²_{L²}`,

with Hilbert–Schmidt norms on the matrix fields. For a solenoidal field the last term vanishes,
so the gradient energy of a divergence-free `H¹` field is controlled by its vorticity alone. Both
terms are needed in general: a gradient field `u = ∇φ` has symmetric derivative, so its gradient
energy is all divergence.

## Main statements

* `TauCeti.HasWeakFDerivOn.integral_trace_comp_self_eq_integral_trace_sq`:
  `∫ tr ((∇u)²) = ∫ (tr ∇u)²`.
* `TauCeti.HasWeakFDerivOn.integral_sq_hilbertSchmidtNorm_eq_sub_adjoint_add_trace_sq`:
  `∫ ‖∇u‖_HS² = ½ ∫ ‖∇u - (∇u)†‖_HS² + ∫ (tr ∇u)²`.
* `TauCeti.IsSolenoidalOn.integral_sq_hilbertSchmidtNorm_eq_sub_adjoint`: for a solenoidal field,
  `∫ ‖∇u‖_HS² = ½ ∫ ‖∇u - (∇u)†‖_HS²`.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace ContinuousLinearMap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {u : E → E} {U : E → E →L[ℝ] E}

/-- **Weak mixed partials of an `H¹` field pair symmetrically.** For `u ∈ L²(E; E)` with a weak
derivative `U ∈ L²` on the whole space and directions `i, j` of an orthonormal basis,
`∫ ∂ⱼuᵢ ∂ᵢuⱼ = ∫ ∂ᵢuᵢ ∂ⱼuⱼ`. -/
private theorem integral_inner_mul_inner_comm (hu : HasWeakFDerivOn μ ⊤ u U)
    (hu₂ : MemLp u 2 μ) (hU₂ : MemLp U 2 μ) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (i j : ι) :
    ∫ x, ⟪b i, U x (b j)⟫_ℝ * ⟪b j, U x (b i)⟫_ℝ ∂μ =
      ∫ x, ⟪b i, U x (b i)⟫_ℝ * ⟪b j, U x (b j)⟫_ℝ ∂μ := by
  -- The component `⟪bₖ, u⟫` is a `W^{1,2}` function whose weak gradient pairs with `bₗ` to
  -- `⟪bₖ, U bₗ⟫`.
  have hcomp (k : ι) : ∃ f : W1p μ ⊤ 2,
      ∀ l, (fun x ↦ ⟪W1p.gradient f x, b l⟫_ℝ) =ᵐ[μ] fun x ↦ ⟪b k, U x (b l)⟫_ℝ := by
    have hc : MemLp (fun x ↦ innerSL ℝ (b k) (u x)) 2 μ := (innerSL ℝ (b k)).comp_memLp' hu₂
    have hD : MemLp (fun x ↦ (innerSL ℝ (b k)).comp (U x)) 2 μ :=
      (compL ℝ E E ℝ (innerSL ℝ (b k))).comp_memLp' hU₂
    obtain ⟨f, -, hf⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn (mu := μ)
      (Omega := ⊤) (by simpa only [Opens.coe_top, Measure.restrict_univ] using hc)
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hD)
      (hu.clm_comp (innerSL ℝ (b k)))
    refine ⟨f, fun l ↦ ?_⟩
    simp only [Opens.coe_top, Measure.restrict_univ] at hf
    filter_upwards [hf] with x hx
    rw [hx, InnerProductSpace.toDual_symm_apply, comp_apply, innerSL_apply_apply]
  obtain ⟨fi, hfi⟩ := hcomp i
  obtain ⟨fj, hfj⟩ := hcomp j
  have h := W1p.setIntegral_inner_gradient_mul_inner_gradient_comm fi
    (W1p.mem_w1p0Submodule_top (by norm_num) fj) (b j) (b i)
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  calc ∫ x, ⟪b i, U x (b j)⟫_ℝ * ⟪b j, U x (b i)⟫_ℝ ∂μ
      = ∫ x, ⟪W1p.gradient fi x, b j⟫_ℝ * ⟪W1p.gradient fj x, b i⟫_ℝ ∂μ :=
        integral_congr_ae <| by filter_upwards [hfi j, hfj i] with x h₁ h₂; rw [h₁, h₂]
    _ = ∫ x, ⟪W1p.gradient fi x, b i⟫_ℝ * ⟪W1p.gradient fj x, b j⟫_ℝ ∂μ := h
    _ = ∫ x, ⟪b i, U x (b i)⟫_ℝ * ⟪b j, U x (b j)⟫_ℝ ∂μ :=
        integral_congr_ae <| by filter_upwards [hfi i, hfj j] with x h₁ h₂; rw [h₁, h₂]

/-- **The trace of the square of a weak gradient integrates to the squared divergence.** For
`u ∈ L²(E; E)` with a weak derivative `U ∈ L²` on the whole space,
`∫ tr (U²) = ∫ (tr U)²`, that is, `∫ ∂ⱼuᵢ ∂ᵢuⱼ = ∫ (div u)²`. -/
theorem HasWeakFDerivOn.integral_trace_comp_self_eq_integral_trace_sq (hu : HasWeakFDerivOn μ ⊤ u U)
    (hu₂ : MemLp u 2 μ) (hU₂ : MemLp U 2 μ) :
    ∫ x, LinearMap.trace ℝ E (U x ∘L U x).toLinearMap ∂μ =
      ∫ x, LinearMap.trace ℝ E (U x).toLinearMap ^ 2 ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  have hint (i j k l) : Integrable
      (fun x ↦ ⟪b i, U x (b j)⟫_ℝ * ⟪b k, U x (b l)⟫_ℝ) μ :=
    (((innerSL ℝ (b i)).comp (apply ℝ E (b j))).comp_memLp' hU₂).integrable_mul
      (((innerSL ℝ (b k)).comp (apply ℝ E (b l))).comp_memLp' hU₂)
  have hsq (A : E →L[ℝ] E) : LinearMap.trace ℝ E A.toLinearMap ^ 2 =
      ∑ i, ∑ j, ⟪b i, A (b i)⟫_ℝ * ⟪b j, A (b j)⟫_ℝ := by
    simp only [LinearMap.trace_eq_sum_inner _ b, sq, Finset.sum_mul_sum, coe_coe]
  simp only [trace_comp_eq_sum_sum_inner_mul_inner _ _ b, hsq]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint _ _ _ _,
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint _ _ _ _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ hint _ _ _ _, integral_finsetSum _ fun j _ ↦ hint _ _ _ _]
  exact Finset.sum_congr rfl fun j _ ↦ integral_inner_mul_inner_comm hu hu₂ hU₂ b i j

/-- **The gradient energy splits into vorticity and divergence.** For `u ∈ L²(E; E)` with a weak
derivative `U ∈ L²` on the whole space,
`∫ ‖U‖_HS² = ½ ∫ ‖U - U†‖_HS² + ∫ (tr U)²`, that is,
`‖∇u‖²_{L²} = ½ ‖∇u - (∇u)†‖²_{L²} + ‖div u‖²_{L²}` with Hilbert–Schmidt norms. -/
theorem HasWeakFDerivOn.integral_sq_hilbertSchmidtNorm_eq_sub_adjoint_add_trace_sq
    (hu : HasWeakFDerivOn μ ⊤ u U)
    (hu₂ : MemLp u 2 μ) (hU₂ : MemLp U 2 μ) :
    ∫ x, (U x).hilbertSchmidtNorm ^ 2 ∂μ =
      (∫ x, (U x - adjoint (U x)).hilbertSchmidtNorm ^ 2 ∂μ) / 2 +
        ∫ x, LinearMap.trace ℝ E (U x).toLinearMap ^ 2 ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  have hint : Integrable (fun x ↦ LinearMap.trace ℝ E (U x ∘L U x).toLinearMap) μ := by
    simp only [trace_comp_eq_sum_sum_inner_mul_inner _ _ b]
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (((innerSL ℝ (b i)).comp (apply ℝ E (b j))).comp_memLp' hU₂).integrable_mul
        (((innerSL ℝ (b j)).comp (apply ℝ E (b i))).comp_memLp' hU₂)
  have hHS : Integrable (fun x ↦ (U x).hilbertSchmidtNorm ^ 2) μ := by
    simp only [sq_hilbertSchmidtNorm_eq_sum _ b]
    refine integrable_finsetSum _ fun i _ ↦ ?_
    have hi : MemLp (fun x ↦ U x (b i)) 2 μ := (apply ℝ E (b i)).comp_memLp' hU₂
    exact (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).1 hi
  simp only [sq_hilbertSchmidtNorm_sub_adjoint]
  rw [integral_sub (hHS.const_mul 2) (hint.const_mul 2),
    integral_const_mul, integral_const_mul,
    hu.integral_trace_comp_self_eq_integral_trace_sq hu₂ hU₂]
  ring

/-- **The gradient energy of a solenoidal field is the energy of its vorticity.** For a
solenoidal `u ∈ L²(E; E)` with a weak derivative `U ∈ L²` on the whole space,
`∫ ‖U‖_HS² = ½ ∫ ‖U - U†‖_HS²`, that is, `‖∇u‖²_{L²} = ½ ‖∇u - (∇u)†‖²_{L²}`. -/
theorem IsSolenoidalOn.integral_sq_hilbertSchmidtNorm_eq_sub_adjoint (hdiv : IsSolenoidalOn μ ⊤ u)
    (hu : HasWeakFDerivOn μ ⊤ u U) (hu₂ : MemLp u 2 μ) (hU₂ : MemLp U 2 μ) :
    ∫ x, (U x).hilbertSchmidtNorm ^ 2 ∂μ =
      (∫ x, (U x - adjoint (U x)).hilbertSchmidtNorm ^ 2 ∂μ) / 2 := by
  have htr : (fun x ↦ LinearMap.trace ℝ E (U x).toLinearMap) =ᵐ[μ] 0 := by
    simpa using hu.hasWeakDivergenceOn.ae_eq (isSolenoidalOn_iff_hasWeakDivergenceOn.1 hdiv)
  have h0 : ∫ x, LinearMap.trace ℝ E (U x).toLinearMap ^ 2 ∂μ = 0 :=
    integral_eq_zero_of_ae <| by filter_upwards [htr] with x hx; simp [hx]
  rw [hu.integral_sq_hilbertSchmidtNorm_eq_sub_adjoint_add_trace_sq hu₂ hU₂, h0, add_zero]

end TauCeti
