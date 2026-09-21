/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Second-order weak differentiability from directional derivatives

An element of `W^{2,p}(Ω)` is an element of `W^{1,p}(Ω)` together with an `Lᵖ` weak Fréchet
derivative of its weak gradient. Checking that a given `u ∈ W^{1,p}(Ω)` has one means producing
a single `Lᵖ` field of linear maps; this file reduces that to the componentwise data that a
difference-quotient argument actually supplies, namely an `Lᵖ` weak derivative of each scalar
component `⟪∇u, e_j⟫` in each basis direction `e_i`
(`TauCeti.W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn`).

The assembly is the obvious one: the candidate Hessian is
`x ↦ ∑ i, ∑ j, gᵢⱼ(x) ⟪eᵢ, ·⟫ eⱼ`, whose value on `eᵢ` is the vector `∑ j, gᵢⱼ eⱼ` obtained by
recombining the components of the `i`th directional derivative
(`TauCeti.W1p.hasWeakLineDerivOn_gradient_of_forall_inner`). Weak differentiability in every
direction then follows from the basis directions by
`TauCeti.hasWeakFDerivOn_of_forall_basis`.

No boundedness or boundary regularity of `Ω` is used.

## Main declarations

* `TauCeti.W1p.hasWeakLineDerivOn_gradient_of_forall_inner`: a weak directional derivative of
  the weak gradient, reassembled from its orthonormal components.
* `TauCeti.W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn`: componentwise second weak
  derivatives in `Lᵖ(Ω)` place a `W^{1,p}(Ω)` function in `W^{2,p}(Ω)`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **Recombining the components of a directional derivative of the gradient.** If, in the
direction `v`, each scalar component `⟪∇u, eⱼ⟫` of the weak gradient of `u ∈ W^{1,p}(Ω)` has the
weak derivative `gⱼ ∈ Lᵖ(Ω)`, then `∇u` itself has the weak derivative `∑ j, gⱼ eⱼ`. -/
theorem W1p.hasWeakLineDerivOn_gradient_of_forall_inner {ι : Type*} [Fintype ι]
    (u : W1p mu Omega p) (b : OrthonormalBasis ι ℝ E) (v : E)
    (g : ι → Lp ℝ p (mu.restrict Omega))
    (hg : ∀ j, HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient u x, b j⟫_ℝ) (g j) v) :
    HasWeakLineDerivOn mu Omega (W1p.gradient u : E → E)
      (fun x => ∑ j, (g j : E → ℝ) x • b j) v := by
  have hsum : HasWeakLineDerivOn mu Omega
      (fun x => ∑ j, ⟪W1p.gradient u x, b j⟫_ℝ • b j)
      (fun x => ∑ j, (g j : E → ℝ) x • b j) v :=
    HasWeakLineDerivOn.sum Finset.univ fun j => by
      simpa using (hg j).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (b j))
  refine hsum.congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hcomm : ∀ j, ⟪W1p.gradient u x, b j⟫_ℝ = ⟪b j, W1p.gradient u x⟫_ℝ :=
    fun _ => real_inner_comm _ _
  simp only [hcomm]
  exact b.sum_repr' _

/-- **Second-order weak differentiability from directional derivatives.** Fix an orthonormal
basis `e` of `E`. If, for every pair of indices `i, j`, the scalar component `⟪∇u, eⱼ⟫` of the
weak gradient of `u ∈ W^{1,p}(Ω)` has a weak derivative in `Lᵖ(Ω)` in the direction `eᵢ`, then
`u` is the first-order part of an element of `W^{2,p}(Ω)`.

This is how a difference-quotient argument, which produces exactly these componentwise
derivatives, certifies membership in the second-order Sobolev space. -/
theorem W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn {ι : Type*} [Fintype ι]
    (u : W1p mu Omega p) (b : OrthonormalBasis ι ℝ E)
    (h : ∀ i j : ι, ∃ g : Lp ℝ p (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient u x, b j⟫_ℝ) g (b i)) :
    ∃ U : Wkp mu Omega p 2, Wkp.lowerOrder 1 U = u := by
  classical
  choose G hG using h
  -- The candidate Hessian, and its values on the basis.
  set T : ι × ι → (E →L[ℝ] E) := fun p => (innerSL ℝ (b p.1)).smulRight (b p.2) with hT
  set D : E → (E →L[ℝ] E) := fun x => ∑ p : ι × ι, (G p.1 p.2 : E → ℝ) x • T p with hD
  have hortho : ∀ i k : ι, ⟪b i, b k⟫_ℝ = if i = k then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  have hDb : ∀ (k : ι) (x : E), D x (b k) = ∑ j, (G k j : E → ℝ) x • b j := by
    intro k x
    simp only [hD, hT, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hortho, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single k] <;> simp +contextual
  have hmem : MemLp D p (mu.restrict Omega) := by
    rw [hD]
    refine memLp_finsetSum (ι := ι × ι)
      (f := fun p x => (G p.1 p.2 : E → ℝ) x • T p) Finset.univ fun p _ => ?_
    refine MemLp.mono' ((Lp.memLp (G p.1 p.2)).norm.const_smul ‖T p‖)
      ((Lp.aestronglyMeasurable (G p.1 p.2)).smul aestronglyMeasurable_const) ?_
    filter_upwards with x
    simp [norm_smul, mul_comm]
  refine ⟨Wkp.mk 0 u (hmem.toLp D) ?_, Wkp.lowerOrder_mk 0 _ _ _⟩
  rw [Wkp.iteratedGradient_zero]
  refine HasWeakFDerivOn.congr_ae_deriv ?_ hmem.coeFn_toLp.symm
  refine hasWeakFDerivOn_of_forall_basis b.toBasis (W1p.locallyIntegrableOn_gradient u) fun i => ?_
  rw [OrthonormalBasis.coe_toBasis]
  exact (W1p.hasWeakLineDerivOn_gradient_of_forall_inner u b (b i) (G i)
    (hG i)).congr_ae_deriv (Filter.Eventually.of_forall fun x => (hDb i x).symm)

end TauCeti
