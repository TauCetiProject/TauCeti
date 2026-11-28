/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry

/-!
# Symmetry of second weak derivatives of `W^{1,p}` functions

The first weak derivatives `∂_y u = ⟪∇u, y⟫` of a Sobolev function `u ∈ W^{1,p}(Ω)` are
weak derivatives of `u` itself, so the commutation of weak derivatives
(`TauCeti.HasWeakLineDerivOn.comm`) applies to them: if `∂_y u` has a weak derivative `G` in the
direction `w`, then `∂_w u` has the same weak derivative `G` in the direction `y`. Tested against
a test function `ψ`, the first weak derivatives of `u` pair symmetrically with those of `ψ`:
`∫ (∂_v ψ) ∂_w u = ∫ (∂_w ψ) ∂_v u`, as both equal `-∫ (∂_v ∂_w ψ) u`. Both sides are continuous
in `ψ` for the `W^{1,q}` norm, so the symmetry extends from test functions to `W^{1,q}_0(Ω)`.

## Main declarations

* `TauCeti.W1p.hasWeakLineDerivOn_inner_gradient`: the weak line derivative of a `W^{1,p}`
  function in the direction `z` is `⟪∇u, z⟫`.
* `TauCeti.W1p.hasWeakLineDerivOn_inner_gradient_comm`: second weak derivatives of a
  `W^{1,p}` function are symmetric.
* `TauCeti.W1p.inner_gradient_ae_eq_of_hasWeakLineDerivOn`: the same symmetry for first
  derivatives given as elements `d, d'` of `W^{1,p}(Ω)`, `∂_w d = ∂_y d'`.
* `TauCeti.W1p.integral_lineDeriv_smul_inner_gradient_comm`: first derivatives of a test function
  and of a `W^{1,p}` function pair symmetrically.
* `TauCeti.W1p.setIntegral_inner_gradient_mul_inner_gradient_comm`: the same symmetry for the first
  derivatives of `f ∈ W^{1,p}(Ω)` and `g ∈ W^{1,q}_0(Ω)`, `∫ ∂_v f ∂_w g = ∫ ∂_w f ∂_v g`, by
  density of test functions in `W^{1,q}_0(Ω)`.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The weak line derivative of `u ∈ W^{1,p}(Ω)` in the direction `z` is `⟪∇u, z⟫`. -/
theorem W1p.hasWeakLineDerivOn_inner_gradient (U : W1p μ Ω p) (z : E) :
    HasWeakLineDerivOn μ Ω (W1p.value U) (fun x => ⟪W1p.gradient U x, z⟫_ℝ) z := by
  simpa only [innerSL_apply_apply] using (W1p.hasWeakFDerivOn U).hasWeakLineDerivOn z

/-- **Second derivatives of a Sobolev function are symmetric.** If `∂_y u = ⟪∇u, y⟫` has the weak
derivative `G` in the direction `w`, then `∂_w u` has the weak derivative `G` in the direction
`y`. -/
theorem W1p.hasWeakLineDerivOn_inner_gradient_comm {U : W1p μ Ω p} {y w : E} {G : E → ℝ}
    (hG : HasWeakLineDerivOn μ Ω (fun x => ⟪W1p.gradient U x, y⟫_ℝ) G w) :
    HasWeakLineDerivOn μ Ω (fun x => ⟪W1p.gradient U x, w⟫_ℝ) G y :=
  (W1p.hasWeakLineDerivOn_inner_gradient U y).comm hG (W1p.hasWeakLineDerivOn_inner_gradient U w)

/-- **Second derivatives of a Sobolev function are symmetric, through its first derivatives.** If
`d, d' ∈ W^{1,p}(Ω)` are the weak derivatives of `u` in the directions `y` and `w`, then
`∂_w d = ∂_y d'` almost everywhere on `Ω`. -/
theorem W1p.inner_gradient_ae_eq_of_hasWeakLineDerivOn [BorelSpace E] {U d d' : W1p μ Ω p}
    {y w : E}
    (hd : HasWeakLineDerivOn μ Ω (W1p.value U) (W1p.value d) y)
    (hd' : HasWeakLineDerivOn μ Ω (W1p.value U) (W1p.value d') w) :
    (fun x => ⟪W1p.gradient d x, w⟫_ℝ) =ᵐ[μ.restrict Ω] fun x => ⟪W1p.gradient d' x, y⟫_ℝ :=
  -- Both are weak derivatives of `∂_w u` in the direction `y`.
  (W1p.hasWeakLineDerivOn_inner_gradient_comm ((W1p.hasWeakLineDerivOn_inner_gradient d w).congr_ae
    (hd.ae_eq (W1p.hasWeakLineDerivOn_inner_gradient U y)))).ae_eq
    ((W1p.hasWeakLineDerivOn_inner_gradient d' y).congr_ae
      (hd'.ae_eq (W1p.hasWeakLineDerivOn_inner_gradient U w)))

open LineDeriv in
/-- **Symmetric pairing of first derivatives.** For `u ∈ W^{1,p}(Ω)`, a test function `ψ` on `Ω`
and directions `v`, `w`, `∫ (∂_v ψ) ⟪∇u, w⟫ = ∫ (∂_w ψ) ⟪∇u, v⟫`: integrating by parts, both
sides are `-∫ (∂_w ∂_v ψ) u`, and derivatives of test functions commute. -/
theorem W1p.integral_lineDeriv_smul_inner_gradient_comm (U : W1p μ Ω p) (ψ : 𝓓(Ω, ℝ)) (v w : E) :
    ∫ x, lineDeriv ℝ (ψ : E → ℝ) x v • ⟪W1p.gradient U x, w⟫_ℝ ∂μ =
      ∫ x, lineDeriv ℝ (ψ : E → ℝ) x w • ⟪W1p.gradient U x, v⟫_ℝ ∂μ := by
  have h := fun z z' : E =>
    (W1p.hasWeakLineDerivOn_inner_gradient U z).integral_lineDeriv_smul_eq_neg_integral_smul
      (∂_{z'} ψ)
  simp only [TestFunction.lineDerivOp_apply] at h
  rw [← neg_neg (∫ x, _ ∂μ), ← h w v]
  simp_rw [TestFunction.lineDeriv_lineDerivOp_comm ψ v w]
  rw [h v w, neg_neg]

open LineDeriv in
/-- **Symmetric pairing of first weak derivatives.** For `f ∈ W^{1,p}(Ω)`, `g ∈ W^{1,q}_0(Ω)`
with Hölder conjugate exponents and directions `v`, `w`, `∫_Ω ∂_v f ∂_w g = ∫_Ω ∂_w f ∂_v g`. On the
whole space every `g ∈ W^{1,q}` qualifies for `q < ∞` (`TauCeti.w1p0Submodule_top_eq_top`). -/
theorem W1p.setIntegral_inner_gradient_mul_inner_gradient_comm [BorelSpace E] {q : ENNReal}
    [Fact (1 ≤ q)] [p.HolderConjugate q] (f : W1p μ Ω p) {g : W1p μ Ω q}
    (hg : g ∈ w1p0Submodule μ Ω q) (v w : E) :
    ∫ x in Ω, ⟪W1p.gradient f x, v⟫_ℝ * ⟪W1p.gradient g x, w⟫_ℝ ∂μ =
      ∫ x in Ω, ⟪W1p.gradient f x, w⟫_ℝ * ⟪W1p.gradient g x, v⟫_ℝ ∂μ := by
  -- The pairing `h ↦ ∫_Ω ∂_a f ∂_b h` is a continuous linear functional on `W^{1,q}(Ω)`.
  let Φ : E → E → W1p μ Ω q →L[ℝ] ℝ := fun a b ↦
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (μ.restrict Ω) p q
      ((innerSL ℝ a).compLp (W1p.gradient f))).comp
      ((ContinuousLinearMap.compLpL q (μ.restrict Ω) (innerSL ℝ b)).comp W1p.gradientL)
  have hΦ (a b : E) (h : W1p μ Ω q) : Φ a b h =
      ∫ x in Ω, ⟪W1p.gradient f x, a⟫_ℝ * ⟪W1p.gradient h x, b⟫_ℝ ∂μ := by
    simp only [Φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.lpPairing_eq_integral,
      W1p.gradientL_apply]
    refine integral_congr_ae ?_
    filter_upwards [(innerSL ℝ a).coeFn_compLp (W1p.gradient f),
      (innerSL ℝ b).coeFn_compLpL (W1p.gradient h)] with x h₁ h₂
    rw [ContinuousLinearMap.mul_apply', h₁, h₂, innerSL_apply_apply, innerSL_apply_apply,
      real_inner_comm a, real_inner_comm b]
  -- Both functionals agree on test functions, hence on their closure `W^{1,q}_0(Ω)`.
  have key := w1p0Submodule_subset_of_isClosed
    (isClosed_eq (Φ v w).continuous (Φ w v).continuous) (fun φ ↦ ?_) hg
  · simpa only [Set.mem_ofPred_eq, hΦ] using key
  have hφ (a b : E) : Φ a b (W1p.ofTestFunctionₗ μ Ω q φ) =
      ∫ x, lineDeriv ℝ (φ : E → ℝ) x b • ⟪W1p.gradient f x, a⟫_ℝ ∂μ := by
    rw [hΦ, ← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul]
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_ofTestFunctionₗ (mu := μ) (Omega := Ω) (p := q) φ ▸
      gradientTestFunctionLp_apply_ae (mu := μ) q φ] with x hx
    rw [hx, TestFunction.lineDeriv_eq_fderiv, smul_eq_mul, mul_comm, _root_.gradient,
      InnerProductSpace.toDual_symm_apply]
  simp only [Set.mem_ofPred_eq, hφ]
  exact W1p.integral_lineDeriv_smul_inner_gradient_comm f φ w v

end TauCeti
