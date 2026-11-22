/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Pullback
public import TauCeti.Analysis.Normed.Operator.BallDiam
public import TauCeti.Analysis.Sobolev.WeakDeriv.Affine
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.Wkp.LinearIsometry
public import TauCeti.Analysis.Sobolev.Wkp.Seminorm
public import TauCeti.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.MeasureTheory.Function.Lp.Dilation
-- Private: submodule restriction of continuous linear equivalences, translation of test functions,
-- and restricted Haar pushforward bounds are used only inside proofs and private helpers.
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Affine transport and order-by-order seminorm scaling in `W^{k,p}`

Let `B : E ≃L[ℝ] E'` be a continuous linear equivalence between finite-dimensional real inner
product spaces carrying additive Haar measures `μ` and `ν`, let `b : E'`, and let `U ⊆ E`,
`W ⊆ E'` be open sets.

1. **Affine pullback for all `1 ≤ p ≤ ∞` (`TauCeti.Wkp.compAffineL`).** Whenever `x ↦ B x + b` maps
   `U` into `W`, precomposition `u ↦ u (B · + b)` defines a continuous linear operator
   `W^{k,p}(W) →L[ℝ] W^{k,p}(U)` at every order `k` and every exponent `1 ≤ p ≤ ∞` (including
   `p = ∞`, where smooth functions are not dense). Its value is `u (B · + b)` almost everywhere, and
   its weak derivative of order `k + 1` is `(B.iteratedGradientPullback k) (D^{k+1}u (B · + b))`
   almost everywhere—with zero lower-order derivative terms, because higher derivatives of an affine
   map vanish. When `U = (fun x ↦ B x + b) ⁻¹' W`, precomposition with the inverse affine map
   `y ↦ B.symm y - B.symm b` furnishes a Banach-space isomorphism
   `TauCeti.Wkp.compAffineEquiv : W^{k,p}(W) ≃L[ℝ] W^{k,p}(U)` that preserves and reflects zero
   boundary values (`TauCeti.wkp0Submodule`).

2. **Pure order-by-order seminorm scaling.** On a single space `(E, μ)`, unlike general `C^k`
   diffeomorphisms (which mix lower-order derivatives into higher-order norms), affine transport
   scales each derivative order homogeneously without mixing orders:
   * `‖value k (compAffineEquiv μ B b hUW k u)‖ = |det B|⁻¹ ^ (1 / p).toReal * ‖value k u‖`;
   * `‖iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u)‖ ≤
       ‖B‖ ^ (k + 1) * |det B|⁻¹ ^ (1 / p).toReal * ‖iteratedGradient k u‖`;
   * `‖iteratedGradient k u‖ ≤
       ‖B.symm‖ ^ (k + 1) * |det B| ^ (1 / p).toReal *
         ‖iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u)‖`.
   At `p = ∞`, Lean's convention `(1 / ⊤ : ℝ≥0∞).toReal = 0` automatically sets the Jacobian factor
   to `1`. Combining these bounds with Ciarlet's ball-to-diameter inequalities
   (`ContinuousLinearMap.opNorm_le_diam_div_two_mul_of_mapsTo_add_ball`) yields the geometric
   finite-element scaling estimates in terms of domain diameters and inscribed-ball radii, while
   specializing `B` to a nonzero scalar multiple `r • id` gives exact equality at every order.

## Main declarations

* `TauCeti.Wkp.compAffineL`, `TauCeti.Wkp.compAffineEquiv`: affine pullback and Banach-space
  isomorphism on `W^{k,p}` for `1 ≤ p ≤ ∞`.
* `TauCeti.Wkp.value_compAffineL_ae`, `TauCeti.Wkp.iteratedGradient_compAffineL_ae`: value and
  all-order weak-derivative formulas.
* `TauCeti.Wkp.toOrderL_compAffineL`, `TauCeti.Wkp.restrictL_compAffineL`,
  `TauCeti.Wkp.compAffineL_eq_compL`, `TauCeti.Wkp.compAffineL_eq_compLinearIsometryEquiv`:
  commutation with order truncation and subdomain restriction, and compatibility with general `C^k`
  changes of variables and measure-preserving linear isometries.
* `TauCeti.Wkp.compAffineEquiv_mem_wkp0Submodule_iff`, `TauCeti.Wkp0.compAffineEquiv`: invariance
  of `W^{k,p}_0` under invertible affine maps.
* `TauCeti.Wkp.seminorm_compAffineL_le`, `TauCeti.Wkp.seminorm_compAffineEquiv_le`,
  `TauCeti.Wkp.seminorm_le_mul_seminorm_compAffineEquiv`,
  `TauCeti.Wkp.norm_value_compAffineEquiv`,
  `TauCeti.Wkp.norm_value_eq_mul_norm_value_compAffineEquiv`,
  `TauCeti.Wkp.norm_iteratedGradient_compAffineEquiv_le`,
  `TauCeti.Wkp.norm_iteratedGradient_le_mul_norm_iteratedGradient_compAffineEquiv`: two-sided
  order-by-order scaling.
* `TauCeti.Wkp.seminorm_compAffineEquiv_le_of_ball_subset`,
  `TauCeti.Wkp.seminorm_le_mul_seminorm_compAffineEquiv_of_ball_subset`,
  `TauCeti.Wkp.norm_iteratedGradient_compAffineEquiv_le_of_ball_subset`,
  `TauCeti.Wkp.norm_iteratedGradient_le_mul_norm_iteratedGradient_compAffineEquiv_of_ball_subset`:
  Ciarlet geometric scaling bounds.
* `TauCeti.Wkp.seminorm_compAffineEquiv_smulLeft`,
  `TauCeti.Wkp.norm_value_compAffineEquiv_smulLeft`,
  `TauCeti.Wkp.norm_iteratedGradient_compAffineEquiv_smulLeft`: exact dilation identities at every
  order.

## References

* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, SIAM, 2002, §3.1,
  Theorem 3.1.3.
* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, §4.3.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace

namespace TauCeti

section GeneralSpaces

variable {E E' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] {ν : Measure E'} [ν.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {U : Opens E} {W : Opens E'}

namespace Wkp

/-! ### `Lᵖ` pullbacks along an affine map -/

/-- Contravariant pullback of `Lᵖ` iterated-gradient fields along `x ↦ B x + b`. -/
private def pullbackGradientLp (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (j : ℕ) :
    Lp (IteratedGradient E' j) p (ν.restrict W) →L[ℝ] Lp (IteratedGradient E j) p (μ.restrict U) :=
  (((B : E →L[ℝ] E').iteratedGradientPullback j).compLpL p (μ.restrict U)).comp
    (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b W.isOpen.measurableSet hUW)

private theorem pullbackGradientLp_ae (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (j : ℕ)
    (f : Lp (IteratedGradient E' j) p (ν.restrict W)) :
    pullbackGradientLp μ B b hUW j f =ᵐ[μ.restrict U]
      fun x ↦ (B : E →L[ℝ] E').iteratedGradientPullback j (f (B x + b)) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      ((B : E →L[ℝ] E').iteratedGradientPullback j)
      (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b W.isOpen.measurableSet hUW f),
    Lp.coeFn_compContinuousLinearEquivAddRestrict (𝕜 := ℝ) B b W.isOpen.measurableSet hUW f]
    with x h1 h2
  exact h1.trans (congrArg ((B : E →L[ℝ] E').iteratedGradientPullback j) h2)

/-! ### First-order and arbitrary-order affine pullback -/

private theorem hasWeakFDerivOn_compAffineW1p (μ : Measure E) [μ.IsAddHaarMeasure]
    (B : E ≃L[ℝ] E') (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W) (u : W1p ν W p) :
    HasWeakFDerivOn μ U
      (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b W.isOpen.measurableSet hUW (W1p.value u))
      (fun x ↦ innerSL ℝ (pullbackGradientLp μ B b hUW 0 (W1p.gradient u) x)) := by
  have hweak := (W1p.hasWeakFDerivOn u).comp_continuousLinearEquiv_add μ B b hUW
  refine (hweak.congr_ae
    (Lp.coeFn_compContinuousLinearEquivAddRestrict (𝕜 := ℝ) B b W.isOpen.measurableSet hUW
      (W1p.value u)).symm).congr_ae_deriv ?_
  filter_upwards [pullbackGradientLp_ae μ B b hUW 0 (W1p.gradient u)] with x hx
  ext w
  rw [hx, ContinuousLinearMap.iteratedGradientPullback_zero, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left]

private def compAffineW1p (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (u : W1p ν W p) : W1p μ U p :=
  W1p.mk
    (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b W.isOpen.measurableSet hUW (W1p.value u))
    (pullbackGradientLp μ B b hUW 0 (W1p.gradient u)) (hasWeakFDerivOn_compAffineW1p μ B b hUW u)

private theorem gradient_compAffineW1p (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W) (u : Wkp ν W p 1) :
    iteratedGradient 0 (compAffineW1p μ B b hUW u : Wkp μ U p 1) =
      pullbackGradientLp μ B b hUW 0 (iteratedGradient 0 u) := by
  rw [iteratedGradient_zero (mu := μ) (Omega := U) (p := p) (compAffineW1p μ B b hUW u),
    iteratedGradient_zero u]
  exact W1p.gradient_mk _ _ _

/-- Order-`k + 1` affine transport paired with its highest-derivative formula, by recursion on
`k`. -/
private def compAffineSpec (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) :
    (k : ℕ) → {T : Wkp ν W p (k + 1) → Wkp μ U p (k + 1) //
      ∀ u, iteratedGradient k (T u) = pullbackGradientLp μ B b hUW k (iteratedGradient k u)}
  | 0 => ⟨fun u ↦ compAffineW1p μ B b hUW u, gradient_compAffineW1p μ B b hUW⟩
  | k + 1 => ⟨fun u ↦ mk k ((compAffineSpec μ B b hUW k).val (lowerOrder (k + 1) u))
      (pullbackGradientLp μ B b hUW (k + 1) (iteratedGradient (k + 1) u)) (by
        rw [(compAffineSpec μ B b hUW k).property]
        have h :=
          ((hasWeakFDerivOn_iteratedGradient k u).comp_continuousLinearEquiv_add μ B b hUW).clm_comp
            ((B : E →L[ℝ] E').iteratedGradientPullback k)
        refine (h.congr_ae (pullbackGradientLp_ae μ B b hUW k _).symm).congr_ae_deriv ?_
        filter_upwards [pullbackGradientLp_ae μ B b hUW (k + 1) (iteratedGradient (k + 1) u)]
          with x hx
        rw [hx, ContinuousLinearMap.iteratedGradientPullback_succ_apply]),
      fun _ ↦ iteratedGradient_mk _ _ _ _⟩

private theorem lowerOrder_compAffineSpec (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p (k + 2)) :
    lowerOrder (k + 1) ((compAffineSpec μ B b hUW (k + 1)).val u) =
      (compAffineSpec μ B b hUW k).val (lowerOrder (k + 1) u) :=
  lowerOrder_mk _ _ _ _

private theorem value_compAffineSpec (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) :
    ∀ (k : ℕ) (u : Wkp ν W p (k + 1)),
      value (k + 1) ((compAffineSpec μ B b hUW k).val u) =
        Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b W.isOpen.measurableSet hUW
          (value (k + 1) u)
  | 0, u => (value_one (mu := μ) (Omega := U) (p := p) (compAffineW1p μ B b hUW u)).trans <| by
      rw [value_one u]
      exact W1p.value_mk _ _ _
  | k + 1, u => by
      rw [value_succ (k + 1), lowerOrder_compAffineSpec, value_compAffineSpec μ B b hUW k,
        value_succ (k + 1) u]

private def compAffineBound (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) : ℕ → ℝ
  | 0 => ‖Lp.compContinuousLinearEquivAddRestrict (G := ℝ) (p := p) ℝ μ ν B b
      W.isOpen.measurableSet hUW‖ +
      ‖pullbackGradientLp (ν := ν) (p := p) μ B b hUW 0‖
  | k + 1 => compAffineBound μ B b hUW k +
      ‖pullbackGradientLp (ν := ν) (p := p) μ B b hUW (k + 1)‖

private theorem compAffineBound_nonneg (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) :
    0 ≤ compAffineBound (ν := ν) (p := p) μ B b hUW k := by
  induction k with
  | zero =>
      exact add_nonneg (ContinuousLinearMap.opNorm_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)
  | succ k ih => exact add_nonneg ih (ContinuousLinearMap.opNorm_nonneg _)

private theorem norm_compAffineSpec_le (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W) :
    ∀ (k : ℕ) (u : Wkp ν W p (k + 1)),
      ‖(compAffineSpec μ B b hUW k).val u‖ ≤ compAffineBound (ν := ν) (p := p) μ B b hUW k * ‖u‖
  | 0, u => by
      refine (norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 _).trans ?_
      have hlow : lowerOrder 0 ((compAffineSpec μ B b hUW 0).val u) =
          Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b W.isOpen.measurableSet hUW
            (value 1 u) :=
        (value_zero _).symm.trans ((value_succ 0 _).symm.trans (value_compAffineSpec μ B b hUW 0 u))
      rw [hlow, (compAffineSpec μ B b hUW 0).property, compAffineBound, add_mul]
      exact add_le_add
        (((Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b W.isOpen.measurableSet hUW).le_opNorm
          _).trans (mul_le_mul_of_nonneg_left (norm_value_le 1 u) (norm_nonneg _)))
        (((pullbackGradientLp μ B b hUW 0).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (norm_iteratedGradient_le 0 u) (norm_nonneg _)))
  | k + 1, u => by
      refine (norm_le_norm_lowerOrder_add_norm_iteratedGradient (k + 1) _).trans ?_
      rw [lowerOrder_compAffineSpec, (compAffineSpec μ B b hUW (k + 1)).property,
        compAffineBound, add_mul]
      exact add_le_add
        ((norm_compAffineSpec_le μ B b hUW k _).trans
          (mul_le_mul_of_nonneg_left (norm_lowerOrder_le (k + 1) u)
            (compAffineBound_nonneg μ B b hUW k)))
        (((pullbackGradientLp μ B b hUW (k + 1)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (norm_iteratedGradient_le (k + 1) u) (norm_nonneg _)))

private def compAffineₗ (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) : (k : ℕ) → Wkp ν W p k →ₗ[ℝ] Wkp μ U p k
  | 0 => (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b W.isOpen.measurableSet hUW).toLinearMap
  | k + 1 =>
    { toFun := (compAffineSpec μ B b hUW k).val
      map_add' u v := ext (k + 1) <| by
        rw [value_add, value_compAffineSpec, value_compAffineSpec, value_compAffineSpec,
          value_add, map_add]
      map_smul' c u := ext (k + 1) <| by
        rw [value_smul, value_compAffineSpec, value_compAffineSpec, value_smul, RingHom.id_apply,
          map_smul] }

/-- **Affine pullback on `W^{k,p}` for all `1 ≤ p ≤ ∞`.** If `B : E ≃L[ℝ] E'`, `b : E'`, and
`x ↦ B x + b` maps `U` into `W`, then precomposition `u ↦ u (B · + b)` is a continuous linear map
`W^{k,p}(W) →L[ℝ] W^{k,p}(U)` at every order `k` and every exponent `1 ≤ p ≤ ∞`. -/
def compAffineL (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) : (k : ℕ) → Wkp ν W p k →L[ℝ] Wkp μ U p k
  | 0 => Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b W.isOpen.measurableSet hUW
  | k + 1 => (compAffineₗ μ B b hUW (k + 1)).mkContinuous
      (compAffineBound (ν := ν) (p := p) μ B b hUW k) (norm_compAffineSpec_le μ B b hUW k)

private theorem compAffineL_succ_apply (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    compAffineL μ B b hUW (k + 1) u = (compAffineSpec μ B b hUW k).val u := by
  simp [compAffineL, compAffineₗ]

private theorem value_compAffineL_eq (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) :
    ∀ (k : ℕ) (u : Wkp ν W p k),
      value k (compAffineL μ B b hUW k u) =
        Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b W.isOpen.measurableSet hUW (value k u)
  | 0, u => by simp [compAffineL]
  | k + 1, u => by
      rw [compAffineL_succ_apply]
      exact value_compAffineSpec μ B b hUW k u

/-- The value of `compAffineL μ B b hUW k u` is `x ↦ value k u (B x + b)` almost everywhere on
`U`. -/
theorem value_compAffineL_ae (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p k) :
    (value k (compAffineL μ B b hUW k u) : E → ℝ) =ᵐ[μ.restrict U]
      fun x ↦ value k u (B x + b) := by
  rw [value_compAffineL_eq]
  exact Lp.coeFn_compContinuousLinearEquivAddRestrict (𝕜 := ℝ) B b W.isOpen.measurableSet hUW
    (value k u)

/-- **All-order chain rule for affine pullback.** The highest weak derivative of
`compAffineL μ B b hUW (k + 1) u` at `x` is the pullback along `B` in all `k + 1` slots of the
highest weak derivative of `u` at `B x + b`, with no lower-order derivative terms. -/
theorem iteratedGradient_compAffineL_ae (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    iteratedGradient k (compAffineL μ B b hUW (k + 1) u) =ᵐ[μ.restrict U]
      fun x ↦ (B : E →L[ℝ] E').iteratedGradientPullback k (iteratedGradient k u (B x + b)) := by
  rw [compAffineL_succ_apply, (compAffineSpec μ B b hUW k).property]
  exact pullbackGradientLp_ae μ B b hUW k (iteratedGradient k u)

/-- An element of `W^{k,p}(U)` equals `compAffineL μ B b hUW k u` if and only if its value is
`x ↦ value k u (B x + b)` almost everywhere on `U`. -/
theorem compAffineL_eq_iff (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p k) (w : Wkp μ U p k) :
    compAffineL μ B b hUW k u = w ↔
      (value k w : E → ℝ) =ᵐ[μ.restrict U] fun x ↦ value k u (B x + b) :=
  ⟨fun hw ↦ hw ▸ value_compAffineL_ae μ B b hUW k u,
    fun hw ↦ ext k (Lp.ext ((value_compAffineL_ae μ B b hUW k u).trans hw.symm))⟩

/-- Affine pullback commutes with forgetting the highest weak derivative. -/
theorem lowerOrder_compAffineL (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    lowerOrder k (compAffineL μ B b hUW (k + 1) u) = compAffineL μ B b hUW k (lowerOrder k u) := by
  refine ((compAffineL_eq_iff μ B b hUW k (lowerOrder k u) _).2 ?_).symm
  filter_upwards [value_compAffineL_ae μ B b hUW (k + 1) u] with x hx
  rw [← value_succ, hx, value_succ]

/-- Affine pullback commutes with order truncation `TauCeti.Wkp.toOrderL`. -/
theorem toOrderL_compAffineL (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) {j k : ℕ} (h : j ≤ k) (u : Wkp ν W p k) :
    toOrderL h (compAffineL μ B b hUW k u) = compAffineL μ B b hUW j (toOrderL h u) := by
  refine ((compAffineL_eq_iff μ B b hUW j (toOrderL h u) _).2 ?_).symm
  rw [value_toOrderL]
  filter_upwards [value_compAffineL_ae μ B b hUW k u] with x hx
  rw [hx, value_toOrderL]

/-- Affine pullback commutes with taking the first-order Sobolev component. -/
theorem firstOrder_compAffineL (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    firstOrder k (compAffineL μ B b hUW (k + 1) u) =
      (compAffineL μ B b hUW 1 (firstOrder k u) : W1p μ U p) := by
  refine W1p.ext_value (Lp.ext ?_)
  rw [value_firstOrder, ← value_one (mu := μ) (Omega := U) (p := p)]
  filter_upwards [value_compAffineL_ae μ B b hUW (k + 1) u,
    value_compAffineL_ae μ B b hUW 1 (firstOrder k u)] with x hx1 hx2
  rw [hx1, hx2, value_one (mu := ν) (Omega := W) (p := p) (firstOrder k u), value_firstOrder]

/-- Affine pullback commutes with restriction to open subdomains. -/
theorem restrictL_compAffineL (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    {U' : Opens E} {W' : Opens E'} (hU : U' ≤ U) (hW : W' ≤ W)
    (hUW : MapsTo (fun x ↦ B x + b) U W) (hUW' : MapsTo (fun x ↦ B x + b) U' W')
    (k : ℕ) (u : Wkp ν W p k) :
    restrictL hU k (compAffineL μ B b hUW k u) =
      compAffineL μ B b hUW' k (restrictL hW k u) := by
  refine ((compAffineL_eq_iff μ B b hUW' k (restrictL hW k u) _).2 ?_).symm
  have hqmp := Measure.quasiMeasurePreserving_continuousLinearEquiv_add_restrict μ ν B b hUW'
  filter_upwards [value_restrictL_ae hU k (compAffineL μ B b hUW k u),
    ae_restrict_of_ae_restrict_of_subset hU (value_compAffineL_ae μ B b hUW k u),
    hqmp.ae (value_restrictL_ae hW k u)] with x h1 h2 h3
  rw [h1, h2, h3]

/-- Precomposing with the identity affine map `x ↦ x + 0` is the identity operator on
`W^{k,p}(U)`. -/
@[simp]
theorem compAffineL_refl_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    (hU : MapsTo (fun x : E ↦ ContinuousLinearEquiv.refl ℝ E x + 0) U U) (k : ℕ) :
    compAffineL (ν := μ) (p := p) μ (ContinuousLinearEquiv.refl ℝ E) 0 hU k =
      ContinuousLinearMap.id ℝ (Wkp μ U p k) := by
  ext1 u
  refine (compAffineL_eq_iff μ _ _ hU k u u).2 ?_
  filter_upwards with x
  simp

/-- **Contravariant functoriality.** Precomposing with `y ↦ B₂ y + b₂` and then with
`x ↦ B₁ x + b₁` equals precomposing with `x ↦ (B₁.trans B₂) x + (B₂ b₁ + b₂)`. -/
theorem compAffineL_comp {E'' : Type*} [NormedAddCommGroup E''] [InnerProductSpace ℝ E'']
    [FiniteDimensional ℝ E''] [MeasurableSpace E''] [BorelSpace E''] {ρ : Measure E''}
    [ρ.IsAddHaarMeasure] (μ : Measure E) [μ.IsAddHaarMeasure] {O : Opens E''}
    (B₁ : E ≃L[ℝ] E') (b₁ : E') (hUW : MapsTo (fun x ↦ B₁ x + b₁) U W)
    (B₂ : E' ≃L[ℝ] E'') (b₂ : E'') (hWO : MapsTo (fun y ↦ B₂ y + b₂) W O)
    (hUO : MapsTo (fun x ↦ (B₁.trans B₂) x + (B₂ b₁ + b₂)) U O) (k : ℕ) :
    (compAffineL (ν := ν) (p := p) μ B₁ b₁ hUW k).comp
        (compAffineL (ν := ρ) (p := p) ν B₂ b₂ hWO k) =
      compAffineL (ν := ρ) (p := p) μ (B₁.trans B₂) (B₂ b₁ + b₂) hUO k := by
  ext1 u
  symm
  refine (compAffineL_eq_iff μ _ _ hUO k u _).2 ?_
  have hqmp := Measure.quasiMeasurePreserving_continuousLinearEquiv_add_restrict μ ν B₁ b₁ hUW
  filter_upwards [value_compAffineL_ae μ B₁ b₁ hUW k (compAffineL ν B₂ b₂ hWO k u),
    hqmp.ae (value_compAffineL_ae ν B₂ b₂ hWO k u)] with x h1 h2
  rw [ContinuousLinearMap.comp_apply, h1, h2]
  simp [add_assoc]

/-- For a measure-preserving linear isometry `e`, `compAffineL` with zero translation agrees with
`TauCeti.Wkp.compLinearIsometryEquiv`. -/
theorem compAffineL_eq_compLinearIsometryEquiv {μ : Measure E} [μ.IsAddHaarMeasure]
    (e : E ≃ₗᵢ[ℝ] E') (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ)
    (u : Wkp ν W p k) :
    compAffineL μ e.toContinuousLinearEquiv 0
        (fun x hx ↦ by simpa [hUW] using hx) k u =
      compLinearIsometryEquiv he hUW k u := by
  refine (compAffineL_eq_iff μ _ _ _ k u _).2 ?_
  filter_upwards [value_compLinearIsometryEquiv_ae he hUW k u] with x hx
  simpa using hx

/-- On a single space, `compAffineL` agrees with the general `C^k` change-of-variables operator
`TauCeti.Wkp.compL`. -/
theorem compAffineL_eq_compL {μ : Measure E} [μ.IsAddHaarMeasure] {V : Opens E} {L c : ℝ}
    (B : E ≃L[ℝ] E) (b : E) (h : IsChangeOfVariables k U V (fun x ↦ B x + b) L c) :
    compAffineL (ν := μ) (p := p) μ B b h.mapsTo k = compL h := by
  ext1 u
  exact ((compL_eq_iff h u _).2 (value_compAffineL_ae μ B b h.mapsTo k u)).symm

/-! ### Preimage Banach-space isomorphism and `W^{k,p}_0` invariance -/

/-- **Affine Banach-space isomorphism of `W^{k,p}` for all `1 ≤ p ≤ ∞`.** When
`U = (fun x ↦ B x + b) ⁻¹' W`, precomposition with `x ↦ B x + b` is a continuous linear equivalence
`W^{k,p}(W) ≃L[ℝ] W^{k,p}(U)`, with inverse the precomposition with `y ↦ B.symm y - B.symm b`. -/
def compAffineEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) :
    Wkp ν W p k ≃L[ℝ] Wkp μ U p k :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (compAffineL μ B b (hUW ▸ mapsTo_preimage _ _) k)
    (compAffineL ν B.symm (-B.symm b) (B.toLinearEquiv.mapsTo_symm_add_neg b hUW) k)
    (by
      rw [compAffineL_comp (ν := ν) (ρ := μ) (p := p) μ
        B b (hUW ▸ mapsTo_preimage _ _) B.symm (-B.symm b)
        (B.toLinearEquiv.mapsTo_symm_add_neg b hUW)
        (fun x hx ↦ by simpa [B.symm_apply_apply] using hx) k]
      simp [B.self_trans_symm])
    (by
      rw [compAffineL_comp (ν := μ) (ρ := ν) (p := p) ν
        B.symm (-B.symm b) (B.toLinearEquiv.mapsTo_symm_add_neg b hUW) B b
        (hUW ▸ mapsTo_preimage _ _) (fun y hy ↦ by simpa using hy) k]
      simp [B.symm_trans_self])

/-- Evaluating `compAffineEquiv` applies `compAffineL` along the preimage inclusion. -/
theorem compAffineEquiv_apply (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp ν W p k) :
    compAffineEquiv μ B b hUW k u = compAffineL μ B b (hUW ▸ mapsTo_preimage _ _) k u := by
  simp [compAffineEquiv]

/-- As a continuous linear map, `compAffineEquiv` is `compAffineL` along the preimage inclusion. -/
@[simp]
theorem coe_compAffineEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) :
    (compAffineEquiv (ν := ν) (p := p) μ B b hUW k : Wkp ν W p k →L[ℝ] Wkp μ U p k) =
      compAffineL μ B b (hUW ▸ mapsTo_preimage _ _) k := by
  ext1 u
  exact compAffineEquiv_apply μ B b hUW k u

/-- Evaluating `(compAffineEquiv μ B b hUW k).symm` applies `compAffineL` along the inverse affine
map `y ↦ B.symm y + -B.symm b`. -/
theorem compAffineEquiv_symm_apply (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (w : Wkp μ U p k) :
    (compAffineEquiv (ν := ν) (p := p) μ B b hUW k).symm w =
      compAffineL ν B.symm (-B.symm b) (by exact B.toLinearEquiv.mapsTo_symm_add_neg b hUW)
        k w := by
  simp [compAffineEquiv]

/-- The inverse of `compAffineEquiv μ B b` is `compAffineEquiv ν B.symm (-B.symm b)`. -/
theorem compAffineEquiv_symm (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) :
    (compAffineEquiv (ν := ν) (p := p) μ B b hUW k).symm =
      compAffineEquiv ν B.symm (-B.symm b)
        (by exact B.toLinearEquiv.eq_preimage_symm_add_neg b hUW) k :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ by
    rw [compAffineEquiv_symm_apply μ B b hUW k w, compAffineEquiv_apply]

/-- An element of `W^{k,p}(U)` equals `compAffineEquiv μ B b hUW k u` if and only if its value is
`x ↦ value k u (B x + b)` almost everywhere on `U`. -/
theorem compAffineEquiv_eq_iff (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp ν W p k) (w : Wkp μ U p k) :
    compAffineEquiv μ B b hUW k u = w ↔
      (value k w : E → ℝ) =ᵐ[μ.restrict U] fun x ↦ value k u (B x + b) := by
  rw [compAffineEquiv_apply]
  exact compAffineL_eq_iff μ B b (hUW ▸ mapsTo_preimage _ _) k u w

/-- The value of `compAffineEquiv μ B b hUW k u` is `x ↦ value k u (B x + b)` almost everywhere on
`U`. -/
theorem value_compAffineEquiv_ae (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp ν W p k) :
    (value k (compAffineEquiv μ B b hUW k u) : E → ℝ) =ᵐ[μ.restrict U]
      fun x ↦ value k u (B x + b) := by
  rw [compAffineEquiv_apply]
  exact value_compAffineL_ae μ B b (hUW ▸ mapsTo_preimage _ _) k u

/-- **All-order chain rule for `compAffineEquiv`.** -/
theorem iteratedGradient_compAffineEquiv_ae (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u) =ᵐ[μ.restrict U]
      fun x ↦ (B : E →L[ℝ] E').iteratedGradientPullback k (iteratedGradient k u (B x + b)) := by
  rw [compAffineEquiv_apply]
  exact iteratedGradient_compAffineL_ae μ B b (hUW ▸ mapsTo_preimage _ _) k u

/-- `compAffineEquiv` commutes with forgetting the highest derivative. -/
theorem lowerOrder_compAffineEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    lowerOrder k (compAffineEquiv μ B b hUW (k + 1) u) =
      compAffineEquiv μ B b hUW k (lowerOrder k u) := by
  rw [compAffineEquiv_apply, compAffineEquiv_apply]
  exact lowerOrder_compAffineL μ B b (hUW ▸ mapsTo_preimage _ _) k u

/-- `compAffineEquiv` commutes with order truncation `TauCeti.Wkp.toOrderL`. -/
theorem toOrderL_compAffineEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) {j k : ℕ} (h : j ≤ k) (u : Wkp ν W p k) :
    toOrderL h (compAffineEquiv μ B b hUW k u) =
      compAffineEquiv μ B b hUW j (toOrderL h u) := by
  rw [compAffineEquiv_apply, compAffineEquiv_apply]
  exact toOrderL_compAffineL μ B b (hUW ▸ mapsTo_preimage _ _) h u

/-- `compAffineEquiv` commutes with taking the first-order Sobolev component. -/
theorem firstOrder_compAffineEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    firstOrder k (compAffineEquiv μ B b hUW (k + 1) u) =
      (compAffineEquiv μ B b hUW 1 (firstOrder k u) : W1p μ U p) := by
  rw [compAffineEquiv_apply]
  exact (firstOrder_compAffineL μ B b (hUW ▸ mapsTo_preimage _ _) k u).trans
    (compAffineEquiv_apply μ B b hUW 1 (firstOrder k u)).symm

/-- Precomposing with the identity affine map `x ↦ x + 0` is the identity equivalence on
`W^{k,p}(U)`. -/
@[simp]
theorem compAffineEquiv_refl_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    (hU : (U : Set E) = (fun x : E ↦ ContinuousLinearEquiv.refl ℝ E x + 0) ⁻¹' U) (k : ℕ) :
    compAffineEquiv (ν := μ) (p := p) μ (ContinuousLinearEquiv.refl ℝ E) 0 hU k =
      ContinuousLinearEquiv.refl ℝ (Wkp μ U p k) :=
  ContinuousLinearEquiv.ext <| funext fun u ↦ by simp [compAffineEquiv_apply]

/-- **Contravariant functoriality of `compAffineEquiv`.** Transporting along `y ↦ B₂ y + b₂` and
then along `x ↦ B₁ x + b₁` equals transporting along `x ↦ (B₁.trans B₂) x + (B₂ b₁ + b₂)`. -/
theorem compAffineEquiv_trans {E'' : Type*} [NormedAddCommGroup E''] [InnerProductSpace ℝ E'']
    [FiniteDimensional ℝ E''] [MeasurableSpace E''] [BorelSpace E''] {ρ : Measure E''}
    [ρ.IsAddHaarMeasure] (μ : Measure E) [μ.IsAddHaarMeasure] {O : Opens E''}
    (B₁ : E ≃L[ℝ] E') (b₁ : E') (hUW : (U : Set E) = (fun x ↦ B₁ x + b₁) ⁻¹' W)
    (B₂ : E' ≃L[ℝ] E'') (b₂ : E'') (hWO : (W : Set E') = (fun y ↦ B₂ y + b₂) ⁻¹' O)
    (hUO : (U : Set E) = (fun x ↦ (B₁.trans B₂) x + (B₂ b₁ + b₂)) ⁻¹' O) (k : ℕ) :
    (compAffineEquiv (ν := ρ) (p := p) ν B₂ b₂ hWO k).trans
        (compAffineEquiv (ν := ν) (p := p) μ B₁ b₁ hUW k) =
      compAffineEquiv (ν := ρ) (p := p) μ (B₁.trans B₂) (B₂ b₁ + b₂) hUO k :=
  ContinuousLinearEquiv.ext <| funext fun u ↦ by
    simp only [ContinuousLinearEquiv.trans_apply, compAffineEquiv_apply,
      ← ContinuousLinearMap.comp_apply,
      compAffineL_comp μ B₁ b₁ (hUW ▸ mapsTo_preimage _ _) B₂ b₂ (hWO ▸ mapsTo_preimage _ _)
        (hUO ▸ mapsTo_preimage _ _) k]

/-- Pulling back a compactly supported test function on `W` along `x ↦ B x + b` lands in the
embedded test functions on `U`. -/
theorem exists_compAffineEquiv_ofTestFunctionₗ (μ : Measure E) [μ.IsAddHaarMeasure]
    (B : E ≃L[ℝ] E') (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ)
    (φ : 𝓓(W, ℝ)) :
    ∃ ψ : 𝓓(U, ℝ),
      compAffineEquiv (ν := ν) (p := p) μ B b hUW k (ofTestFunctionₗ k φ) =
        ofTestFunctionₗ k ψ ∧
      ∀ x, ψ x = φ (B x + b) := by
  let W' : Opens E' := ⟨(· + b) ⁻¹' W, W.isOpen.preimage (continuous_add_const b)⟩
  have hWW' : MapsTo (· + -b) W W' := fun y hy ↦ by
    simpa [W'] using hy
  have hW'U : MapsTo B.symm W' U := fun y hy ↦ by
    rw [hUW, mem_preimage, B.apply_symm_apply]
    exact hy
  let ψ : 𝓓(U, ℝ) := B.symm.transportTestFunction hW'U (translateTestFunction hWW' φ)
  have hψ : ∀ x, ψ x = φ (B x + b) := fun x ↦ by
    simp [ψ, sub_neg_eq_add]
  refine ⟨ψ, ?_, hψ⟩
  rw [compAffineEquiv_apply]
  refine (compAffineL_eq_iff μ _ _ _ k (ofTestFunctionₗ k φ) (ofTestFunctionₗ k ψ)).2 ?_
  have hqmp := Measure.quasiMeasurePreserving_continuousLinearEquiv_add_restrict μ ν B b
    (hUW ▸ mapsTo_preimage _ _)
  filter_upwards [value_ofTestFunctionₗ (mu := μ) (p := p) k ψ ▸ testFunctionLp_apply_ae p ψ,
    hqmp.ae (value_ofTestFunctionₗ (mu := ν) (p := p) k φ ▸ testFunctionLp_apply_ae p φ)]
    with x hx hy
  exact hx.trans ((hψ x).trans hy.symm)

/-- `compAffineEquiv` maps `W^{k,p}_0(W)` into `W^{k,p}_0(U)` for every `1 ≤ p ≤ ∞`. -/
theorem compAffineEquiv_mem_wkp0Submodule (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) {u : Wkp ν W p k}
    (hu : u ∈ wkp0Submodule ν W p k) :
    compAffineEquiv μ B b hUW k u ∈ wkp0Submodule μ U p k := by
  refine wkp0Submodule_subset_of_isClosed k
    ((wkp0Submodule μ U p k).isClosed.preimage (compAffineEquiv μ B b hUW k).continuous)
    (fun φ ↦ ?_) hu
  obtain ⟨ψ, hψ, _⟩ := exists_compAffineEquiv_ofTestFunctionₗ (ν := ν) (p := p) μ B b hUW k φ
  rw [mem_preimage, hψ]
  exact ofTestFunctionₗ_mem_wkp0Submodule k ψ

/-- **Zero boundary values are invariant under invertible affine maps** at every order `k` and
every exponent `1 ≤ p ≤ ∞`. -/
@[simp]
theorem compAffineEquiv_mem_wkp0Submodule_iff (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) {u : Wkp ν W p k} :
    compAffineEquiv μ B b hUW k u ∈ wkp0Submodule μ U p k ↔ u ∈ wkp0Submodule ν W p k := by
  refine ⟨fun hu ↦ ?_, compAffineEquiv_mem_wkp0Submodule μ B b hUW k⟩
  have h := compAffineEquiv_mem_wkp0Submodule (ν := μ) (p := p) ν B.symm (-B.symm b)
    (B.toLinearEquiv.eq_preimage_symm_add_neg b hUW) k hu
  rwa [← compAffineEquiv_symm μ B b hUW k, ContinuousLinearEquiv.symm_apply_apply] at h

end Wkp

/-- **Affine Banach-space isomorphism of `W^{k,p}_0` for all `1 ≤ p ≤ ∞`.** -/
def Wkp0.compAffineEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) :
    Wkp0 ν W p k ≃L[ℝ] Wkp0 μ U p k :=
  (Wkp.compAffineEquiv (ν := ν) (p := p) μ B b hUW k).ofSubmodules
    (wkp0Submodule ν W p k).toSubmodule (wkp0Submodule μ U p k).toSubmodule <| by
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact Wkp.compAffineEquiv_mem_wkp0Submodule μ B b hUW k hu
      · intro hw
        exact ⟨(Wkp.compAffineEquiv μ B b hUW k).symm w,
          (Wkp.compAffineEquiv_mem_wkp0Submodule_iff μ B b hUW k).1 (by simpa using hw),
          by simp⟩

/-- Forgetting the zero-boundary condition intertwines `Wkp0.compAffineEquiv` with
`Wkp.compAffineEquiv`. -/
@[simp]
theorem Wkp0.coe_compAffineEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp0 ν W p k) :
    (Wkp0.compAffineEquiv μ B b hUW k u : Wkp μ U p k) =
      Wkp.compAffineEquiv μ B b hUW k (u : Wkp ν W p k) := by
  simp [Wkp0.compAffineEquiv]

/-- Forgetting the zero-boundary condition intertwines `(Wkp0.compAffineEquiv ...).symm` with
`(Wkp.compAffineEquiv ...).symm`. -/
@[simp]
theorem Wkp0.coe_compAffineEquiv_symm (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (w : Wkp0 μ U p k) :
    ((Wkp0.compAffineEquiv (ν := ν) (p := p) μ B b hUW k).symm w : Wkp ν W p k) =
      (Wkp.compAffineEquiv (ν := ν) (p := p) μ B b hUW k).symm (w : Wkp μ U p k) := by
  simp [Wkp0.compAffineEquiv]

/-- The inverse of `Wkp0.compAffineEquiv μ B b` is `Wkp0.compAffineEquiv ν B.symm (-B.symm b)`. -/
theorem Wkp0.compAffineEquiv_symm (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) :
    (Wkp0.compAffineEquiv (ν := ν) (p := p) μ B b hUW k).symm =
      Wkp0.compAffineEquiv ν B.symm (-B.symm b)
        (by exact B.toLinearEquiv.eq_preimage_symm_add_neg b hUW) k :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ Subtype.ext <| by
    simp [Wkp.compAffineEquiv_symm μ B b hUW k]

/-- Precomposing with the identity affine map `x ↦ x + 0` is the identity equivalence on
`W^{k,p}_0(U)`. -/
@[simp]
theorem Wkp0.compAffineEquiv_refl_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    (hU : (U : Set E) = (fun x : E ↦ ContinuousLinearEquiv.refl ℝ E x + 0) ⁻¹' U) (k : ℕ) :
    Wkp0.compAffineEquiv (ν := μ) (p := p) μ (ContinuousLinearEquiv.refl ℝ E) 0 hU k =
      ContinuousLinearEquiv.refl ℝ (Wkp0 μ U p k) :=
  ContinuousLinearEquiv.ext <| funext fun u ↦ Subtype.ext <| by simp

/-- **Contravariant functoriality of `Wkp0.compAffineEquiv`.** -/
theorem Wkp0.compAffineEquiv_trans {E'' : Type*} [NormedAddCommGroup E''] [InnerProductSpace ℝ E'']
    [FiniteDimensional ℝ E''] [MeasurableSpace E''] [BorelSpace E''] {ρ : Measure E''}
    [ρ.IsAddHaarMeasure] (μ : Measure E) [μ.IsAddHaarMeasure] {O : Opens E''}
    (B₁ : E ≃L[ℝ] E') (b₁ : E') (hUW : (U : Set E) = (fun x ↦ B₁ x + b₁) ⁻¹' W)
    (B₂ : E' ≃L[ℝ] E'') (b₂ : E'') (hWO : (W : Set E') = (fun y ↦ B₂ y + b₂) ⁻¹' O)
    (hUO : (U : Set E) = (fun x ↦ (B₁.trans B₂) x + (B₂ b₁ + b₂)) ⁻¹' O) (k : ℕ) :
    (Wkp0.compAffineEquiv (ν := ρ) (p := p) ν B₂ b₂ hWO k).trans
        (Wkp0.compAffineEquiv (ν := ν) (p := p) μ B₁ b₁ hUW k) =
      Wkp0.compAffineEquiv (ν := ρ) (p := p) μ (B₁.trans B₂) (B₂ b₁ + b₂) hUO k :=
  ContinuousLinearEquiv.ext <| funext fun u ↦ Subtype.ext <| by
    simpa using congrArg (fun e ↦ e (u : Wkp ρ O p k))
      (Wkp.compAffineEquiv_trans μ B₁ b₁ hUW B₂ b₂ hWO hUO k)

/-- `Wkp0.compAffineEquiv` commutes with forgetting the highest derivative (`Wkp0.lowerOrderL`). -/
theorem Wkp0.lowerOrderL_compAffineEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp0 ν W p (k + 1)) :
    Wkp0.lowerOrderL k (Wkp0.compAffineEquiv μ B b hUW (k + 1) u) =
      Wkp0.compAffineEquiv μ B b hUW k (Wkp0.lowerOrderL k u) :=
  Subtype.ext <| by
    rw [Wkp0.coe_lowerOrderL, Wkp0.coe_compAffineEquiv, Wkp.lowerOrder_compAffineEquiv,
      Wkp0.coe_compAffineEquiv, Wkp0.coe_lowerOrderL]

end GeneralSpaces

/-! ### Order-by-order seminorm scaling, Ciarlet geometric bounds, and homotheties -/

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {U W : Opens E}

namespace Wkp

/-- **Order-zero upper bound under `MapsTo`.** For `x ↦ B x + b` mapping `U` into `W`, the `Lᵖ`
value norm of `compAffineL μ B b hUW k u` is bounded by `|det B|⁻¹ ^ (1 / p).toReal * ‖value k u‖`
(with exponent `0`, hence factor `1`, at `p = ∞`). -/
theorem norm_value_compAffineL_le (B : E ≃L[ℝ] E) (b : E)
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp μ W p k) :
    ‖value k (compAffineL μ B b hUW k u)‖ ≤
      |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal * ‖value k u‖ := by
  have he : eLpNorm (value k (compAffineL μ B b hUW k u)) p (μ.restrict U) ≤
      ENNReal.ofReal |(LinearMap.det (B : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
        eLpNorm (value k u) p (μ.restrict W) := by
    calc
      eLpNorm (value k (compAffineL μ B b hUW k u)) p (μ.restrict U)
          = eLpNorm (fun x ↦ value k u (B x + b)) p (μ.restrict U) :=
            eLpNorm_congr_ae (value_compAffineL_ae μ B b hUW k u)
      _ ≤ eLpNorm (fun x ↦ value k u (B x + b)) p (μ.restrict ((fun x ↦ B x + b) ⁻¹' W)) :=
            eLpNorm_mono_measure _ (Measure.restrict_mono hUW.subset_preimage le_rfl)
      _ = ENNReal.ofReal |(LinearMap.det (B : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
            eLpNorm (value k u) p (μ.restrict W) :=
            Measure.eLpNorm_comp_continuousLinearEquiv_add_restrict_preimage μ _ B b p
  have hfin : ENNReal.ofReal |(LinearMap.det (B : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
      eLpNorm (value k u) p (μ.restrict W) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
      (Lp.eLpNorm_ne_top _)
  rw [Lp.norm_def, Lp.norm_def, ← Measure.toReal_ofReal_abs_inv_rpow _ (1 / p).toReal,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hfin he

/-- **Order-`k + 1` upper bound under `MapsTo`.** For `x ↦ B x + b` mapping `U` into `W`, the
highest weak-derivative norm scales by at most `‖B‖ ^ (k + 1) * |det B|⁻¹ ^ (1 / p).toReal`, with
zero lower-order mixing and valid for every `1 ≤ p ≤ ∞`. -/
theorem norm_iteratedGradient_compAffineL_le (B : E ≃L[ℝ] E) (b : E)
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp μ W p (k + 1)) :
    ‖iteratedGradient k (compAffineL μ B b hUW (k + 1) u)‖ ≤
      ‖(B : E →L[ℝ] E)‖ ^ (k + 1) * |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal *
        ‖iteratedGradient k u‖ := by
  have hpt : ∀ᵐ x ∂μ.restrict U,
      ‖iteratedGradient k (compAffineL μ B b hUW (k + 1) u) x‖ ≤
        ‖(B : E →L[ℝ] E)‖ ^ (k + 1) * ‖(fun x ↦ iteratedGradient k u (B x + b)) x‖ := by
    filter_upwards [iteratedGradient_compAffineL_ae μ B b hUW k u] with x hx
    rw [hx]
    exact (B : E →L[ℝ] E).norm_iteratedGradientPullback_apply_le k _
  have he : eLpNorm (iteratedGradient k (compAffineL μ B b hUW (k + 1) u)) p (μ.restrict U) ≤
      ENNReal.ofReal (‖(B : E →L[ℝ] E)‖ ^ (k + 1)) *
        (ENNReal.ofReal |(LinearMap.det (B : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
          eLpNorm (iteratedGradient k u) p (μ.restrict W)) := by
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.aestronglyMeasurable _) hpt p).trans ?_
    gcongr
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono hUW.subset_preimage le_rfl)).trans_eq
      (Measure.eLpNorm_comp_continuousLinearEquiv_add_restrict_preimage μ _ B b p)
  have hfin : ENNReal.ofReal (‖(B : E →L[ℝ] E)‖ ^ (k + 1)) *
      (ENNReal.ofReal |(LinearMap.det (B : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal *
        eLpNorm (iteratedGradient k u) p (μ.restrict W)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top <| ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
      (Lp.eLpNorm_ne_top _)
  have h1 := ENNReal.toReal_mono hfin he
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    Measure.toReal_ofReal_abs_inv_rpow _ (1 / p).toReal, ← Lp.norm_def, ← Lp.norm_def,
    ← mul_assoc] at h1
  exact h1

/-- **Seminorm upper bound under `MapsTo` (`1 ≤ p ≤ ∞`).** For any derivative order `j ≤ k`,
`|compAffineL μ B b hUW k u|_{j,p,U} ≤ ‖B‖ ^ j * |det B|⁻¹ ^ (1 / p).toReal * |u|_{j,p,W}`. -/
theorem seminorm_compAffineL_le (B : E ≃L[ℝ] E) (b : E)
    (hUW : MapsTo (fun x ↦ B x + b) U W) {j k : ℕ} (hj : j ≤ k) (u : Wkp μ W p k) :
    seminorm k j hj (compAffineL μ B b hUW k u) ≤
      ‖(B : E →L[ℝ] E)‖ ^ j * |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal *
        seminorm k j hj u := by
  cases j with
  | zero =>
      simpa only [seminorm_zero_apply, pow_zero, one_mul] using
        norm_value_compAffineL_le B b hUW k u
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply, toOrderL_compAffineL]
      exact norm_iteratedGradient_compAffineL_le B b hUW j (toOrderL hj u)

/-- **Exact order-zero scaling on preimages.** When `U = (fun x ↦ B x + b) ⁻¹' W`, the `Lᵖ` value
norm of `compAffineEquiv μ B b hUW k u` equals `|det B|⁻¹ ^ (1 / p).toReal * ‖value k u‖`. -/
@[simp]
theorem norm_value_compAffineEquiv (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp μ W p k) :
    ‖value k (compAffineEquiv μ B b hUW k u)‖ =
      |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal * ‖value k u‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (value_compAffineEquiv_ae μ B b hUW k u), hUW,
    Measure.eLpNorm_comp_continuousLinearEquiv_add_restrict_preimage μ _ B b p,
    ENNReal.toReal_mul, Measure.toReal_ofReal_abs_inv_rpow _ (1 / p).toReal]

/-- **Reverse exact order-zero scaling on preimages.** -/
theorem norm_value_eq_mul_norm_value_compAffineEquiv (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp μ W p k) :
    ‖value k u‖ =
      |LinearMap.det (B : E →ₗ[ℝ] E)| ^ (1 / p).toReal *
        ‖value k (compAffineEquiv μ B b hUW k u)‖ := by
  have hd : 0 < |LinearMap.det (B : E →ₗ[ℝ] E)| :=
    abs_pos.2 (LinearEquiv.isUnit_det' B.toLinearEquiv).ne_zero
  rw [norm_value_compAffineEquiv, ← mul_assoc, Real.inv_rpow hd.le,
    mul_inv_cancel₀ (Real.rpow_pos_of_pos hd _).ne', one_mul]

/-- **Forward order-by-order seminorm scaling (`1 ≤ p ≤ ∞`).** When `U = (fun x ↦ B x + b) ⁻¹' W`,
`|u ∘ F|_{k+1,p,U} ≤ ‖B‖ ^ (k + 1) * |det B| ^ (-(1/p)) * |u|_{k+1,p,W}`. -/
theorem norm_iteratedGradient_compAffineEquiv_le (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp μ W p (k + 1)) :
    ‖iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u)‖ ≤
      ‖(B : E →L[ℝ] E)‖ ^ (k + 1) * |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal *
        ‖iteratedGradient k u‖ :=
  norm_iteratedGradient_compAffineL_le B b (hUW ▸ mapsTo_preimage _ _) k u

/-- **Reverse order-by-order seminorm scaling (`1 ≤ p ≤ ∞`).** When `U = (fun x ↦ B x + b) ⁻¹' W`,
`|u|_{k+1,p,W} ≤ ‖B.symm‖ ^ (k + 1) * |det B| ^ (1/p) * |u ∘ F|_{k+1,p,U}`. -/
theorem norm_iteratedGradient_le_mul_norm_iteratedGradient_compAffineEquiv (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp μ W p (k + 1)) :
    ‖iteratedGradient k u‖ ≤
      ‖(B.symm : E →L[ℝ] E)‖ ^ (k + 1) * |LinearMap.det (B : E →ₗ[ℝ] E)| ^ (1 / p).toReal *
        ‖iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u)‖ := by
  have hsymm := norm_iteratedGradient_compAffineEquiv_le (μ := μ) (p := p)
    B.symm (-B.symm b) (B.toLinearEquiv.eq_preimage_symm_add_neg b hUW) k
    (compAffineEquiv μ B b hUW (k + 1) u)
  rw [← compAffineEquiv_symm μ B b hUW (k + 1), ContinuousLinearEquiv.symm_apply_apply] at hsymm
  rwa [ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, abs_inv,
    inv_inv] at hsymm

/-- **Forward `Wkp.seminorm` scaling on preimages (`1 ≤ p ≤ ∞`).** For any derivative order
`j ≤ k`, `|u ∘ F|_{j,p,U} ≤ ‖B‖ ^ j * |det B|⁻¹ ^ (1 / p).toReal * |u|_{j,p,W}`. -/
theorem seminorm_compAffineEquiv_le (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) {j k : ℕ} (hj : j ≤ k) (u : Wkp μ W p k) :
    seminorm k j hj (compAffineEquiv μ B b hUW k u) ≤
      ‖(B : E →L[ℝ] E)‖ ^ j * |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal *
        seminorm k j hj u :=
  seminorm_compAffineL_le B b (hUW ▸ mapsTo_preimage _ _) hj u

/-- **Reverse `Wkp.seminorm` scaling on preimages (`1 ≤ p ≤ ∞`).** For any derivative order
`j ≤ k`, `|u|_{j,p,W} ≤ ‖B.symm‖ ^ j * |det B| ^ (1 / p).toReal * |u ∘ F|_{j,p,U}`. -/
theorem seminorm_le_mul_seminorm_compAffineEquiv (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) {j k : ℕ} (hj : j ≤ k) (u : Wkp μ W p k) :
    seminorm k j hj u ≤
      ‖(B.symm : E →L[ℝ] E)‖ ^ j * |LinearMap.det (B : E →ₗ[ℝ] E)| ^ (1 / p).toReal *
        seminorm k j hj (compAffineEquiv μ B b hUW k u) := by
  have hsymm := seminorm_compAffineEquiv_le (μ := μ) (p := p)
    B.symm (-B.symm b) (B.toLinearEquiv.eq_preimage_symm_add_neg b hUW) hj
    (compAffineEquiv μ B b hUW k u)
  rw [← compAffineEquiv_symm μ B b hUW k, ContinuousLinearEquiv.symm_apply_apply] at hsymm
  rwa [ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, abs_inv,
    inv_inv] at hsymm

/-- **Ciarlet forward geometric seminorm bound.** If `U = (fun x ↦ B x + b) ⁻¹' W`, `W` is bounded,
and `U` contains a ball of positive radius `ρ'`, then the `(k + 1)`-st weak derivative of `u ∘ F` on
`U` is bounded in terms of `diam W / (2 * ρ')` and `|det B|⁻¹ ^ (1 / p).toReal`. -/
theorem norm_iteratedGradient_compAffineEquiv_le_of_ball_subset (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) {y : E} {ρ' : ℝ} (hρ' : 0 < ρ')
    (hbdd : Bornology.IsBounded (W : Set E)) (hball : Metric.ball y ρ' ⊆ (U : Set E))
    (k : ℕ) (u : Wkp μ W p (k + 1)) :
    ‖iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u)‖ ≤
      (Metric.diam (W : Set E) / (2 * ρ')) ^ (k + 1) *
        |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal * ‖iteratedGradient k u‖ := by
  refine (norm_iteratedGradient_compAffineEquiv_le B b hUW k u).trans ?_
  have hB : ‖(B : E →L[ℝ] E)‖ ≤ Metric.diam (W : Set E) / (2 * ρ') :=
    (B : E →L[ℝ] E).opNorm_le_diam_div_two_mul_of_mapsTo_add_ball hρ' hbdd
      (fun x hx ↦ hUW ▸ hball hx)
  gcongr

/-- **Ciarlet reverse geometric seminorm bound.** If `U = (fun x ↦ B x + b) ⁻¹' W`, `U` is bounded,
and `W` contains a ball of positive radius `ρ`, then the `(k + 1)`-st weak derivative of `u` on `W`
is bounded in terms of `diam U / (2 * ρ)` and `|det B| ^ (1 / p).toReal`. -/
theorem norm_iteratedGradient_le_mul_norm_iteratedGradient_compAffineEquiv_of_ball_subset
    (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) {z : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hbdd : Bornology.IsBounded (U : Set E)) (hball : Metric.ball z ρ ⊆ (W : Set E))
    (k : ℕ) (u : Wkp μ W p (k + 1)) :
    ‖iteratedGradient k u‖ ≤
      (Metric.diam (U : Set E) / (2 * ρ)) ^ (k + 1) *
        |LinearMap.det (B : E →ₗ[ℝ] E)| ^ (1 / p).toReal *
        ‖iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u)‖ := by
  refine (norm_iteratedGradient_le_mul_norm_iteratedGradient_compAffineEquiv B b hUW k u).trans ?_
  have hB : ‖(B.symm : E →L[ℝ] E)‖ ≤ Metric.diam (U : Set E) / (2 * ρ) :=
    B.opNorm_symm_le_diam_div_two_mul_of_ball_subset hρ hbdd hUW.symm.subset hball
  gcongr

/-- **Ciarlet forward geometric `Wkp.seminorm` bound.** For any derivative order `j ≤ k`, if
`U = (fun x ↦ B x + b) ⁻¹' W`, `W` is bounded, and `U` contains a ball of positive radius `ρ'`,
then `seminorm k j hj (compAffineEquiv μ B b hUW k u)` is bounded in terms of
`diam W / (2 * ρ')` and `|det B|⁻¹ ^ (1 / p).toReal`. -/
theorem seminorm_compAffineEquiv_le_of_ball_subset (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) {y : E} {ρ' : ℝ} (hρ' : 0 < ρ')
    (hbdd : Bornology.IsBounded (W : Set E)) (hball : Metric.ball y ρ' ⊆ (U : Set E))
    {j k : ℕ} (hj : j ≤ k) (u : Wkp μ W p k) :
    seminorm k j hj (compAffineEquiv μ B b hUW k u) ≤
      (Metric.diam (W : Set E) / (2 * ρ')) ^ j *
        |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal * seminorm k j hj u := by
  refine (seminorm_compAffineEquiv_le B b hUW hj u).trans ?_
  have hB : ‖(B : E →L[ℝ] E)‖ ≤ Metric.diam (W : Set E) / (2 * ρ') :=
    (B : E →L[ℝ] E).opNorm_le_diam_div_two_mul_of_mapsTo_add_ball hρ' hbdd
      (fun x hx ↦ hUW ▸ hball hx)
  gcongr

/-- **Ciarlet reverse geometric `Wkp.seminorm` bound.** For any derivative order `j ≤ k`, if
`U = (fun x ↦ B x + b) ⁻¹' W`, `U` is bounded, and `W` contains a ball of positive radius `ρ`, then
`seminorm k j hj u` is bounded in terms of `diam U / (2 * ρ)` and `|det B| ^ (1 / p).toReal`. -/
theorem seminorm_le_mul_seminorm_compAffineEquiv_of_ball_subset (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) {z : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hbdd : Bornology.IsBounded (U : Set E)) (hball : Metric.ball z ρ ⊆ (W : Set E))
    {j k : ℕ} (hj : j ≤ k) (u : Wkp μ W p k) :
    seminorm k j hj u ≤
      (Metric.diam (U : Set E) / (2 * ρ)) ^ j *
        |LinearMap.det (B : E →ₗ[ℝ] E)| ^ (1 / p).toReal *
        seminorm k j hj (compAffineEquiv μ B b hUW k u) := by
  refine (seminorm_le_mul_seminorm_compAffineEquiv B b hUW hj u).trans ?_
  have hB : ‖(B.symm : E →L[ℝ] E)‖ ≤ Metric.diam (U : Set E) / (2 * ρ) :=
    B.opNorm_symm_le_diam_div_two_mul_of_ball_subset hρ hbdd hUW.symm.subset hball
  gcongr

/-! ### Exact scaling for homotheties `x ↦ r • x + b` -/

/-- **Exact order-zero dilation identity** along `x ↦ r • x + b` (`r ≠ 0`). -/
theorem norm_value_compAffineEquiv_smulLeft {r : ℝ} (hr : r ≠ 0) (b : E)
    (hUW : (U : Set E) = (fun x ↦ ContinuousLinearEquiv.smulLeft (Units.mk0 r hr) x + b) ⁻¹' W)
    (k : ℕ) (u : Wkp μ W p k) :
    ‖value k (compAffineEquiv μ (ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)) b hUW k u)‖ =
      |r|⁻¹ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) * ‖value k u‖ := by
  rw [norm_value_compAffineEquiv, Measure.abs_inv_det_smulLeft_rpow E p hr]

/-- **Exact order-`k + 1` dilation identity** along `x ↦ r • x + b` (`r ≠ 0`), valid for every
order `k` and every exponent `1 ≤ p ≤ ∞`. -/
theorem norm_iteratedGradient_compAffineEquiv_smulLeft {r : ℝ} (hr : r ≠ 0) (b : E)
    (hUW : (U : Set E) = (fun x ↦ ContinuousLinearEquiv.smulLeft (Units.mk0 r hr) x + b) ⁻¹' W)
    (k : ℕ) (u : Wkp μ W p (k + 1)) :
    ‖iteratedGradient k
        (compAffineEquiv μ (ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)) b hUW (k + 1) u)‖ =
      |r| ^ (k + 1) * |r|⁻¹ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        ‖iteratedGradient k u‖ := by
  set B : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)
  have hclm : (B : E →L[ℝ] E) = r • ContinuousLinearMap.id ℝ E := by
    ext v
    simp [B, Units.smul_def]
  have hae : iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u) =ᵐ[μ.restrict U]
      r ^ (k + 1) • fun x ↦ iteratedGradient k u (B x + b) := by
    filter_upwards [iteratedGradient_compAffineEquiv_ae μ B b hUW k u] with x hx
    rw [hx, hclm, ContinuousLinearMap.iteratedGradientPullback_smul,
      ContinuousLinearMap.iteratedGradientPullback_id, Pi.smul_apply, smul_apply,
      ContinuousLinearMap.id_apply]
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hae, eLpNorm_const_smul, hUW,
    Measure.eLpNorm_comp_continuousLinearEquiv_add_restrict_preimage μ _ B b p,
    ENNReal.toReal_mul, ENNReal.toReal_mul, Measure.toReal_ofReal_abs_inv_rpow _ (1 / p).toReal,
    Measure.abs_inv_det_smulLeft_rpow E p hr, ← mul_assoc]
  congr 2
  rw [toReal_eNorm, Real.norm_eq_abs, abs_pow]

/-- **Exact `Wkp.seminorm` dilation identity** along `x ↦ r • x + b` (`r ≠ 0`), valid for every
derivative order `j ≤ k` and every exponent `1 ≤ p ≤ ∞`. -/
theorem seminorm_compAffineEquiv_smulLeft {r : ℝ} (hr : r ≠ 0) (b : E)
    (hUW : (U : Set E) = (fun x ↦ ContinuousLinearEquiv.smulLeft (Units.mk0 r hr) x + b) ⁻¹' W)
    {j k : ℕ} (hj : j ≤ k) (u : Wkp μ W p k) :
    seminorm k j hj
        (compAffineEquiv μ (ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)) b hUW k u) =
      |r| ^ j * |r|⁻¹ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) * seminorm k j hj u := by
  cases j with
  | zero =>
      simpa only [seminorm_zero_apply, pow_zero, one_mul] using
        norm_value_compAffineEquiv_smulLeft hr b hUW k u
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply, toOrderL_compAffineEquiv]
      exact norm_iteratedGradient_compAffineEquiv_smulLeft hr b hUW j (toOrderL hj u)

end Wkp

end Scaling

/-! ### Concrete checks on intervals -/

section Examples

private def realOpenIoo (a b : ℝ) : Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩

-- Preimage check for `F(x) = 2x + 1` mapping `(0, 1)` onto `(1, 3)`:
-- at `p = 2` on `ℝ`, the value norm scales by `2⁻¹ ^ (1/2)` and the gradient norm by
-- `2 * 2⁻¹ ^ (1/2)`; at `p = ∞`, the exponent-zero convention gives exact factor `2` on the
-- gradient and `4` on the second derivative.
example (u : Wkp volume (realOpenIoo 1 3) 2 1) :
    let B : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero)
    have hUW : (realOpenIoo 0 1 : Set ℝ) = (fun x : ℝ ↦ B x + 1) ⁻¹' (realOpenIoo 1 3 : Set ℝ) := by
      ext x
      simp only [realOpenIoo, Opens.coe_mk, mem_preimage, mem_Ioo, B,
        ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0, smul_eq_mul]
      constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
    ‖Wkp.value 1 (Wkp.compAffineEquiv volume B 1 hUW 1 u)‖ =
        (2 : ℝ)⁻¹ ^ (1 / 2 : ℝ) * ‖Wkp.value 1 u‖ ∧
      ‖Wkp.iteratedGradient 0 (Wkp.compAffineEquiv volume B 1 hUW 1 u)‖ =
        2 * (2 : ℝ)⁻¹ ^ (1 / 2 : ℝ) * ‖Wkp.iteratedGradient 0 u‖ := by
  intro B hUW
  refine ⟨?_, ?_⟩
  · simpa [Module.finrank_self] using
      Wkp.norm_value_compAffineEquiv_smulLeft two_ne_zero (1 : ℝ) hUW 1 u
  · simpa [Module.finrank_self] using
      Wkp.norm_iteratedGradient_compAffineEquiv_smulLeft two_ne_zero (1 : ℝ) hUW 0 u

example (u : Wkp volume (realOpenIoo 1 3) ⊤ 2) :
    let B : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero)
    have hUW : (realOpenIoo 0 1 : Set ℝ) = (fun x : ℝ ↦ B x + 1) ⁻¹' (realOpenIoo 1 3 : Set ℝ) := by
      ext x
      simp only [realOpenIoo, Opens.coe_mk, mem_preimage, mem_Ioo, B,
        ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0, smul_eq_mul]
      constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
    ‖Wkp.iteratedGradient 0 (Wkp.compAffineEquiv volume B 1 hUW 1 (Wkp.lowerOrder 1 u))‖ =
        2 * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ ∧
      ‖Wkp.iteratedGradient 1 (Wkp.compAffineEquiv volume B 1 hUW 2 u)‖ =
        4 * ‖Wkp.iteratedGradient 1 u‖ := by
  intro B hUW
  refine ⟨?_, ?_⟩
  · simpa using Wkp.norm_iteratedGradient_compAffineEquiv_smulLeft two_ne_zero (1 : ℝ) hUW 0
      (Wkp.lowerOrder 1 u)
  · have h := Wkp.norm_iteratedGradient_compAffineEquiv_smulLeft two_ne_zero (1 : ℝ) hUW 1 u
    norm_num [ENNReal.toReal_top] at h
    exact h

end Examples

end TauCeti
