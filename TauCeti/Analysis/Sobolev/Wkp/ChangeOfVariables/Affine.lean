/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Pullback
public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import TauCeti.Analysis.Distribution.TestFunction.Translation
public import TauCeti.Analysis.Normed.Operator.BallDiam
public import TauCeti.Analysis.Sobolev.WeakDeriv.Affine
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
public import TauCeti.Analysis.Sobolev.Wkp.Seminorm
public import TauCeti.Analysis.Sobolev.Wkp.Zero
public import TauCeti.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.MeasureTheory.Function.Lp.Dilation
-- Private: submodule restriction of continuous linear equivalences and restricted Haar
-- pushforward bounds are used only inside proofs and private helpers.
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Topology.Algebra.Module.Determinant
import TauCeti.Topology.Sets.Opens

/-!
# Affine transport and order-by-order seminorm scaling in `W^{k,p}`

Let `B : E ≃L[ℝ] E'` be a continuous linear equivalence between finite-dimensional real inner
product spaces carrying additive Haar measures `μ` and `ν`, let `b : E'`, and let `U ⊆ E`,
`W ⊆ E'` be open sets.

1. **Affine pullback for all `1 ≤ p ≤ ∞` (`TauCeti.Wkp.compAffineL`).** Whenever `x ↦ B x + b` maps
   `U` into `W`, precomposition `u ↦ u (B · + b)` defines `W^{k,p}(W) →L[ℝ] W^{k,p}(U)` at every
   order `k` and exponent `1 ≤ p ≤ ∞` (including `p = ∞`). Its value is `u (B · + b)` a.e., and its
   order-`k + 1` weak derivative is `(B.iteratedGradientPullback k) (D^{k+1}u (B · + b))` a.e.,
   with zero lower-order mixing. When `U = (fun x ↦ B x + b) ⁻¹' W`, the inverse map
   `y ↦ B.symm y - B.symm b` furnishes an isomorphism `TauCeti.Wkp.compAffineEquiv` preserving and
   reflecting `W^{k,p}_0` (`TauCeti.wkp0Submodule`).

2. **Order-by-order and full seminorm scaling.** On `(E, μ)`, affine transport scales each
   derivative order homogeneously (`|det B|⁻¹ ^ (1 / p).toReal` on `value`, times `‖B‖ ^ (k + 1)` on
   `iteratedGradient k`), giving full Sobolev norm and operator-norm bounds (`norm_compAffineL_le`,
   `opNorm_compAffineL_le`), Ciarlet ball-to-diameter geometric estimates, and exact homothety
   identities (`B = r • id`) at every order and exponent (with `(1 / ⊤ : ℝ≥0∞).toReal = 0`).

## Main declarations

* `TauCeti.Wkp.compAffineL`, `TauCeti.Wkp.compAffineEquiv`: affine pullback and Banach-space
  isomorphism on `W^{k,p}` for `1 ≤ p ≤ ∞`.
* `TauCeti.Wkp.value_compAffineL_eq`, `TauCeti.Wkp.iteratedGradient_compAffineL_eq`,
  `TauCeti.Wkp.value_compAffineL_ae`, `TauCeti.Wkp.iteratedGradient_compAffineL_ae`,
  `TauCeti.Wkp.iteratedGradient_one_compAffineEquiv_ae`: bundled and a.e. value and
  weak-derivative formulas.
* `TauCeti.Wkp.toOrderL_compAffineL`, `TauCeti.Wkp.restrictL_compAffineL`: order truncation and
  restriction compatibility.
* `TauCeti.Wkp.compAffineL_ofTestFunctionₗ`, `TauCeti.Wkp.compAffineEquiv_ofTestFunctionₗ`,
  `TauCeti.Wkp.compAffineEquiv_mem_wkp0Submodule_iff`, `TauCeti.Wkp0.compAffineEquiv`: test
  function transport and invariance of `W^{k,p}_0`.
* `TauCeti.Wkp.norm_compAffineL_le`, `TauCeti.Wkp.opNorm_compAffineL_le`,
  `TauCeti.Wkp.seminorm_compAffineL_le`, `TauCeti.Wkp.seminorm_compAffineEquiv_le`,
  `TauCeti.Wkp.seminorm_le_mul_seminorm_compAffineEquiv`, `TauCeti.Wkp.norm_value_compAffineEquiv`,
  `TauCeti.Wkp.norm_value_eq_mul_norm_value_compAffineEquiv`,
  `TauCeti.Wkp.norm_iteratedGradient_compAffineEquiv_le`,
  `TauCeti.Wkp.norm_iteratedGradient_le_mul_norm_iteratedGradient_compAffineEquiv`: norm, operator
  norm, and order-by-order scaling.
* `TauCeti.Wkp.seminorm_compAffineEquiv_le_of_ball_subset`,
  `TauCeti.Wkp.seminorm_le_mul_seminorm_compAffineEquiv_of_ball_subset`,
  `TauCeti.Wkp.norm_iteratedGradient_compAffineEquiv_le_of_ball_subset`,
  `TauCeti.Wkp.norm_iteratedGradient_le_mul_norm_iteratedGradient_compAffineEquiv_of_ball_subset`:
  Ciarlet geometric bounds.
* `TauCeti.Wkp.seminorm_compAffineEquiv_smulLeft`,
  `TauCeti.Wkp.norm_value_compAffineEquiv_smulLeft`,
  `TauCeti.Wkp.norm_iteratedGradient_compAffineEquiv_smulLeft`: exact dilation identities.

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
    (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW)

private theorem pullbackGradientLp_ae (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (j : ℕ)
    (f : Lp (IteratedGradient E' j) p (ν.restrict W)) :
    pullbackGradientLp μ B b hUW j f =ᵐ[μ.restrict U]
      fun x ↦ (B : E →L[ℝ] E').iteratedGradientPullback j (f (B x + b)) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      ((B : E →L[ℝ] E').iteratedGradientPullback j)
      (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW f),
    Lp.coeFn_compContinuousLinearEquivAddRestrict (𝕜 := ℝ) B b hUW f]
    with x h1 h2
  exact h1.trans (congrArg ((B : E →L[ℝ] E').iteratedGradientPullback j) h2)

/-! ### First-order and arbitrary-order affine pullback -/

private theorem hasWeakFDerivOn_compAffineW1p (μ : Measure E) [μ.IsAddHaarMeasure]
    (B : E ≃L[ℝ] E') (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W) (u : W1p ν W p) :
    HasWeakFDerivOn μ U
      (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW (W1p.value u))
      (fun x ↦ innerSL ℝ (pullbackGradientLp μ B b hUW 0 (W1p.gradient u) x)) := by
  have hweak := (W1p.hasWeakFDerivOn u).comp_continuousLinearEquiv_add μ B b hUW
  refine (hweak.congr_ae
    (Lp.coeFn_compContinuousLinearEquivAddRestrict (𝕜 := ℝ) B b hUW
      (W1p.value u)).symm).congr_ae_deriv ?_
  filter_upwards [pullbackGradientLp_ae μ B b hUW 0 (W1p.gradient u)] with x hx
  ext w
  rw [hx, ContinuousLinearMap.iteratedGradientPullback_zero, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left]

private def compAffineW1p (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (u : W1p ν W p) : W1p μ U p :=
  W1p.mk
    (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW (W1p.value u))
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
        Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW (value (k + 1) u)
  | 0, u => (value_one (mu := μ) (Omega := U) (p := p) (compAffineW1p μ B b hUW u)).trans <| by
      rw [value_one u]
      exact W1p.value_mk _ _ _
  | k + 1, u => by
      rw [value_succ (k + 1), lowerOrder_compAffineSpec, value_compAffineSpec μ B b hUW k,
        value_succ (k + 1) u]

private def compAffineBound (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) : ℕ → ℝ
  | 0 => ‖Lp.compContinuousLinearEquivAddRestrict (G := ℝ) (p := p) ℝ μ ν B b hUW‖ +
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
          Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW (value 1 u) :=
        (value_zero _).symm.trans ((value_succ 0 _).symm.trans (value_compAffineSpec μ B b hUW 0 u))
      rw [hlow, (compAffineSpec μ B b hUW 0).property, compAffineBound, add_mul]
      exact add_le_add
        (((Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW).le_opNorm
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
  | 0 => (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW).toLinearMap
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
  | 0 => Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW
  | k + 1 => (compAffineₗ μ B b hUW (k + 1)).mkContinuous
      (compAffineBound (ν := ν) (p := p) μ B b hUW k) (norm_compAffineSpec_le μ B b hUW k)

private theorem compAffineL_succ_apply (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    compAffineL μ B b hUW (k + 1) u = (compAffineSpec μ B b hUW k).val u := by
  simp [compAffineL, compAffineₗ]

/-- The bundled `Lᵖ` value of `compAffineL μ B b hUW k u` is the restricted affine precomposition
of `value k u`. -/
theorem value_compAffineL_eq (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p k) :
    value k (compAffineL μ B b hUW k u) =
      Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW (value k u) := by
  cases k with
  | zero => simp [compAffineL]
  | succ k =>
      rw [compAffineL_succ_apply]
      exact value_compAffineSpec μ B b hUW k u

/-- The bundled `Lᵖ` highest weak derivative of `compAffineL μ B b hUW (k + 1) u` is the
iterated-gradient pullback postcomposed with restricted affine precomposition. -/
theorem iteratedGradient_compAffineL_eq (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    iteratedGradient k (compAffineL μ B b hUW (k + 1) u) =
      ((B : E →L[ℝ] E').iteratedGradientPullback k).compLpL p (μ.restrict U)
        (Lp.compContinuousLinearEquivAddRestrict ℝ μ ν B b hUW (iteratedGradient k u)) := by
  rw [compAffineL_succ_apply, (compAffineSpec μ B b hUW k).property]
  rfl

/-- The value of `compAffineL μ B b hUW k u` is `x ↦ value k u (B x + b)` almost everywhere on
`U`. -/
theorem value_compAffineL_ae (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp ν W p k) :
    (value k (compAffineL μ B b hUW k u) : E → ℝ) =ᵐ[μ.restrict U]
      fun x ↦ value k u (B x + b) := by
  rw [value_compAffineL_eq]
  exact Lp.coeFn_compContinuousLinearEquivAddRestrict (𝕜 := ℝ) B b hUW (value k u)

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
      compAffineL μ B b (hUW ▸ mapsTo_preimage _ _) k :=
  ContinuousLinearMap.ext (compAffineEquiv_apply μ B b hUW k)

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
      (value k w : E → ℝ) =ᵐ[μ.restrict U] fun x ↦ value k u (B x + b) :=
  (compAffineEquiv_apply μ B b hUW k u).symm ▸
    compAffineL_eq_iff μ B b (hUW ▸ mapsTo_preimage _ _) k u w

/-- The value of `compAffineEquiv μ B b hUW k u` is `x ↦ value k u (B x + b)` almost everywhere on
`U`. -/
theorem value_compAffineEquiv_ae (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp ν W p k) :
    (value k (compAffineEquiv μ B b hUW k u) : E → ℝ) =ᵐ[μ.restrict U]
      fun x ↦ value k u (B x + b) :=
  (compAffineEquiv_apply μ B b hUW k u).symm ▸
    value_compAffineL_ae μ B b (hUW ▸ mapsTo_preimage _ _) k u

/-- **All-order chain rule for `compAffineEquiv`.** -/
theorem iteratedGradient_compAffineEquiv_ae (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u) =ᵐ[μ.restrict U]
      fun x ↦ (B : E →L[ℝ] E').iteratedGradientPullback k (iteratedGradient k u (B x + b)) :=
  (compAffineEquiv_apply μ B b hUW (k + 1) u).symm ▸
    iteratedGradient_compAffineL_ae μ B b (hUW ▸ mapsTo_preimage _ _) k u

/-- **Order-two chain rule for `compAffineEquiv`.** The weak Hessian of `u ∘ (B · + b)` is
`B† ∘L D²u(B · + b) ∘L B` almost everywhere on `U`. -/
theorem iteratedGradient_one_compAffineEquiv_ae (μ : Measure E) [μ.IsAddHaarMeasure]
    (B : E ≃L[ℝ] E') (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W)
    (u : Wkp ν W p 2) :
    iteratedGradient 1 (compAffineEquiv μ B b hUW 2 u) =ᵐ[μ.restrict U]
      fun x ↦ (B : E →L[ℝ] E').adjoint.comp
        ((iteratedGradient 1 u (B x + b)).comp (B : E →L[ℝ] E')) := by
  filter_upwards [iteratedGradient_compAffineEquiv_ae μ B b hUW 1 u] with x hx
  rw [hx, ContinuousLinearMap.iteratedGradientPullback_one_apply]

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
    toOrderL h (compAffineEquiv μ B b hUW k u) = compAffineEquiv μ B b hUW j (toOrderL h u) := by
  rw [compAffineEquiv_apply, compAffineEquiv_apply]
  exact toOrderL_compAffineL μ B b (hUW ▸ mapsTo_preimage _ _) h u

/-- `compAffineEquiv` commutes with taking the first-order Sobolev component. -/
theorem firstOrder_compAffineEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    firstOrder k (compAffineEquiv μ B b hUW (k + 1) u) =
      (compAffineEquiv μ B b hUW 1 (firstOrder k u) : W1p μ U p) := by
  rw [compAffineEquiv_apply μ B b hUW (k + 1) u]
  exact (firstOrder_compAffineL μ B b (hUW ▸ mapsTo_preimage _ _) k u).trans
    (congrArg (fun x : Wkp μ U p 1 ↦ (x : W1p μ U p))
      (compAffineEquiv_apply μ B b hUW 1 (firstOrder k u)).symm)

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

/-- Pulling back an embedded test function `φ` on `W` along `x ↦ B x + b` gives the translated
and linearly transported test function on `U`, whenever the inverse affine map carries `W` into
`U`. -/
theorem compAffineL_ofTestFunctionₗ (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : MapsTo (fun x ↦ B x + b) U W)
    (hWU : MapsTo (fun y ↦ B.symm y + -B.symm b) W U) (k : ℕ) (φ : 𝓓(W, ℝ)) :
    compAffineL μ B b hUW k (ofTestFunctionₗ (mu := ν) (p := p) k φ) =
      ofTestFunctionₗ k (translateTestFunction (h := -B.symm b) (mapsTo_preimage _ _)
        (B.symm.transportTestFunction ℝ
          (Ω := ⟨(· + -B.symm b) ⁻¹' U, U.isOpen.preimage (continuous_add_const _)⟩) hWU φ)) := by
  let ψ : 𝓓(U, ℝ) := translateTestFunction (h := -B.symm b) (mapsTo_preimage _ _)
    (B.symm.transportTestFunction ℝ
      (Ω := ⟨(· + -B.symm b) ⁻¹' U, U.isOpen.preimage (continuous_add_const _)⟩) hWU φ)
  refine (compAffineL_eq_iff μ B b hUW k _ _).2 ?_
  have hqmp := Measure.quasiMeasurePreserving_continuousLinearEquiv_add_restrict μ ν B b hUW
  filter_upwards [value_ofTestFunctionₗ (mu := μ) (p := p) k ψ ▸ testFunctionLp_apply_ae p ψ,
    hqmp.ae (value_ofTestFunctionₗ (mu := ν) (p := p) k φ ▸ testFunctionLp_apply_ae p φ)]
    with x hx hy
  simp only [ψ] at hx
  rw [hx, hy, translateTestFunction_apply]
  exact (ContinuousLinearEquiv.transportTestFunction_apply _ _ φ _).trans (congrArg φ (by simp))

/-- Pulling back an embedded test function `φ` on `W` by `compAffineEquiv` gives the translated
and linearly transported test function on `U`. -/
theorem compAffineEquiv_ofTestFunctionₗ (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (φ : 𝓓(W, ℝ)) :
    compAffineEquiv (ν := ν) (p := p) μ B b hUW k (ofTestFunctionₗ k φ) =
      ofTestFunctionₗ k (translateTestFunction (h := -B.symm b) (mapsTo_preimage _ _)
        (B.symm.transportTestFunction ℝ
          (Ω := ⟨(· + -B.symm b) ⁻¹' U, U.isOpen.preimage (continuous_add_const _)⟩)
          (B.toLinearEquiv.mapsTo_symm_add_neg b hUW) φ)) := by
  rw [compAffineEquiv_apply]
  exact compAffineL_ofTestFunctionₗ μ B b (hUW ▸ mapsTo_preimage _ _)
    (B.toLinearEquiv.mapsTo_symm_add_neg b hUW) k φ

/-- `compAffineEquiv` maps `W^{k,p}_0(W)` into `W^{k,p}_0(U)` for every `1 ≤ p ≤ ∞`. -/
theorem compAffineEquiv_mem_wkp0Submodule (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E')
    (b : E') (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) {u : Wkp ν W p k}
    (hu : u ∈ wkp0Submodule ν W p k) :
    compAffineEquiv μ B b hUW k u ∈ wkp0Submodule μ U p k := by
  refine wkp0Submodule_subset_of_isClosed k
    ((wkp0Submodule μ U p k).isClosed.preimage (compAffineEquiv μ B b hUW k).continuous)
    (fun φ ↦ ?_) hu
  rw [mem_preimage, compAffineEquiv_ofTestFunctionₗ]
  exact ofTestFunctionₗ_mem_wkp0Submodule k _

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
      exact ⟨by rintro ⟨u, hu, rfl⟩; exact Wkp.compAffineEquiv_mem_wkp0Submodule μ B b hUW k hu,
        fun hw ↦ ⟨(Wkp.compAffineEquiv μ B b hUW k).symm w,
          (Wkp.compAffineEquiv_mem_wkp0Submodule_iff μ B b hUW k).1 (by simpa using hw), by simp⟩⟩

/-- Forgetting the zero-boundary condition intertwines `Wkp0.compAffineEquiv` with
`Wkp.compAffineEquiv`. -/
@[simp]
theorem Wkp0.coe_compAffineEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E') (b : E')
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp0 ν W p k) :
    (Wkp0.compAffineEquiv μ B b hUW k u : Wkp μ U p k) =
      Wkp.compAffineEquiv μ B b hUW k (u : Wkp ν W p k) := by simp [Wkp0.compAffineEquiv]

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
    (Wkp0.compAffineEquiv (ν := ν) (p := p) μ B b hUW k).symm = Wkp0.compAffineEquiv ν B.symm
      (-B.symm b) (by exact B.toLinearEquiv.eq_preimage_symm_add_neg b hUW) k :=
  ContinuousLinearEquiv.ext <| funext fun w ↦
    Subtype.ext <| by simp [Wkp.compAffineEquiv_symm μ B b hUW k]

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
      Wkp0.compAffineEquiv μ B b hUW k (Wkp0.lowerOrderL k u) := Subtype.ext <| by
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
  simpa only [one_mul] using Lp.norm_le_mul_det_inv_of_ae_le B b hUW zero_le_one
    ((value_compAffineL_ae μ B b hUW k u).mono fun x hx ↦ by rw [hx, one_mul])

/-- **Order-`k + 1` upper bound under `MapsTo`.** For `x ↦ B x + b` mapping `U` into `W`, the
highest weak-derivative norm scales by at most `‖B‖ ^ (k + 1) * |det B|⁻¹ ^ (1 / p).toReal`, with
zero lower-order mixing and valid for every `1 ≤ p ≤ ∞`. -/
theorem norm_iteratedGradient_compAffineL_le (B : E ≃L[ℝ] E) (b : E)
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp μ W p (k + 1)) :
    ‖iteratedGradient k (compAffineL μ B b hUW (k + 1) u)‖ ≤
      ‖(B : E →L[ℝ] E)‖ ^ (k + 1) * |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal *
        ‖iteratedGradient k u‖ :=
  Lp.norm_le_mul_det_inv_of_ae_le B b hUW (by positivity)
    ((iteratedGradient_compAffineL_ae μ B b hUW k u).mono fun x hx ↦ by
      rw [hx]; exact (B : E →L[ℝ] E).norm_iteratedGradientPullback_apply_le k _)

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

/-- **Full Sobolev norm bound under `MapsTo` (`1 ≤ p ≤ ∞`).** For `x ↦ B x + b` mapping `U` into
`W`, `‖compAffineL μ B b hUW k u‖ ≤ |det B|⁻¹ ^ (1 / p).toReal * (max 1 ‖B‖) ^ k * ‖u‖`. -/
theorem norm_compAffineL_le (B : E ≃L[ℝ] E) (b : E)
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) (u : Wkp μ W p k) :
    ‖compAffineL μ B b hUW k u‖ ≤
      |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal * max 1 ‖(B : E →L[ℝ] E)‖ ^ k * ‖u‖ :=
  norm_le_mul_pow_of_ae_le
    (Measure.quasiMeasurePreserving_continuousLinearEquiv_add_restrict μ μ B b hUW)
    (fun j w ↦ compAffineL μ B b hUW j w)
    (fun j w ↦ lowerOrder_compAffineL μ B b hUW j w)
    (by positivity) (le_max_left 1 ‖(B : E →L[ℝ] E)‖)
    (fun w ↦ by simpa only [value_zero] using norm_value_compAffineL_le B b hUW 0 w)
    (fun f g hpt ↦ by
      rw [mul_comm (_ ^ _) (max _ _)]
      exact Lp.norm_le_mul_det_inv_of_ae_le B b hUW (zero_le_one.trans (le_max_left _ _)) hpt)
    (fun w ↦ (value_compAffineL_ae μ B b hUW 1 w).mono fun _ hx ↦ by
      rw [hx]
      exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
    (fun w ↦ (iteratedGradient_compAffineL_ae μ B b hUW 0 w).mono fun _ hx ↦ by
      rw [hx, ContinuousLinearMap.iteratedGradientPullback_zero]
      refine ((B : E →L[ℝ] E).adjoint.le_opNorm _).trans ?_
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    (fun j w ↦ (norm_iteratedGradient_compAffineL_le B b hUW (j + 1) w).trans <| by
      rw [mul_comm (‖(B : E →L[ℝ] E)‖ ^ (j + 2)) _]
      gcongr
      exact le_max_right _ _)
    k u

/-- **Operator-norm bound for `compAffineL` (`1 ≤ p ≤ ∞`).** For `x ↦ B x + b` mapping `U` into
`W`, `‖compAffineL (ν := μ) (p := p) μ B b hUW k‖ ≤ |det B|⁻¹ ^ (1 / p).toReal * (max 1 ‖B‖) ^ k`.
-/
theorem opNorm_compAffineL_le (μ : Measure E) [μ.IsAddHaarMeasure] (B : E ≃L[ℝ] E) (b : E)
    (hUW : MapsTo (fun x ↦ B x + b) U W) (k : ℕ) :
    ‖compAffineL (ν := μ) (p := p) μ B b hUW k‖ ≤
      |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal * max 1 ‖(B : E →L[ℝ] E)‖ ^ k :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_compAffineL_le (μ := μ) B b hUW k)

/-- **Exact order-zero scaling on preimages.** When `U = (fun x ↦ B x + b) ⁻¹' W`, the `Lᵖ` value
norm of `compAffineEquiv μ B b hUW k u` equals `|det B|⁻¹ ^ (1 / p).toReal * ‖value k u‖`. -/
@[simp]
theorem norm_value_compAffineEquiv (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) (k : ℕ) (u : Wkp μ W p k) :
    ‖value k (compAffineEquiv μ B b hUW k u)‖ =
      |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal * ‖value k u‖ := by
  have hae : (value k (compAffineEquiv μ B b hUW k u) : E → ℝ) =ᵐ[μ.restrict U]
      fun x ↦ (1 : ℝ) • value k u (B x + b) := by
    simpa only [one_smul] using value_compAffineEquiv_ae μ B b hUW k u
  simpa only [norm_one, one_mul] using Lp.norm_eq_mul_det_inv_of_ae_eq B b hUW (1 : ℝ) hae

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
  have h := norm_iteratedGradient_compAffineEquiv_le (μ := μ) (p := p) B.symm (-B.symm b)
    (B.toLinearEquiv.eq_preimage_symm_add_neg b hUW) k (compAffineEquiv μ B b hUW (k + 1) u)
  rw [← compAffineEquiv_symm μ B b hUW (k + 1), ContinuousLinearEquiv.symm_apply_apply] at h
  rwa [ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, abs_inv, inv_inv] at h

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
  have h := seminorm_compAffineEquiv_le (μ := μ) (p := p) B.symm (-B.symm b)
    (B.toLinearEquiv.eq_preimage_symm_add_neg b hUW) hj (compAffineEquiv μ B b hUW k u)
  rw [← compAffineEquiv_symm μ B b hUW k, ContinuousLinearEquiv.symm_apply_apply] at h
  rwa [ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm, abs_inv, inv_inv] at h

/-- **Ciarlet forward geometric seminorm bound.** If `U = (fun x ↦ B x + b) ⁻¹' W`, `W` is bounded,
and `U` contains a ball of positive radius `ρ'`, then the `(k + 1)`-st weak derivative of `u ∘ F` on
`U` is bounded in terms of `diam W / (2 * ρ')` and `|det B|⁻¹ ^ (1 / p).toReal`. -/
theorem norm_iteratedGradient_compAffineEquiv_le_of_ball_subset (B : E ≃L[ℝ] E) (b : E)
    (hUW : (U : Set E) = (fun x ↦ B x + b) ⁻¹' W) {y : E} {ρ' : ℝ} (hρ' : 0 < ρ')
    (hbdd : Bornology.IsBounded (W : Set E)) (hball : Metric.ball y ρ' ⊆ (U : Set E))
    (k : ℕ) (u : Wkp μ W p (k + 1)) :
    ‖iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u)‖ ≤
      (Metric.diam (W : Set E) / (2 * ρ')) ^ (k + 1) *
        |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal * ‖iteratedGradient k u‖ :=
  (norm_iteratedGradient_compAffineEquiv_le B b hUW k u).trans <| by
    gcongr; exact (B : E →L[ℝ] E).opNorm_le_diam_div_two_mul_of_mapsTo_add_ball hρ' hbdd
      (fun x hx ↦ hUW ▸ hball hx)

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
        ‖iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u)‖ :=
  (norm_iteratedGradient_le_mul_norm_iteratedGradient_compAffineEquiv B b hUW k u).trans <| by
    gcongr; exact B.opNorm_symm_le_diam_div_two_mul_of_ball_subset hρ hbdd hUW.symm.subset hball

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
        |LinearMap.det (B : E →ₗ[ℝ] E)|⁻¹ ^ (1 / p).toReal * seminorm k j hj u :=
  (seminorm_compAffineEquiv_le B b hUW hj u).trans <| by
    gcongr; exact (B : E →L[ℝ] E).opNorm_le_diam_div_two_mul_of_mapsTo_add_ball hρ' hbdd
      (fun x hx ↦ hUW ▸ hball hx)

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
        seminorm k j hj (compAffineEquiv μ B b hUW k u) :=
  (seminorm_le_mul_seminorm_compAffineEquiv B b hUW hj u).trans <| by
    gcongr; exact B.opNorm_symm_le_diam_div_two_mul_of_ball_subset hρ hbdd hUW.symm.subset hball

/-! ### Exact scaling for homotheties `x ↦ r • x + b` -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fact (1 ≤ p)] in
private theorem abs_inv_det_smulLeft_rpow {r : ℝ} (hr : r ≠ 0) :
    |LinearMap.det
        ((ContinuousLinearEquiv.smulLeft (Units.mk0 r hr) : E ≃L[ℝ] E) : E →ₗ[ℝ] E)|⁻¹ ^
        (1 / p).toReal =
      |r|⁻¹ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) := by
  rw [ContinuousLinearEquiv.det_smulLeft, Units.val_mk0, abs_pow, ← inv_pow,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div, ENNReal.toReal_inv,
    div_eq_mul_inv]

/-- **Exact order-zero dilation identity** along `x ↦ r • x + b` (`r ≠ 0`). -/
theorem norm_value_compAffineEquiv_smulLeft {r : ℝ} (hr : r ≠ 0) (b : E)
    (hUW : (U : Set E) = (fun x ↦ ContinuousLinearEquiv.smulLeft (Units.mk0 r hr) x + b) ⁻¹' W)
    (k : ℕ) (u : Wkp μ W p k) :
    ‖value k (compAffineEquiv μ (ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)) b hUW k u)‖ =
      |r|⁻¹ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) * ‖value k u‖ := by
  rw [norm_value_compAffineEquiv, abs_inv_det_smulLeft_rpow hr]

/-- **Exact order-`k + 1` dilation identity** along `x ↦ r • x + b` (`r ≠ 0`), valid for every
order `k` and every exponent `1 ≤ p ≤ ∞`. -/
theorem norm_iteratedGradient_compAffineEquiv_smulLeft {r : ℝ} (hr : r ≠ 0) (b : E)
    (hUW : (U : Set E) = (fun x ↦ ContinuousLinearEquiv.smulLeft (Units.mk0 r hr) x + b) ⁻¹' W)
    (k : ℕ) (u : Wkp μ W p (k + 1)) :
    ‖iteratedGradient k
        (compAffineEquiv μ (ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)) b hUW (k + 1) u)‖ =
      |r| ^ (k + 1) * |r|⁻¹ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) * ‖iteratedGradient k u‖ := by
  set B : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)
  have hclm : (B : E →L[ℝ] E) = r • ContinuousLinearMap.id ℝ E := by
    ext v; simp [B, Units.smul_def]
  have hae : (iteratedGradient k (compAffineEquiv μ B b hUW (k + 1) u) :
      E → IteratedGradient E k) =ᵐ[μ.restrict U]
      fun x ↦ r ^ (k + 1) • iteratedGradient k u (B x + b) := by
    filter_upwards [iteratedGradient_compAffineEquiv_ae μ B b hUW k u] with x hx
    rw [hx, hclm, ContinuousLinearMap.iteratedGradientPullback_smul,
      ContinuousLinearMap.iteratedGradientPullback_id, smul_apply,
      ContinuousLinearMap.id_apply]
  rw [Lp.norm_eq_mul_det_inv_of_ae_eq B b hUW (r ^ (k + 1)) hae,
    abs_inv_det_smulLeft_rpow hr, Real.norm_eq_abs, abs_pow]

/-- **Exact `Wkp.seminorm` dilation identity** along `x ↦ r • x + b` (`r ≠ 0`), valid for every
derivative order `j ≤ k` and every exponent `1 ≤ p ≤ ∞`. -/
theorem seminorm_compAffineEquiv_smulLeft {r : ℝ} (hr : r ≠ 0) (b : E)
    (hUW : (U : Set E) = (fun x ↦ ContinuousLinearEquiv.smulLeft (Units.mk0 r hr) x + b) ⁻¹' W)
    {j k : ℕ} (hj : j ≤ k) (u : Wkp μ W p k) :
    seminorm k j hj
        (compAffineEquiv μ (ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)) b hUW k u) =
      |r| ^ j * |r|⁻¹ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) * seminorm k j hj u := by
  cases j with
  | zero => simpa only [seminorm_zero_apply, pow_zero, one_mul] using
      norm_value_compAffineEquiv_smulLeft hr b hUW k u
  | succ j => rw [seminorm_succ_apply, seminorm_succ_apply, toOrderL_compAffineEquiv]
              exact norm_iteratedGradient_compAffineEquiv_smulLeft hr b hUW j (toOrderL hj u)

end Wkp

end Scaling

/-! ### Concrete checks on intervals -/

section Examples

private theorem opensIoo_0_1_eq : (Opens.Ioo (0 : ℝ) 1 : Set ℝ) =
    (fun x : ℝ ↦ (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero) : ℝ ≃L[ℝ] ℝ)
      x + 1) ⁻¹' (Opens.Ioo (1 : ℝ) 3 : Set ℝ) := by
  ext x
  simp only [Opens.coe_Ioo, mem_preimage, mem_Ioo,
    ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0, smul_eq_mul]
  exact ⟨fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩,
    fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩⟩

example (u : Wkp volume (Opens.Ioo (1 : ℝ) 3) 2 1) :
    ‖Wkp.value 1 (Wkp.compAffineEquiv volume _ 1 opensIoo_0_1_eq 1 u)‖ =
        (2 : ℝ)⁻¹ ^ (1 / 2 : ℝ) * ‖Wkp.value 1 u‖ ∧
      ‖Wkp.iteratedGradient 0 (Wkp.compAffineEquiv volume _ 1 opensIoo_0_1_eq 1 u)‖ =
        2 * (2 : ℝ)⁻¹ ^ (1 / 2 : ℝ) * ‖Wkp.iteratedGradient 0 u‖ := by
  refine ⟨?_, ?_⟩
  · simpa [Module.finrank_self] using
      Wkp.norm_value_compAffineEquiv_smulLeft two_ne_zero (1 : ℝ) opensIoo_0_1_eq 1 u
  · simpa [Module.finrank_self] using
      Wkp.norm_iteratedGradient_compAffineEquiv_smulLeft two_ne_zero (1 : ℝ) opensIoo_0_1_eq 0 u

example (u : Wkp volume (Opens.Ioo (1 : ℝ) 3) ⊤ 2) :
    ‖Wkp.iteratedGradient 1 (Wkp.compAffineEquiv volume _ 1 opensIoo_0_1_eq 2 u)‖ =
      4 * ‖Wkp.iteratedGradient 1 u‖ := by
  have h := Wkp.norm_iteratedGradient_compAffineEquiv_smulLeft two_ne_zero (1 : ℝ)
    opensIoo_0_1_eq 1 u
  norm_num [ENNReal.toReal_top] at h
  exact h

end Examples

end TauCeti
