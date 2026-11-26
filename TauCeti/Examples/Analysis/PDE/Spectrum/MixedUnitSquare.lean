/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Examples.SquareBoundaryPart
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.Fourier.SineCosineSeries
import TauCeti.Analysis.Sobolev.W1p.Lipschitz
import TauCeti.Analysis.Sobolev.W1p.VanishingBoundary

/-!
# The mixed spectrum of `-Δ` on the unit square with one Dirichlet side

On the open unit square `(0, 1)²` of the Euclidean plane (`TauCeti.openUnitSquare`), impose a
Dirichlet condition on the left side `Γ = {0} × (0, 1)` (`TauCeti.squareLeftPart (Ioo 0 1)`) and
the natural Neumann condition on the other three sides. The weak eigenvalue problem asks for a
nonzero `u ∈ H¹_Γ((0, 1)²)`, the space of Sobolev functions vanishing on `Γ`
(`TauCeti.w1pVanishingOnSubmodule`), with `∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ((0, 1)²)`.
This file computes its spectrum by separation of variables.

* The modes `(x, y) ↦ sin ((2m + 1) π x / 2) cos (l π y)`, `m, l ≥ 0` (`squareMode`), products of
  the quarter-wave sines of `(0, 1)` with a Dirichlet condition at `0` and the cosines of `(0, 1)`
  with Neumann conditions at both ends, are weak eigenfunctions with eigenvalues
  `((2m + 1) π / 2)² + (l π)²` (`exists_value_ae_eq_squareMode_and_inner_gradient_eq`).
* They are complete in `L²((0, 1)²)` (`eq_zero_of_forall_setIntegral_mul_squareMode_eq_zero`), so
  there are no other eigenvalues: `κ` is a weak mixed eigenvalue exactly when
  `κ = ((2m + 1) π / 2)² + (l π)²` for some `m, l ≥ 0`
  (`exists_ne_zero_forall_inner_gradient_eq_iff_unitSquare`).
* The least eigenvalue is `π² / 4`, with eigenfunction `sin (π x / 2)`
  (`isLeast_exists_ne_zero_forall_inner_gradient_eq_unitSquare`), and it is simple: every
  eigenfunction for it is a multiple of `sin (π x / 2)`
  (`exists_value_ae_eq_mul_sin_of_inner_gradient_eq`). The least eigenvalue above it is
  `5 π² / 4 = (π / 2)² + π²`, with eigenfunction `sin (π x / 2) cos (π y)`, not the value
  `9 π² / 4` of the second quarter-wave sine
  (`isLeast_exists_ne_zero_forall_inner_gradient_eq_unitSquare_of_lt`). So, counted with
  multiplicity, the first two mixed eigenvalues are `π² / 4` and `5 π² / 4`.

## The argument

Each mode extends smoothly to the plane. Cut off in `y` by a bump equal to one near the closed
square, it vanishes on the frontier of the box `(0, 2) × (-3, 3)`, which misses `Γ`: on the sides
`x = 0` and `x = 2` because `sin 0 = sin ((2m + 1) π) = 0`, and on the sides `y = ± 3` because of
the cutoff. So it lies in `H¹₀` of that box, and its restriction to the square lies in `H¹_Γ`
(`TauCeti.W1p.restrictL_mem_w1pVanishingOnSubmodule`).

The weak eigenvalue identity needs to be checked only against the generators of `H¹_Γ`, smooth
functions `ψ` on the plane vanishing near `closure Γ = {0} × [0, 1]`. For them it is Green's
identity on the square: by the divergence theorem on a rectangle
(`MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le`) applied to `ψ ∇g`,
`∫ ∇g · ∇ψ = κ ∫ g ψ` up to boundary terms, and the four boundary terms vanish: `ψ = 0` on the left
side, `∂ₓg = 0` on the right side since `cos ((2m + 1) π / 2) = 0`, and `∂_y g = 0` on the bottom
and top sides since `sin (l π) = 0`.

Completeness is proved slice by slice
(`TauCeti.ae_eq_zero_prod_of_forall_integral_mul_eq_zero`): for `f ∈ L²((0, 1)²)` orthogonal to
every mode, each coefficient `y ↦ ∫ f (x, y) sin ((2m + 1) π x / 2) dx` is orthogonal to every
cosine, so it vanishes by the completeness of the cosines
(`TauCeti.ae_eq_zero_of_forall_integral_mul_cos_eq_zero`); then almost every slice `f (·, y)` is
orthogonal to every quarter-wave sine, so it vanishes
(`TauCeti.ae_eq_zero_of_forall_integral_mul_sin_two_mul_add_one_eq_zero`). An eigenfunction for
any other `κ` is orthogonal to all modes, since the form `∫ ∇u · ∇v` is symmetric, hence zero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.5.1 (eigenvalues of symmetric elliptic
  operators, separation of variables).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace TauCeti
open scoped Real InnerProductSpace Gradient Distributions ContDiff

namespace TauCeti.Examples.MixedSpectrumUnitSquare

/-- The open unit square `(0, 1)²` as an open subset of the Euclidean plane. -/
def unitSquare : Opens (WithLp 2 (ℝ × ℝ)) :=
  ⟨openUnitSquare, isOpen_openUnitSquare⟩

@[simp]
theorem coe_unitSquare : (unitSquare : Set (WithLp 2 (ℝ × ℝ))) = openUnitSquare :=
  (rfl)

/-- The separated mode `(x, y) ↦ sin ((2m + 1) π x / 2) cos (l π y)` of the unit square. -/
def squareMode (m l : ℕ) (x : WithLp 2 (ℝ × ℝ)) : ℝ :=
  Real.sin ((2 * m + 1) * π / 2 * x.fst) * Real.cos (l * π * x.snd)

/-- The formula for the separated mode. -/
theorem squareMode_def (m l : ℕ) (x : WithLp 2 (ℝ × ℝ)) :
    squareMode m l x = Real.sin ((2 * m + 1) * π / 2 * x.fst) * Real.cos (l * π * x.snd) :=
  (rfl)

/-- A product `x ↦ A x.fst * B x.snd` of functions of the two coordinates is differentiable, with
partial derivatives `A' B` and `A B'`. -/
private theorem hasFDerivAt_mul_fst_snd {A B : ℝ → ℝ} {A' B' : ℝ} {x : WithLp 2 (ℝ × ℝ)}
    (hA : HasDerivAt A A' x.fst) (hB : HasDerivAt B B' x.snd) :
    HasFDerivAt (fun y : WithLp 2 (ℝ × ℝ) => A y.fst * B y.snd)
      ((A' * B x.snd) • WithLp.fstL 2 ℝ ℝ ℝ + (A x.fst * B') • WithLp.sndL 2 ℝ ℝ ℝ) x := by
  have h1 := hA.comp_hasFDerivAt x (WithLp.fstL 2 ℝ ℝ ℝ).hasFDerivAt
  have h2 := hB.comp_hasFDerivAt x (WithLp.sndL 2 ℝ ℝ ℝ).hasFDerivAt
  refine (h1.mul h2).congr_fderiv ?_
  ext w
  simp
  ring

/-- A product `x ↦ A x.fst * B x.snd` of smooth functions of the two coordinates is smooth. -/
private theorem contDiff_mul_fst_snd {n : WithTop ℕ∞} {A B : ℝ → ℝ} (hA : ContDiff ℝ n A)
    (hB : ContDiff ℝ n B) : ContDiff ℝ n (fun y : WithLp 2 (ℝ × ℝ) => A y.fst * B y.snd) :=
  (hA.comp (WithLp.fstL 2 ℝ ℝ ℝ).contDiff).mul (hB.comp (WithLp.sndL 2 ℝ ℝ ℝ).contDiff)

/-- The modes are smooth. -/
private theorem contDiff_squareMode (m l : ℕ) {n : WithTop ℕ∞} : ContDiff ℝ n (squareMode m l) :=
  contDiff_mul_fst_snd (A := fun t => Real.sin ((2 * m + 1) * π / 2 * t))
    (B := fun t => Real.cos (l * π * t)) (by fun_prop) (by fun_prop)

/-- The gradient on the Euclidean plane of a function with partial derivatives `a` and `b`. -/
private theorem gradient_eq_toLp {f : WithLp 2 (ℝ × ℝ) → ℝ} {a b : ℝ} {x : WithLp 2 (ℝ × ℝ)}
    (h : HasFDerivAt f (a • WithLp.fstL 2 ℝ ℝ ℝ + b • WithLp.sndL 2 ℝ ℝ ℝ) x) :
    ∇ f x = WithLp.toLp 2 (a, b) := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_gradient_left, h.fderiv, WithLp.prod_inner_apply]
  simp [mul_comm]

/-- **The divergence theorem on the unit square**, for continuously differentiable `Φ₁` and `Φ₂`
on the Euclidean plane, with `e₁ = (1, 0)` and `e₂ = (0, 1)`:
`∫_{(0,1)²} (∂₁Φ₁ + ∂₂Φ₂) = ∫₀¹ (Φ₂(t, 1) - Φ₂(t, 0)) dt + ∫₀¹ (Φ₁(1, s) - Φ₁(0, s)) ds`. -/
private theorem setIntegral_unitSquare_fderiv_add_fderiv {Φ₁ Φ₂ : WithLp 2 (ℝ × ℝ) → ℝ}
    (h₁ : ContDiff ℝ 1 Φ₁) (h₂ : ContDiff ℝ 1 Φ₂) :
    ∫ x in unitSquare, (fderiv ℝ Φ₁ x (WithLp.toLp 2 (1, 0)) +
        fderiv ℝ Φ₂ x (WithLp.toLp 2 (0, 1))) =
      (((∫ t in (0 : ℝ)..1, Φ₂ (WithLp.toLp 2 (t, 1))) -
          ∫ t in (0 : ℝ)..1, Φ₂ (WithLp.toLp 2 (t, 0))) +
        ∫ s in (0 : ℝ)..1, Φ₁ (WithLp.toLp 2 (1, s))) -
          ∫ s in (0 : ℝ)..1, Φ₁ (WithLp.toLp 2 (0, s)) := by
  set L : ℝ × ℝ →L[ℝ] WithLp 2 (ℝ × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap
  have hL (y : ℝ × ℝ) : L y = WithLp.toLp 2 y := by
    simp [L, WithLp.prodContinuousLinearEquiv_symm_apply]
  have hd (Φ : WithLp 2 (ℝ × ℝ) → ℝ) (hΦ : ContDiff ℝ 1 Φ) (y : ℝ × ℝ) :
      HasFDerivAt (fun y => Φ (L y)) ((fderiv ℝ Φ (L y)).comp L) y :=
    ((hΦ.differentiable one_ne_zero) (L y)).hasFDerivAt.comp y L.hasFDerivAt
  have hc (Φ : WithLp 2 (ℝ × ℝ) → ℝ) (hΦ : ContDiff ℝ 1 Φ) :
      Continuous fun y => Φ (L y) := hΦ.continuous.comp L.continuous
  have hi : IntegrableOn (fun y : ℝ × ℝ => (fderiv ℝ Φ₁ (L y)).comp L (1, 0) +
      (fderiv ℝ Φ₂ (L y)).comp L (0, 1)) (Icc (0, 0) (1, 1)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
    have c₁ := (h₁.continuous_fderiv one_ne_zero).comp L.continuous
    have c₂ := (h₂.continuous_fderiv one_ne_zero).comp L.continuous
    exact (c₁.clm_apply continuous_const).add (c₂.clm_apply continuous_const)
  have key := integral_divergence_prod_Icc_of_hasFDerivAt_of_le (fun y => Φ₁ (L y))
    (fun y => Φ₂ (L y)) (fun y => (fderiv ℝ Φ₁ (L y)).comp L)
    (fun y => (fderiv ℝ Φ₂ (L y)).comp L) (0, 0) (1, 1) (by simp [Prod.le_def])
    (hc Φ₁ h₁).continuousOn (hc Φ₂ h₂).continuousOn (fun y _ => hd Φ₁ h₁ y)
    (fun y _ => hd Φ₂ h₂ y) hi
  simp only [hL, ContinuousLinearMap.comp_apply] at key
  rw [← key]
  -- Transport the integral over the square to the rectangle `[0, 1]²` of `ℝ × ℝ`.
  have hpre : WithLp.toLp 2 ⁻¹' (unitSquare : Set (WithLp 2 (ℝ × ℝ))) = Ioo 0 1 ×ˢ Ioo 0 1 := by
    ext y
    simp [mem_openUnitSquare]
  rw [← (WithLp.volume_preserving_toLp ℝ ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding, hpre]
  rw [Icc_prod_eq, Measure.volume_eq_prod,
    Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)]

/-- A continuous function is integrable on the unit square. -/
private theorem integrableOn_unitSquare {f : WithLp 2 (ℝ × ℝ) → ℝ} (hf : Continuous f) :
    IntegrableOn f unitSquare := by
  refine (hf.continuousOn.integrableOn_compact (((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).image
      (WithLp.prod_continuous_toLp 2 ℝ ℝ))).mono_set fun x hx => ?_
  rw [coe_unitSquare, mem_openUnitSquare] at hx
  exact ⟨WithLp.ofLp x, ⟨Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hx.2⟩, by simp⟩

/-- `t ↦ sin (a t)` has derivative `a cos (a t)`. -/
private theorem hasDerivAt_sin_mul (a t : ℝ) :
    HasDerivAt (fun s => Real.sin (a * s)) (a * Real.cos (a * t)) t :=
  ((hasDerivAt_id' t).const_mul a).sin.congr_deriv (by ring)

/-- `t ↦ cos (a t)` has derivative `-a sin (a t)`. -/
private theorem hasDerivAt_cos_mul (a t : ℝ) :
    HasDerivAt (fun s => Real.cos (a * s)) (-a * Real.sin (a * t)) t :=
  ((hasDerivAt_id' t).const_mul a).cos.congr_deriv (by ring)

/-- The partial derivative `∂ₓ` of the mode `squareMode m l`. -/
private def squareModeDx (m l : ℕ) (x : WithLp 2 (ℝ × ℝ)) : ℝ :=
  (2 * m + 1) * π / 2 * Real.cos ((2 * m + 1) * π / 2 * x.fst) * Real.cos (l * π * x.snd)

/-- The partial derivative `∂_y` of the mode `squareMode m l`. -/
private def squareModeDy (m l : ℕ) (x : WithLp 2 (ℝ × ℝ)) : ℝ :=
  Real.sin ((2 * m + 1) * π / 2 * x.fst) * (-(l * π) * Real.sin (l * π * x.snd))

/-- The gradient of a mode is `(∂ₓ, ∂_y)`. -/
private theorem gradient_squareMode (m l : ℕ) (x : WithLp 2 (ℝ × ℝ)) :
    ∇ (squareMode m l) x = WithLp.toLp 2 (squareModeDx m l x, squareModeDy m l x) :=
  gradient_eq_toLp (hasFDerivAt_mul_fst_snd (hasDerivAt_sin_mul _ x.fst)
    (hasDerivAt_cos_mul _ x.snd))

/-- **The divergence of `ψ ∇g` for a mode `g`.** For differentiable `ψ`, the field
`(ψ ∂ₓg, ψ ∂_y g)` has divergence `∇g · ∇ψ - κ g ψ`, since `Δg = -κ g` with
`κ = ((2m + 1) π / 2)² + (l π)²`. -/
private theorem fderiv_mul_squareModeDx_add_fderiv_mul_squareModeDy (m l : ℕ)
    {ψ : WithLp 2 (ℝ × ℝ) → ℝ} (hψ : Differentiable ℝ ψ) (x : WithLp 2 (ℝ × ℝ)) :
    fderiv ℝ (fun y => ψ y * squareModeDx m l y) x (WithLp.toLp 2 (1, 0)) +
        fderiv ℝ (fun y => ψ y * squareModeDy m l y) x (WithLp.toLp 2 (0, 1)) =
      ⟪∇ (squareMode m l) x, ∇ ψ x⟫_ℝ -
        (((2 * m + 1) * π / 2) ^ 2 + (l * π) ^ 2) * (squareMode m l x * ψ x) := by
  have hv : WithLp.toLp 2 (squareModeDx m l x, squareModeDy m l x) =
      squareModeDx m l x • WithLp.toLp 2 ((1 : ℝ), (0 : ℝ)) +
        squareModeDy m l x • WithLp.toLp 2 ((0 : ℝ), (1 : ℝ)) := by
    refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;> simp
  have e₁ : fderiv ℝ (fun y => ψ y * squareModeDx m l y) x = _ :=
    ((hψ x).hasFDerivAt.mul (hasFDerivAt_mul_fst_snd
      ((hasDerivAt_cos_mul _ x.fst).const_mul _) (hasDerivAt_cos_mul _ x.snd))).fderiv
  have e₂ : fderiv ℝ (fun y => ψ y * squareModeDy m l y) x = _ :=
    ((hψ x).hasFDerivAt.mul (hasFDerivAt_mul_fst_snd (hasDerivAt_sin_mul _ x.fst)
      ((hasDerivAt_sin_mul _ x.snd).const_mul _))).fderiv
  rw [e₁, e₂, gradient_squareMode, real_inner_comm, inner_gradient_left, hv, map_add, map_smul,
    map_smul]
  simp only [squareMode, squareModeDx, squareModeDy]
  simp
  ring

/-- **Green's identity for a separated mode.** Let `ψ` be continuously differentiable on the plane
and vanish on the closed left side `{0} × [0, 1]` of the unit square. Then the mode
`g = squareMode m l` satisfies `∫_{(0,1)²} ∇g · ∇ψ = κ ∫_{(0,1)²} g ψ` with
`κ = ((2m + 1) π / 2)² + (l π)²`: the boundary terms of the integration by parts vanish, since
`ψ = 0` on the left side, `∂ₓg = 0` on the right side and `∂_y g = 0` on the bottom and top
sides. -/
private theorem setIntegral_inner_gradient_squareMode (m l : ℕ) {ψ : WithLp 2 (ℝ × ℝ) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψ0 : ∀ s ∈ Icc (0 : ℝ) 1, ψ (WithLp.toLp 2 (0, s)) = 0) :
    ∫ x in unitSquare, ⟪∇ (squareMode m l) x, ∇ ψ x⟫_ℝ =
      (((2 * m + 1) * π / 2) ^ 2 + (l * π) ^ 2) *
        ∫ x in unitSquare, squareMode m l x * ψ x := by
  have hc₁ : ContDiff ℝ 1 (squareModeDx m l) :=
    contDiff_mul_fst_snd (A := fun t => (2 * m + 1) * π / 2 * Real.cos ((2 * m + 1) * π / 2 * t))
      (B := fun t => Real.cos (l * π * t)) (by fun_prop) (by fun_prop)
  have hc₂ : ContDiff ℝ 1 (squareModeDy m l) :=
    contDiff_mul_fst_snd (A := fun t => Real.sin ((2 * m + 1) * π / 2 * t))
      (B := fun t => -(l * π) * Real.sin (l * π * t)) (by fun_prop) (by fun_prop)
  have key := setIntegral_unitSquare_fderiv_add_fderiv (hψ.mul hc₁) (hψ.mul hc₂)
  -- All four boundary terms vanish: `∂_y g = 0` for `y ∈ {0, 1}`, `∂ₓg = 0` for `x = 1`, since
  -- `cos ((2m + 1) π / 2) = 0`, and `ψ = 0` for `x = 0`.
  have hcos : Real.cos ((2 * m + 1) * π / 2) = 0 := by
    rw [show (2 * m + 1) * π / 2 = m * π + π / 2 by ring, Real.cos_add_pi_div_two,
      Real.sin_nat_mul_pi, neg_zero]
  have hb₁ : (∫ t in (0 : ℝ)..1,
      ψ (WithLp.toLp 2 (t, 1)) * squareModeDy m l (WithLp.toLp 2 (t, 1))) = 0 := by
    simp [squareModeDy, Real.sin_nat_mul_pi]
  have hb₂ : (∫ t in (0 : ℝ)..1,
      ψ (WithLp.toLp 2 (t, 0)) * squareModeDy m l (WithLp.toLp 2 (t, 0))) = 0 := by
    simp [squareModeDy]
  have hb₃ : (∫ s in (0 : ℝ)..1,
      ψ (WithLp.toLp 2 (1, s)) * squareModeDx m l (WithLp.toLp 2 (1, s))) = 0 := by
    simp [squareModeDx, hcos]
  have hb₄ : (∫ s in (0 : ℝ)..1,
      ψ (WithLp.toLp 2 (0, s)) * squareModeDx m l (WithLp.toLp 2 (0, s))) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le zero_le_one] at hs
    simp [hψ0 s hs]
  rw [hb₁, hb₂, hb₃, hb₄, sub_zero, add_zero, sub_zero] at key
  have hcont : Continuous fun x => fderiv ℝ (fun y => ψ y * squareModeDx m l y) x
      (WithLp.toLp 2 (1, 0)) + fderiv ℝ (fun y => ψ y * squareModeDy m l y) x
        (WithLp.toLp 2 (0, 1)) :=
    (((hψ.mul hc₁).continuous_fderiv one_ne_zero).clm_apply continuous_const).add
      (((hψ.mul hc₂).continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hgψ : Continuous fun x => squareMode m l x * ψ x :=
    (contDiff_squareMode m l (n := 0)).continuous.mul hψ.continuous
  have hdiv := fderiv_mul_squareModeDx_add_fderiv_mul_squareModeDy m l
    (hψ.differentiable one_ne_zero)
  calc ∫ x in unitSquare, ⟪∇ (squareMode m l) x, ∇ ψ x⟫_ℝ
      = ∫ x in unitSquare, ((fderiv ℝ (fun y => ψ y * squareModeDx m l y) x
          (WithLp.toLp 2 (1, 0)) + fderiv ℝ (fun y => ψ y * squareModeDy m l y) x
            (WithLp.toLp 2 (0, 1))) +
            (((2 * m + 1) * π / 2) ^ 2 + (l * π) ^ 2) * (squareMode m l x * ψ x)) :=
        integral_congr_ae (ae_of_all _ fun x => by simp only [hdiv]; ring)
    _ = _ := by
        rw [integral_add (integrableOn_unitSquare hcont)
          ((integrableOn_unitSquare hgψ).const_mul _), integral_const_mul, key, zero_add]

/-- The box `(0, 2) × (-3, 3)`, on which the doubled modes, cut off in the second variable, vanish
on the frontier. -/
private def bigBox : Opens (WithLp 2 (ℝ × ℝ)) :=
  ⟨{x | x.fst ∈ Ioo 0 2 ∧ x.snd ∈ Ioo (-3) 3},
    (isOpen_Ioo.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst).inter
      (isOpen_Ioo.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).snd)⟩

/-- A bump `χ` around the origin of outer radius `3` vanishes for `|y| ≥ 3`, so the product of a
mode with it vanishes on the frontier of the box `(0, 2) × (-3, 3)`: the mode vanishes on the sides
`x = 0` and `x = 2`, since `sin 0 = sin ((2m + 1) π) = 0`, and `χ` on the sides `y = ± 3`. -/
private theorem squareMode_mul_eq_zero_of_mem_frontier (m l : ℕ)
    (χ : ContDiffBump (0 : WithLp 2 (ℝ × ℝ))) (hχ : χ.rOut = 3) {x : WithLp 2 (ℝ × ℝ)}
    (hx : x ∈ frontier (bigBox : Set (WithLp 2 (ℝ × ℝ)))) : squareMode m l x * χ x = 0 := by
  have hcl : closure (bigBox : Set (WithLp 2 (ℝ × ℝ))) ⊆
      {x | x.fst ∈ Icc 0 2 ∧ x.snd ∈ Icc (-3) 3} :=
    closure_minimal (fun y hy => ⟨Ioo_subset_Icc_self hy.1, Ioo_subset_Icc_self hy.2⟩)
      ((isClosed_Icc.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst).inter
        (isClosed_Icc.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).snd))
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcl hx.1
  have hnot : x ∉ (bigBox : Set (WithLp 2 (ℝ × ℝ))) := by
    have := hx.2
    rwa [bigBox.isOpen.interior_eq] at this
  rw [mul_eq_zero]
  by_cases hy : x.snd ∈ Ioo (-3) 3
  · left
    have hx' : x.fst = 0 ∨ x.fst = 2 := by
      by_contra! h
      exact hnot ⟨⟨lt_of_le_of_ne h1 (Ne.symm h.1), lt_of_le_of_ne h2 h.2⟩, hy⟩
    rcases hx' with h | h
    · simp [squareMode, h]
    · rw [squareMode, h, show (2 * m + 1) * π / 2 * 2 = ((2 * m + 1 : ℕ) : ℝ) * π by
        push_cast; ring, Real.sin_nat_mul_pi, zero_mul]
  · right
    refine χ.zero_of_le_dist ?_
    have hy' : (3 : ℝ) ≤ |x.snd| := by
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at hy
      rcases hy with h | h
      · rw [show x.snd = -3 by linarith, abs_neg, abs_of_pos three_pos]
      · rw [show x.snd = 3 by linarith, abs_of_pos three_pos]
    rw [hχ, dist_zero_right]
    exact hy'.trans ((Real.norm_eq_abs _).symm.le.trans (WithLp.norm_snd_le (x := x)))

/-- Each mode is the value of a function in `H¹_Γ((0, 1)²)`, `Γ = {0} × (0, 1)`. Cut off by a
bump equal to one on the closed square, it is a test function on the plane that vanishes on the
frontier of the box `(0, 2) × (-3, 3)`, so it lies in `H¹₀` of that box, which misses `Γ`, and
restricts to an element of `H¹_Γ((0, 1)²)`. -/
private theorem exists_mem_w1pVanishingOnSubmodule_value_ae_eq_squareMode (m l : ℕ) :
    ∃ u ∈ w1pVanishingOnSubmodule volume unitSquare 2 (squareLeftPart (Ioo 0 1)),
      W1p.value u =ᵐ[volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ)))] squareMode m l := by
  let χ : ContDiffBump (0 : WithLp 2 (ℝ × ℝ)) := ⟨2, 3, by norm_num, by norm_num⟩
  let φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × ℝ))), ℝ) :=
    ⟨fun x => squareMode m l x * χ x, (contDiff_squareMode m l).mul χ.contDiff,
      χ.hasCompactSupport.mul_left, subset_univ _⟩
  have hχ : ∀ x ∈ (unitSquare : Set (WithLp 2 (ℝ × ℝ))), χ x = 1 := fun x hx => by
    refine χ.one_of_mem_closedBall ?_
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_openUnitSquare.1 hx
    have hsq : ‖x‖ ^ 2 ≤ 2 ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      nlinarith
    exact mem_closedBall_zero_iff.2 (le_of_pow_le_pow_left₀ two_ne_zero zero_le_two hsq)
  have hle : unitSquare ≤ bigBox := fun x hx => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_openUnitSquare.1 hx
    exact ⟨⟨h1, h2.trans one_lt_two⟩, ⟨by linarith, by linarith⟩⟩
  have hΓ : Disjoint (squareLeftPart (Ioo 0 1)) (bigBox : Set (WithLp 2 (ℝ × ℝ))) :=
    disjoint_left.2 fun x hx hx' => (lt_irrefl (0 : ℝ)) ((mem_squareLeftPart.1 hx).1 ▸ hx'.1.1)
  have hbd : Bornology.IsBounded (bigBox : Set (WithLp 2 (ℝ × ℝ))) := by
    refine (((isCompact_Icc (a := (0 : ℝ)) (b := 2)).prod (isCompact_Icc (a := (-3 : ℝ))
      (b := 3))).image (WithLp.prod_continuous_toLp 2 ℝ ℝ)).isBounded.subset fun x hx => ?_
    exact ⟨WithLp.ofLp x, ⟨Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hx.2⟩, by simp⟩
  set T := W1p.restrictL (le_top : bigBox ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ 2 φ)
  have hT : T ∈ w1p0Submodule volume bigBox 2 :=
    W1p.mem_w1p0Submodule_of_continuousOn_closure (by norm_num) hbd φ.continuous.continuousOn
      (fun x hx => squareMode_mul_eq_zero_of_mem_frontier m l χ rfl hx)
      (W1p.value_restrictL_ofTestFunctionₗ_ae le_top φ)
  refine ⟨_, W1p.restrictL_mem_w1pVanishingOnSubmodule hle hΓ hT, ?_⟩
  filter_upwards [W1p.value_restrictL_ae hle T, ae_restrict_of_ae_restrict_of_subset hle
    (W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := 2) le_top φ),
    ae_restrict_mem unitSquare.isOpen.measurableSet] with x h1 h2 h3
  rw [h1, h2, TestFunction.coe_mk, hχ x h3, mul_one]

/-- A function `u` with a mode as its value satisfies the weak mixed eigenvalue identity against
every `v ∈ H¹_Γ((0, 1)²)`. By density it suffices to test against the generators of `H¹_Γ`, test
functions on the plane vanishing near `closure Γ = {0} × [0, 1]`, where it is Green's identity
`setIntegral_inner_gradient_squareMode`. -/
private theorem inner_gradient_eq_of_value_ae_eq_squareMode (m l : ℕ)
    {u : W1p volume unitSquare 2}
    (hu : W1p.value u =ᵐ[volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ)))] squareMode m l)
    {v : W1p volume unitSquare 2}
    (hv : v ∈ w1pVanishingOnSubmodule volume unitSquare 2 (squareLeftPart (Ioo 0 1))) :
    ⟪W1p.gradient u, W1p.gradient v⟫_ℝ =
      (((2 * m + 1) * π / 2) ^ 2 + (l * π) ^ 2) * ⟪W1p.value u, W1p.value v⟫_ℝ := by
  have hgrad := W1p.gradient_ae_eq_of_locallyLipschitzOn _ hu
    ((contDiff_squareMode m l (n := 1)).locallyLipschitz.locallyLipschitzOn)
  refine w1pVanishingOnSubmodule_subset_of_isClosed (s := {w | ⟪W1p.gradient u,
      W1p.gradient w⟫_ℝ = (((2 * m + 1) * π / 2) ^ 2 + (l * π) ^ 2) *
        ⟪W1p.value u, W1p.value w⟫_ℝ})
    (isClosed_eq (continuous_const.inner (W1p.gradientL.continuous.congr W1p.gradientL_apply))
      (continuous_const.mul (continuous_const.inner
        (W1p.valueL.continuous.congr W1p.valueL_apply)))) (fun ψ hψ => ?_) hv
  have hψ0 : ∀ s ∈ Icc (0 : ℝ) 1, ψ (WithLp.toLp 2 (0, s)) = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport fun h => hψ.notMem_of_mem_left h (by
      rw [closure_squareLeftPart, closure_Ioo zero_ne_one]
      exact mem_squareLeftPart.2 ⟨rfl, hs⟩)
  rw [mem_ofPred_eq, L2.inner_def, W1p.inner_value_eq_setIntegral]
  calc ∫ x, ⟪W1p.gradient u x,
        W1p.gradient (W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ 2 ψ)) x⟫_ℝ
          ∂volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ)))
      = ∫ x in unitSquare, ⟪∇ (squareMode m l) x, ∇ (ψ : WithLp 2 (ℝ × ℝ) → ℝ) x⟫_ℝ := by
        refine integral_congr_ae ?_
        filter_upwards [hgrad, W1p.gradient_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := 2)
          (le_top : unitSquare ≤ ⊤) ψ] with x h1 h2
        rw [h1, h2]
    _ = (((2 * m + 1) * π / 2) ^ 2 + (l * π) ^ 2) *
          ∫ x in unitSquare, squareMode m l x * ψ x :=
        setIntegral_inner_gradient_squareMode m l (ψ.contDiff.of_le (by exact_mod_cast le_top)) hψ0
    _ = _ := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [hu, W1p.value_restrictL_ofTestFunctionₗ_ae (mu := volume) (p := 2)
          (le_top : unitSquare ≤ ⊤) ψ] with x h1 h2
        rw [h1, h2]

/-- **The separated modes are weak mixed eigenfunctions of `-Δ` on the unit square**, with a
Dirichlet condition on the left side `Γ = {0} × (0, 1)` and a Neumann condition on the other three
sides. For all `m, l : ℕ` the mode `(x, y) ↦ sin ((2m + 1) π x / 2) cos (l π y)` is the value of
some `u ∈ H¹_Γ((0, 1)²)` with

`∫ ∇u · ∇v = (((2m + 1) π / 2)² + (l π)²) ∫ u v` for every `v ∈ H¹_Γ((0, 1)²)`. -/
theorem exists_value_ae_eq_squareMode_and_inner_gradient_eq (m l : ℕ) :
    ∃ u : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)),
      W1p.value (u : W1p volume unitSquare 2)
          =ᵐ[volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ)))] squareMode m l ∧
      ∀ v : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)),
        ⟪W1p.gradient (u : W1p volume unitSquare 2),
            W1p.gradient (v : W1p volume unitSquare 2)⟫_ℝ =
          (((2 * m + 1) * π / 2) ^ 2 + (l * π) ^ 2) *
            ⟪W1p.value (u : W1p volume unitSquare 2),
              W1p.value (v : W1p volume unitSquare 2)⟫_ℝ := by
  obtain ⟨u, hu, hval⟩ := exists_mem_w1pVanishingOnSubmodule_value_ae_eq_squareMode m l
  exact ⟨⟨u, hu⟩, hval, fun v => inner_gradient_eq_of_value_ae_eq_squareMode m l hval v.property⟩

/-- The quarter-wave sines `t ↦ sin ((2m + 1) π t / 2)`, `m ≥ 0`, are complete on `(0, 1)`. -/
private theorem ae_eq_zero_of_forall_integral_mul_sin_eq_zero {g : ℝ → ℝ}
    (hg : Integrable g (volume.restrict (Ioo (0 : ℝ) 1)))
    (h : ∀ m : ℕ, ∫ t, g t * Real.sin ((2 * m + 1) * π / 2 * t)
      ∂volume.restrict (Ioo (0 : ℝ) 1) = 0) :
    g =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] 0 := by
  have hIoc : volume.restrict (Ioo (0 : ℝ) 1) = volume.restrict (Ioc 0 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [hIoc] at hg ⊢
  refine ae_eq_zero_of_forall_integral_mul_sin_two_mul_add_one_eq_zero hg fun k => ?_
  rw [intervalIntegral.integral_of_le zero_le_one, ← hIoc]
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun t => ?_)) (h k)
  simp only
  ring_nf

/-- The unit square of the Euclidean plane is the image of `(0, 1) × (0, 1) ⊆ ℝ × ℝ`, with the
product of the restricted Lebesgue measures. -/
private theorem measurePreserving_toLp_unitSquare :
    MeasurePreserving (MeasurableEquiv.toLp 2 (ℝ × ℝ))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))
      (volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ)))) := by
  have hpre : MeasurableEquiv.toLp 2 (ℝ × ℝ) ⁻¹' (unitSquare : Set (WithLp 2 (ℝ × ℝ))) =
      Ioo 0 1 ×ˢ Ioo 0 1 := by
    ext y
    simp [mem_openUnitSquare]
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← hpre]
  exact (WithLp.volume_preserving_toLp ℝ ℝ).restrict_preimage unitSquare.isOpen.measurableSet

/-- **Completeness of the separated modes.** An element of `L²((0, 1)²)` orthogonal to every mode
`(x, y) ↦ sin ((2m + 1) π x / 2) cos (l π y)`, `m, l ≥ 0`, is zero. -/
theorem eq_zero_of_forall_setIntegral_mul_squareMode_eq_zero
    (f : Lp ℝ 2 (volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ)))))
    (h : ∀ m l : ℕ, ∫ x in unitSquare, f x * squareMode m l x = 0) : f = 0 := by
  set μ := volume.restrict (Ioo (0 : ℝ) 1)
  set T := MeasurableEquiv.toLp 2 (ℝ × ℝ)
  -- Read `f` on `(0, 1) × (0, 1) ⊆ ℝ × ℝ`.
  have hmp := measurePreserving_toLp_unitSquare
  have : IsFiniteMeasure (volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ)))) := by
    rw [← hmp.map_eq]
    infer_instance
  set G : ℝ × ℝ → ℝ := fun y => f (T y)
  have hG : Integrable G (μ.prod μ) :=
    (hmp.integrable_comp_emb T.measurableEmbedding).2 ((Lp.memLp f).integrable one_le_two)
  -- The coefficients of `G` in the first variable are orthogonal to every cosine, so they vanish.
  have hH (m : ℕ) : (fun y => ∫ t, G (t, y) * Real.sin ((2 * m + 1) * π / 2 * t) ∂μ) =ᵐ[μ] 0 := by
    have hGs : Integrable (fun z : ℝ × ℝ => G z * Real.sin ((2 * m + 1) * π / 2 * z.1))
        (μ.prod μ) :=
      hG.mul_bdd (by fun_prop) (ae_of_all _ fun z => by simpa using Real.abs_sin_le_one _)
    have hIoc : μ = volume.restrict (Ioc 0 1) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
    have hi := hGs.integral_prod_right
    rw [hIoc] at hi ⊢
    refine ae_eq_zero_of_forall_integral_mul_cos_eq_zero hi fun l => ?_
    rw [intervalIntegral.integral_of_le zero_le_one, ← hIoc]
    have hint : Integrable (fun z : ℝ × ℝ => G z * Real.sin ((2 * m + 1) * π / 2 * z.1) *
        Real.cos (l * π * z.2)) (μ.prod μ) :=
      hGs.mul_bdd (by fun_prop) (ae_of_all _ fun z => by simpa using Real.abs_cos_le_one _)
    calc ∫ y, (∫ t, G (t, y) * Real.sin ((2 * m + 1) * π / 2 * t) ∂μ) *
          Real.cos (l * π * (y - 0) / (1 - 0)) ∂μ
        = ∫ z, G z * Real.sin ((2 * m + 1) * π / 2 * z.1) * Real.cos (l * π * z.2)
            ∂μ.prod μ := by
          rw [integral_prod_symm _ hint]
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp only
          rw [← integral_mul_const]
          refine integral_congr_ae (ae_of_all _ fun t => ?_)
          simp only
          ring_nf
      _ = ∫ x in unitSquare, f x * squareMode m l x := by
          refine Eq.trans (integral_congr_ae (ae_of_all _ fun z => ?_))
            (hmp.integral_comp' (g := fun x => f x * squareMode m l x))
          simp only [G, squareMode, mul_assoc]
          rfl
      _ = 0 := h m l
  have hG0 := ae_eq_zero_prod_of_forall_integral_mul_eq_zero
    (e := fun (m : ℕ) t => Real.sin ((2 * m + 1) * π / 2 * t))
    (fun g hg hgm => ae_eq_zero_of_forall_integral_mul_sin_eq_zero hg hgm) hG hH
  refine Lp.ext (Filter.EventuallyEq.trans ?_ (Lp.coeFn_zero ℝ 2 _).symm)
  have hGe : G ∘ T.symm = f := funext fun x => by simp [G]
  rw [← hGe]
  exact (hmp.symm T).quasiMeasurePreserving.ae_eq_comp hG0

/-- The mode `(x, y) ↦ sin ((2m + 1) π x / 2) cos (l π y)` is positive at a point of the square. -/
private theorem exists_mem_unitSquare_squareMode_pos (m l : ℕ) :
    ∃ x ∈ (unitSquare : Set (WithLp 2 (ℝ × ℝ))), 0 < squareMode m l x := by
  have hl : (0 : ℝ) < l + 1 := by positivity
  set t : ℝ := 1 / (2 * (2 * m + 1)) with ht
  set s : ℝ := 1 / (2 * (l + 1)) with hs
  have ht1 : t < 1 := by
    rw [ht, div_lt_one (by positivity)]
    linarith
  have hs1 : s < 1 := by
    rw [hs, div_lt_one (by positivity)]
    linarith
  -- At `(t, s)` the first factor is `sin (π / 4)` and the second `cos (π l / (2 (l + 1)))`.
  have hct : (2 * m + 1) * π / 2 * t = π / 4 := by
    rw [ht]
    field_simp
    ring
  have hds : l * π * s = π / 2 * (l / (l + 1)) := by
    rw [hs]
    field_simp
  have hl1 : (l : ℝ) / (l + 1) < 1 := by
    rw [div_lt_one hl]
    linarith
  have hl0 : (0 : ℝ) ≤ l / (l + 1) := by positivity
  have ht0 : 0 < t := by positivity
  have hs0 : 0 < s := by positivity
  refine ⟨WithLp.toLp 2 (t, s), mem_openUnitSquare.2 ⟨⟨ht0, ht1⟩, hs0, hs1⟩, ?_⟩
  simp only [squareMode, WithLp.toLp_fst, WithLp.toLp_snd, hct, hds]
  refine mul_pos (Real.sin_pos_of_pos_of_lt_pi ?_ ?_) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;>
    nlinarith [Real.pi_pos]

/-- A function whose value is a mode is not `0` in `L²((0, 1)²)`: the mode is continuous and
positive somewhere on the open square. -/
private theorem value_ne_zero_of_value_ae_eq_squareMode {m l : ℕ} {w : W1p volume unitSquare 2}
    (hw : W1p.value w =ᵐ[volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ)))] squareMode m l) :
    W1p.value w ≠ 0 := fun hval => by
  obtain ⟨x, hx, hpos⟩ := exists_mem_unitSquare_squareMode_pos m l
  have hz : EqOn (squareMode m l) 0 unitSquare := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ unitSquare.isOpen
      (contDiff_squareMode m l (n := 0)).continuous.continuousOn continuousOn_const
    filter_upwards [hw, Lp.coeFn_zero ℝ 2
      (volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ))))] with y h1 h2
    rw [← h1, hval, h2]
  exact hpos.ne' (hz hx)

/-- The `L²((0, 1)²)` pairing with a function whose value is a mode is the integral against the
mode. -/
private theorem inner_value_eq_setIntegral_mul_squareMode {m l : ℕ} {w : W1p volume unitSquare 2}
    (hw : W1p.value w =ᵐ[volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ)))] squareMode m l)
    (f : Lp ℝ 2 (volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ))))) :
    ⟪f, W1p.value w⟫_ℝ = ∫ x in unitSquare, f x * squareMode m l x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw] with x hx
  rw [← hx]
  simp [mul_comm]

/-- Weak mixed eigenfunctions of the square for distinct eigenvalues are orthogonal in
`L²((0, 1)²)`, since the form `∫ ∇u · ∇v` is symmetric. -/
private theorem inner_value_eq_zero_of_ne
    {u w : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1))} {κ κ' : ℝ}
    (hne : κ ≠ κ')
    (hu : ∀ v : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)),
      ⟪W1p.gradient (u : W1p volume unitSquare 2), W1p.gradient (v : W1p volume unitSquare 2)⟫_ℝ =
        κ * ⟪W1p.value (u : W1p volume unitSquare 2), W1p.value (v : W1p volume unitSquare 2)⟫_ℝ)
    (hw : ∀ v : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)),
      ⟪W1p.gradient (w : W1p volume unitSquare 2), W1p.gradient (v : W1p volume unitSquare 2)⟫_ℝ =
        κ' * ⟪W1p.value (w : W1p volume unitSquare 2), W1p.value (v : W1p volume unitSquare 2)⟫_ℝ) :
    ⟪W1p.value (u : W1p volume unitSquare 2), W1p.value (w : W1p volume unitSquare 2)⟫_ℝ = 0 := by
  have h := (hu w).symm.trans ((real_inner_comm _ _).trans (hw u))
  rw [real_inner_comm (W1p.value (u : W1p volume unitSquare 2)), ← sub_eq_zero, ← sub_mul,
    mul_eq_zero] at h
  exact h.resolve_left (sub_ne_zero.2 hne)

/-- **The weak mixed eigenvalues of `-Δ` on the unit square with one Dirichlet side.** With the
Dirichlet part `Γ = {0} × (0, 1)`, the problem `∫ ∇u · ∇v = κ ∫ u v` for every `v ∈ H¹_Γ((0, 1)²)`
has a nonzero solution `u ∈ H¹_Γ((0, 1)²)` exactly for the numbers
`κ = ((2m + 1) π / 2)² + (l π)²` with `m, l ≥ 0`. It imposes `u = 0` on the left side and the
natural Neumann condition `∂_ν u = 0` on the other three sides. -/
theorem exists_ne_zero_forall_inner_gradient_eq_iff_unitSquare {kappa : ℝ} :
    (∃ u : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)), u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)),
        ⟪W1p.gradient (u : W1p volume unitSquare 2),
            W1p.gradient (v : W1p volume unitSquare 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume unitSquare 2),
            W1p.value (v : W1p volume unitSquare 2)⟫_ℝ) ↔
      ∃ m l : ℕ, kappa = ((2 * m + 1) * π / 2) ^ 2 + (l * π) ^ 2 := by
  choose w hwv hw using exists_value_ae_eq_squareMode_and_inner_gradient_eq
  constructor
  · rintro ⟨u, hu0, hu⟩
    by_contra hne
    push Not at hne
    -- `u` is orthogonal to every mode, whose eigenvalues all differ from `κ`, so it vanishes.
    refine hu0 (W1pVanishingOn.valueL_injective ?_)
    rw [map_zero, W1pVanishingOn.valueL_apply]
    refine eq_zero_of_forall_setIntegral_mul_squareMode_eq_zero _ fun m l => ?_
    rw [← inner_value_eq_setIntegral_mul_squareMode (hwv m l)]
    exact inner_value_eq_zero_of_ne (hne m l) hu (hw m l)
  · rintro ⟨m, l, rfl⟩
    refine ⟨w m l, fun h => value_ne_zero_of_value_ae_eq_squareMode (hwv m l) ?_, hw m l⟩
    rw [← W1pVanishingOn.valueL_apply, h, map_zero]

/-- Every mode other than `m = l = 0` has an eigenvalue above `(π / 2)²`. -/
private theorem pi_div_two_sq_lt {m l : ℕ} (h : m ≠ 0 ∨ l ≠ 0) :
    (π / 2) ^ 2 < ((2 * m + 1) * π / 2) ^ 2 + (l * π) ^ 2 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : π / 2 ≤ (2 * m + 1) * π / 2 := by nlinarith [hm, Real.pi_pos]
  rcases h with h | h
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
    have h3 : 3 * π / 2 ≤ (2 * m + 1) * π / 2 := by nlinarith [Real.pi_pos]
    nlinarith [h3, Real.pi_pos, sq_nonneg (l * π)]
  · have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
    have h2 : π ≤ l * π := by nlinarith [Real.pi_pos]
    nlinarith [Real.pi_pos]

/-- **The least mixed eigenvalue `π² / 4` is simple.** Every `u ∈ H¹_Γ((0, 1)²)` with
`∫ ∇u · ∇v = (π / 2)² ∫ u v` for every `v ∈ H¹_Γ((0, 1)²)` is almost everywhere a multiple of
`(x, y) ↦ sin (π x / 2)`. Its component orthogonal to `sin (π x / 2)` is orthogonal to every
mode, since the other modes have other eigenvalues, so it vanishes by completeness. -/
theorem exists_value_ae_eq_mul_sin_of_inner_gradient_eq
    {u : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1))}
    (hu : ∀ v : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)),
      ⟪W1p.gradient (u : W1p volume unitSquare 2), W1p.gradient (v : W1p volume unitSquare 2)⟫_ℝ =
        (π / 2) ^ 2 *
          ⟪W1p.value (u : W1p volume unitSquare 2), W1p.value (v : W1p volume unitSquare 2)⟫_ℝ) :
    ∃ c : ℝ, W1p.value (u : W1p volume unitSquare 2)
      =ᵐ[volume.restrict (unitSquare : Set (WithLp 2 (ℝ × ℝ)))]
        fun x => c * Real.sin (π / 2 * x.fst) := by
  choose w hwv hw using exists_value_ae_eq_squareMode_and_inner_gradient_eq
  set U := W1p.value (u : W1p volume unitSquare 2)
  set W := W1p.value (w 0 0 : W1p volume unitSquare 2)
  have hW : ⟪W, W⟫_ℝ ≠ 0 := inner_self_ne_zero.2 (value_ne_zero_of_value_ae_eq_squareMode (hwv 0 0))
  have h00 : ((2 * ((0 : ℕ) : ℝ) + 1) * π / 2) ^ 2 + (((0 : ℕ) : ℝ) * π) ^ 2 = (π / 2) ^ 2 := by
    simp
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ⟪U, W⟫_ℝ / ⟪W, W⟫_ℝ := ⟨_, rfl⟩
  have hzero : U - c • W = 0 := by
    refine eq_zero_of_forall_setIntegral_mul_squareMode_eq_zero _ fun m l => ?_
    rw [← inner_value_eq_setIntegral_mul_squareMode (hwv m l), inner_sub_left, real_inner_smul_left]
    by_cases hml : m = 0 ∧ l = 0
    · obtain ⟨rfl, rfl⟩ := hml
      rw [hc]
      field_simp
      ring
    · have hne := (pi_div_two_sq_lt (not_and_or.1 hml)).ne
      rw [inner_value_eq_zero_of_ne hne hu (hw m l),
        inner_value_eq_zero_of_ne (h00 ▸ hne) (hw 0 0) (hw m l), mul_zero, sub_zero]
  refine ⟨c, ?_⟩
  rw [sub_eq_zero.1 hzero]
  filter_upwards [Lp.coeFn_smul c W, hwv 0 0] with x h1 h2
  rw [h1, Pi.smul_apply, h2, squareMode_def]
  simp

/-- **The least mixed eigenvalue of the square with one Dirichlet side is `π² / 4`**, the value at
`m = l = 0`, with eigenfunction `(x, y) ↦ sin (π x / 2)`. It is the least eigenvalue `(π / 2)²` of
the interval `(0, 1)` with a Dirichlet condition at `0` and a Neumann condition at `1`, extended
constantly in `y`. -/
theorem isLeast_exists_ne_zero_forall_inner_gradient_eq_unitSquare :
    IsLeast {kappa | ∃ u : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)), u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)),
        ⟪W1p.gradient (u : W1p volume unitSquare 2),
            W1p.gradient (v : W1p volume unitSquare 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume unitSquare 2),
            W1p.value (v : W1p volume unitSquare 2)⟫_ℝ} ((π / 2) ^ 2) := by
  refine ⟨exists_ne_zero_forall_inner_gradient_eq_iff_unitSquare.2 ⟨0, 0, by simp⟩,
    fun kappa hkappa => ?_⟩
  obtain ⟨m, l, rfl⟩ := exists_ne_zero_forall_inner_gradient_eq_iff_unitSquare.1 hkappa
  have hm : (1 : ℝ) ≤ 2 * m + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have : π / 2 ≤ (2 * m + 1) * π / 2 := by nlinarith [hm, Real.pi_pos]
  nlinarith [sq_nonneg (l * π), Real.pi_pos]

/-- **The second mixed eigenvalue of the square with one Dirichlet side is `5 π² / 4`**: the least
mixed eigenvalue above `π² / 4` is `(π / 2)² + π²`, at `m = 0`, `l = 1`, with eigenfunction
`(x, y) ↦ sin (π x / 2) cos (π y)`. It comes from the second variable: the second eigenvalue
`(3 π / 2)² = 9 π² / 4` of the interval with one Dirichlet endpoint, at `m = 1`, `l = 0`, is
larger. Since `π² / 4` is simple (`exists_value_ae_eq_mul_sin_of_inner_gradient_eq`), `5 π² / 4` is
the second mixed eigenvalue counted with multiplicity. -/
theorem isLeast_exists_ne_zero_forall_inner_gradient_eq_unitSquare_of_lt :
    IsLeast {kappa | (π / 2) ^ 2 < kappa ∧
      ∃ u : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)), u ≠ 0 ∧
      ∀ v : W1pVanishingOn volume unitSquare 2 (squareLeftPart (Ioo 0 1)),
        ⟪W1p.gradient (u : W1p volume unitSquare 2),
            W1p.gradient (v : W1p volume unitSquare 2)⟫_ℝ =
          kappa * ⟪W1p.value (u : W1p volume unitSquare 2),
            W1p.value (v : W1p volume unitSquare 2)⟫_ℝ} (5 * (π / 2) ^ 2) := by
  refine ⟨⟨by nlinarith [Real.pi_pos],
    exists_ne_zero_forall_inner_gradient_eq_iff_unitSquare.2 ⟨0, 1, by ring⟩⟩,
    fun kappa ⟨hlt, hkappa⟩ => ?_⟩
  obtain ⟨m, l, rfl⟩ := exists_ne_zero_forall_inner_gradient_eq_iff_unitSquare.1 hkappa
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · -- With `l = 0`, the eigenvalue exceeds `(π / 2)²` only for `m ≥ 1`.
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at hlt
    · have hm' : (3 : ℝ) ≤ 2 * m + 1 := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      have : 3 * π / 2 ≤ (2 * m + 1) * π / 2 := by nlinarith [Real.pi_pos]
      nlinarith [Real.pi_pos]
  · have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have hm : (1 : ℝ) ≤ 2 * m + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have h1 : π / 2 ≤ (2 * m + 1) * π / 2 := by nlinarith [hm, Real.pi_pos]
    have h2 : π ≤ l * π := by nlinarith [Real.pi_pos]
    nlinarith [Real.pi_pos]

end TauCeti.Examples.MixedSpectrumUnitSquare
