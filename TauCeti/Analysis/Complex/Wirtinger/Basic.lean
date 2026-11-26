/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.LinearAlgebra.Complex.LinearPart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Analysis.Calculus.FDeriv.Pow
import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Normed.Module.RCLike.Basic
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.Topology.Algebra.Module.Equiv.RestrictScalars

/-!
# Wirtinger derivatives

For a function `g : V → W` between complex normed spaces, the **Wirtinger derivatives** of `g`
at `x` are the complex-linear and complex-antilinear parts of its real derivative:

`∂g(x) v = (Dg(x) v - I • Dg(x)(I • v)) / 2`,  `\bar∂g(x) v = (Dg(x) v + I • Dg(x)(I • v)) / 2`.

In holomorphic coordinates `z_j = x_j + I y_j` with coordinate vectors `e_j`, these are the
classical operators `∂g(x) e_j = ∂g/∂z_j = (∂g/∂x_j - I ∂g/∂y_j) / 2` and
`\bar∂g(x) e_j = ∂g/∂(conj z_j) = (∂g/∂x_j + I ∂g/∂y_j) / 2`.

Their comparison with the Levi form is in `TauCeti.Analysis.Complex.Wirtinger.LeviForm`.

## Main definitions

* `TauCeti.wirtingerDeriv g x`: the complex-linear Wirtinger derivative `∂g(x) : V →L[ℂ] W`.
* `TauCeti.conjWirtingerDeriv g x`: the complex-antilinear Wirtinger derivative
  `\bar∂g(x) : V →L⋆[ℂ] W`.
* `TauCeti.wirtingerPartsCLM a b`: the real-linear map `v ↦ v • a + conj v • b` of the plane with
  Wirtinger parts `a` and `b`.
* `TauCeti.wirtingerPartsL`: the continuous real-linear map `(a, b) ↦ wirtingerPartsCLM a b`.

## Main results

* `TauCeti.wirtingerDeriv_add_conjWirtingerDeriv`: `∂g + \bar∂g = Dg`.
* `TauCeti.fderiv_apply_one_add_I_smul_fderiv_apply_I`: in one variable,
  `∂ₛ g + i ∂ₜ g = 2 \bar∂g`.
* `TauCeti.norm_wirtingerDeriv_apply_le`, `TauCeti.norm_conjWirtingerDeriv_apply_le`: both
  Wirtinger derivatives are bounded by the real derivative, `‖∂g(x) v‖ ≤ ‖Dg(x)‖ ‖v‖`.
* `TauCeti.coe_wirtingerDeriv_eq_complexLinearPart`,
  `TauCeti.coe_conjWirtingerDeriv_eq_complexAntilinearPart`: the Wirtinger derivatives are the
  complex-linear and complex-antilinear parts of the real derivative.
* `TauCeti.conjWirtingerDeriv_ofReal_comp_apply`: for real-valued `f`, `\bar∂f = conj ∂f`;
  `TauCeti.conjWirtingerDeriv_ofReal_comp_apply_eq_lineDeriv` writes `\bar∂f` with directional
  derivatives.
* `TauCeti.wirtingerDeriv_smul_apply`, `TauCeti.conjWirtingerDeriv_smul_apply`: the product rules
  `∂(c g) = c ∂g + (∂c) g` and `\bar∂(c g) = c \bar∂g + (\bar∂c) g` for a complex-valued factor `c`.
* `TauCeti.norm_wirtingerDeriv_smul_sub_smul_le`,
  `TauCeti.norm_conjWirtingerDeriv_smul_sub_smul_le`: for a real factor `χ`,
  `‖∂(χ u)(x) v - χ ∂u(x) v‖ ≤ ‖Dχ(x)‖ ‖v‖ ‖u(x)‖`, and likewise for `\bar∂`.
* `ContDiffAt.wirtingerDeriv_apply`, `ContDiffAt.conjWirtingerDeriv_apply`: both Wirtinger
  derivatives of a `C^(m+1)` map are `C^m`; in particular the conjugate one is continuous for a
  `C¹` map (`ContDiff.continuous_conjWirtingerDeriv_apply`).
* `TauCeti.conjWirtingerDeriv_of_notMem_tsupport`: `\bar∂g` vanishes off the topological support.
* `DifferentiableAt.conjWirtingerDeriv_eq_zero`, `DifferentiableAt.wirtingerDeriv_eq_fderiv`:
  for complex differentiable `g`, `\bar∂g = 0` and `∂g` is the complex derivative.
* `TauCeti.wirtingerDeriv_const_smul`, `TauCeti.conjWirtingerDeriv_const_smul`: `∂` and `\bar∂`
  commute with complex scalar multiplication.
* `TauCeti.wirtingerDeriv_apply_one_ofReal_im`, `TauCeti.conjWirtingerDeriv_apply_one_ofReal_im`:
  the Wirtinger derivatives of the imaginary part are `∂ Im = -i/2` and `\bar∂ Im = i/2`.
* `TauCeti.conjWirtingerDeriv_eq_sum_smul`: `\bar∂` depends complex-linearly on the real
  derivative.
* `TauCeti.conjWirtingerDeriv_fun_sub`, `TauCeti.conjWirtingerDeriv_fun_sum`: `\bar∂` of a
  pointwise difference and of a finite sum of real-differentiable functions.
* `TauCeti.conjWirtingerDeriv_comp`: the chain rule `\bar∂(φ ∘ g) = Dφ(g x) ∘ \bar∂g` after a
  holomorphic map `φ`, and `TauCeti.conjWirtingerDeriv_comp_eq_comp_fderiv`, the chain rule
  `\bar∂(φ ∘ g) = \bar∂φ(g x) ∘ Dg(x)` before a holomorphic map `g`; in one variable
  `TauCeti.conjWirtingerDeriv_comp_eq_conj_smul` writes it as `\bar∂(φ ∘ g) = \bar{g'} \bar∂φ`.
* `ContinuousLinearMap.conjWirtingerDeriv_comp_left`: the chain rule `\bar∂(L ∘ g) = L ∘ \bar∂g`
  after a continuous complex-linear map `L`.
* `ContinuousLinearEquiv.conjWirtingerDeriv_comp_left_apply`: the chain rule after a complex-linear
  isomorphism, for maps into a space with any compatible real structure.
* `ContinuousLinearMap.wirtingerDeriv_comp_right`,
  `ContinuousLinearMap.conjWirtingerDeriv_comp_right`: the chain rules
  `∂(f ∘ L)(x) = ∂f(L x) ∘ L` and `\bar∂(f ∘ L)(x) = \bar∂f(L x) ∘ L` before a complex-linear
  map `L`.
* `TauCeti.wirtingerDeriv_comp_mul_left`, `TauCeti.conjWirtingerDeriv_comp_mul_left`: in one
  variable, `∂(f(c ·))(z) = c ∂f(c z)` and `\bar∂(f(c ·))(z) = conj c \bar∂f(c z)`, with no
  differentiability assumption.
* `TauCeti.conjWirtingerDeriv_fun_mul`, `TauCeti.conjWirtingerDeriv_fun_pow`: the Leibniz and
  power rules for complex-valued functions.
* `TauCeti.conjWirtingerDeriv_finsetProd`, `TauCeti.norm_conjWirtingerDeriv_finsetProd_le`: the
  Leibniz rule for a finite product, and the consequence that bounds
  `‖\bar∂ (f i)(x)‖ ≤ K |f i (x)|` on the factors give `‖\bar∂ (∏ f i)(x)‖ ≤ #s K |∏ f i (x)|`.
* `TauCeti.smul_conjWirtingerDeriv_apply_one_eq_sub`,
  `TauCeti.smul_wirtingerDeriv_apply_one_eq_sub`: in one variable, for all `ω₁`, `ω₂`,
  `2 i Im (conj ω₁ ω₂) \bar∂f = ω₂ Df ω₁ - ω₁ Df ω₂` and
  `2 i Im (conj ω₁ ω₂) ∂f = conj ω₁ Df ω₂ - conj ω₂ Df ω₁`.
* `TauCeti.conjWirtingerDeriv_apply_one_eq_inv_smul_sub`: hence `\bar∂f` is determined by
  `Df ω₁` and `Df ω₂` for `ℝ`-linearly independent `ω₁`, `ω₂`.
* `TauCeti.conjWirtingerDeriv_apply_eq_conjWirtingerDeriv_line`: `\bar∂g(x) v` is the
  one-variable conjugate Wirtinger derivative of the restriction of `g` to the complex line
  `t ↦ x + t • v`.
* `TauCeti.wirtingerDeriv_cexp_mul_sub_conj_mul_conj`,
  `TauCeti.conjWirtingerDeriv_cexp_mul_sub_conj_mul_conj`: the twisted exponential
  `exp (a z - conj a conj z)` has `∂ = a ·` and `\bar∂ = -conj a ·`.
  Translation by `w` multiplies it by `exp (2πiθ)` when `Im (a w) = π (k + θ)` for an integer `k`
  (`TauCeti.cexp_mul_add_sub_conj_mul_conj_add_of_im_mul_eq`).
* `TauCeti.exists_eq_wirtingerPartsCLM`: every real-linear map `ℂ →L[ℝ] W` is
  `v ↦ v • a + conj v • b`; `TauCeti.smulRight_id_eq_wirtingerPartsCLM` and
  `TauCeti.smulRight_conjCLE_eq_wirtingerPartsCLM` give `v ↦ v • c` and `v ↦ conj v • c`.
* `TauCeti.fderiv_eq_wirtingerPartsCLM`, `TauCeti.wirtingerPartsCLM_inj`: in one variable the
  real derivative is `wirtingerPartsCLM` of its two Wirtinger parts, which it determines; the
  Wirtinger parts of `wirtingerPartsCLM a b` are `a` and `b`
  (`TauCeti.wirtingerDeriv_wirtingerPartsCLM_apply_one`,
  `TauCeti.conjWirtingerDeriv_wirtingerPartsCLM_apply_one`).
* `ContDiffAt.hasFDerivAt_wirtingerDeriv_apply`, `ContDiffAt.hasFDerivAt_conjWirtingerDeriv_apply`:
  the derivatives of `y ↦ ∂g(y) u` and `y ↦ \bar∂g(y) u` for a `C²` map `g`, in terms of the
  second derivative of `g`.
* `TauCeti.conjWirtingerDeriv_wirtingerDeriv_self`,
  `TauCeti.wirtingerDeriv_conjWirtingerDeriv_self`: `\bar∂_v ∂_v g` and `∂_v \bar∂_v g` are a
  quarter of the sum of the second real derivatives of `g` along `v` and `I • v`; in coordinates,
  `4 ∑_j ∂²g / ∂(conj z_j) ∂z_j` is the real Laplacian of `g`.
* `TauCeti.wirtingerDeriv_wirtingerDeriv_comm`, `TauCeti.wirtingerDeriv_conjWirtingerDeriv_comm`,
  `TauCeti.conjWirtingerDeriv_conjWirtingerDeriv_comm`: second Wirtinger derivatives of a `C²`
  map commute.

## Implementation notes

Both derivatives are built from the totalized real derivative `fderiv ℝ g x`, so at a point where
`g` is not real-differentiable both are the junk value `0`. Results that need a genuine derivative
therefore assume differentiability; for instance, the converse "`\bar∂g = 0` implies complex
differentiability" (`TauCeti.differentiableAt_iff_conjWirtingerDeriv_eq_zero` in
`TauCeti.Analysis.Complex.Wirtinger.Holomorphic`) assumes `DifferentiableAt ℝ g x`.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*.
* L. Hörmander, *An introduction to complex analysis in several variables*, Chapter II.
-/

public section

open Complex ComplexConjugate Topology

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

section Wirtinger

variable (g : V → W) (x : V)

/-- The **Wirtinger derivative** `∂g(x)` of a function into a complex normed space: the
complex-linear part `v ↦ (Dg(x) v - I • Dg(x)(I • v)) / 2` of its real derivative
(`ContinuousLinearMap.complexLinearPart`). On a coordinate vector `e_j` it is `∂g / ∂z_j`. Like
`fderiv ℝ g x`, from which it is built, it is the junk value `0` at points where `g` is not
real-differentiable, so results that need a genuine derivative assume differentiability of `g`
at `x`. -/
noncomputable def wirtingerDeriv : V →L[ℂ] W :=
  (fderiv ℝ g x).complexLinearPart

/-- The **conjugate Wirtinger derivative** `\bar∂g(x)` of a function into a complex normed space:
the complex-antilinear part `v ↦ (Dg(x) v + I • Dg(x)(I • v)) / 2` of its real derivative
(`ContinuousLinearMap.complexAntilinearPart`). On a coordinate vector `e_j` it is
`∂g / ∂(conj z_j)`. Like `fderiv ℝ g x`, from which it is built, it is the junk value `0` at
points where `g` is not real-differentiable, so results that need a genuine derivative assume
differentiability of `g` at `x`. -/
noncomputable def conjWirtingerDeriv : V →L⋆[ℂ] W :=
  (fderiv ℝ g x).complexAntilinearPart

/-- The Wirtinger derivative is the complex-linear part of the real derivative. -/
theorem wirtingerDeriv_eq_complexLinearPart :
    wirtingerDeriv g x = (fderiv ℝ g x).complexLinearPart :=
  (rfl)

/-- The conjugate Wirtinger derivative is the complex-antilinear part of the real derivative. -/
theorem conjWirtingerDeriv_eq_complexAntilinearPart :
    conjWirtingerDeriv g x = (fderiv ℝ g x).complexAntilinearPart :=
  (rfl)

/-- The defining formula of the Wirtinger derivative. -/
theorem wirtingerDeriv_apply (v : V) :
    wirtingerDeriv g x v = (2 : ℂ)⁻¹ • (fderiv ℝ g x v - I • fderiv ℝ g x (I • v)) := by
  rw [wirtingerDeriv_eq_complexLinearPart, ContinuousLinearMap.complexLinearPart_apply,
    ← ofReal_ofNat, ← ofReal_inv, Complex.coe_smul]

/-- The defining formula of the conjugate Wirtinger derivative. -/
theorem conjWirtingerDeriv_apply (v : V) :
    conjWirtingerDeriv g x v = (2 : ℂ)⁻¹ • (fderiv ℝ g x v + I • fderiv ℝ g x (I • v)) := by
  rw [conjWirtingerDeriv_eq_complexAntilinearPart,
    ContinuousLinearMap.complexAntilinearPart_apply, ← ofReal_ofNat, ← ofReal_inv,
    Complex.coe_smul]

/-- The conjugate Wirtinger derivative evaluates the bundled real-linear conjugate projection
of the real derivative. -/
theorem conjWirtingerDeriv_apply_eq_complexAntilinearPartL (v : V) :
    conjWirtingerDeriv g x v =
      ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ g x) v := by
  rw [conjWirtingerDeriv_eq_complexAntilinearPart,
    ContinuousLinearMap.complexAntilinearPart_apply,
    ContinuousLinearMap.complexAntilinearPartL_apply_apply]

/-- In one variable the operator `D = ∂ₛ + i ∂ₜ` of the Cauchy–Pompeiu formula is twice the
conjugate Wirtinger derivative. This holds for the totalized derivative, with no differentiability
assumption. -/
theorem fderiv_apply_one_add_I_smul_fderiv_apply_I (u : ℂ → W) (z : ℂ) :
    fderiv ℝ u z 1 + I • fderiv ℝ u z I = (2 : ℂ) • conjWirtingerDeriv u z 1 := by
  rw [conjWirtingerDeriv_apply, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul, smul_eq_mul,
    mul_one]

/-- The two Wirtinger derivatives add up to the real derivative. -/
@[simp]
theorem wirtingerDeriv_add_conjWirtingerDeriv (v : V) :
    wirtingerDeriv g x v + conjWirtingerDeriv g x v = fderiv ℝ g x v := by
  rw [wirtingerDeriv_apply, conjWirtingerDeriv_apply]
  module

/-- The Wirtinger derivative is bounded by the real derivative: `‖∂g(x) v‖ ≤ ‖Dg(x)‖ ‖v‖`. -/
theorem norm_wirtingerDeriv_apply_le (v : V) :
    ‖wirtingerDeriv g x v‖ ≤ ‖fderiv ℝ g x‖ * ‖v‖ := by
  have h := (fderiv ℝ g x).le_opNorm_of_le (x := I • v) (c := ‖v‖) (by simp [norm_smul])
  rw [wirtingerDeriv_apply, sub_eq_add_neg]
  exact norm_two_inv_smul_add_le ((fderiv ℝ g x).le_opNorm v) (by simpa [norm_smul] using h)

/-- The conjugate Wirtinger derivative is bounded by the real derivative:
`‖\bar∂g(x) v‖ ≤ ‖Dg(x)‖ ‖v‖`. -/
theorem norm_conjWirtingerDeriv_apply_le (v : V) :
    ‖conjWirtingerDeriv g x v‖ ≤ ‖fderiv ℝ g x‖ * ‖v‖ := by
  have h := (fderiv ℝ g x).le_opNorm_of_le (x := I • v) (c := ‖v‖) (by simp [norm_smul])
  rw [conjWirtingerDeriv_apply]
  exact norm_two_inv_smul_add_le ((fderiv ℝ g x).le_opNorm v) (by simpa [norm_smul] using h)

/-- The Wirtinger derivative is the complex-linear part `TauCeti.complexLinearPart` of the real
derivative, for the complex structures given by multiplication by `I`. -/
theorem coe_wirtingerDeriv_eq_complexLinearPart :
    ⇑(wirtingerDeriv g x) =
      complexLinearPart (DistribSMul.toLinearMap ℝ V I) (DistribSMul.toLinearMap ℝ W I)
        (fderiv ℝ g x : V →ₗ[ℝ] W) :=
  (fderiv ℝ g x).coe_complexLinearPart

/-- The conjugate Wirtinger derivative is the complex-antilinear part
`TauCeti.complexAntilinearPart` of the real derivative, for the complex structures given by
multiplication by `I`. -/
theorem coe_conjWirtingerDeriv_eq_complexAntilinearPart :
    ⇑(conjWirtingerDeriv g x) =
      complexAntilinearPart (DistribSMul.toLinearMap ℝ V I)
        (DistribSMul.toLinearMap ℝ W I) (fderiv ℝ g x : V →ₗ[ℝ] W) :=
  (fderiv ℝ g x).coe_complexAntilinearPart

/-- The Wirtinger derivative only depends on the germ of the function. -/
theorem _root_.Filter.EventuallyEq.wirtingerDeriv_eq {g₁ g : V → W} {x : V}
    (h : g₁ =ᶠ[𝓝 x] g) : wirtingerDeriv g₁ x = wirtingerDeriv g x := by
  ext v
  simp only [wirtingerDeriv_apply, h.fderiv_eq]

/-- The conjugate Wirtinger derivative only depends on the germ of the function. -/
theorem _root_.Filter.EventuallyEq.conjWirtingerDeriv_eq {g₁ g : V → W} {x : V}
    (h : g₁ =ᶠ[𝓝 x] g) : conjWirtingerDeriv g₁ x = conjWirtingerDeriv g x := by
  ext v
  simp only [conjWirtingerDeriv_apply, h.fderiv_eq]

/-- The Wirtinger derivative is additive on real-differentiable functions. -/
theorem wirtingerDeriv_add {g₁ g₂ : V → W} {x : V} (h₁ : DifferentiableAt ℝ g₁ x)
    (h₂ : DifferentiableAt ℝ g₂ x) :
    wirtingerDeriv (g₁ + g₂) x = wirtingerDeriv g₁ x + wirtingerDeriv g₂ x := by
  ext v
  simp only [wirtingerDeriv_apply, fderiv_add h₁ h₂, add_apply]
  module

/-- The Wirtinger derivative commutes with subtraction of real-differentiable functions. -/
theorem wirtingerDeriv_sub {g₁ g₂ : V → W} {x : V} (h₁ : DifferentiableAt ℝ g₁ x)
    (h₂ : DifferentiableAt ℝ g₂ x) :
    wirtingerDeriv (g₁ - g₂) x = wirtingerDeriv g₁ x - wirtingerDeriv g₂ x := by
  ext v
  simp only [wirtingerDeriv_apply, fderiv_sub h₁ h₂, sub_apply]
  module

/-- The conjugate Wirtinger derivative is additive on real-differentiable functions. -/
theorem conjWirtingerDeriv_add {g₁ g₂ : V → W} {x : V} (h₁ : DifferentiableAt ℝ g₁ x)
    (h₂ : DifferentiableAt ℝ g₂ x) :
    conjWirtingerDeriv (g₁ + g₂) x = conjWirtingerDeriv g₁ x + conjWirtingerDeriv g₂ x := by
  ext v
  simp only [conjWirtingerDeriv_apply, fderiv_add h₁ h₂, add_apply]
  module

/-- The conjugate Wirtinger derivative commutes with subtraction of real-differentiable
functions. -/
theorem conjWirtingerDeriv_sub {g₁ g₂ : V → W} {x : V} (h₁ : DifferentiableAt ℝ g₁ x)
    (h₂ : DifferentiableAt ℝ g₂ x) :
    conjWirtingerDeriv (g₁ - g₂) x = conjWirtingerDeriv g₁ x - conjWirtingerDeriv g₂ x := by
  ext v
  simp only [conjWirtingerDeriv_apply, fderiv_sub h₁ h₂, sub_apply]
  module

/-- The conjugate Wirtinger derivative commutes with pointwise subtraction of real-differentiable
functions. -/
theorem conjWirtingerDeriv_fun_sub {g₁ g₂ : V → W} {x : V} (h₁ : DifferentiableAt ℝ g₁ x)
    (h₂ : DifferentiableAt ℝ g₂ x) :
    conjWirtingerDeriv (fun y ↦ g₁ y - g₂ y) x =
      conjWirtingerDeriv g₁ x - conjWirtingerDeriv g₂ x :=
  conjWirtingerDeriv_sub h₁ h₂

/-- Adding a constant does not change the conjugate Wirtinger derivative. -/
@[simp]
theorem conjWirtingerDeriv_add_const (g : V → W) (c : W) (x : V) :
    conjWirtingerDeriv (fun y ↦ g y + c) x = conjWirtingerDeriv g x := by
  rw [conjWirtingerDeriv_eq_complexAntilinearPart, fderiv_add_const,
    conjWirtingerDeriv_eq_complexAntilinearPart]

/-- The conjugate Wirtinger derivative commutes with translations of the source. -/
theorem conjWirtingerDeriv_comp_add_right (g : V → W) (a x : V) :
    conjWirtingerDeriv (fun y ↦ g (y + a)) x = conjWirtingerDeriv g (x + a) := by
  rw [conjWirtingerDeriv_eq_complexAntilinearPart, fderiv_comp_add_right,
    conjWirtingerDeriv_eq_complexAntilinearPart]

/-- The conjugate Wirtinger derivative commutes with multiplication by a complex constant. -/
theorem conjWirtingerDeriv_const_smul {g : V → W} {x : V} (c : ℂ) :
    conjWirtingerDeriv (c • g) x = c • conjWirtingerDeriv g x := by
  ext v
  simp only [conjWirtingerDeriv_apply, fderiv_const_smul_field c, Pi.smul_apply, smul_apply]
  module

/-- The Wirtinger derivative commutes with multiplication by a complex constant. -/
theorem wirtingerDeriv_const_smul {g : V → W} {x : V} (c : ℂ) :
    wirtingerDeriv (c • g) x = c • wirtingerDeriv g x := by
  ext v
  simp only [wirtingerDeriv_apply, fderiv_const_smul_field c, Pi.smul_apply, smul_apply]
  module

/-- The conjugate Wirtinger derivative in the direction `v` is the one-variable conjugate
Wirtinger derivative `∂/∂(conj t)` of the restriction `t ↦ g (x + t • v)` to the complex line
through `x` in the direction `v`. -/
theorem conjWirtingerDeriv_apply_eq_conjWirtingerDeriv_line {g : V → W} {x : V}
    (hg : DifferentiableAt ℝ g x) (v : V) :
    conjWirtingerDeriv g x v = conjWirtingerDeriv (fun t : ℂ ↦ g (x + t • v)) 0 1 := by
  have hline : HasFDerivAt (fun t : ℂ ↦ x + t • v) ((ContinuousLinearMap.id ℝ ℂ).smulRight v)
      0 := (hasFDerivAt_id (0 : ℂ)).smul_const v |>.const_add x
  have hcomp : HasFDerivAt (fun t : ℂ ↦ g (x + t • v)) _ 0 := (by simpa using hg.hasFDerivAt :
    HasFDerivAt g (fderiv ℝ g x) (x + (0 : ℂ) • v)).comp (0 : ℂ) hline
  rw [conjWirtingerDeriv_apply, conjWirtingerDeriv_apply, hcomp.fderiv]
  simp

/-- The conjugate Wirtinger derivative of a `C^(m+1)` map, evaluated on a fixed vector, is `C^m`. -/
theorem _root_.ContDiffAt.conjWirtingerDeriv_apply {g : V → W} {x : V} {m n : WithTop ℕ∞}
    (hg : ContDiffAt ℝ n g x) (hmn : m + 1 ≤ n) (v : V) :
    ContDiffAt ℝ m (fun z ↦ conjWirtingerDeriv g z v) x := by
  have h (w : V) : ContDiffAt ℝ m (fun z ↦ fderiv ℝ g z w) x :=
    (hg.fderiv_right hmn).clm_apply contDiffAt_const
  simp only [TauCeti.conjWirtingerDeriv_apply]
  exact ((h v).add ((h (I • v)).const_smul I)).const_smul _

/-- The Wirtinger derivative of a `C^(m+1)` map, evaluated on a fixed vector, is `C^m`. -/
theorem _root_.ContDiffAt.wirtingerDeriv_apply {g : V → W} {x : V} {m n : WithTop ℕ∞}
    (hg : ContDiffAt ℝ n g x) (hmn : m + 1 ≤ n) (v : V) :
    ContDiffAt ℝ m (fun z ↦ wirtingerDeriv g z v) x := by
  have h (w : V) : ContDiffAt ℝ m (fun z ↦ fderiv ℝ g z w) x :=
    (hg.fderiv_right hmn).clm_apply contDiffAt_const
  simp only [TauCeti.wirtingerDeriv_apply]
  exact ((h v).sub ((h (I • v)).const_smul I)).const_smul _

/-- The conjugate Wirtinger derivative of a `C¹` map, evaluated on a fixed vector, is
continuous. -/
theorem _root_.ContDiff.continuous_conjWirtingerDeriv_apply {g : V → W} (hg : ContDiff ℝ 1 g)
    (v : V) : Continuous fun z ↦ conjWirtingerDeriv g z v :=
  continuous_iff_continuousAt.2 fun x ↦
    (hg.contDiffAt.conjWirtingerDeriv_apply (m := 0) (by simp) v).continuousAt

/-- The Wirtinger derivative of a `C¹` map, evaluated on a fixed vector, is continuous. -/
theorem _root_.ContDiff.continuous_wirtingerDeriv_apply {g : V → W} (hg : ContDiff ℝ 1 g)
    (v : V) : Continuous fun z ↦ wirtingerDeriv g z v :=
  continuous_iff_continuousAt.2 fun x ↦
    (hg.contDiffAt.wirtingerDeriv_apply (m := 0) (by simp) v).continuousAt

/-- The conjugate Wirtinger derivative vanishes off the topological support. -/
theorem conjWirtingerDeriv_of_notMem_tsupport {g : V → W} {x : V} (hx : x ∉ tsupport g) :
    conjWirtingerDeriv g x = 0 := by
  ext v
  simp [conjWirtingerDeriv_apply, fderiv_of_notMem_tsupport ℝ hx]

/-- For complex differentiable `g`, the conjugate Wirtinger derivative vanishes: this is the
Cauchy–Riemann equation `\bar∂g = 0`. -/
@[simp]
theorem _root_.DifferentiableAt.conjWirtingerDeriv_eq_zero {g : V → W} {x : V}
    (hg : DifferentiableAt ℂ g x) : conjWirtingerDeriv g x = 0 := by
  ext v
  rw [conjWirtingerDeriv_apply, hg.fderiv_restrictScalars ℝ]
  simp [smul_smul]

/-- For complex differentiable `g`, the Wirtinger derivative is the complex derivative. -/
@[simp]
theorem _root_.DifferentiableAt.wirtingerDeriv_eq_fderiv {g : V → W} {x : V}
    (hg : DifferentiableAt ℂ g x) : wirtingerDeriv g x = fderiv ℂ g x := by
  ext v
  rw [wirtingerDeriv_apply, hg.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_smul, I_mul_I]
  module

/-- The Wirtinger derivative of the identity is the identity: `∂z = 1`. -/
theorem wirtingerDeriv_id : wirtingerDeriv (id : V → V) x = ContinuousLinearMap.id ℂ V := by
  rw [(differentiableAt_id (𝕜 := ℂ)).wirtingerDeriv_eq_fderiv, fderiv_id]

/-- The conjugate Wirtinger derivative of the identity vanishes: `\bar∂z = 0`. -/
theorem conjWirtingerDeriv_id : conjWirtingerDeriv (id : V → V) x = 0 :=
  (differentiableAt_id (𝕜 := ℂ)).conjWirtingerDeriv_eq_zero

/-- Adding a complex differentiable map does not change the conjugate Wirtinger derivative:
`\bar∂(g + f) = \bar∂f`. Where `f` is not real-differentiable, neither is `g + f`, and both sides
vanish. -/
theorem _root_.DifferentiableAt.conjWirtingerDeriv_add_left {g f : V → W} {y : V}
    (hg : DifferentiableAt ℂ g y) :
    conjWirtingerDeriv (fun z ↦ g z + f z) y = conjWirtingerDeriv f y := by
  have hgR : DifferentiableAt ℝ g y := hg.restrictScalars ℝ
  by_cases hf : DifferentiableAt ℝ f y
  · exact (conjWirtingerDeriv_add hgR hf).trans (by rw [hg.conjWirtingerDeriv_eq_zero, zero_add])
  · have hf' : ¬DifferentiableAt ℝ (fun z ↦ g z + f z) y := fun h ↦
      hf (by simpa using h.fun_sub hgR)
    ext v
    simp only [conjWirtingerDeriv_apply, fderiv_zero_of_not_differentiableAt hf,
      fderiv_zero_of_not_differentiableAt hf']

/-- Adding the identity does not change the conjugate Wirtinger derivative:
`\bar∂(z + f) = \bar∂f`. -/
@[simp]
theorem conjWirtingerDeriv_id_add (f : V → V) (y : V) :
    conjWirtingerDeriv (fun z ↦ z + f z) y = conjWirtingerDeriv f y :=
  (differentiableAt_id (𝕜 := ℂ)).conjWirtingerDeriv_add_left

/-- Adding the identity adds the identity to the Wirtinger derivative of a real-differentiable
function: `∂(z + f) = 1 + ∂f`. -/
theorem wirtingerDeriv_id_add {f : V → V} {y : V} (hf : DifferentiableAt ℝ f y) :
    wirtingerDeriv (fun z ↦ z + f z) y = ContinuousLinearMap.id ℂ V + wirtingerDeriv f y :=
  (wirtingerDeriv_add differentiableAt_id hf).trans (by rw [wirtingerDeriv_id])

/-- For a real function, the conjugate Wirtinger derivative is the complex conjugate of the
Wirtinger derivative. -/
theorem conjWirtingerDeriv_ofReal_comp_apply (f : V → ℝ) (x v : V) :
    conjWirtingerDeriv (fun y ↦ (f y : ℂ)) x v = conj (wirtingerDeriv (fun y ↦ (f y : ℂ)) x v) := by
  apply Complex.ext <;>
  simp [conjWirtingerDeriv_apply, wirtingerDeriv_apply]

/-- For a real function differentiable at `x`, the conjugate Wirtinger derivative of its
complexification is half the complex combination `∂ᵥf + i ∂_{iv}f` of its directional
derivatives. -/
theorem conjWirtingerDeriv_ofReal_comp_apply_eq_lineDeriv {f : V → ℝ} {x : V}
    (hf : DifferentiableAt ℝ f x) (v : V) :
    conjWirtingerDeriv (fun y ↦ (f y : ℂ)) x v =
      (2 : ℂ)⁻¹ * (((lineDeriv ℝ f x v : ℝ) : ℂ) + I * ((lineDeriv ℝ f x (I • v) : ℝ) : ℂ)) := by
  simp [conjWirtingerDeriv_apply, hf.lineDeriv_eq_fderiv]

end Wirtinger

/-- **The product rule for the Wirtinger derivative**: for a complex-valued factor `c`,
`∂(c g) = c ∂g + (∂c) g`. -/
theorem wirtingerDeriv_smul_apply {c : V → ℂ} {g : V → W} {x : V}
    (hc : DifferentiableAt ℝ c x) (hg : DifferentiableAt ℝ g x) (v : V) :
    wirtingerDeriv (fun y ↦ c y • g y) x v =
      c x • wirtingerDeriv g x v + wirtingerDeriv c x v • g x := by
  simp only [wirtingerDeriv_apply, fderiv_fun_smul hc hg, add_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.smulRight_apply]
  module

/-- **The product rule for the conjugate Wirtinger derivative**: for a complex-valued factor `c`,
`\bar∂(c g) = c \bar∂g + (\bar∂c) g`. -/
theorem conjWirtingerDeriv_smul_apply {c : V → ℂ} {g : V → W} {x : V}
    (hc : DifferentiableAt ℝ c x) (hg : DifferentiableAt ℝ g x) (v : V) :
    conjWirtingerDeriv (fun y ↦ c y • g y) x v =
      c x • conjWirtingerDeriv g x v + conjWirtingerDeriv c x v • g x := by
  simp only [conjWirtingerDeriv_apply, fderiv_fun_smul hc hg, add_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.smulRight_apply]
  module

/-- Against a real factor `χ`, `∂(χ u)` differs from `χ ∂u` by `(∂χ) u`, whose norm is at most
`‖Dχ‖ ‖v‖ ‖u‖`. -/
theorem norm_wirtingerDeriv_smul_sub_smul_le {χ : V → ℝ} {u : V → W} {x : V}
    (hχ : DifferentiableAt ℝ χ x) (hu : DifferentiableAt ℝ u x) (v : V) :
    ‖wirtingerDeriv (fun y ↦ χ y • u y) x v - χ x • wirtingerDeriv u x v‖ ≤
      ‖fderiv ℝ χ x‖ * ‖v‖ * ‖u x‖ := by
  simp_rw [← Complex.coe_smul]
  rw [wirtingerDeriv_smul_apply hχ.ofReal_comp hu, add_sub_cancel_left,
    norm_smul]
  gcongr
  exact (norm_wirtingerDeriv_apply_le _ _ _).trans (by gcongr; exact norm_fderiv_ofReal_comp_le χ x)

/-- Against a real factor `χ`, `\bar∂(χ u)` differs from `χ \bar∂u` by `(\bar∂χ) u`, whose norm is
at most `‖Dχ‖ ‖v‖ ‖u‖`. -/
theorem norm_conjWirtingerDeriv_smul_sub_smul_le {χ : V → ℝ} {u : V → W} {x : V}
    (hχ : DifferentiableAt ℝ χ x) (hu : DifferentiableAt ℝ u x) (v : V) :
    ‖conjWirtingerDeriv (fun y ↦ χ y • u y) x v - χ x • conjWirtingerDeriv u x v‖ ≤
      ‖fderiv ℝ χ x‖ * ‖v‖ * ‖u x‖ := by
  simp_rw [← Complex.coe_smul]
  rw [conjWirtingerDeriv_smul_apply hχ.ofReal_comp hu, add_sub_cancel_left,
    norm_smul]
  gcongr
  exact (norm_conjWirtingerDeriv_apply_le _ _ _).trans
    (by gcongr; exact norm_fderiv_ofReal_comp_le χ x)

/-- The conjugate Wirtinger derivative depends complex-linearly on the real derivative: if
`Df(x) = ∑ cᵢ Dgᵢ(x)` with complex coefficients, then `\bar∂f(x) = ∑ cᵢ \bar∂gᵢ(x)`. -/
theorem conjWirtingerDeriv_eq_sum_smul {f : V → W} {x : V} {ι : Type*} {s : Finset ι}
    {c : ι → ℂ} {g : ι → V → W} (h : fderiv ℝ f x = ∑ i ∈ s, c i • fderiv ℝ (g i) x) :
    conjWirtingerDeriv f x = ∑ i ∈ s, c i • conjWirtingerDeriv (g i) x := by
  ext v
  simp only [conjWirtingerDeriv_apply, h, sum_apply, smul_apply, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  module

/-- The conjugate Wirtinger derivative of a finite sum of real-differentiable functions is the sum
of their conjugate Wirtinger derivatives. -/
theorem conjWirtingerDeriv_fun_sum {ι : Type*} {s : Finset ι} {g : ι → V → W} {x : V}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (g i) x) :
    conjWirtingerDeriv (fun y ↦ ∑ i ∈ s, g i y) x = ∑ i ∈ s, conjWirtingerDeriv (g i) x := by
  simpa using conjWirtingerDeriv_eq_sum_smul (c := fun _ ↦ (1 : ℂ)) (g := g)
    ((fderiv_fun_sum h).trans (by simp))

/-- **The chain rule for the conjugate Wirtinger derivative** after a holomorphic map: if `φ` is
complex differentiable at `g x`, then `\bar∂(φ ∘ g) = Dφ(g x) ∘ \bar∂g`. -/
theorem conjWirtingerDeriv_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {φ : W → X} {g : V → W} {x : V} (hφ : DifferentiableAt ℂ φ (g x))
    (hg : DifferentiableAt ℝ g x) :
    conjWirtingerDeriv (φ ∘ g) x = (fderiv ℂ φ (g x)).comp (conjWirtingerDeriv g x) := by
  rw [conjWirtingerDeriv_eq_complexAntilinearPart, conjWirtingerDeriv_eq_complexAntilinearPart,
    fderiv_comp x (hφ.restrictScalars ℝ) hg, hφ.fderiv_restrictScalars ℝ,
    ContinuousLinearMap.complexAntilinearPart_restrictScalars_comp]

/-- **The chain rule for the conjugate Wirtinger derivative** before a complex-linear change of
variables: `\bar∂(g ∘ e) = \bar∂g(e x) ∘ e`. No differentiability is needed, since `e` is an
isomorphism. -/
theorem conjWirtingerDeriv_comp_continuousLinearEquiv {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] (e : X ≃L[ℂ] V) (g : V → W) (x : X) :
    conjWirtingerDeriv (g ∘ e) x = (conjWirtingerDeriv g (e x)).comp (e : X →L[ℂ] V) := by
  have h := (e.restrictScalars' ℝ).comp_right_fderiv (f := g) (x := x)
  rw [ContinuousLinearEquiv.coe_restrictScalars'] at h
  rw [conjWirtingerDeriv_eq_complexAntilinearPart, conjWirtingerDeriv_eq_complexAntilinearPart, h,
    ← ContinuousLinearMap.complexAntilinearPart_comp_restrictScalars]
  -- The real map underlying `e.restrictScalars' ℝ` is `e` with scalars restricted.
  congr 2
  ext
  simp

/-- **The chain rule for the conjugate Wirtinger derivative** before a holomorphic map: if `g` is
complex differentiable at `x`, then `\bar∂(φ ∘ g) = \bar∂φ(g x) ∘ Dg(x)`. -/
theorem conjWirtingerDeriv_comp_eq_comp_fderiv {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {φ : W → X} {g : V → W} {x : V} (hφ : DifferentiableAt ℝ φ (g x))
    (hg : DifferentiableAt ℂ g x) :
    conjWirtingerDeriv (φ ∘ g) x = (conjWirtingerDeriv φ (g x)).comp (fderiv ℂ g x) := by
  rw [conjWirtingerDeriv_eq_complexAntilinearPart, conjWirtingerDeriv_eq_complexAntilinearPart,
    fderiv_comp x hφ (hg.restrictScalars ℝ), hg.fderiv_restrictScalars ℝ,
    ContinuousLinearMap.complexAntilinearPart_comp_restrictScalars]

/-- **The chain rule for the conjugate Wirtinger derivative** before a holomorphic function of one
variable: if `g` has complex derivative `a` at `x`, then `\bar∂(φ ∘ g)(x) = \bar a \bar∂φ(g x)`. -/
theorem conjWirtingerDeriv_comp_eq_conj_smul {φ : ℂ → W} {g : ℂ → ℂ} {x a : ℂ}
    (hφ : DifferentiableAt ℝ φ (g x)) (hg : HasDerivAt g a x) :
    conjWirtingerDeriv (φ ∘ g) x = conj a • conjWirtingerDeriv φ (g x) := by
  ext v
  rw [conjWirtingerDeriv_comp_eq_comp_fderiv hφ hg.differentiableAt, hg.hasFDerivAt.fderiv]
  simpa [mul_comm] using map_smulₛₗ (conjWirtingerDeriv φ (g x)) a v

/-- **The chain rule for the conjugate Wirtinger derivative** after a continuous complex-linear
map: `\bar∂(L ∘ g) = L ∘ \bar∂g`. -/
theorem _root_.ContinuousLinearMap.conjWirtingerDeriv_comp_left {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] (L : W →L[ℂ] X) {g : V → W} {x : V} (hg : DifferentiableAt ℝ g x) :
    conjWirtingerDeriv (fun y ↦ L (g y)) x = L.comp (conjWirtingerDeriv g x) := by
  rw [← Function.comp_def, TauCeti.conjWirtingerDeriv_comp L.differentiableAt hg, L.fderiv]

/-- **The chain rule for the conjugate Wirtinger derivative** after a complex-linear isomorphism,
for a map `u` into a complex normed space `X` whose real structure is any one compatible with the
complex structure: `\bar∂(e ∘ u)(x) v = e ((Du(x))^{0,1} v)`, where `(Du(x))^{0,1}` is the
complex-antilinear part `ContinuousLinearMap.complexAntilinearPartL` of the real derivative. No
differentiability is needed, since `e` is an isomorphism. -/
theorem _root_.ContinuousLinearEquiv.conjWirtingerDeriv_comp_left_apply {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X] [IsScalarTower ℝ ℂ X]
    (e : X ≃L[ℂ] W) (u : V → X) (x v : V) :
    conjWirtingerDeriv (fun y ↦ e (u y)) x v =
      e (ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ u x) v) := by
  have h := (e.restrictScalars' ℝ).comp_fderiv (f := u) (x := x)
  rw [ContinuousLinearEquiv.coe_restrictScalars', Function.comp_def] at h
  rw [conjWirtingerDeriv_apply, h, ContinuousLinearMap.complexAntilinearPartL_apply_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ) (E := X), e.map_smul, e.map_add, e.map_smul]
  simp [ContinuousLinearEquiv.coe_restrictScalars']

section Mul

variable {f g : V → ℂ} {x : V}

/-- The **Leibniz rule** for the conjugate Wirtinger derivative:
`\bar∂(f g) = f \bar∂g + g \bar∂f`. -/
theorem conjWirtingerDeriv_fun_mul (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    conjWirtingerDeriv (fun y ↦ f y * g y) x =
      f x • conjWirtingerDeriv g x + g x • conjWirtingerDeriv f x := by
  ext v
  simp only [conjWirtingerDeriv_apply, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul]
  ring

/-- The conjugate Wirtinger derivative of a power: `\bar∂(fⁿ) = n f^(n-1) \bar∂f`. -/
theorem conjWirtingerDeriv_fun_pow (hf : DifferentiableAt ℝ f x) (n : ℕ) :
    conjWirtingerDeriv (fun y ↦ f y ^ n) x = (n * f x ^ (n - 1)) • conjWirtingerDeriv f x := by
  ext v
  simp only [conjWirtingerDeriv_apply, fderiv_fun_pow n hf, nsmul_eq_mul, smul_apply,
    smul_eq_mul]
  ring

/-- **The Leibniz rule for a finite product**:
`\bar∂ (∏_{i ∈ s} f i) = ∑_{i ∈ s} (∏_{j ∈ s ∖ i} f j) \bar∂ (f i)`. -/
theorem conjWirtingerDeriv_finsetProd {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → V → ℂ} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    conjWirtingerDeriv (fun y ↦ ∏ i ∈ s, f i y) x =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j x) • conjWirtingerDeriv (f i) x :=
  conjWirtingerDeriv_eq_sum_smul (fderiv_finsetProd hf)

/-- **Logarithmic derivative bound for a finite product.** If every factor satisfies
`‖\bar∂ (f i)(x)‖ ≤ K |f i (x)|`, then the product satisfies
`‖\bar∂ (∏ f i)(x)‖ ≤ #s K |∏ f i (x)|`. -/
theorem norm_conjWirtingerDeriv_finsetProd_le {ι : Type*} {s : Finset ι} {f : ι → V → ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) {K : ℝ}
    (hK : ∀ i ∈ s, ‖conjWirtingerDeriv (f i) x‖ ≤ K * ‖f i x‖) :
    ‖conjWirtingerDeriv (fun y ↦ ∏ i ∈ s, f i y) x‖ ≤ (s.card * K) * ‖∏ i ∈ s, f i x‖ := by
  classical
  rw [conjWirtingerDeriv_finsetProd hf]
  calc ‖∑ i ∈ s, (∏ j ∈ s.erase i, f j x) • conjWirtingerDeriv (f i) x‖
      ≤ ∑ i ∈ s, ‖(∏ j ∈ s.erase i, f j x) • conjWirtingerDeriv (f i) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, K * ‖∏ i ∈ s, f i x‖ := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [norm_smul, ← Finset.prod_erase_mul s (fun j ↦ f j x) hi, norm_mul]
      calc ‖∏ j ∈ s.erase i, f j x‖ * ‖conjWirtingerDeriv (f i) x‖
          ≤ ‖∏ j ∈ s.erase i, f j x‖ * (K * ‖f i x‖) := by gcongr; exact hK i hi
        _ = K * (‖∏ j ∈ s.erase i, f j x‖ * ‖f i x‖) := by ring
    _ = (s.card * K) * ‖∏ i ∈ s, f i x‖ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

end Mul

/-- In one variable the Wirtinger derivative is determined by its value at `1`. -/
theorem wirtingerDeriv_apply_eq_smul_apply_one {f : ℂ → W} (x v : ℂ) :
    wirtingerDeriv f x v = v • wirtingerDeriv f x 1 := by
  simpa only [smul_eq_mul, mul_one] using (wirtingerDeriv f x).map_smul v (1 : ℂ)

/-- In one variable the conjugate Wirtinger derivative is determined by its value at `1`
through complex-antilinearity. -/
theorem conjWirtingerDeriv_apply_eq_conj_smul_apply_one {f : ℂ → W} (x v : ℂ) :
    conjWirtingerDeriv f x v = conj v • conjWirtingerDeriv f x 1 := by
  simpa only [smul_eq_mul, mul_one] using (conjWirtingerDeriv f x).map_smulₛₗ v (1 : ℂ)

/-- In one variable the real differential is the sum of its `dz` and `dbar z` terms.
This identity also holds for the totalized derivative, without a differentiability assumption. -/
theorem fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv {f : ℂ → W} (x v : ℂ) :
    fderiv ℝ f x v =
      v • wirtingerDeriv f x 1 + conj v • conjWirtingerDeriv f x 1 := by
  rw [← wirtingerDeriv_add_conjWirtingerDeriv f x v,
    wirtingerDeriv_apply_eq_smul_apply_one, conjWirtingerDeriv_apply_eq_conj_smul_apply_one]

/-- In one variable, for any two directions `ω₁`, `ω₂`,
`2 i Im (conj ω₁ ω₂) \bar∂f(x) = ω₂ Df(x) ω₁ - ω₁ Df(x) ω₂`. -/
theorem smul_conjWirtingerDeriv_apply_one_eq_sub (f : ℂ → W) (ω₁ ω₂ x : ℂ) :
    (2 * I * (conj ω₁ * ω₂).im : ℂ) • conjWirtingerDeriv f x 1 =
      ω₂ • fderiv ℝ f x ω₁ - ω₁ • fderiv ℝ f x ω₂ := by
  rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv,
    fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv, two_mul_I_mul_im_conj_mul]
  module

/-- In one variable, for any two directions `ω₁`, `ω₂`,
`2 i Im (conj ω₁ ω₂) ∂f(x) = conj ω₁ Df(x) ω₂ - conj ω₂ Df(x) ω₁`. -/
theorem smul_wirtingerDeriv_apply_one_eq_sub (f : ℂ → W) (ω₁ ω₂ x : ℂ) :
    (2 * I * (conj ω₁ * ω₂).im : ℂ) • wirtingerDeriv f x 1 =
      conj ω₁ • fderiv ℝ f x ω₂ - conj ω₂ • fderiv ℝ f x ω₁ := by
  rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv,
    fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv, two_mul_I_mul_im_conj_mul]
  module

/-- In one variable, `\bar∂f` is determined by the real derivatives along two `ℝ`-linearly
independent directions `ω₁`, `ω₂`:
`\bar∂f(x) = (2 i Im (conj ω₁ ω₂))⁻¹ (ω₂ Df(x) ω₁ - ω₁ Df(x) ω₂)`. -/
theorem conjWirtingerDeriv_apply_one_eq_inv_smul_sub {f : ℂ → W} {ω₁ ω₂ : ℂ}
    (hω : (conj ω₁ * ω₂).im ≠ 0) (x : ℂ) :
    conjWirtingerDeriv f x 1 = (2 * I * (conj ω₁ * ω₂).im : ℂ)⁻¹ •
      (ω₂ • fderiv ℝ f x ω₁ - ω₁ • fderiv ℝ f x ω₂) := by
  have hne : (2 * I * (conj ω₁ * ω₂).im : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (mod_cast hω)
  rw [eq_inv_smul_iff₀ hne, smul_conjWirtingerDeriv_apply_one_eq_sub]

/-- In one variable the conjugate Wirtinger derivative vanishes exactly when its value
at `1` vanishes, since it is complex-antilinear. -/
theorem conjWirtingerDeriv_eq_zero_iff_apply_one_eq_zero {f : ℂ → W} {x : ℂ} :
    conjWirtingerDeriv f x = 0 ↔ conjWirtingerDeriv f x 1 = 0 := by
  constructor
  · intro h
    simp only [h, zero_apply]
  · intro h
    ext v
    rw [conjWirtingerDeriv_apply_eq_conj_smul_apply_one, h, smul_zero, zero_apply]

/-- The Wirtinger derivative of the imaginary part: `∂ Im = -i/2`. -/
@[simp]
theorem wirtingerDeriv_apply_one_ofReal_im (z : ℂ) :
    wirtingerDeriv (fun w : ℂ ↦ (w.im : ℂ)) z 1 = -I / 2 := by
  rw [wirtingerDeriv_apply, fderiv_ofReal_im]
  simp [div_eq_inv_mul]

/-- The conjugate Wirtinger derivative of the imaginary part: `\bar∂ Im = i/2`. -/
@[simp]
theorem conjWirtingerDeriv_apply_one_ofReal_im (z : ℂ) :
    conjWirtingerDeriv (fun w : ℂ ↦ (w.im : ℂ)) z 1 = I / 2 := by
  rw [conjWirtingerDeriv_apply, fderiv_ofReal_im]
  simp [div_eq_inv_mul]

/-- **The chain rule for the Wirtinger derivative** after a complex-linear map `L`:
`∂(f ∘ L)(x) = ∂f(L x) ∘ L`. -/
theorem _root_.ContinuousLinearMap.wirtingerDeriv_comp_right {V' : Type*} [NormedAddCommGroup V']
    [NormedSpace ℂ V'] (L : V' →L[ℂ] V) {f : V → W} {x : V'} (hf : DifferentiableAt ℝ f (L x)) :
    wirtingerDeriv (f ∘ L) x = (wirtingerDeriv f (L x)).comp L := by
  have hd : HasFDerivAt (f ∘ L) ((fderiv ℝ f (L x)).comp (L.restrictScalars ℝ)) x :=
    hf.hasFDerivAt.comp x (L.restrictScalars ℝ).hasFDerivAt
  rw [wirtingerDeriv_eq_complexLinearPart, wirtingerDeriv_eq_complexLinearPart, hd.fderiv,
    ContinuousLinearMap.complexLinearPart_comp_restrictScalars]

/-- **The chain rule for the conjugate Wirtinger derivative** after a complex-linear map `L`:
`\bar∂(f ∘ L)(x) = \bar∂f(L x) ∘ L`. -/
theorem _root_.ContinuousLinearMap.conjWirtingerDeriv_comp_right {V' : Type*}
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] (L : V' →L[ℂ] V) {f : V → W} {x : V'}
    (hf : DifferentiableAt ℝ f (L x)) :
    conjWirtingerDeriv (f ∘ L) x = (conjWirtingerDeriv f (L x)).comp L := by
  have hd : HasFDerivAt (f ∘ L) ((fderiv ℝ f (L x)).comp (L.restrictScalars ℝ)) x :=
    hf.hasFDerivAt.comp x (L.restrictScalars ℝ).hasFDerivAt
  rw [conjWirtingerDeriv_eq_complexAntilinearPart, conjWirtingerDeriv_eq_complexAntilinearPart,
    hd.fderiv, ContinuousLinearMap.complexAntilinearPart_comp_restrictScalars]

/-- **The Wirtinger derivative of a rotated or dilated function.** In one variable,
`∂(f(c ·))(z) = c ∂f(c z)`. Like `TauCeti.fderiv_comp_smul_apply`, this needs no
differentiability of `f`. -/
theorem wirtingerDeriv_comp_mul_left (f : ℂ → W) (c z v : ℂ) :
    wirtingerDeriv (fun w ↦ f (c * w)) z v = c • wirtingerDeriv f (c * z) v := by
  have h := fderiv_comp_smul_apply (𝕜 := ℝ) f c z
  simp only [smul_eq_mul] at h
  rw [← map_smul, wirtingerDeriv_apply, wirtingerDeriv_apply, h, h, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, mul_left_comm]

/-- **The conjugate Wirtinger derivative of a rotated or dilated function.** In one variable,
`\bar∂(f(c ·))(z) = conj c \bar∂f(c z)`. Like `TauCeti.fderiv_comp_smul_apply`, this needs no
differentiability of `f`. -/
theorem conjWirtingerDeriv_comp_mul_left (f : ℂ → W) (c z v : ℂ) :
    conjWirtingerDeriv (fun w ↦ f (c * w)) z v = conj c • conjWirtingerDeriv f (c * z) v := by
  have h := fderiv_comp_smul_apply (𝕜 := ℝ) f c z
  simp only [smul_eq_mul] at h
  rw [← map_smulₛₗ, conjWirtingerDeriv_apply, conjWirtingerDeriv_apply, h, h,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-! ### The twisted exponentials `exp (a z - conj a conj z)` -/

section TwistedExp

variable (a : ℂ)

/-- The derivative of the twisted exponential `z ↦ exp (a z - conj a conj z) = exp (2i Im (a z))`,
of modulus one. -/
theorem hasFDerivAt_cexp_mul_sub_conj_mul_conj (z : ℂ) :
    HasFDerivAt (fun z ↦ cexp (a * z - conj a * conj z))
      (cexp (a * z - conj a * conj z) •
        (a • ContinuousLinearMap.id ℝ ℂ - conj a • (conjCLE : ℂ →L[ℝ] ℂ))) z :=
  (((hasFDerivAt_id z).const_mul a).sub
    ((conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.const_mul (conj a))).cexp

/-- The twisted exponential `exp (a z - conj a conj z)` is smooth. -/
theorem contDiff_cexp_mul_sub_conj_mul_conj {n : WithTop ℕ∞} :
    ContDiff ℝ n fun z ↦ cexp (a * z - conj a * conj z) :=
  ((contDiff_const.mul contDiff_id).sub
    (contDiff_const.mul (conjCLE : ℂ →L[ℝ] ℂ).contDiff)).cexp

/-- The twisted exponential `exp (a z - conj a conj z)` is an eigenfunction of `∂` with
eigenvalue `a`. -/
@[simp]
theorem wirtingerDeriv_cexp_mul_sub_conj_mul_conj (z : ℂ) :
    wirtingerDeriv (fun z ↦ cexp (a * z - conj a * conj z)) z 1 =
      a * cexp (a * z - conj a * conj z) := by
  rw [wirtingerDeriv_apply, (hasFDerivAt_cexp_mul_sub_conj_mul_conj a z).fderiv]
  simp only [smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul,
    map_one, mul_one, conj_I]
  linear_combination (-(cexp (a * z - conj a * conj z) * (a + conj a) / 2)) * I_sq

/-- The twisted exponential `exp (a z - conj a conj z)` is an eigenfunction of `\bar∂` with
eigenvalue `-conj a`. -/
@[simp]
theorem conjWirtingerDeriv_cexp_mul_sub_conj_mul_conj (z : ℂ) :
    conjWirtingerDeriv (fun z ↦ cexp (a * z - conj a * conj z)) z 1 =
      -conj a * cexp (a * z - conj a * conj z) := by
  rw [conjWirtingerDeriv_apply, (hasFDerivAt_cexp_mul_sub_conj_mul_conj a z).fderiv]
  simp only [smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, smul_eq_mul,
    map_one, mul_one, conj_I]
  linear_combination (cexp (a * z - conj a * conj z) * (a + conj a) / 2) * I_sq

/-- Under translation by `w`, the twisted exponential `exp (a z - conj a conj z)` is multiplied by
the unit complex number `exp (2i Im (a w))`. -/
theorem cexp_mul_add_sub_conj_mul_conj_add (z w : ℂ) :
    cexp (a * (z + w) - conj a * conj (z + w)) =
      cexp (((2 * (a * w).im : ℝ) : ℂ) * I) * cexp (a * z - conj a * conj z) := by
  rw [← sub_conj, map_mul, ← Complex.exp_add, map_add]
  ring_nf

open scoped Real in
/-- If `Im (a w) = π (k + θ)` for an integer `k`, then under translation by `w` the twisted
exponential `exp (a z - conj a conj z)` is multiplied by `exp (2πiθ)`. In particular it is a
section of the flat line with holonomy `exp (2πiθ)` along `w`. -/
theorem cexp_mul_add_sub_conj_mul_conj_add_of_im_mul_eq {w : ℂ} {θ : ℝ} {k : ℤ}
    (h : (a * w).im = π * (k + θ)) (z : ℂ) :
    cexp (a * (z + w) - conj a * conj (z + w)) =
      cexp (2 * π * θ * I) * cexp (a * z - conj a * conj z) := by
  rw [cexp_mul_add_sub_conj_mul_conj_add, h]
  congr 1
  push_cast
  rw [show (2 * (π * (k + θ)) * I : ℂ) = k * (2 * π * I) + 2 * π * θ * I by ring, Complex.exp_add,
    exp_int_mul_two_pi_mul_I, one_mul]

end TwistedExp

/-! ### Real-linear maps through their Wirtinger parts -/

/-- The continuous real-linear map `(a, b) ↦ (v ↦ v • a + conj v • b)` sending a pair of Wirtinger
parts to the real-linear map of the plane with these parts (`TauCeti.wirtingerPartsCLM`). -/
noncomputable def wirtingerPartsL : W × W →L[ℝ] ℂ →L[ℝ] W :=
  (ContinuousLinearMap.lsmul ℝ ℂ).flip.coprod
    (((ContinuousLinearMap.compL ℝ ℂ ℂ W).flip conjCLE.toContinuousLinearMap).comp
      (ContinuousLinearMap.lsmul ℝ ℂ).flip)

/-- The real-linear map `v ↦ v • a + conj v • b` of the plane into `W`. Its Wirtinger parts are
`a` and `b` (`TauCeti.wirtingerDeriv_wirtingerPartsCLM_apply_one`,
`TauCeti.conjWirtingerDeriv_wirtingerPartsCLM_apply_one`), it determines them
(`TauCeti.wirtingerPartsCLM_inj`), and every real derivative in one variable has this form
(`TauCeti.fderiv_eq_wirtingerPartsCLM`). It is jointly real-linear in `(a, b)`
(`TauCeti.wirtingerPartsL`). -/
noncomputable def wirtingerPartsCLM (a b : W) : ℂ →L[ℝ] W :=
  wirtingerPartsL (a, b)

@[simp]
theorem wirtingerPartsL_apply (ab : W × W) : wirtingerPartsL ab = wirtingerPartsCLM ab.1 ab.2 := by
  rw [wirtingerPartsCLM]

@[simp]
theorem wirtingerPartsCLM_apply (a b : W) (v : ℂ) :
    wirtingerPartsCLM a b v = v • a + conj v • b := by
  simp [wirtingerPartsCLM, wirtingerPartsL]

@[simp]
theorem wirtingerPartsCLM_zero : wirtingerPartsCLM (0 : W) 0 = 0 :=
  map_zero wirtingerPartsL

theorem wirtingerPartsCLM_add (a b a' b' : W) :
    wirtingerPartsCLM (a + a') (b + b') = wirtingerPartsCLM a b + wirtingerPartsCLM a' b' :=
  map_add wirtingerPartsL (a, b) (a', b')

theorem wirtingerPartsCLM_neg (a b : W) :
    wirtingerPartsCLM (-a) (-b) = -wirtingerPartsCLM a b :=
  map_neg wirtingerPartsL (a, b)

theorem wirtingerPartsCLM_sub (a b a' b' : W) :
    wirtingerPartsCLM (a - a') (b - b') = wirtingerPartsCLM a b - wirtingerPartsCLM a' b' :=
  map_sub wirtingerPartsL (a, b) (a', b')

theorem wirtingerPartsCLM_smul {S : Type*} [Monoid S] [DistribMulAction S W]
    [SMulCommClass ℂ S W] [SMulCommClass ℝ S W] [ContinuousConstSMul S W] (s : S) (a b : W) :
    wirtingerPartsCLM (s • a) (s • b) = s • wirtingerPartsCLM a b := by
  ext v
  simp only [wirtingerPartsCLM_apply, smul_apply, smul_add, smul_comm v s, smul_comm (conj v) s]

/-- `x ↦ wirtingerPartsCLM (a x) (b x)` is continuous when both parts are. -/
theorem _root_.Continuous.wirtingerPartsCLM {X : Type*} [TopologicalSpace X] {a b : X → W}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x ↦ wirtingerPartsCLM (a x) (b x) :=
  wirtingerPartsL.continuous.comp (ha.prodMk hb)

/-- The operator norm of `v ↦ v • a + conj v • b` is at most `‖a‖ + ‖b‖`. -/
theorem norm_wirtingerPartsCLM_le (a b : W) : ‖wirtingerPartsCLM a b‖ ≤ ‖a‖ + ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [wirtingerPartsCLM_apply]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_smul, norm_smul, Complex.norm_conj]
  ring

/-- The two Wirtinger parts are determined by the real-linear map. -/
@[simp]
theorem wirtingerPartsCLM_inj {a b a' b' : W} :
    wirtingerPartsCLM a b = wirtingerPartsCLM a' b' ↔ a = a' ∧ b = b' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.1 ▸ h.2 ▸ rfl⟩
  have h1 := congrArg (· 1) h
  have hI := congrArg (· I) h
  simp only [wirtingerPartsCLM_apply, map_one, one_smul, conj_I, neg_smul] at h1 hI
  have hI' : a - b = a' - b' := by
    have := congrArg ((-I) • ·) hI
    simp only [smul_add, smul_neg, smul_smul, neg_mul, I_mul_I, neg_neg, one_smul] at this
    simpa only [sub_eq_add_neg] using this
  constructor
  · have h2 : (2 : ℂ) • a = (2 : ℂ) • a' := by
      rw [two_smul, two_smul]
      linear_combination (norm := module) h1 + hI'
    exact smul_right_injective W two_ne_zero h2
  · have h2 : (2 : ℂ) • b = (2 : ℂ) • b' := by
      rw [two_smul, two_smul]
      linear_combination (norm := module) h1 - hI'
    exact smul_right_injective W two_ne_zero h2

/-- In one variable the real derivative is the real-linear map with its two Wirtinger parts. -/
theorem fderiv_eq_wirtingerPartsCLM (f : ℂ → W) (x : ℂ) :
    fderiv ℝ f x = wirtingerPartsCLM (wirtingerDeriv f x 1) (conjWirtingerDeriv f x 1) := by
  ext v
  rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv, wirtingerPartsCLM_apply]

/-- Every real-linear map `D : ℂ →L[ℝ] W` is `v ↦ v • a + conj v • b` for some `a b : W`. -/
theorem exists_eq_wirtingerPartsCLM (D : ℂ →L[ℝ] W) : ∃ a b : W, D = wirtingerPartsCLM a b :=
  ⟨_, _, by simpa only [ContinuousLinearMap.fderiv] using fderiv_eq_wirtingerPartsCLM D 0⟩

/-- The map `v ↦ v • c` is the real-linear map with Wirtinger parts `c` and `0`. -/
theorem smulRight_id_eq_wirtingerPartsCLM (c : W) :
    (ContinuousLinearMap.id ℝ ℂ).smulRight c = wirtingerPartsCLM c 0 := by
  ext v
  simp

/-- The map `v ↦ conj v • c` is the real-linear map with Wirtinger parts `0` and `c`. -/
theorem smulRight_conjCLE_eq_wirtingerPartsCLM (c : W) :
    conjCLE.toContinuousLinearMap.smulRight c = wirtingerPartsCLM 0 c := by
  ext v
  simp

/-- In one variable the real derivative is controlled by its two Wirtinger parts:
`‖Df(x)‖ ≤ ‖∂f(x)‖ + ‖bar∂f(x)‖`. -/
theorem norm_fderiv_le_norm_wirtingerDeriv_add_norm_conjWirtingerDeriv (f : ℂ → W) (x : ℂ) :
    ‖fderiv ℝ f x‖ ≤ ‖wirtingerDeriv f x 1‖ + ‖conjWirtingerDeriv f x 1‖ := by
  rw [fderiv_eq_wirtingerPartsCLM]
  exact norm_wirtingerPartsCLM_le _ _

/-- The complex-linear Wirtinger part of `v ↦ v • a + conj v • b` is `a`. -/
@[simp]
theorem wirtingerDeriv_wirtingerPartsCLM_apply_one (a b : W) (x : ℂ) :
    wirtingerDeriv (wirtingerPartsCLM a b) x 1 = a := by
  have h := fderiv_eq_wirtingerPartsCLM (wirtingerPartsCLM a b) x
  rw [ContinuousLinearMap.fderiv] at h
  exact (wirtingerPartsCLM_inj.1 h).1.symm

/-- The complex-antilinear Wirtinger part of `v ↦ v • a + conj v • b` is `b`. -/
@[simp]
theorem conjWirtingerDeriv_wirtingerPartsCLM_apply_one (a b : W) (x : ℂ) :
    conjWirtingerDeriv (wirtingerPartsCLM a b) x 1 = b := by
  have h := fderiv_eq_wirtingerPartsCLM (wirtingerPartsCLM a b) x
  rw [ContinuousLinearMap.fderiv] at h
  exact (wirtingerPartsCLM_inj.1 h).2.symm

/-! ### Second Wirtinger derivatives -/

/-- A conjugate Wirtinger derivative of a `C^{m+1}` map on an open set is `C^m` there. -/
theorem _root_.ContDiffOn.conjWirtingerDeriv_apply_of_isOpen {g : V → W} {s : Set V}
    {m n : WithTop ℕ∞} (hg : ContDiffOn ℝ n g s) (hs : IsOpen s) (hmn : m + 1 ≤ n) (v : V) :
    ContDiffOn ℝ m (fun y ↦ conjWirtingerDeriv g y v) s :=
  fun _ hy ↦ ((hg.contDiffAt (hs.mem_nhds hy)).conjWirtingerDeriv_apply hmn v).contDiffWithinAt

/-- A Wirtinger derivative of a `C^{m+1}` map on an open set is `C^m` there. -/
theorem _root_.ContDiffOn.wirtingerDeriv_apply_of_isOpen {g : V → W} {s : Set V}
    {m n : WithTop ℕ∞} (hg : ContDiffOn ℝ n g s) (hs : IsOpen s) (hmn : m + 1 ≤ n) (v : V) :
    ContDiffOn ℝ m (fun y ↦ wirtingerDeriv g y v) s :=
  fun _ hy ↦ ((hg.contDiffAt (hs.mem_nhds hy)).wirtingerDeriv_apply hmn v).contDiffWithinAt

/-- For a `C²` map, the conjugate Wirtinger derivative `y ↦ \bar∂g(y) u` in a fixed direction `u`
is differentiable, with derivative built from the second derivative of `g`. -/
theorem _root_.ContDiffAt.hasFDerivAt_conjWirtingerDeriv_apply {g : V → W} {x : V}
    (hg : ContDiffAt ℝ 2 g x) (u : V) :
    HasFDerivAt (fun y ↦ conjWirtingerDeriv g y u)
      ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ g) x).flip u +
        I • (fderiv ℝ (fderiv ℝ g) x).flip (I • u))) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  refine (((hD.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).add
    ((hD.hasFDerivAt.clm_apply (hasFDerivAt_const (I • u) x)).const_smul I)).const_smul
      (2 : ℂ)⁻¹).congr_of_eventuallyEq
        (.of_forall fun y ↦ conjWirtingerDeriv_apply _ y u) |>.congr_fderiv ?_
  ext a
  simp

/-- For a `C²` map, the Wirtinger derivative `y ↦ ∂g(y) u` in a fixed direction `u` is
differentiable, with derivative built from the second derivative of `g`. -/
theorem _root_.ContDiffAt.hasFDerivAt_wirtingerDeriv_apply {g : V → W} {x : V}
    (hg : ContDiffAt ℝ 2 g x) (u : V) :
    HasFDerivAt (fun y ↦ wirtingerDeriv g y u)
      ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ g) x).flip u -
        I • (fderiv ℝ (fderiv ℝ g) x).flip (I • u))) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  refine (((hD.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).sub
    ((hD.hasFDerivAt.clm_apply (hasFDerivAt_const (I • u) x)).const_smul I)).const_smul
      (2 : ℂ)⁻¹).congr_of_eventuallyEq
        (.of_forall fun y ↦ wirtingerDeriv_apply _ y u) |>.congr_fderiv ?_
  ext a
  simp

/-- **The Laplacian in Wirtinger form.** For a `C²` map, `\bar∂_v ∂_v g` is a quarter of the sum
of the second real derivatives of `g` along `v` and along `I • v`. On a coordinate vector `e_j`
of `z_j = x_j + I y_j` this is `∂²g / ∂(conj z_j) ∂z_j = (∂²g / ∂x_j² + ∂²g / ∂y_j²) / 4`. -/
theorem conjWirtingerDeriv_wirtingerDeriv_self {g : V → W} {x : V} (hg : ContDiffAt ℝ 2 g x)
    (v : V) :
    conjWirtingerDeriv (fun y ↦ wirtingerDeriv g y v) x v =
      (4 : ℂ)⁻¹ • (iteratedFDeriv ℝ 2 g x ![v, v] + iteratedFDeriv ℝ 2 g x ![I • v, I • v]) := by
  have hsymm := hg.isSymmSndFDerivAt (by simp)
  rw [conjWirtingerDeriv_apply, (hg.hasFDerivAt_wirtingerDeriv_apply v).fderiv,
    iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp only [smul_apply, sub_apply, ContinuousLinearMap.flip_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, hsymm v (I • v)]
  match_scalars
  · ring
  · ring
  · linear_combination (-4⁻¹ : ℂ) * I_mul_I

/-- **Mixed Wirtinger derivatives commute.** For a `C²` map, `∂_w \bar∂_v g = \bar∂_v ∂_w g`; on
coordinate vectors this is `∂²g / ∂z_k ∂(conj z_j) = ∂²g / ∂(conj z_j) ∂z_k`. -/
theorem wirtingerDeriv_conjWirtingerDeriv_comm {g : V → W} {x : V}
    (hg : ContDiffAt ℝ 2 g x) (v w : V) :
    wirtingerDeriv (fun y ↦ conjWirtingerDeriv g y v) x w =
      conjWirtingerDeriv (fun y ↦ wirtingerDeriv g y w) x v := by
  have hsymm := hg.isSymmSndFDerivAt (by simp)
  rw [wirtingerDeriv_apply, conjWirtingerDeriv_apply,
    (hg.hasFDerivAt_conjWirtingerDeriv_apply v).fderiv,
    (hg.hasFDerivAt_wirtingerDeriv_apply w).fderiv]
  simp only [smul_apply, add_apply, sub_apply, ContinuousLinearMap.flip_apply, hsymm w v,
    hsymm (I • w) v, hsymm w (I • v), hsymm (I • w) (I • v)]
  module

/-- For a `C²` map, `∂_v \bar∂_v g` is also a quarter of the sum of the second real derivatives
of `g` along `v` and along `I • v`. -/
theorem wirtingerDeriv_conjWirtingerDeriv_self {g : V → W} {x : V} (hg : ContDiffAt ℝ 2 g x)
    (v : V) :
    wirtingerDeriv (fun y ↦ conjWirtingerDeriv g y v) x v =
      (4 : ℂ)⁻¹ • (iteratedFDeriv ℝ 2 g x ![v, v] + iteratedFDeriv ℝ 2 g x ![I • v, I • v]) :=
  (wirtingerDeriv_conjWirtingerDeriv_comm hg v v).trans
    (conjWirtingerDeriv_wirtingerDeriv_self hg v)

/-- **Symmetry of second Wirtinger derivatives.** For a `C²` map, `∂_w ∂_v g = ∂_v ∂_w g`; on
coordinate vectors this is `∂²g / ∂z_j ∂z_k = ∂²g / ∂z_k ∂z_j`. -/
theorem wirtingerDeriv_wirtingerDeriv_comm {g : V → W} {x : V}
    (hg : ContDiffAt ℝ 2 g x) (v w : V) :
    wirtingerDeriv (fun y ↦ wirtingerDeriv g y v) x w =
      wirtingerDeriv (fun y ↦ wirtingerDeriv g y w) x v := by
  have hsymm := hg.isSymmSndFDerivAt (by simp)
  rw [wirtingerDeriv_apply, wirtingerDeriv_apply,
    (hg.hasFDerivAt_wirtingerDeriv_apply v).fderiv,
    (hg.hasFDerivAt_wirtingerDeriv_apply w).fderiv]
  simp only [smul_apply, sub_apply, ContinuousLinearMap.flip_apply, hsymm w v, hsymm (I • w) v,
    hsymm w (I • v), hsymm (I • w) (I • v)]
  module

/-- **Symmetry of second conjugate Wirtinger derivatives.** For a `C²` map,
`\bar∂_w \bar∂_v g = \bar∂_v \bar∂_w g`; on coordinate vectors this is
`∂²g / ∂(conj z_j) ∂(conj z_k) = ∂²g / ∂(conj z_k) ∂(conj z_j)`. -/
theorem conjWirtingerDeriv_conjWirtingerDeriv_comm {g : V → W} {x : V}
    (hg : ContDiffAt ℝ 2 g x) (v w : V) :
    conjWirtingerDeriv (fun y ↦ conjWirtingerDeriv g y v) x w =
      conjWirtingerDeriv (fun y ↦ conjWirtingerDeriv g y w) x v := by
  have hsymm := hg.isSymmSndFDerivAt (by simp)
  rw [conjWirtingerDeriv_apply, conjWirtingerDeriv_apply,
    (hg.hasFDerivAt_conjWirtingerDeriv_apply v).fderiv,
    (hg.hasFDerivAt_conjWirtingerDeriv_apply w).fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply, hsymm w v, hsymm (I • w) v,
    hsymm w (I • v), hsymm (I • w) (I • v)]
  module

end TauCeti
