/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import TauCeti.LinearAlgebra.Complex.Module

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

## Main results

* `TauCeti.wirtingerDeriv_add_conjWirtingerDeriv`: `∂g + \bar∂g = Dg`.
* `TauCeti.coe_wirtingerDeriv_eq_complexLinearPart`,
  `TauCeti.coe_conjWirtingerDeriv_eq_complexAntilinearPart`: the Wirtinger derivatives are the
  complex-linear and complex-antilinear parts of the real derivative.
* `TauCeti.conjWirtingerDeriv_ofReal_comp_apply`: for real-valued `f`, `\bar∂f = conj ∂f`.
* `DifferentiableAt.conjWirtingerDeriv_eq_zero`, `DifferentiableAt.wirtingerDeriv_eq_fderiv`:
  for complex differentiable `g`, `\bar∂g = 0` and `∂g` is the complex derivative.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*.
* L. Hörmander, *An introduction to complex analysis in several variables*, Chapter II.
-/

public section

open Complex ComplexConjugate

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

section Wirtinger

variable (g : V → W) (x : V)

/-- The **Wirtinger derivative** `∂g(x)` of a function into a complex normed space: the
complex-linear part `v ↦ (Dg(x) v - I • Dg(x)(I • v)) / 2` of its real derivative. On a coordinate
vector `e_j` it is `∂g / ∂z_j`. -/
noncomputable def wirtingerDeriv : V →L[ℂ] W where
  toFun v := (2 : ℂ)⁻¹ • (fderiv ℝ g x v - I • fderiv ℝ g x (I • v))
  map_add' v w := by simp only [smul_add, map_add]; module
  map_smul' c v := by
    -- Split `c • v` into real multiples of `v` and `I • v`.
    rw [← re_smul_add_im_smul c v]
    simp only [smul_add, smul_comm I, smul_smul, I_mul_I, neg_smul, one_smul, map_add,
      map_smul, map_neg, RingHom.id_apply]
    match_scalars <;> apply Complex.ext <;> simp <;> ring
  cont := by fun_prop

/-- The **conjugate Wirtinger derivative** `\bar∂g(x)` of a function into a complex normed space:
the complex-antilinear part `v ↦ (Dg(x) v + I • Dg(x)(I • v)) / 2` of its real derivative. On a
coordinate vector `e_j` it is `∂g / ∂(conj z_j)`. -/
noncomputable def conjWirtingerDeriv : V →L⋆[ℂ] W where
  toFun v := (2 : ℂ)⁻¹ • (fderiv ℝ g x v + I • fderiv ℝ g x (I • v))
  map_add' v w := by simp only [smul_add, map_add]; module
  map_smul' c v := by
    rw [← re_smul_add_im_smul c v]
    simp only [smul_add, smul_comm I, smul_smul, I_mul_I, neg_smul, one_smul, map_add,
      map_smul, map_neg, starRingEnd_apply]
    match_scalars <;> apply Complex.ext <;> simp <;> ring
  cont := by fun_prop

/-- The defining formula of the Wirtinger derivative. -/
theorem wirtingerDeriv_apply (v : V) :
    wirtingerDeriv g x v = (2 : ℂ)⁻¹ • (fderiv ℝ g x v - I • fderiv ℝ g x (I • v)) :=
  (rfl)

/-- The defining formula of the conjugate Wirtinger derivative. -/
theorem conjWirtingerDeriv_apply (v : V) :
    conjWirtingerDeriv g x v = (2 : ℂ)⁻¹ • (fderiv ℝ g x v + I • fderiv ℝ g x (I • v)) :=
  (rfl)

/-- The two Wirtinger derivatives add up to the real derivative. -/
@[simp]
theorem wirtingerDeriv_add_conjWirtingerDeriv (v : V) :
    wirtingerDeriv g x v + conjWirtingerDeriv g x v = fderiv ℝ g x v := by
  rw [wirtingerDeriv_apply, conjWirtingerDeriv_apply]
  module

/-- The Wirtinger derivative is the complex-linear part `TauCeti.complexLinearPart` of the real
derivative, for the complex structures given by multiplication by `I`. -/
theorem coe_wirtingerDeriv_eq_complexLinearPart :
    ⇑(wirtingerDeriv g x) =
      complexLinearPart (DistribSMul.toLinearMap ℝ V I) (DistribSMul.toLinearMap ℝ W I)
        (fderiv ℝ g x : V →ₗ[ℝ] W) := by
  ext v
  simp only [wirtingerDeriv_apply, complexLinearPart_apply, ContinuousLinearMap.coe_coe,
    DistribSMul.toLinearMap_apply]
  module

/-- The conjugate Wirtinger derivative is the complex-antilinear part
`TauCeti.complexAntilinearPart` of the real derivative, for the complex structures given by
multiplication by `I`. -/
theorem coe_conjWirtingerDeriv_eq_complexAntilinearPart :
    ⇑(conjWirtingerDeriv g x) =
      complexAntilinearPart (DistribSMul.toLinearMap ℝ V I)
        (DistribSMul.toLinearMap ℝ W I) (fderiv ℝ g x : V →ₗ[ℝ] W) := by
  ext v
  simp only [conjWirtingerDeriv_apply, complexAntilinearPart_apply, ContinuousLinearMap.coe_coe,
    DistribSMul.toLinearMap_apply]
  module

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

/-- For a real function, the conjugate Wirtinger derivative is the complex conjugate of the
Wirtinger derivative. -/
theorem conjWirtingerDeriv_ofReal_comp_apply (f : V → ℝ) (x v : V) :
    conjWirtingerDeriv (fun y ↦ (f y : ℂ)) x v = conj (wirtingerDeriv (fun y ↦ (f y : ℂ)) x v) := by
  apply Complex.ext <;>
  simp [conjWirtingerDeriv_apply, wirtingerDeriv_apply]

end Wirtinger

end TauCeti
