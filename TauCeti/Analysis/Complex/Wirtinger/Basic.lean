/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Analysis.Calculus.FDeriv.OfReal
import TauCeti.Analysis.Normed.Module.RCLike.Basic
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
* `TauCeti.norm_wirtingerDeriv_apply_le`, `TauCeti.norm_conjWirtingerDeriv_apply_le`: both
  Wirtinger derivatives are bounded by the real derivative, `‖∂g(x) v‖ ≤ ‖Dg(x)‖ ‖v‖`.
* `TauCeti.coe_wirtingerDeriv_eq_complexLinearPart`,
  `TauCeti.coe_conjWirtingerDeriv_eq_complexAntilinearPart`: the Wirtinger derivatives are the
  complex-linear and complex-antilinear parts of the real derivative.
* `TauCeti.conjWirtingerDeriv_ofReal_comp_apply`: for real-valued `f`, `\bar∂f = conj ∂f`.
* `TauCeti.wirtingerDeriv_smul_apply`, `TauCeti.conjWirtingerDeriv_smul_apply`: the product rules
  `∂(c g) = c ∂g + (∂c) g` and `\bar∂(c g) = c \bar∂g + (\bar∂c) g` for a complex-valued factor `c`.
* `TauCeti.norm_wirtingerDeriv_smul_sub_smul_le`,
  `TauCeti.norm_conjWirtingerDeriv_smul_sub_smul_le`: for a real factor `χ`,
  `‖∂(χ u)(x) v - χ ∂u(x) v‖ ≤ ‖Dχ(x)‖ ‖v‖ ‖u(x)‖`, and likewise for `\bar∂`.
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

end TauCeti
