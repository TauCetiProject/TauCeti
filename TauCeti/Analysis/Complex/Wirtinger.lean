/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.Analysis.Complex.LeviForm
public import TauCeti.LinearAlgebra.Complex.LinearPart
import TauCeti.Analysis.Calculus.FDeriv.OfReal

/-!
# Wirtinger derivatives and the Levi form

For a function `g : V → W` between complex normed spaces, the **Wirtinger derivatives** of `g`
at `x` are the complex-linear and complex-antilinear parts of its real derivative:

`∂g(x) v = (Dg(x) v - I • Dg(x)(I • v)) / 2`,  `\bar∂g(x) v = (Dg(x) v + I • Dg(x)(I • v)) / 2`.

In holomorphic coordinates `z_j = x_j + I y_j` with coordinate vectors `e_j`, these are the
classical operators `∂g(x) e_j = ∂g/∂z_j = (∂g/∂x_j - I ∂g/∂y_j) / 2` and
`\bar∂g(x) e_j = ∂g/∂(conj z_j) = (∂g/∂x_j + I ∂g/∂y_j) / 2`.

The Levi form `TauCeti.leviForm f x` of a real function `f` is defined from the real second
derivative. The main results of this file compare it with the second Wirtinger derivatives: for
`C²` real `f`, the mixed Wirtinger derivative `∂²f / ∂z_j ∂(conj z_k)`, taken in either order, is
the Levi form entry `leviForm f x (e_k) (e_j)`. Consequently, in any complex basis `e` of `V`, the
Hermitian form with matrix `L_{j \bar k} = ∂²f / ∂z_j ∂(conj z_k)` evaluated at the coordinates
`ξ_j = dz_j(v)` of a real tangent vector `v` is one quarter of the real second-derivative sum
`D²f(x)(v, v) + D²f(x)(I • v, I • v)`.

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
* `TauCeti.wirtingerDeriv_conjWirtingerDeriv_eq_leviForm`,
  `TauCeti.conjWirtingerDeriv_wirtingerDeriv_eq_leviForm`: the mixed second Wirtinger
  derivatives of a `C²` real function, in either order, are the entries of its Levi form.
* `TauCeti.toMatrix₂_leviForm`: the matrix of the Levi form in a complex basis is the matrix of
  mixed second Wirtinger derivatives.
* `TauCeti.sum_wirtingerDeriv_conjWirtingerDeriv_eq_hessianQuadraticForm`: the Levi matrix
  evaluated on the coordinates of `v` is `(D²f(x)(v, v) + D²f(x)(I • v, I • v)) / 4`.

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

end Wirtinger

section Real

variable {f : V → ℝ} {x : V}

/-- For a real function, the conjugate Wirtinger derivative is the complex conjugate of the
Wirtinger derivative. -/
theorem conjWirtingerDeriv_ofReal_comp_apply (f : V → ℝ) (x v : V) :
    conjWirtingerDeriv (fun y ↦ (f y : ℂ)) x v = conj (wirtingerDeriv (fun y ↦ (f y : ℂ)) x v) := by
  apply Complex.ext <;>
  simp [conjWirtingerDeriv_apply, wirtingerDeriv_apply]

/-- **Wirtinger comparison.** For a `C²` real function `f`, the mixed second Wirtinger derivative
`∂_w \bar∂_v f`, that is `∂²f / ∂z_j ∂(conj z_k)` for coordinate vectors `v = e_k` and `w = e_j`,
is the Levi form `leviForm f x v w`. -/
theorem wirtingerDeriv_conjWirtingerDeriv_eq_leviForm (hf : ContDiffAt ℝ 2 f x) (v w : V) :
    wirtingerDeriv (fun y ↦ conjWirtingerDeriv (fun z ↦ (f z : ℂ)) y v) x w =
      leviForm f x v w := by
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  have hD := hf.hasFDerivAt_fderiv_ofReal_comp_apply
  have hd : HasFDerivAt (fun y ↦ conjWirtingerDeriv (fun z ↦ (f z : ℂ)) y v) _ x :=
    ((hD v).add ((hD (I • v)).const_smul I)).const_smul (2 : ℂ)⁻¹
  rw [wirtingerDeriv_apply, hd.fderiv]
  apply Complex.ext <;> simp [hsymm w v, hsymm (I • w) v, hsymm w (I • v),
    hsymm (I • w) (I • v)] <;> ring

/-- **Wirtinger comparison**, in the other order. For a `C²` real function `f`, the mixed second
Wirtinger derivative `\bar∂_v ∂_w f` is the Levi form `leviForm f x v w`. -/
theorem conjWirtingerDeriv_wirtingerDeriv_eq_leviForm (hf : ContDiffAt ℝ 2 f x) (v w : V) :
    conjWirtingerDeriv (fun y ↦ wirtingerDeriv (fun z ↦ (f z : ℂ)) y w) x v =
      leviForm f x v w := by
  have hD := hf.hasFDerivAt_fderiv_ofReal_comp_apply
  have hd : HasFDerivAt (fun y ↦ wirtingerDeriv (fun z ↦ (f z : ℂ)) y w) _ x :=
    ((hD w).sub ((hD (I • w)).const_smul I)).const_smul (2 : ℂ)⁻¹
  rw [conjWirtingerDeriv_apply, hd.fderiv]
  apply Complex.ext <;> simp <;> ring

/-- **The Levi matrix.** In a complex basis `b` of `V`, the matrix of the Levi form of a `C²`
real function has `(k, j)` entry the mixed second Wirtinger derivative
`∂²f / ∂z_j ∂(conj z_k)`. -/
theorem toMatrix₂_leviForm {ι : Type*} [Fintype ι] [DecidableEq ι] (hf : ContDiffAt ℝ 2 f x)
    (b : Module.Basis ι ℂ V) :
    LinearMap.toMatrix₂ b b (leviForm f x) = Matrix.of fun k j ↦
      wirtingerDeriv (fun y ↦ conjWirtingerDeriv (fun z ↦ (f z : ℂ)) y (b k)) x (b j) := by
  ext k j
  simp [wirtingerDeriv_conjWirtingerDeriv_eq_leviForm hf]

/-- **The diagonal of the Levi matrix.** In a complex basis `b` of `V`, with holomorphic
coordinates `ξ_j = dz_j(v)` of `v`, the Hermitian form `∑ L_{j \bar k} ξ_j conj ξ_k` with Levi
matrix `L_{j \bar k} = ∂²f / ∂z_j ∂(conj z_k)` of a `C²` real function `f` is one quarter of the
real second-derivative sum `D²f(x)(v, v) + D²f(x)(I • v, I • v)`. -/
theorem sum_wirtingerDeriv_conjWirtingerDeriv_eq_hessianQuadraticForm {ι : Type*} [Fintype ι]
    (hf : ContDiffAt ℝ 2 f x) (b : Module.Basis ι ℂ V) (v : V) :
    ∑ j, ∑ k, b.repr v j * conj (b.repr v k) *
        wirtingerDeriv (fun y ↦ conjWirtingerDeriv (fun z ↦ (f z : ℂ)) y (b k)) x (b j) =
      ((hessianQuadraticForm f x v + hessianQuadraticForm f x (I • v)) / 4 : ℝ) := by
  classical
  rw [← leviForm_apply_self hf, apply_eq_dotProduct_toMatrix₂_mulVec b b,
    toMatrix₂_leviForm hf]
  simp only [dotProduct, Matrix.mulVec, Function.comp_apply, Matrix.of_apply, RingHom.id_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

end Real

end TauCeti
