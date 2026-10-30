/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.Analysis.Complex.LeviForm
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import TauCeti.Analysis.Calculus.FDeriv.OfReal

/-!
# Wirtinger derivatives and the Levi form

The Levi form `TauCeti.leviForm f x` of a real function `f` is defined from the real second
derivative. This file compares it with the second Wirtinger derivatives
`TauCeti.wirtingerDeriv` and `TauCeti.conjWirtingerDeriv`: for `C²` real `f`, the mixed Wirtinger
derivative `∂²f / ∂z_j ∂(conj z_k)`, taken in either order, is the Levi form entry
`leviForm f x (e_k) (e_j)`. Consequently, in any complex basis `e` of `V`, the Hermitian form with
matrix `L_{j \bar k} = ∂²f / ∂z_j ∂(conj z_k)` evaluated at the coordinates `ξ_j = dz_j(v)` of a
real tangent vector `v` is one quarter of the real second-derivative sum
`D²f(x)(v, v) + D²f(x)(I • v, I • v)`.

## Main results

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

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℝ} {x : V}

/-- **Wirtinger comparison.** For a `C²` real function `f`, the mixed second Wirtinger derivative
`∂_w \bar∂_v f`, that is `∂²f / ∂z_j ∂(conj z_k)` for coordinate vectors `v = e_k` and `w = e_j`,
is the Levi form `leviForm f x v w`. -/
theorem wirtingerDeriv_conjWirtingerDeriv_eq_leviForm (hf : ContDiffAt ℝ 2 f x) (v w : V) :
    wirtingerDeriv (fun y ↦ conjWirtingerDeriv (fun z ↦ (f z : ℂ)) y v) x w =
      leviForm f x v w := by
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  have hD := hf.hasFDerivAt_fderiv_ofReal_comp_apply
  have hd : HasFDerivAt (fun y ↦ conjWirtingerDeriv (fun z ↦ (f z : ℂ)) y v) _ x :=
    (((hD v).add ((hD (I • v)).const_smul I)).const_smul (2 : ℂ)⁻¹).congr_of_eventuallyEq
      (.of_forall fun y ↦ conjWirtingerDeriv_apply _ y v)
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
    (((hD w).sub ((hD (I • w)).const_smul I)).const_smul (2 : ℂ)⁻¹).congr_of_eventuallyEq
      (.of_forall fun y ↦ wirtingerDeriv_apply _ y w)
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

end TauCeti
