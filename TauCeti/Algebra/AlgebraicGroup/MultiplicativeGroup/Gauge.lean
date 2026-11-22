/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Gauge
public import TauCeti.RingTheory.LaurentSeries.Basic
public import TauCeti.RingTheory.LaurentSeries.Derivative

/-!
# The gauge action of the multiplicative group

For `𝔾ₘ`, points are units `u ∈ Bˣ` (`TauCeti.MultiplicativeGroup.pointsMulEquiv`) and tangent
vectors are elements of `B` (`TauCeti.MultiplicativeGroup.tangentLinearEquiv`). In these terms
the logarithmic derivative of a point along a derivation `D` of `B` is `Du / u`, and since `𝔾ₘ`
is commutative its adjoint action is trivial, so the gauge action is the translation
`A ↦ A - Du / u`. For `B = R⸨t⸩` and `D = d/dt`, gauge transformation by the loop `t` changes
the connection `d + A dt` into `d + (A - t⁻¹) dt`.

## Main results

* `TauCeti.MultiplicativeGroup.tangentLinearEquiv_pointRightLogDeriv`: `dlog u = Du * u⁻¹`.
* `TauCeti.MultiplicativeGroup.tangentLinearEquiv_pointGauge`: `gauge u A = A - Du * u⁻¹`.
-/

public section

open WithConv
open scoped LaurentPolynomial LaurentSeries

namespace TauCeti.MultiplicativeGroup

section CommSemiring

variable {R B : Type*} [CommSemiring R] [CommRing B] [Algebra R B] (D : Derivation R B B)

/-- A convolution product of linear maps on `R[T;T⁻¹]`, evaluated at the group-like `T`, is the
product of their values. -/
private lemma ofConv_convMul_apply_T (f h : WithConv (R[T;T⁻¹] →ₗ[R] B)) :
    (f * h).ofConv (LaurentPolynomial.T 1) =
      f.ofConv (LaurentPolynomial.T 1) * h.ofConv (LaurentPolynomial.T 1) := by
  rw [LinearMap.convMul_apply, LaurentPolynomial.comul_T, TensorProduct.map_tmul,
    LinearMap.mul'_apply]

/-- **The logarithmic derivative of a point of `𝔾ₘ` is `Du / u`.** -/
theorem tangentLinearEquiv_pointRightLogDeriv (g : WithConv (R[T;T⁻¹] →ₐ[R] B)) :
    tangentLinearEquiv (D.pointRightLogDeriv g) =
      D (pointsMulEquiv g : B) * ((pointsMulEquiv g)⁻¹ : Bˣ) := by
  rw [tangentLinearEquiv_apply, Derivation.algEquivSelf_pointRightLogDeriv_apply,
    ofConv_convMul_apply_T, ← map_inv]
  simp [pointsMulEquiv_apply]

/-- The value of a point of `𝔾ₘ` at `T` times the value of its inverse at `T` is `1`. -/
private lemma ofConv_apply_T_mul_ofConv_inv_apply_T (g : WithConv (R[T;T⁻¹] →ₐ[R] B)) :
    g.ofConv (LaurentPolynomial.T 1) * (g⁻¹).ofConv (LaurentPolynomial.T 1) = 1 := by
  simpa [pointsMulEquiv_apply, ← map_inv] using (pointsMulEquiv g).mul_inv

end CommSemiring

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (D : Derivation R B B)

/-- **The gauge action of `𝔾ₘ` is translation by `-Du / u`**: the adjoint action of the
commutative group `𝔾ₘ` is trivial. -/
theorem tangentLinearEquiv_pointGauge (g : WithConv (R[T;T⁻¹] →ₐ[R] B))
    (A : Derivation R R[T;T⁻¹] (Bialgebra.CounitAlgebra R R[T;T⁻¹] B)) :
    tangentLinearEquiv (D.pointGauge g A) =
      tangentLinearEquiv A - D (pointsMulEquiv g : B) * ((pointsMulEquiv g)⁻¹ : Bˣ) := by
  rw [Derivation.pointGauge_def, map_sub, tangentLinearEquiv_pointRightLogDeriv]
  congr 1
  have h := LinearMap.congr_fun
    (congrArg ofConv (Derivation.toConv_algEquivSelf_comp_adDerivation g A))
    (LaurentPolynomial.T 1)
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe] at h
  rw [tangentLinearEquiv_apply, tangentLinearEquiv_apply, h, ofConv_convMul_apply_T,
    ofConv_convMul_apply_T]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply,
    Derivation.coeFn_coe]
  rw [mul_right_comm, ofConv_apply_T_mul_ofConv_inv_apply_T, one_mul]

/-- **The logarithmic derivative of the loop `t`**: for the point `t` of `𝔾ₘ` over `R⸨t⸩` and
`D = d/dt`, `dlog t = t⁻¹`, so gauge transformation by `t` changes `d + A dt` into
`d + (A - t⁻¹) dt`. -/
theorem tangentLinearEquiv_pointRightLogDeriv_unitX :
    tangentLinearEquiv ((laurentSeriesAlgebraDerivation R).pointRightLogDeriv
        ((pointsMulEquiv (R := R) (A := R⸨X⸩)).symm TauCeti.LaurentSeries.unitX)) =
      HahnSeries.single (-1) 1 := by
  rw [tangentLinearEquiv_pointRightLogDeriv, MulEquiv.apply_symm_apply,
    coe_laurentSeriesAlgebraDerivation, laurentSeriesDerivation_apply,
    TauCeti.LaurentSeries.val_unitX, TauCeti.LaurentSeries.val_inv_unitX,
    _root_.LaurentSeries.derivative_apply, _root_.LaurentSeries.hasseDeriv_single]
  simp

end TauCeti.MultiplicativeGroup
