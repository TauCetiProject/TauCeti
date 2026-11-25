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

/-- **The logarithmic derivative of a point of `𝔾ₘ` is `Du / u`.** -/
theorem tangentLinearEquiv_pointRightLogDeriv (g : WithConv (R[T;T⁻¹] →ₐ[R] B)) :
    tangentLinearEquiv (D.pointRightLogDeriv g) =
      D (pointsMulEquiv g : B) * ((pointsMulEquiv g)⁻¹ : Bˣ) := by
  have hT : IsGroupLikeElem R (LaurentPolynomial.T 1 : R[T;T⁻¹]) :=
    groupLikeT_val R ▸ (groupLikeT R).isGroupLikeElem_val
  rw [tangentLinearEquiv_apply, Derivation.algEquivSelf_pointRightLogDeriv_apply,
    hT.ofConv_convMul_apply, ← map_inv]
  simp [pointsMulEquiv_apply]

end CommSemiring

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (D : Derivation R B B)

/-- **The gauge action of `𝔾ₘ` is translation by `-Du / u`**: the adjoint action of the
commutative group `𝔾ₘ` is trivial (`Derivation.pointGauge_of_isCocomm`). -/
theorem tangentLinearEquiv_pointGauge (g : WithConv (R[T;T⁻¹] →ₐ[R] B))
    (A : Derivation R R[T;T⁻¹] (Bialgebra.CounitAlgebra R R[T;T⁻¹] B)) :
    tangentLinearEquiv (D.pointGauge g A) =
      tangentLinearEquiv A - D (pointsMulEquiv g : B) * ((pointsMulEquiv g)⁻¹ : Bˣ) := by
  rw [Derivation.pointGauge_of_isCocomm, map_sub, tangentLinearEquiv_pointRightLogDeriv]

/-- **The logarithmic derivative of the loop `t`**: for the point `t` of `𝔾ₘ` over `R⸨t⸩` and
`D = d/dt`, `dlog t = t⁻¹`, so gauge transformation by `t` changes `d + A dt` into
`d + (A - t⁻¹) dt`. -/
theorem tangentLinearEquiv_pointRightLogDeriv_unitX :
    tangentLinearEquiv ((laurentSeriesAlgebraDerivation R).pointRightLogDeriv
        ((pointsMulEquiv (R := R) (A := R⸨X⸩)).symm TauCeti.LaurentSeries.unitX)) =
      HahnSeries.single (-1) 1 := by
  rw [tangentLinearEquiv_pointRightLogDeriv]
  simp [_root_.LaurentSeries.derivative_apply]

end TauCeti.MultiplicativeGroup
