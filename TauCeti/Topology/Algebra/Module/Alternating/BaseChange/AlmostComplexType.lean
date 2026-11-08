/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import TauCeti.Topology.Algebra.Module.Alternating.AlmostComplexType
public import TauCeti.Topology.Algebra.Module.Alternating.BaseChange.Basic

import Mathlib.Tactic.Module

/-!
# Type components of one- and two-forms through the complexification

Let `J` be an almost complex structure on a real topological vector space `V` and let `F` be a
complex topological vector space. A real vector `v` splits in the complexification
`ℂ ⊗[ℝ] V` as `1 ⊗ v = v^(1,0) + v^(0,1)` into its parts of type `(1,0)` and `(0,1)`, the
`i`- and `-i`-eigenvectors of the complexified `J`. This file computes the complex-multilinear
extensions of complex-valued one- and two-forms on these parts and identifies the results with the
type components of the forms, which `ContinuousLinearMap.typeProjection` defines on the real
alternating carrier:

* `α^(1,0)(v) = α(v^(1,0))` and `α^(0,1)(v) = α(v^(0,1))` for a one-form `α`;
* `β^(2,0)(v, w) = β(v^(1,0), w^(1,0))`, `β^(0,2)(v, w) = β(v^(0,1), w^(0,1))` and
  `β^(1,1)(v, w) = β(v^(1,0), w^(0,1)) + β(v^(0,1), w^(1,0))` for a two-form `β`.

In particular a form of type `(1,0)`, `(0,1)`, `(2,0)` or `(0,2)` is recovered on real vectors from
the values of its extension on their parts of the corresponding type. This is the comparison
between the type decomposition of forms on the real carrier and the description of the types
through the eigenspaces `T^(1,0)` and `T^(0,1)` of the complexification, in degrees one and two.

## Main declarations

* `ContinuousLinearMap.typeProjection_one_zero_apply_eq_liftBaseChangeFinOne`,
  `ContinuousLinearMap.typeProjection_zero_one_apply_eq_liftBaseChangeFinOne`: one-forms.
* `ContinuousLinearMap.typeProjection_two_zero_apply_eq_liftBaseChangeFinTwo`,
  `ContinuousLinearMap.typeProjection_one_one_apply_eq_liftBaseChangeFinTwo`,
  `ContinuousLinearMap.typeProjection_zero_two_apply_eq_liftBaseChangeFinTwo`: two-forms.
* `ContinuousAlternatingMap.IsOfType.liftBaseChangeFinTwo_antiholomorphicPart_antiholomorphicPart`
  and its companions: forms of pure type evaluated through the parts of real vectors.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 1.2.
-/

public section

open Complex
open TauCeti (AlmostComplexStructure)
open scoped TensorProduct

variable {V F : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] (J : AlmostComplexStructure V)

namespace ContinuousAlternatingMap

/-! ### Extensions evaluated on the parts of real vectors -/

/-- The extension of a one-form `α` on the `(1,0)`-part of `v` is `(α v - i α (J v)) / 2`. -/
@[simp]
theorem liftBaseChangeFinOne_holomorphicPart (α : V [⋀^Fin 1]→L[ℝ] F) (v : V) :
    α.liftBaseChangeFinOne ℂ (J.holomorphicPart v) = (2 : ℂ)⁻¹ • (α ![v] - I • α ![J v]) := by
  simp [liftBaseChangeFinOne_def, Matrix.vec_single_eq_const]

/-- The extension of a one-form `α` on the `(0,1)`-part of `v` is `(α v + i α (J v)) / 2`. -/
@[simp]
theorem liftBaseChangeFinOne_antiholomorphicPart (α : V [⋀^Fin 1]→L[ℝ] F) (v : V) :
    α.liftBaseChangeFinOne ℂ (J.antiholomorphicPart v) = (2 : ℂ)⁻¹ • (α ![v] + I • α ![J v]) := by
  simp [liftBaseChangeFinOne_def, Matrix.vec_single_eq_const]

/-- The extension of a two-form `β` on the `(1,0)`-parts of `v` and `w` is
`(β (v, w) - β (J v, J w) - i (β (J v, w) + β (v, J w))) / 4`. -/
theorem liftBaseChangeFinTwo_holomorphicPart_holomorphicPart (β : V [⋀^Fin 2]→L[ℝ] F)
    (v w : V) :
    β.liftBaseChangeFinTwo ℂ (J.holomorphicPart v) (J.holomorphicPart w) =
      (4 : ℂ)⁻¹ • (β ![v, w] - β ![J v, J w] - I • (β ![J v, w] + β ![v, J w])) := by
  simp only [AlmostComplexStructure.holomorphicPart_apply, map_smul, map_sub, LinearMap.smul_apply,
    LinearMap.sub_apply, liftBaseChangeFinTwo_tmul, mul_one]
  linear_combination (norm := module) I_mul_I • ((4 : ℂ)⁻¹ • β ![J v, J w])

/-- The extension of a two-form `β` on the `(0,1)`-parts of `v` and `w` is
`(β (v, w) - β (J v, J w) + i (β (J v, w) + β (v, J w))) / 4`. -/
theorem liftBaseChangeFinTwo_antiholomorphicPart_antiholomorphicPart (β : V [⋀^Fin 2]→L[ℝ] F)
    (v w : V) :
    β.liftBaseChangeFinTwo ℂ (J.antiholomorphicPart v) (J.antiholomorphicPart w) =
      (4 : ℂ)⁻¹ • (β ![v, w] - β ![J v, J w] + I • (β ![J v, w] + β ![v, J w])) := by
  simp only [AlmostComplexStructure.antiholomorphicPart_apply, map_smul, map_add,
    LinearMap.smul_apply, LinearMap.add_apply, liftBaseChangeFinTwo_tmul, mul_one]
  linear_combination (norm := module) I_mul_I • ((4 : ℂ)⁻¹ • β ![J v, J w])

/-- The extension of a two-form `β` on the mixed parts of `v` and `w`, in both orders, sums to
`(β (v, w) + β (J v, J w)) / 2`. -/
theorem liftBaseChangeFinTwo_holomorphicPart_antiholomorphicPart_add (β : V [⋀^Fin 2]→L[ℝ] F)
    (v w : V) :
    β.liftBaseChangeFinTwo ℂ (J.holomorphicPart v) (J.antiholomorphicPart w) +
        β.liftBaseChangeFinTwo ℂ (J.antiholomorphicPart v) (J.holomorphicPart w) =
      (2 : ℂ)⁻¹ • (β ![v, w] + β ![J v, J w]) := by
  simp only [AlmostComplexStructure.holomorphicPart_apply,
    AlmostComplexStructure.antiholomorphicPart_apply, map_smul, map_add, map_sub,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, liftBaseChangeFinTwo_tmul,
    mul_one]
  linear_combination (norm := module) I_mul_I • (-(2 : ℂ)⁻¹ • β ![J v, J w])

end ContinuousAlternatingMap

/-! ### Type components -/

variable [IsTopologicalAddGroup F] [ContinuousConstSMul ℂ F]

namespace ContinuousLinearMap

variable {J} {K : V →L[ℝ] V} (hK : ∀ v, K v = J v)
include hK

/-- `K` squares to `-1` when it agrees with an almost complex structure. -/
private theorem apply_apply_of_forall_eq (v : V) : K (K v) = -v := by
  rw [hK, hK, AlmostComplexStructure.apply_apply]

/-- The `(1,0)`-component of a one-form `α` at `v` is the extension of `α` on the `(1,0)`-part
of `v`. -/
theorem typeProjection_one_zero_apply_eq_liftBaseChangeFinOne (α : V [⋀^Fin 1]→L[ℝ] F) (v : V) :
    K.typeProjection 1 0 α ![v] = α.liftBaseChangeFinOne ℂ (J.holomorphicPart v) := by
  rw [typeProjection_one_zero, ContinuousAlternatingMap.liftBaseChangeFinOne_holomorphicPart]
  simp [alternatingDerivation_apply_vecCons_fin_one, hK]

/-- The `(0,1)`-component of a one-form `α` at `v` is the extension of `α` on the `(0,1)`-part
of `v`. -/
theorem typeProjection_zero_one_apply_eq_liftBaseChangeFinOne (α : V [⋀^Fin 1]→L[ℝ] F) (v : V) :
    K.typeProjection 0 1 α ![v] = α.liftBaseChangeFinOne ℂ (J.antiholomorphicPart v) := by
  rw [typeProjection_zero_one, ContinuousAlternatingMap.liftBaseChangeFinOne_antiholomorphicPart]
  simp [alternatingDerivation_apply_vecCons_fin_one, hK]

/-- The `(2,0)`-component of a two-form `β` at `(v, w)` is the extension of `β` on the
`(1,0)`-parts of `v` and `w`. -/
theorem typeProjection_two_zero_apply_eq_liftBaseChangeFinTwo (β : V [⋀^Fin 2]→L[ℝ] F)
    (v w : V) :
    K.typeProjection 2 0 β ![v, w] =
      β.liftBaseChangeFinTwo ℂ (J.holomorphicPart v) (J.holomorphicPart w) := by
  rw [typeProjection_two_zero_apply (apply_apply_of_forall_eq hK),
    ContinuousAlternatingMap.liftBaseChangeFinTwo_holomorphicPart_holomorphicPart, hK, hK]

/-- The `(1,1)`-component of a two-form `β` at `(v, w)` is the sum of the extensions of `β` on
the `(1,0)`-part of `v` and the `(0,1)`-part of `w`, and on the `(0,1)`-part of `v` and the
`(1,0)`-part of `w`. -/
theorem typeProjection_one_one_apply_eq_liftBaseChangeFinTwo (β : V [⋀^Fin 2]→L[ℝ] F)
    (v w : V) :
    K.typeProjection 1 1 β ![v, w] =
      β.liftBaseChangeFinTwo ℂ (J.holomorphicPart v) (J.antiholomorphicPart w) +
        β.liftBaseChangeFinTwo ℂ (J.antiholomorphicPart v) (J.holomorphicPart w) := by
  rw [typeProjection_one_one_apply (apply_apply_of_forall_eq hK),
    ContinuousAlternatingMap.liftBaseChangeFinTwo_holomorphicPart_antiholomorphicPart_add, hK, hK]

/-- The `(0,2)`-component of a two-form `β` at `(v, w)` is the extension of `β` on the
`(0,1)`-parts of `v` and `w`. -/
theorem typeProjection_zero_two_apply_eq_liftBaseChangeFinTwo (β : V [⋀^Fin 2]→L[ℝ] F)
    (v w : V) :
    K.typeProjection 0 2 β ![v, w] =
      β.liftBaseChangeFinTwo ℂ (J.antiholomorphicPart v) (J.antiholomorphicPart w) := by
  rw [typeProjection_zero_two_apply (apply_apply_of_forall_eq hK),
    ContinuousAlternatingMap.liftBaseChangeFinTwo_antiholomorphicPart_antiholomorphicPart, hK, hK]

end ContinuousLinearMap

/-! ### Forms of pure type -/

namespace ContinuousAlternatingMap.IsOfType

variable {J} {K : V →L[ℝ] V} (hK : ∀ v, K v = J v)
include hK

/-- A one-form of type `(1,0)` takes the value `α(v)` on the `(1,0)`-part of `v`. -/
theorem liftBaseChangeFinOne_holomorphicPart {α : V [⋀^Fin 1]→L[ℝ] F} (hα : α.IsOfType K 1 0)
    (v : V) :
    α.liftBaseChangeFinOne ℂ (J.holomorphicPart v) = α ![v] := by
  rw [← ContinuousLinearMap.typeProjection_one_zero_apply_eq_liftBaseChangeFinOne hK,
    hα.typeProjection_self]

/-- A one-form of type `(0,1)` takes the value `α(v)` on the `(0,1)`-part of `v`. -/
theorem liftBaseChangeFinOne_antiholomorphicPart {α : V [⋀^Fin 1]→L[ℝ] F}
    (hα : α.IsOfType K 0 1) (v : V) :
    α.liftBaseChangeFinOne ℂ (J.antiholomorphicPart v) = α ![v] := by
  rw [← ContinuousLinearMap.typeProjection_zero_one_apply_eq_liftBaseChangeFinOne hK,
    hα.typeProjection_self]

/-- A two-form of type `(2,0)` takes the value `β(v, w)` on the `(1,0)`-parts of `v` and `w`. -/
theorem liftBaseChangeFinTwo_holomorphicPart_holomorphicPart {β : V [⋀^Fin 2]→L[ℝ] F}
    (hβ : β.IsOfType K 2 0) (v w : V) :
    β.liftBaseChangeFinTwo ℂ (J.holomorphicPart v) (J.holomorphicPart w) = β ![v, w] := by
  rw [← ContinuousLinearMap.typeProjection_two_zero_apply_eq_liftBaseChangeFinTwo hK,
    hβ.typeProjection_self]

/-- A two-form of type `(0,2)` takes the value `β(v, w)` on the `(0,1)`-parts of `v` and `w`. -/
theorem liftBaseChangeFinTwo_antiholomorphicPart_antiholomorphicPart {β : V [⋀^Fin 2]→L[ℝ] F}
    (hβ : β.IsOfType K 0 2) (v w : V) :
    β.liftBaseChangeFinTwo ℂ (J.antiholomorphicPart v) (J.antiholomorphicPart w) = β ![v, w] := by
  rw [← ContinuousLinearMap.typeProjection_zero_two_apply_eq_liftBaseChangeFinTwo hK,
    hβ.typeProjection_self]

end ContinuousAlternatingMap.IsOfType
