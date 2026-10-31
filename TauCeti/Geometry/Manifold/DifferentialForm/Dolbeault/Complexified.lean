/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.BaseChange
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Basic

/-!
# `∂bar²` and `∂²` on complexified tangent vectors

Let `J` be a smooth almost complex structure on a manifold `M` and let `F` be a complex normed
space. A complex-valued `k`-form at `x`, a real alternating map on `T_x M`, extends
complex-multilinearly to the complexified tangent space `ℂ ⊗[ℝ] T_x M`; for one- and two-forms
these are `ContinuousAlternatingMap.liftBaseChangeFinOne` and
`ContinuousAlternatingMap.liftBaseChangeFinTwo`. The Nijenhuis tensor `N_J` extends
complex-bilinearly by `LinearMap.BilinMap.baseChange`. The tangent vectors of type `(1,0)` and
`(0,1)` at `x` are the `i`- and `-i`-eigenvectors of the complexification of `J`.

For a smooth function `f`, the extensions of the squares of `∂bar` and `∂` are
`∂bar ∂bar f(X, Y) = -∂f(N_J(X, Y)) / 4` and `∂∂f(X, Y) = -∂bar f(N_J(X, Y)) / 4`
for all complexified tangent vectors `X` and `Y`, in particular for two vectors of type `(0,1)`,
respectively `(1,0)`. Since `N_J` maps a vector of type `(1,0)` and any second vector to a vector
of type `(0,1)`, and the extension of the `(1,0)`-form `∂f` vanishes on the vectors of type `(0,1)`
(`TauCeti.SmoothForm.isOfType_one_zero_iff_eigenspace_le_ker`), `∂bar ∂bar f(X, Y)` vanishes as
soon as `X` or `Y` has type `(1,0)`; symmetrically `∂∂f(X, Y)` vanishes as soon as `X` or `Y` has
type `(0,1)`.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.liftBaseChangeFinTwo_delBar_delBar_apply`,
  `TauCeti.SmoothAlmostComplexStructure.liftBaseChangeFinTwo_del_del_apply`: `∂bar²` and `∂²` on
  functions through the complex-bilinear extension of the Nijenhuis tensor.
* `TauCeti.SmoothAlmostComplexStructure.liftBaseChangeFinTwo_delBar_delBar_eq_zero_of_mem_left`
  and its companions: the vanishing of `∂bar ∂bar f` and `∂∂f` off the vectors of type `(0,1)`,
  respectively `(1,0)`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Sections 1.2 and 2.6.
-/

public section

noncomputable section

open Module.End
open LinearMap (BilinMap)
open scoped Manifold ContDiff TensorProduct

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TauCeti

/-! ### The squares of `∂bar` and `∂` on complexified tangent vectors -/

namespace SmoothAlmostComplexStructure

variable [FiniteDimensional ℝ E] (J : SmoothAlmostComplexStructure I M)

/-- **`∂bar²` on functions through the complexified Nijenhuis tensor.** For a smooth function `f`
and complexified tangent vectors `X` and `Y`, in particular two vectors of type `(0,1)`,
`∂bar ∂bar f(X, Y) = -∂f(N_J(X, Y)) / 4`, with the forms extended complex-multilinearly and `N_J`
complex-bilinearly. -/
theorem liftBaseChangeFinTwo_delBar_delBar_apply (f : SmoothForm I M F 0) (x : M)
    (X Y : ℂ ⊗[ℝ] TangentSpace I x) :
    ((J.delBar (J.delBar f)).1 x).liftBaseChangeFinTwo ℂ X Y =
      -(4 : ℂ)⁻¹ • ((J.del f).1 x).liftBaseChangeFinOne ℂ
        (BilinMap.baseChange ℂ (J.nijenhuis x).toLinearMap₁₂ X Y) :=
  ContinuousAlternatingMap.liftBaseChangeFinTwo_apply_of_eq_smul ℂ (J.delBar_delBar_apply f x) X Y

/-- **`∂²` on functions through the complexified Nijenhuis tensor.** For a smooth function `f`
and complexified tangent vectors `X` and `Y`, in particular two vectors of type `(1,0)`,
`∂∂f(X, Y) = -∂bar f(N_J(X, Y)) / 4`, with the forms extended complex-multilinearly and `N_J`
complex-bilinearly. -/
theorem liftBaseChangeFinTwo_del_del_apply (f : SmoothForm I M F 0) (x : M)
    (X Y : ℂ ⊗[ℝ] TangentSpace I x) :
    ((J.del (J.del f)).1 x).liftBaseChangeFinTwo ℂ X Y =
      -(4 : ℂ)⁻¹ • ((J.delBar f).1 x).liftBaseChangeFinOne ℂ
        (BilinMap.baseChange ℂ (J.nijenhuis x).toLinearMap₁₂ X Y) :=
  ContinuousAlternatingMap.liftBaseChangeFinTwo_apply_of_eq_smul ℂ (J.del_del_apply f x) X Y

variable {x : M} {X Y : ℂ ⊗[ℝ] TangentSpace I x}

/-- `∂bar ∂bar f(X, Y)` vanishes when `X` has type `(1,0)`. -/
theorem liftBaseChangeFinTwo_delBar_delBar_eq_zero_of_mem_left (f : SmoothForm I M F 0)
    (hX : X ∈ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) Complex.I)
    (Y : ℂ ⊗[ℝ] TangentSpace I x) :
    ((J.delBar (J.delBar f)).1 x).liftBaseChangeFinTwo ℂ X Y = 0 := by
  have hf : (J.del f).IsOfType J 1 0 := (SmoothForm.isOfType_zero_zero f J).del
  rw [liftBaseChangeFinTwo_delBar_delBar_apply,
    SmoothForm.isOfType_one_zero_iff_eigenspace_le_ker.1 hf x
      (J.baseChange_nijenhuis_mem_eigenspace_neg_of_mem_left hX Y), smul_zero]

/-- `∂bar ∂bar f(X, Y)` vanishes when `Y` has type `(1,0)`. -/
theorem liftBaseChangeFinTwo_delBar_delBar_eq_zero_of_mem_right (f : SmoothForm I M F 0)
    (X : ℂ ⊗[ℝ] TangentSpace I x)
    (hY : Y ∈ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) Complex.I) :
    ((J.delBar (J.delBar f)).1 x).liftBaseChangeFinTwo ℂ X Y = 0 := by
  rw [ContinuousAlternatingMap.liftBaseChangeFinTwo_swap,
    J.liftBaseChangeFinTwo_delBar_delBar_eq_zero_of_mem_left f hY, neg_zero]

/-- `∂∂f(X, Y)` vanishes when `X` has type `(0,1)`. -/
theorem liftBaseChangeFinTwo_del_del_eq_zero_of_mem_left (f : SmoothForm I M F 0)
    (hX : X ∈ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) (-Complex.I))
    (Y : ℂ ⊗[ℝ] TangentSpace I x) :
    ((J.del (J.del f)).1 x).liftBaseChangeFinTwo ℂ X Y = 0 := by
  have hf : (J.delBar f).IsOfType J 0 1 := (SmoothForm.isOfType_zero_zero f J).delBar
  have hN := J.baseChange_nijenhuis_mem_eigenspace_neg_of_mem_left hX Y
  rw [_root_.neg_neg] at hN
  rw [liftBaseChangeFinTwo_del_del_apply,
    SmoothForm.isOfType_zero_one_iff_eigenspace_le_ker.1 hf x hN, smul_zero]

/-- `∂∂f(X, Y)` vanishes when `Y` has type `(0,1)`. -/
theorem liftBaseChangeFinTwo_del_del_eq_zero_of_mem_right (f : SmoothForm I M F 0)
    (X : ℂ ⊗[ℝ] TangentSpace I x)
    (hY : Y ∈ eigenspace ((J.almostComplexStructureAt x).toLinearMap.baseChange ℂ) (-Complex.I)) :
    ((J.del (J.del f)).1 x).liftBaseChangeFinTwo ℂ X Y = 0 := by
  rw [ContinuousAlternatingMap.liftBaseChangeFinTwo_swap,
    J.liftBaseChangeFinTwo_del_del_eq_zero_of_mem_left f hY, neg_zero]

end SmoothAlmostComplexStructure

end TauCeti
