/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.BaseChange.AlmostComplexType
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

On real tangent vectors `v` and `w` the same formulas read
`∂bar ∂bar f(v, w) = -∂f(N_J(v, w)^(1,0)) / 4` and `∂∂f(v, w) = -∂bar f(N_J(v, w)^(0,1)) / 4`:
the `(0,2)`-form `∂bar ∂bar f` takes the value `∂bar ∂bar f(v, w)` on the `(0,1)`-parts
`v^(0,1)` and `w^(0,1)`, and `N_J(v^(0,1), w^(0,1)) = N_J(v, w)^(1,0)`, and symmetrically for
`∂∂f`. With the normalization `N' = N_J / 4` of the Nijenhuis tensor the formulas read
`∂bar ∂bar f(X, Y) = -∂f(N'(X, Y))` and `∂∂f(X, Y) = -∂bar f(N'(X, Y))`.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.liftBaseChangeFinTwo_delBar_delBar_apply`,
  `TauCeti.SmoothAlmostComplexStructure.liftBaseChangeFinTwo_del_del_apply`: `∂bar²` and `∂²` on
  functions through the complex-bilinear extension of the Nijenhuis tensor.
* `TauCeti.SmoothAlmostComplexStructure.liftBaseChangeFinTwo_delBar_delBar_eq_zero_of_mem_left`
  and its companions: the vanishing of `∂bar ∂bar f` and `∂∂f` off the vectors of type `(0,1)`,
  respectively `(1,0)`.
* `TauCeti.SmoothAlmostComplexStructure.delBar_delBar_apply_eq_liftBaseChangeFinOne_holomorphicPart`
  and
  `TauCeti.SmoothAlmostComplexStructure.del_del_apply_eq_liftBaseChangeFinOne_antiholomorphicPart`:
  the formulas on real tangent vectors through their `(0,1)`- and `(1,0)`-parts.
* In the namespace `TauCeti.SmoothAlmostComplexStructure`,
  `liftBaseChangeFinTwo_delBar_delBar_apply_inv_four_smul_nijenhuis` and
  `liftBaseChangeFinTwo_del_del_apply_inv_four_smul_nijenhuis`: the formulas for the
  normalization `N' = N_J / 4`.

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

/-- **`∂bar²` on real tangent vectors through their `(0,1)`-parts.** For a smooth function `f`
and real tangent vectors `v` and `w`, `∂bar ∂bar f(v, w) = -∂f(N_J(v, w)^(1,0)) / 4`, with `∂f`
extended complex-linearly. -/
theorem delBar_delBar_apply_eq_liftBaseChangeFinOne_holomorphicPart (f : SmoothForm I M F 0)
    (x : M) (v w : TangentSpace I x) :
    (J.delBar (J.delBar f)).1 x ![v, w] =
      -(4 : ℂ)⁻¹ • ((J.del f).1 x).liftBaseChangeFinOne ℂ
        ((J.almostComplexStructureAt x).holomorphicPart (J.nijenhuis x v w)) := by
  rw [← ((SmoothForm.isOfType_zero_zero f J).delBar.delBar.apply x)
      |>.liftBaseChangeFinTwo_antiholomorphicPart_antiholomorphicPart
        (J.almostComplexStructureAt_apply x · |>.symm),
    liftBaseChangeFinTwo_delBar_delBar_apply,
    baseChange_nijenhuis_antiholomorphicPart_antiholomorphicPart]

/-- **`∂²` on real tangent vectors through their `(1,0)`-parts.** For a smooth function `f` and
real tangent vectors `v` and `w`, `∂∂f(v, w) = -∂bar f(N_J(v, w)^(0,1)) / 4`, with `∂bar f`
extended complex-linearly. -/
theorem del_del_apply_eq_liftBaseChangeFinOne_antiholomorphicPart (f : SmoothForm I M F 0)
    (x : M) (v w : TangentSpace I x) :
    (J.del (J.del f)).1 x ![v, w] =
      -(4 : ℂ)⁻¹ • ((J.delBar f).1 x).liftBaseChangeFinOne ℂ
        ((J.almostComplexStructureAt x).antiholomorphicPart (J.nijenhuis x v w)) := by
  rw [← ((SmoothForm.isOfType_zero_zero f J).del.del.apply x)
      |>.liftBaseChangeFinTwo_holomorphicPart_holomorphicPart
        (J.almostComplexStructureAt_apply x · |>.symm),
    liftBaseChangeFinTwo_del_del_apply, baseChange_nijenhuis_holomorphicPart_holomorphicPart]

/-- **`∂bar²` for the normalized Nijenhuis tensor.** With the convention `N' = N_J / 4`, for a
smooth function `f` and complexified tangent vectors `X` and `Y`, in particular two vectors of
type `(0,1)` or two real vectors `1 ⊗ v` and `1 ⊗ w`, `∂bar ∂bar f(X, Y) = -∂f(N'(X, Y))`. -/
theorem liftBaseChangeFinTwo_delBar_delBar_apply_inv_four_smul_nijenhuis (f : SmoothForm I M F 0)
    (x : M) (X Y : ℂ ⊗[ℝ] TangentSpace I x) :
    ((J.delBar (J.delBar f)).1 x).liftBaseChangeFinTwo ℂ X Y =
      -((J.del f).1 x).liftBaseChangeFinOne ℂ
        (BilinMap.baseChange ℂ ((4 : ℝ)⁻¹ • J.nijenhuis x).toLinearMap₁₂ X Y) := by
  rw [← neg_one_smul ℂ]
  refine ContinuousAlternatingMap.liftBaseChangeFinTwo_apply_of_eq_smul ℂ (fun v w ↦ ?_) X Y
  simp [delBar_delBar_apply, ContinuousAlternatingMap.vecCons_smul, ← Complex.coe_smul]

/-- **`∂²` for the normalized Nijenhuis tensor.** With the convention `N' = N_J / 4`, for a
smooth function `f` and complexified tangent vectors `X` and `Y`, in particular two vectors of
type `(1,0)` or two real vectors `1 ⊗ v` and `1 ⊗ w`, `∂∂f(X, Y) = -∂bar f(N'(X, Y))`. -/
theorem liftBaseChangeFinTwo_del_del_apply_inv_four_smul_nijenhuis (f : SmoothForm I M F 0)
    (x : M) (X Y : ℂ ⊗[ℝ] TangentSpace I x) :
    ((J.del (J.del f)).1 x).liftBaseChangeFinTwo ℂ X Y =
      -((J.delBar f).1 x).liftBaseChangeFinOne ℂ
        (BilinMap.baseChange ℂ ((4 : ℝ)⁻¹ • J.nijenhuis x).toLinearMap₁₂ X Y) := by
  rw [← neg_one_smul ℂ]
  refine ContinuousAlternatingMap.liftBaseChangeFinTwo_apply_of_eq_smul ℂ (fun v w ↦ ?_) X Y
  simp [del_del_apply, ContinuousAlternatingMap.vecCons_smul, ← Complex.coe_smul]

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
