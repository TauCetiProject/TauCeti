/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
public import TauCeti.Analysis.Calculus.SecondDerivative
public import TauCeti.Analysis.InnerProductSpace.Projection.RestrictScalars

/-!
# The second fundamental form of a map into an inner product space

Let `i : V → E` be a map from a finite-dimensional normed space over `𝕜 = ℝ` or `ℂ` into an inner
product space over `𝕜`. Its tangent space at `x` is the range of the derivative `Di(x)`, and its
normal space is the orthogonal complement `(Di(x)).rangeᗮ`. The **second fundamental form**
`TauCeti.secondFundamentalForm 𝕜 i x` is the normal component of the second derivative,

`B(v, w) = P_N (D²i(x)(v, w))`,

where `P_N` is the orthogonal projection onto the normal space. When `i` is an immersion
parametrising a submanifold of `E`, this is the second fundamental form of the submanifold,
evaluated on the tangent vectors `Di(x) v` and `Di(x) w` (the Gauss formula). It is symmetric,
and it is unchanged by a reparametrisation of the source, up to the derivative of the
reparametrisation: the second derivative of a change of coordinates contributes only a tangent
term, which the projection removes.

For a holomorphic map into a complex inner product space, the real and complex constructions are
compared. Equip `E` with the real inner product `re ⟪x, y⟫`. The real tangent space and the real
normal space are then complex subspaces, so multiplication by `I` (the complex structure `J`)
preserves both. The real second fundamental form `secondFundamentalForm ℝ i x` agrees with the
complex-bilinear, normal-valued form `secondFundamentalForm ℂ i x`, which gives the identities

`B(Jv, w) = J B(v, w) = B(v, Jw)` and `B(Jv, Jw) = -B(v, w)`.

These identities are what make the shape operators of a complex submanifold anticommute with `J`,
so that their eigenvalues come in pairs `±λ`.

## Main definitions

* `TauCeti.secondFundamentalForm 𝕜 i x`: the normal component of the second derivative of `i`.

## Main results

* `TauCeti.secondFundamentalForm_apply_mem_orthogonal`: the second fundamental form is
  normal-valued.
* `TauCeti.inner_secondFundamentalForm_apply_of_mem_orthogonal`: against a normal vector, the
  second fundamental form pairs like the second derivative.
* `ContDiffAt.secondFundamentalForm_apply_comm`: symmetry.
* `ContDiffAt.secondFundamentalForm_comp`: invariance under reparametrisation of the source.
* `DifferentiableAt.orthogonal_range_fderiv_restrictScalars`: the real normal space of a
  holomorphic map is its complex normal space.
* `ContDiffAt.secondFundamentalForm_restrictScalars_apply`: the real second fundamental form of a
  holomorphic map is its complex second fundamental form.
* `ContDiffAt.secondFundamentalForm_I_smul_left`, `ContDiffAt.secondFundamentalForm_I_smul_right`,
  `ContDiffAt.secondFundamentalForm_I_smul_I_smul`: the identities displayed above.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Chapter IX.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer, 2018, Chapter 8.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

section General

variable {𝕜 V W E : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- The **second fundamental form** of `i : V → E` at `x`: the component of the second derivative
`D²i(x)(v, w)` orthogonal to the tangent space `(Di(x)).range`. For an immersion this is the
second fundamental form of the parametrised submanifold, evaluated on `Di(x) v` and `Di(x) w`. -/
noncomputable def secondFundamentalForm (i : V → E) (x : V) : V →L[𝕜] V →L[𝕜] E :=
  ContinuousLinearMap.compL 𝕜 V E E (fderiv 𝕜 i x).rangeᗮ.starProjection ∘L
    fderiv 𝕜 (fderiv 𝕜 i) x

/-- The second fundamental form is the normal projection of the second derivative. -/
theorem secondFundamentalForm_apply (i : V → E) (x : V) (v w : V) :
    secondFundamentalForm 𝕜 i x v w =
      (fderiv 𝕜 i x).rangeᗮ.starProjection (fderiv 𝕜 (fderiv 𝕜 i) x v w) :=
  (rfl)

/-- The second fundamental form takes values in the normal space. -/
@[simp]
theorem secondFundamentalForm_apply_mem_orthogonal (i : V → E) (x : V) (v w : V) :
    secondFundamentalForm 𝕜 i x v w ∈ (fderiv 𝕜 i x).rangeᗮ :=
  Submodule.starProjection_apply_mem _ _

/-- Paired with a normal vector `ν`, the second fundamental form agrees with the second
derivative: `⟪ν, B(v, w)⟫ = ⟪ν, D²i(x)(v, w)⟫`. -/
theorem inner_secondFundamentalForm_apply_of_mem_orthogonal {i : V → E} {x : V} {ν : E}
    (hν : ν ∈ (fderiv 𝕜 i x).rangeᗮ) (v w : V) :
    ⟪ν, secondFundamentalForm 𝕜 i x v w⟫_𝕜 = ⟪ν, fderiv 𝕜 (fderiv 𝕜 i) x v w⟫_𝕜 := by
  rw [secondFundamentalForm_apply, ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hν]

/-- The second fundamental form of a `C²` map is symmetric. -/
theorem _root_.ContDiffAt.secondFundamentalForm_apply_comm {i : V → E} {x : V}
    (hi : ContDiffAt 𝕜 2 i x) (v w : V) :
    secondFundamentalForm 𝕜 i x v w = secondFundamentalForm 𝕜 i x w v := by
  rw [secondFundamentalForm_apply, secondFundamentalForm_apply,
    (hi.isSymmSndFDerivAt (by simp)).eq v w]

variable [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-- **Invariance under reparametrisation.** If `φ : W → V` is `C²` at `y` with surjective
derivative, then the second fundamental form of `i ∘ φ` at `y` is that of `i` at `φ y`, evaluated
on the images under `Dφ(y)`. The term `Di(D²φ(v, w))` of the second-order chain rule is tangent,
and the normal projection removes it. -/
theorem _root_.ContDiffAt.secondFundamentalForm_comp {i : V → E} {φ : W → V} {y : W}
    (hi : ContDiffAt 𝕜 2 i (φ y)) (hφ : ContDiffAt 𝕜 2 φ y)
    (hsurj : Function.Surjective (fderiv 𝕜 φ y)) (v w : W) :
    secondFundamentalForm 𝕜 (i ∘ φ) y v w =
      secondFundamentalForm 𝕜 i (φ y) (fderiv 𝕜 φ y v) (fderiv 𝕜 φ y w) := by
  have hrange : (fderiv 𝕜 (i ∘ φ) y).range = (fderiv 𝕜 i (φ y)).range := by
    rw [fderiv_comp y (hi.differentiableAt (by norm_num)) (hφ.differentiableAt (by norm_num)),
      ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.mpr hsurj
  rw [secondFundamentalForm_apply, secondFundamentalForm_apply, fderiv_fderiv_comp_apply hi hφ,
    map_add]
  -- The normal space depends on the submodule only, so `simp` can rewrite it under the
  -- projection, whose `HasOrthogonalProjection` argument is a proposition.
  simp only [hrange, add_eq_left, Submodule.starProjection_apply_eq_zero_iff]
  exact Submodule.le_orthogonal_orthogonal _ (LinearMap.mem_range_self _ _)

end General

section Complex

/-! ### Holomorphic maps

The real inner product `re ⟪x, y⟫` on a complex inner product space is enabled locally; the real
second fundamental form below is taken with respect to it. -/

open Complex

attribute [local instance] InnerProductSpace.complexToReal

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] {i : V → E} {x : V}

/-- The real normal space of a complex-differentiable map, for the real inner product
`re ⟪x, y⟫`, is its complex normal space; in particular it is stable under multiplication
by `I`. -/
theorem _root_.DifferentiableAt.orthogonal_range_fderiv_restrictScalars
    (hi : DifferentiableAt ℂ i x) :
    (fderiv ℝ i x).rangeᗮ = (fderiv ℂ i x).rangeᗮ.restrictScalars ℝ := by
  rw [hi.range_fderiv_restrictScalars ℝ, Submodule.orthogonal_restrictScalars]

variable [FiniteDimensional ℂ V]

/-- The real second fundamental form of a holomorphic map is its complex second fundamental form.
In particular it is complex bilinear. -/
theorem _root_.ContDiffAt.secondFundamentalForm_restrictScalars_apply (hi : ContDiffAt ℂ 2 i x)
    (v w : V) : secondFundamentalForm ℝ i x v w = secondFundamentalForm ℂ i x v w := by
  rw [secondFundamentalForm_apply, secondFundamentalForm_apply,
    hi.fderiv_fderiv_restrictScalars_apply]
  -- As in `ContDiffAt.secondFundamentalForm_comp`, `simp` rewrites the normal space under the
  -- projection.
  simp only [(hi.differentiableAt (by norm_num)).orthogonal_range_fderiv_restrictScalars,
    Submodule.starProjection_restrictScalars_apply]

/-- The real second fundamental form of a holomorphic map satisfies `B(Jv, w) = J B(v, w)`. -/
@[simp]
theorem _root_.ContDiffAt.secondFundamentalForm_I_smul_left (hi : ContDiffAt ℂ 2 i x) (v w : V) :
    secondFundamentalForm ℝ i x (I • v) w = I • secondFundamentalForm ℝ i x v w := by
  simp [hi.secondFundamentalForm_restrictScalars_apply]

/-- The real second fundamental form of a holomorphic map satisfies `B(v, Jw) = J B(v, w)`. -/
@[simp]
theorem _root_.ContDiffAt.secondFundamentalForm_I_smul_right (hi : ContDiffAt ℂ 2 i x)
    (v w : V) :
    secondFundamentalForm ℝ i x v (I • w) = I • secondFundamentalForm ℝ i x v w := by
  simp [hi.secondFundamentalForm_restrictScalars_apply]

/-- The real second fundamental form of a holomorphic map satisfies `B(Jv, Jw) = -B(v, w)`. -/
theorem _root_.ContDiffAt.secondFundamentalForm_I_smul_I_smul (hi : ContDiffAt ℂ 2 i x)
    (v w : V) :
    secondFundamentalForm ℝ i x (I • v) (I • w) = -secondFundamentalForm ℝ i x v w := by
  simp [hi.secondFundamentalForm_restrictScalars_apply, smul_smul]

end Complex

end TauCeti
