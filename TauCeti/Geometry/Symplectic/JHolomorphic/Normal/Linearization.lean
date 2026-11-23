/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Linearization
public import TauCeti.Geometry.Symplectic.AlmostComplex.Quotient

/-!
# Descent of the Cauchy–Riemann linearization to normal directions

For a parametrized curve `u`, the normal fiber at `x` is the actual quotient
`V ⧸ range (du x)`. If `u` is C² at `x` and J-holomorphic on a neighbourhood of `x`,
and `J` is differentiable at `u x`, projecting the ambient Cauchy–Riemann linearization to
this quotient removes infinitesimal reparametrizations. We prove this by differentiating the
holomorphicity identity and using symmetry of the second derivative, not by assuming a
splitting of the ambient tangent space. In particular the almost complex structure need not
be integrable.

`normalCauchyRiemannLinearization` is the resulting local-coordinate expression on ambient
lifts of normal sections. Under these hypotheses, its value on a lift differentiable at `x`
is unchanged on adding `du · a` for any source vector field `a` differentiable at `x`.
Its values are complex-antilinear maps into the normal quotient, and its Leibniz rule
identifies the real Cauchy–Riemann symbol for the induced quotient structure. Over a source
of real dimension two, this symbol is bijective at every nonzero real covector by
`cauchyRiemannSymbolAntilinear_bijective`.
These statements do not require `u` to be immersive; for an embedding the quotient is its
normal fiber. Global bundle gluing, Sobolev realizations and Fredholm theory are not asserted
here. The source endomorphism is constant, as in a holomorphic coordinate on a Riemann surface.

We use the unnormalized defect `du ∘ j - J(u) ∘ du` of
`cauchyRiemannOperator`, rather than the normalized anti-complex-linear differential.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 (linearization of the Cauchy–Riemann operator).
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter
open scoped ContDiff Topology

variable {U V : Type*}
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The local normal linearization, evaluated on an ambient lift `ξ` of a normal section.
The target is the quotient by the actual tangent image, without choosing a complement. -/
def normalCauchyRiemannLinearization (j : U →L[ℝ] U) (J : V → V →L[ℝ] V)
    (u ξ : U → V) (x : U) : U →ₗ[ℝ] V ⧸ (fderiv ℝ u x).toLinearMap.range :=
  ((fderiv ℝ u x).toLinearMap.range).mkQ.comp
    (cauchyRiemannLinearization j J u ξ x).toLinearMap

/-- The normal linearization is the quotient class of the ambient linearization. -/
@[simp]
theorem normalCauchyRiemannLinearization_apply (j : U →L[ℝ] U) (J : V → V →L[ℝ] V)
    (u ξ : U → V) (x v : U) :
    normalCauchyRiemannLinearization j J u ξ x v =
      ((fderiv ℝ u x).toLinearMap.range).mkQ
        (cauchyRiemannLinearization j J u ξ x v) := (rfl)

/-- The normal linearization is additive on differentiable ambient lifts. -/
@[simp]
theorem normalCauchyRiemannLinearization_add
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (u ξ η : U → V) (x : U)
    (hξ : DifferentiableAt ℝ ξ x) (hη : DifferentiableAt ℝ η x) :
    normalCauchyRiemannLinearization j J u (ξ + η) x =
      normalCauchyRiemannLinearization j J u ξ x +
        normalCauchyRiemannLinearization j J u η x := by
  ext v
  simp [cauchyRiemannLinearization_add j J u ξ η x hξ hη]

/-- The normal linearization respects real scalar multiplication. -/
@[simp]
theorem normalCauchyRiemannLinearization_smul
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (u ξ : U → V) (x : U) (c : ℝ) :
    normalCauchyRiemannLinearization j J u (c • ξ) x =
      c • normalCauchyRiemannLinearization j J u ξ x := by
  ext v
  simp [cauchyRiemannLinearization_smul]

/-- For `u` C² at `x` and J-holomorphic near `x`, with `J` differentiable at `u x`,
infinitesimal reparametrizations differentiable at `x` vanish in the normal quotient. -/
@[simp]
theorem normalCauchyRiemannLinearization_fderiv_apply
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (u : U → V) (a : U → U) (x : U)
    (hu : ContDiffAt ℝ 2 u x) (ha : DifferentiableAt ℝ a x)
    (hJ : DifferentiableAt ℝ J (u x))
    (hhol : ∀ᶠ y in 𝓝 x, cauchyRiemannOperator j J u y = 0) :
    normalCauchyRiemannLinearization j J u (fun y ↦ fderiv ℝ u y (a y)) x = 0 := by
  ext v
  rw [normalCauchyRiemannLinearization_apply,
    cauchyRiemannLinearization_fderiv_apply j J u a x v hu ha hJ hhol]
  rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self _ _

/-- For `u` C² at `x` and J-holomorphic near `x`, with `J` differentiable at `u x`,
adding `du · a` to a differentiable ambient lift does not change the normal linearization,
provided `a` is differentiable at `x`. This is lift invariance modulo differentiable
infinitesimal reparametrizations. -/
theorem normalCauchyRiemannLinearization_add_fderiv_apply
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (u ξ : U → V) (a : U → U) (x : U)
    (hu : ContDiffAt ℝ 2 u x) (hξ : DifferentiableAt ℝ ξ x)
    (ha : DifferentiableAt ℝ a x) (hJ : DifferentiableAt ℝ J (u x))
    (hhol : ∀ᶠ y in 𝓝 x, cauchyRiemannOperator j J u y = 0) :
    normalCauchyRiemannLinearization j J u (ξ + fun y ↦ fderiv ℝ u y (a y)) x =
      normalCauchyRiemannLinearization j J u ξ x := by
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simp only [normalCauchyRiemannLinearization_add j J u ξ _ x hξ (hdu.clm_apply ha),
    normalCauchyRiemannLinearization_fderiv_apply j J u a x hu ha hJ hhol, add_zero]

/-- The first-order symbol on the normal quotient, read from the Leibniz rule. -/
theorem normalCauchyRiemannLinearization_fun_smul
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (u ξ : U → V) (f : U → ℝ) (x v : U)
    (hf : DifferentiableAt ℝ f x) (hξ : DifferentiableAt ℝ ξ x) :
    normalCauchyRiemannLinearization j J u (fun y ↦ f y • ξ y) x v =
      f x • normalCauchyRiemannLinearization j J u ξ x v +
        ((fderiv ℝ u x).toLinearMap.range).mkQ
          (fderiv ℝ f x (j v) • ξ x - fderiv ℝ f x v • J (u x) (ξ x)) := by
  simp only [normalCauchyRiemannLinearization_apply,
    cauchyRiemannLinearization_fun_smul j J u ξ f x v hf hξ, map_sub, map_add, map_smul]
  abel

/-- The normal linearization is complex-antilinear on the source tangent space, with values
in the normal quotient. This is distinct from complex linearity in the normal section, which
need not hold when `J` is not integrable. -/
theorem isComplexAntilinear_normalCauchyRiemannLinearization
    {j : U →L[ℝ] U} {J : V → V →L[ℝ] V}
    (j₀ : AlmostComplexStructure U) (J₀ : AlmostComplexStructure V)
    (u ξ : U → V) (x : U)
    (hj : j.toLinearMap = j₀.toLinearMap) (hJ₀ : (J (u x)).toLinearMap = J₀.toLinearMap)
    (hJ : ∀ᶠ y in 𝓝 (u x), ∀ v, J y (J y v) = -v)
    (hu : IsComplexLinearMap j₀ J₀ (fderiv ℝ u x).toLinearMap) :
    IsComplexAntilinear j₀.toLinearMap hu.quotientRange.toLinearMap
      (normalCauchyRiemannLinearization j J u ξ x) := by
  have hjv (v : U) : j v = j₀ v := LinearMap.congr_fun hj v
  have hJv (v : V) : J (u x) v = J₀ v := LinearMap.congr_fun hJ₀ v
  have hzero : cauchyRiemannOperator j J u x = 0 := by
    ext v
    simp only [cauchyRiemannOperator_apply, hjv, hJv, _root_.zero_apply,
      sub_eq_zero]
    exact (isComplexLinearMap_iff_apply _ _ _).1 hu v
  have h := isComplexAntilinear_cauchyRiemannLinearization ξ
    (fun v ↦ by simp only [hjv, j₀.apply_apply]) hJ hzero
  rw [hj, hJ₀] at h
  exact ((isComplexLinearMap_iff_isComplexLinear _ _ _).1
    hu.isComplexLinearMap_quotientRange_mkQ).comp_isComplexAntilinear h

/-- The Leibniz remainder of the actual normal linearization is the intrinsic real
Cauchy–Riemann symbol on the normal quotient. Together with
`cauchyRiemannSymbolAntilinear_bijective`, this identifies its elliptic symbol over a source
curve. -/
theorem normalCauchyRiemannLinearization_fun_smul_eq_smul_add_cauchyRiemannSymbol
    {j : U →L[ℝ] U} {J : V → V →L[ℝ] V}
    (j₀ : AlmostComplexStructure U) (J₀ : AlmostComplexStructure V)
    (u ξ : U → V) (f : U → ℝ) (x : U)
    (hj : j.toLinearMap = j₀.toLinearMap) (hJ₀ : (J (u x)).toLinearMap = J₀.toLinearMap)
    (hu : IsComplexLinearMap j₀ J₀ (fderiv ℝ u x).toLinearMap)
    (hf : DifferentiableAt ℝ f x) (hξ : DifferentiableAt ℝ ξ x) :
    normalCauchyRiemannLinearization j J u (fun y ↦ f y • ξ y) x =
      f x • normalCauchyRiemannLinearization j J u ξ x +
      cauchyRiemannSymbol j₀ hu.quotientRange (fderiv ℝ f x).toLinearMap
        ((fderiv ℝ u x).toLinearMap.range.mkQ (ξ x)) := by
  have h := congrArg (fun L : U →ₗ[ℝ] V ↦ (fderiv ℝ u x).toLinearMap.range.mkQ.comp L)
    (cauchyRiemannLinearization_fun_smul_eq_smul_add_cauchyRiemannSymbol j₀ J₀ u ξ f x hj hJ₀ hf hξ)
  rw [LinearMap.comp_add, LinearMap.comp_smul,
    hu.isComplexLinearMap_quotientRange_mkQ.comp_cauchyRiemannSymbol] at h
  ext v
  simpa only [normalCauchyRiemannLinearization_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe] using
    LinearMap.congr_fun h v

end TauCeti
