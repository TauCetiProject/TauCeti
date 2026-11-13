/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Linearization
public import TauCeti.Geometry.Symplectic.AlmostComplex.Quotient
public import TauCeti.Geometry.Symplectic.JHolomorphic.Symbol

/-!
# The complex normal quotient and its Cauchy–Riemann symbol

The derivative of a pseudoholomorphic map has invariant image. Thus its actual normal
quotient inherits an almost complex structure. The normal linearization takes values in
complex-antilinear maps into the normal quotient, and its Leibniz rule is the real Cauchy–Riemann
symbol for this quotient structure. Over a source of real dimension two, the symbol is bijective
at every nonzero real covector by `cauchyRiemannSymbolAntilinear_bijective`.

No complement, metric or integrability assumption on the ambient structure is used. The
statements apply even without immersivity; for an immersion the quotient is the normal fiber.
These local statements do not construct a global normal bundle or its Fredholm realization.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1.
-/

public section

noncomputable section

namespace TauCeti

open scoped Topology

variable {U V : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The almost complex structure on the actual normal quotient of a pseudoholomorphic map. -/
def normalComplexStructure (j : AlmostComplexStructure U) (J : AlmostComplexStructure V)
    (u : U → V) (x : U) (hu : IsComplexLinearMap j J (fderiv ℝ u x).toLinearMap) :
    AlmostComplexStructure (V ⧸ (fderiv ℝ u x).toLinearMap.range) :=
  J.quotient (fderiv ℝ u x).toLinearMap.range (by
    rintro _ ⟨v, rfl⟩
    exact ⟨j v, (isComplexLinearMap_iff_apply _ _ _).1 hu v⟩)

/-- The normal complex structure is induced by the ambient structure on the derivative quotient. -/
theorem normalComplexStructure_def (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : IsComplexLinearMap j J (fderiv ℝ u x).toLinearMap) :
    normalComplexStructure j J u x hu =
      J.quotient (fderiv ℝ u x).toLinearMap.range (by
        rintro _ ⟨v, rfl⟩
        exact ⟨j v, (isComplexLinearMap_iff_apply _ _ _).1 hu v⟩) := (rfl)

/-- Applying the normal complex structure is applying `J` to any ambient lift. -/
@[simp]
theorem normalComplexStructure_mk (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : IsComplexLinearMap j J (fderiv ℝ u x).toLinearMap) (v : V) :
    normalComplexStructure j J u x hu (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (J v) := by
  simp only [normalComplexStructure, AlmostComplexStructure.quotient_mk]

/-- The projection to the normal quotient is complex-linear. -/
@[simp]
theorem isComplexLinearMap_normalComplexStructure_mkQ (j : AlmostComplexStructure U)
    (J : AlmostComplexStructure V) (u : U → V) (x : U)
    (hu : IsComplexLinearMap j J (fderiv ℝ u x).toLinearMap) :
    IsComplexLinearMap J (normalComplexStructure j J u x hu)
      (fderiv ℝ u x).toLinearMap.range.mkQ := by
  rw [normalComplexStructure_def]
  exact J.isComplexLinearMap_mkQ _ _

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
    IsComplexAntilinear j₀.toLinearMap (normalComplexStructure j₀ J₀ u x hu).toLinearMap
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
  apply isComplexAntilinear_of_apply
  intro v
  simpa only [normalCauchyRiemannLinearization_apply, Submodule.mkQ_apply,
    normalComplexStructure_mk, Submodule.Quotient.mk_neg, ContinuousLinearMap.coe_coe] using
      congrArg (fderiv ℝ u x).toLinearMap.range.mkQ (h.apply v)

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
      cauchyRiemannSymbol j₀ (normalComplexStructure j₀ J₀ u x hu) (fderiv ℝ f x).toLinearMap
        ((fderiv ℝ u x).toLinearMap.range.mkQ (ξ x)) := by
  have h := congrArg (fun L : U →ₗ[ℝ] V ↦ (fderiv ℝ u x).toLinearMap.range.mkQ.comp L)
    (cauchyRiemannLinearization_fun_smul_eq_smul_add_cauchyRiemannSymbol j₀ J₀ u ξ f x hj hJ₀ hf hξ)
  rw [LinearMap.comp_add, LinearMap.comp_smul,
    (isComplexLinearMap_normalComplexStructure_mkQ j₀ J₀ u x hu).comp_cauchyRiemannSymbol] at h
  ext v
  simpa only [normalCauchyRiemannLinearization_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe] using
    LinearMap.congr_fun h v

end TauCeti
