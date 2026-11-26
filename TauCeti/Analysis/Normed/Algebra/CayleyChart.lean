/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Algebra.Ring.CayleyChart
import Mathlib.Tactic.NoncommRing

/-!
# The Cayley chart on square roots of `-1` in a Banach algebra

Let `j` be a square root of `-1` in a normed algebra `A` with summable geometric series in which
`2` is a unit, for instance a real Banach algebra of endomorphisms or of endomorphism fields. The
Cayley parametrization `cayleyParam j η = (1 + η)⁻¹ * j * (1 + η)` and the Cayley coordinate
`cayleyCoord j J = (j - J) * (j + J)⁻¹` of `TauCeti.Algebra.Ring.CayleyChart` are mutually inverse
between the `j`-antilinear `η` with `1 + η` invertible and the square roots `J` of `-1` with
`j + J` invertible. This file shows that this is a chart of the space of square roots of `-1`
around `j`, and that its derivative intertwines left multiplication by `j` with left
multiplication by the image point; over the reals this says that the chart is holomorphic.

* Both maps are analytic on the open sets where their denominators are invertible, so the
  bijection is a homeomorphism and the transition maps between the charts at two square roots of
  `-1` are analytic.
* The derivative of `cayleyParam j` at `η` is `ζ ↦ (1 + η)⁻¹ * (j * ζ - ζ * J)`, where
  `J = cayleyParam j η`. It takes values in the tangent space `{X | X * J + J * X = 0}` of the
  square roots of `-1` at `J`, and at `η = 0` it is `ζ ↦ 2 * (j * ζ)` on the `j`-antilinear `ζ`.
* **Holomorphy.** Over any scalar field the derivative intertwines the left multiplication
  operators `ζ ↦ j * ζ` and `X ↦ J * X`: it carries `j * ζ` to `J` times the image of `ζ`. For a
  real normed algebra, these operators make the `j`-antilinear elements and the tangent space at
  `J` complex vector spaces, with multiplication by `i`, and the derivative is complex linear.

For endomorphism fields of a surface, `cayleyParam` is the formula by which Robbin and Salamon
parametrize local holomorphic slices of the space of complex structures; the statements here are
the pointwise and Banach-algebraic content of that construction, for any normed algebra in which
the relevant fields live.

The Cayley coordinate `cayleyCoord j` has derivative `T ↦ -(1 + cayleyCoord j J) T (j + J)⁻¹` at
every `J` with `j + J` invertible (`TauCeti.hasFDerivAt_cayleyCoord`); at the base point `1` this is
`T ↦ -2 (1 + x)⁻¹ T (1 + x)⁻¹` (`TauCeti.hasFDerivAt_cayleyCoord_one`), which applies in particular
to the matrix algebra used to construct unitary-group charts.

## Main statements

* `TauCeti.analyticOnNhd_cayleyParam`, `TauCeti.analyticOnNhd_cayleyCoord`: analyticity of the two
  maps; `TauCeti.analyticAt_uncurry_cayleyParam`, `TauCeti.analyticAt_uncurry_cayleyCoord`: joint
  analyticity in the base point; and `TauCeti.analyticOnNhd_cayleyCoord_comp_cayleyParam`:
  analyticity of the transition maps.
* `TauCeti.cayleyHomeomorph`: the Cayley chart as a homeomorphism.
* `TauCeti.hasFDerivAt_cayleyParam`, `TauCeti.fderiv_cayleyParam_apply`: the derivative of the
  parametrization, and `TauCeti.fderiv_cayleyParam_zero_apply`: its value `2 * (j * ζ)` at `0`.
* `TauCeti.fderiv_cayleyParam_apply_mul_add_mul`: the derivative is tangent to the square roots of
  `-1`.
* `ContinuousLinearMap.coe_cayleyParam`, `ContinuousLinearMap.coe_cayleyCoord`: on a
  finite-dimensional space both maps commute with forgetting continuity of endomorphisms.
* `TauCeti.fderiv_cayleyParam_apply_mul_left`: the derivative intertwines `ζ ↦ j * ζ` and
  `X ↦ cayleyParam j η * X`; for a real normed algebra, it is complex linear for these complex
  structures.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, §7 (holomorphic local slices of the space of complex
  structures).
-/

public section

noncomputable section

open Topology

namespace TauCeti

section Continuity

variable {A : Type*} [NormedRing A] [HasSummableGeomSeries A] {j : A}

/-- The Cayley parametrization is continuous where `1 + η` is invertible. -/
lemma continuousOn_cayleyParam : ContinuousOn (cayleyParam j) {η : A | IsUnit (1 + η)} := by
  rw [cayleyParam_eq_fun]
  intro η hη
  have h1 : ContinuousAt (fun η : A ↦ 1 + η) η := (continuous_const.add continuous_id).continuousAt
  exact ((((NormedRing.inverse_continuousAt hη.unit).comp_of_eq h1 hη.unit_spec.symm).mul
    continuousAt_const).mul h1).continuousWithinAt

/-- The Cayley coordinate is continuous where `j + J` is invertible. -/
lemma continuousOn_cayleyCoord : ContinuousOn (cayleyCoord j) {J : A | IsUnit (j + J)} := by
  rw [cayleyCoord_eq_fun]
  intro J hJ
  exact ((continuous_const.sub continuous_id).continuousAt.mul
    ((NormedRing.inverse_continuousAt hJ.unit).comp_of_eq
      (continuous_const.add continuous_id).continuousAt hJ.unit_spec.symm)).continuousWithinAt

variable (j) in
/-- **The Cayley chart as a homeomorphism.** For a square root `j` of `-1` in a normed ring with
summable geometric series in which `2` is a unit, `cayleyParam j` is a homeomorphism from the
`j`-antilinear `η` with `1 + η` invertible onto the square roots `J` of `-1` with `j + J`
invertible, with inverse `cayleyCoord j`. -/
def cayleyHomeomorph (h2 : IsUnit (2 : A)) (hj : j * j = -1) :
    {η : A // η * j = -(j * η) ∧ IsUnit (1 + η)} ≃ₜ {J : A // J * J = -1 ∧ IsUnit (j + J)} where
  toEquiv := cayleyEquiv j h2 hj
  continuous_toFun := continuous_induced_rng.2 <|
    (continuousOn_cayleyParam.comp_continuous continuous_subtypeVal fun η ↦ η.property.2).congr
      fun η ↦ (coe_cayleyEquiv_apply h2 hj η).symm
  continuous_invFun := continuous_induced_rng.2 <|
    (continuousOn_cayleyCoord.comp_continuous continuous_subtypeVal fun J ↦ J.property.2).congr
      fun J ↦ (coe_cayleyEquiv_symm_apply h2 hj J).symm

/-- The underlying equivalence of `cayleyHomeomorph` is `cayleyEquiv`. -/
@[simp]
lemma cayleyHomeomorph_toEquiv (h2 : IsUnit (2 : A)) (hj : j * j = -1) :
    (cayleyHomeomorph j h2 hj).toEquiv = cayleyEquiv j h2 hj := (rfl)

/-- The underlying map of `cayleyHomeomorph` is `cayleyParam`. -/
@[simp]
lemma coe_cayleyHomeomorph_apply (h2 : IsUnit (2 : A)) (hj : j * j = -1)
    (η : {η : A // η * j = -(j * η) ∧ IsUnit (1 + η)}) :
    (cayleyHomeomorph j h2 hj η : A) = cayleyParam j η :=
  coe_cayleyEquiv_apply h2 hj η

/-- The underlying map of the inverse of `cayleyHomeomorph` is `cayleyCoord`. -/
@[simp]
lemma coe_cayleyHomeomorph_symm_apply (h2 : IsUnit (2 : A)) (hj : j * j = -1)
    (J : {J : A // J * J = -1 ∧ IsUnit (j + J)}) :
    ((cayleyHomeomorph j h2 hj).symm J : A) = cayleyCoord j J :=
  coe_cayleyEquiv_symm_apply h2 hj J

end Continuity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
  [HasSummableGeomSeries A] {j η J : A}

/-! ### Analyticity -/

/-- The Cayley parametrization is analytic at every `η` with `1 + η` invertible. -/
theorem analyticAt_cayleyParam (hη : IsUnit (1 + η)) : AnalyticAt 𝕜 (cayleyParam j) η := by
  rw [cayleyParam_eq_fun]
  have h1 : AnalyticAt 𝕜 (fun η : A ↦ 1 + η) η := analyticAt_const.add analyticAt_id
  exact (((analyticOnNhd_inverse _ hη).comp h1).mul analyticAt_const).mul h1

/-- The Cayley parametrization is analytic on the open set where `1 + η` is invertible. -/
theorem analyticOnNhd_cayleyParam : AnalyticOnNhd 𝕜 (cayleyParam j) {η : A | IsUnit (1 + η)} :=
  fun _ hη ↦ analyticAt_cayleyParam hη

/-- The Cayley coordinate is analytic at every `J` with `j + J` invertible. -/
theorem analyticAt_cayleyCoord (hJ : IsUnit (j + J)) : AnalyticAt 𝕜 (cayleyCoord j) J := by
  rw [cayleyCoord_eq_fun]
  exact (analyticAt_const.sub analyticAt_id).mul
    ((analyticOnNhd_inverse _ hJ).comp (analyticAt_const.add analyticAt_id))

/-- The Cayley coordinate is analytic on the open set where `j + J` is invertible. -/
theorem analyticOnNhd_cayleyCoord : AnalyticOnNhd 𝕜 (cayleyCoord j) {J : A | IsUnit (j + J)} :=
  fun _ hJ ↦ analyticAt_cayleyCoord hJ

/-- The Cayley parametrization is analytic jointly in the base point `j` and the coordinate `η`,
at every `(j, η)` with `1 + η` invertible. This is what makes the Cayley chart of a family of base
points, such as the values of an almost complex structure along a manifold, regular. -/
theorem analyticAt_uncurry_cayleyParam (hη : IsUnit (1 + η)) :
    AnalyticAt 𝕜 (Function.uncurry (cayleyParam (A := A))) (j, η) := by
  have h : Function.uncurry (cayleyParam (A := A)) =
      fun p : A × A ↦ Ring.inverse (1 + p.2) * p.1 * (1 + p.2) :=
    funext fun p ↦ cayleyParam_def p.1 p.2
  have h1 : AnalyticAt 𝕜 (fun p : A × A ↦ 1 + p.2) (j, η) := analyticAt_const.add analyticAt_snd
  rw [h]
  exact ((AnalyticAt.comp (g := Ring.inverse) (f := fun p : A × A ↦ 1 + p.2) (x := (j, η))
    (analyticOnNhd_inverse _ hη) h1).mul analyticAt_fst).mul h1

/-- The Cayley coordinate is analytic jointly in the base point `j` and the point `J`, at every
`(j, J)` with `j + J` invertible. -/
theorem analyticAt_uncurry_cayleyCoord (hJ : IsUnit (j + J)) :
    AnalyticAt 𝕜 (Function.uncurry (cayleyCoord (A := A))) (j, J) := by
  have h : Function.uncurry (cayleyCoord (A := A)) =
      fun p : A × A ↦ (p.1 - p.2) * Ring.inverse (p.1 + p.2) :=
    funext fun p ↦ cayleyCoord_def p.1 p.2
  rw [h]
  exact (analyticAt_fst.sub analyticAt_snd).mul (AnalyticAt.comp (g := Ring.inverse)
    (f := fun p : A × A ↦ p.1 + p.2) (x := (j, J)) (analyticOnNhd_inverse _ hJ)
    (analyticAt_fst.add analyticAt_snd))

/-- **Analytic transition maps.** The transition from the Cayley chart at `j₀` to the Cayley
chart at `j₁` is analytic on its (open) domain of definition. -/
theorem analyticOnNhd_cayleyCoord_comp_cayleyParam (j₀ j₁ : A) :
    AnalyticOnNhd 𝕜 (cayleyCoord j₁ ∘ cayleyParam j₀)
      {η : A | IsUnit (1 + η) ∧ IsUnit (j₁ + cayleyParam j₀ η)} :=
  fun _ hη ↦ (analyticAt_cayleyCoord hη.2).comp (analyticAt_cayleyParam hη.1)

/-! ### Derivatives -/

/-- The derivative of the Cayley coordinate `cayleyCoord j` at `J` with `j + J` a unit is
`T ↦ -(1 + cayleyCoord j J) T (j + J)⁻¹`. -/
theorem hasFDerivAt_cayleyCoord (hJ : IsUnit (j + J)) :
    HasFDerivAt (cayleyCoord j)
      (-ContinuousLinearMap.mulLeftRight 𝕜 A (1 + cayleyCoord j J) (Ring.inverse (j + J))) J := by
  have hinv : HasFDerivAt (fun y : A ↦ Ring.inverse (j + y))
      (-ContinuousLinearMap.mulLeftRight 𝕜 A
        (Ring.inverse (j + J)) (Ring.inverse (j + J))) J := by
    have h := hasFDerivAt_ringInverse (𝕜 := 𝕜) hJ.unit
    rw [← Ring.inverse_unit, hJ.unit_spec] at h
    exact (h.comp J ((hasFDerivAt_id J).const_add j)).congr_fderiv
      (ContinuousLinearMap.comp_id _)
  rw [cayleyCoord_eq_fun]
  refine (((hasFDerivAt_id J).const_sub j).mul' hinv).congr_fderiv ?_
  ext t
  simp only [add_apply, neg_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_apply, id_eq, smul_eq_mul, op_smul_eq_mul]
  noncomm_ring

/-- The derivative of the Cayley transform `cayleyCoord 1` in a normed algebra is
`T ↦ -2 (1 + x)⁻¹ T (1 + x)⁻¹` where `1 + x` is a unit: the case `j = 1` of
`TauCeti.hasFDerivAt_cayleyCoord`. -/
theorem hasFDerivAt_cayleyCoord_one {x : A} (hx : IsUnit (1 + x)) :
    HasFDerivAt (cayleyCoord 1)
      (-(2 : 𝕜) • ContinuousLinearMap.mulLeftRight 𝕜 A
        (Ring.inverse (1 + x)) (Ring.inverse (1 + x))) x := by
  refine (hasFDerivAt_cayleyCoord hx).congr_fderiv ?_
  rw [one_add_cayleyCoord hx, mul_one]
  ext t
  simp only [neg_smul, two_smul, neg_apply, add_apply, ContinuousLinearMap.mulLeftRight_apply,
    two_mul, add_mul]

/-- The derivative of `cayleyParam j` at `η` with `1 + η` invertible: the continuous linear map
`ζ ↦ (1 + η)⁻¹ * (j * ζ - ζ * cayleyParam j η)`. -/
theorem hasFDerivAt_cayleyParam (hη : IsUnit (1 + η)) :
    HasFDerivAt (cayleyParam j)
      (ContinuousLinearMap.mul 𝕜 A (Ring.inverse (1 + η)) ∘L
        (ContinuousLinearMap.mul 𝕜 A j - (ContinuousLinearMap.mul 𝕜 A).flip (cayleyParam j η)))
      η := by
  obtain ⟨u, hu⟩ := hη
  have hadd : HasFDerivAt (fun η : A ↦ 1 + η) (ContinuousLinearMap.id 𝕜 A) η :=
    (hasFDerivAt_id η).const_add 1
  have hinv : HasFDerivAt (fun η : A ↦ Ring.inverse (1 + η))
      (-ContinuousLinearMap.mulLeftRight 𝕜 A ↑u⁻¹ ↑u⁻¹) η := by
    have := hasFDerivAt_ringInverse (𝕜 := 𝕜) u
    rw [hu] at this
    exact (this.comp η hadd).congr_fderiv (ContinuousLinearMap.comp_id _)
  rw [cayleyParam_eq_fun]
  refine ((hinv.mul_const' j).mul' hadd).congr_fderiv ?_
  ext ζ
  simp [← hu, mul_assoc, sub_eq_add_neg]

/-- The derivative of `cayleyParam j` at `η` with `1 + η` invertible is
`ζ ↦ (1 + η)⁻¹ * (j * ζ - ζ * cayleyParam j η)`. -/
theorem fderiv_cayleyParam_apply (hη : IsUnit (1 + η)) (ζ : A) :
    fderiv 𝕜 (cayleyParam j) η ζ = Ring.inverse (1 + η) * (j * ζ - ζ * cayleyParam j η) := by
  rw [(hasFDerivAt_cayleyParam hη).fderiv]
  simp [mul_sub]

/-- At `0` the derivative of `cayleyParam j` is `ζ ↦ 2 * (j * ζ)` on the `j`-antilinear `ζ`. -/
theorem fderiv_cayleyParam_zero_apply {ζ : A} (hζ : ζ * j = -(j * ζ)) :
    fderiv 𝕜 (cayleyParam j) 0 ζ = 2 * (j * ζ) := by
  rw [fderiv_cayleyParam_apply (by simp)]
  simp [hζ, two_mul]

/-- **The derivative is tangent to the square roots of `-1`.** For `j * j = -1` and `1 + η`
invertible, every value `X` of the derivative of `cayleyParam j` at `η` anticommutes with
`J = cayleyParam j η`: `X * J + J * X = 0`. -/
theorem fderiv_cayleyParam_apply_mul_add_mul (hj : j * j = -1) (hη : IsUnit (1 + η)) (ζ : A) :
    fderiv 𝕜 (cayleyParam j) η ζ * cayleyParam j η +
      cayleyParam j η * fderiv 𝕜 (cayleyParam j) η ζ = 0 := by
  have hJJ := cayleyParam_mul_self hj hη
  have hc := cayleyParam_mul_inverse (j := j) hη
  rw [fderiv_cayleyParam_apply hη]
  generalize cayleyParam j η = J at hJJ hc ⊢
  generalize Ring.inverse (1 + η) = v at hc ⊢
  rw [mul_assoc v, ← mul_assoc J, hc, mul_assoc v j, ← mul_add]
  convert mul_zero v using 2
  calc (j * ζ - ζ * J) * J + j * (j * ζ - ζ * J)
      = j * ζ * J - ζ * (J * J) + j * j * ζ - j * ζ * J := by noncomm_ring
    _ = 0 := by rw [hJJ, hj]; noncomm_ring

/-- **Holomorphy of the Cayley parametrization.** For `1 + η` invertible, the derivative of
`cayleyParam j` at `η` carries `j * ζ` to `cayleyParam j η` times the image of `ζ`, that is, it
intertwines left multiplication by `j` and by `cayleyParam j η`. When `𝕜 = ℝ` and `j * j = -1`,
these left multiplications are complex structures on the `j`-antilinear elements and on the
tangent space at `cayleyParam j η` (`fderiv_cayleyParam_apply_mul_add_mul`), and this says that
the derivative is complex linear. -/
theorem fderiv_cayleyParam_apply_mul_left (hη : IsUnit (1 + η)) (ζ : A) :
    fderiv 𝕜 (cayleyParam j) η (j * ζ) =
      cayleyParam j η * fderiv 𝕜 (cayleyParam j) η ζ := by
  have hc := cayleyParam_mul_inverse (j := j) hη
  rw [fderiv_cayleyParam_apply hη, fderiv_cayleyParam_apply hη]
  generalize cayleyParam j η = J at hc ⊢
  generalize Ring.inverse (1 + η) = v at hc ⊢
  rw [← mul_assoc J, hc, mul_assoc v j]
  congr 1
  noncomm_ring

end TauCeti

/-! ### Forgetting continuity in finite dimension -/

namespace ContinuousLinearMap

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {V : Type*}
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- On a finite-dimensional space, forgetting continuity of endomorphisms commutes with the Cayley
parametrization. -/
theorem coe_cayleyParam (j η : V →L[𝕜] V) :
    ((cayleyParam j η : V →L[𝕜] V) : V →ₗ[𝕜] V) = cayleyParam (j : V →ₗ[𝕜] V) η :=
  -- The inverse of `Module.End.toContinuousLinearMap V` is the coercion to linear maps.
  map_cayleyParam (Module.End.toContinuousLinearMap V).symm j η

/-- On a finite-dimensional space, forgetting continuity of endomorphisms commutes with the Cayley
coordinate. -/
theorem coe_cayleyCoord (j J : V →L[𝕜] V) :
    ((cayleyCoord j J : V →L[𝕜] V) : V →ₗ[𝕜] V) = cayleyCoord (j : V →ₗ[𝕜] V) J :=
  -- The inverse of `Module.End.toContinuousLinearMap V` is the coercion to linear maps.
  map_cayleyCoord (Module.End.toContinuousLinearMap V).symm j J

end ContinuousLinearMap
