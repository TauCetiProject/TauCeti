/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import TauCeti.Algebra.Ring.CayleyChart
import Mathlib.Tactic.NoncommRing

/-!
# The Cayley chart on square roots of `-1` in a Banach algebra

Let `j` be a square root of `-1` in a normed algebra `A` with summable geometric series, for
instance a Banach algebra of endomorphisms or of endomorphism fields. The Cayley parametrization
`cayleyParam j η = (1 + η)⁻¹ * j * (1 + η)` and the Cayley coordinate
`cayleyCoord j J = (j - J) * (j + J)⁻¹` of `TauCeti.Algebra.Ring.CayleyChart` are mutually inverse
between the `j`-antilinear `η` with `1 + η` invertible and the square roots `J` of `-1` with
`j + J` invertible. This file shows that this is a chart of the space of square roots of `-1`
around `j`, and that it is holomorphic.

* Both maps are analytic on the open sets where their denominators are invertible, so the
  bijection is a homeomorphism and the transition maps between the charts at two square roots of
  `-1` are analytic.
* The derivative of `cayleyParam j` at `η` is `ζ ↦ (1 + η)⁻¹ * (j * ζ - ζ * J)`, where
  `J = cayleyParam j η`. It takes values in the tangent space `{X | X * J + J * X = 0}` of the
  square roots of `-1` at `J`, and at `η = 0` it is `ζ ↦ 2 * (j * ζ)` on the `j`-antilinear `ζ`.
* **Holomorphy.** The space of `j`-antilinear elements is a complex vector space, with
  multiplication by `i` given by `ζ ↦ j * ζ`, and the tangent space at `J` is one with
  `X ↦ J * X`. The derivative intertwines them: it carries `j * ζ` to `J` times the image of `ζ`.

For endomorphism fields of a surface, `cayleyParam` is the formula by which Robbin and Salamon
parametrize local holomorphic slices of the space of complex structures; the statements here are
the pointwise and Banach-algebraic content of that construction, for any normed algebra in which
the relevant fields live.

## Main statements

* `TauCeti.analyticOnNhd_cayleyParam`, `TauCeti.analyticOnNhd_cayleyCoord`: analyticity of the two
  maps, and `TauCeti.analyticOnNhd_cayleyCoord_comp_cayleyParam`: analyticity of the transition
  maps.
* `TauCeti.cayleyHomeomorph`: the Cayley chart as a homeomorphism.
* `TauCeti.hasFDerivAt_cayleyParam`, `TauCeti.fderiv_cayleyParam_apply`: the derivative of the
  parametrization, and `TauCeti.fderiv_cayleyParam_zero_apply`: its value `2 * (j * ζ)` at `0`.
* `TauCeti.fderiv_cayleyParam_apply_mul_add_mul`: the derivative is tangent to the square roots of
  `-1`.
* `TauCeti.fderiv_cayleyParam_apply_mul_left`: the derivative is complex linear for the complex
  structures `ζ ↦ j * ζ` and `X ↦ cayleyParam j η * X`.

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
  rw [show cayleyParam j = fun η ↦ Ring.inverse (1 + η) * j * (1 + η) from
    funext (cayleyParam_def j)]
  rintro η ⟨u, hu⟩
  refine ContinuousAt.continuousWithinAt ?_
  have hinv : ContinuousAt (fun η : A ↦ Ring.inverse (1 + η)) η :=
    (hu ▸ NormedRing.inverse_continuousAt u).comp (continuous_const.add continuous_id).continuousAt
  exact (hinv.mul continuousAt_const).mul (continuous_const.add continuous_id).continuousAt

/-- The Cayley coordinate is continuous where `j + J` is invertible. -/
lemma continuousOn_cayleyCoord : ContinuousOn (cayleyCoord j) {J : A | IsUnit (j + J)} := by
  rw [show cayleyCoord j = fun J ↦ (j - J) * Ring.inverse (j + J) from funext (cayleyCoord_def j)]
  rintro J ⟨u, hu⟩
  refine ContinuousAt.continuousWithinAt ?_
  have hinv : ContinuousAt (fun J : A ↦ Ring.inverse (j + J)) J :=
    (hu ▸ NormedRing.inverse_continuousAt u).comp (continuous_const.add continuous_id).continuousAt
  exact ((continuous_const.sub continuous_id).continuousAt).mul hinv

variable (j) in
/-- **The Cayley chart as a homeomorphism.** For a square root `j` of `-1` in a normed ring with
summable geometric series in which `2` is a unit, `cayleyParam j` is a homeomorphism from the
`j`-antilinear `η` with `1 + η` invertible onto the square roots `J` of `-1` with `j + J`
invertible, with inverse `cayleyCoord j`. -/
def cayleyHomeomorph (h2 : IsUnit (2 : A)) (hj : j * j = -1) :
    {η : A // η * j = -(j * η) ∧ IsUnit (1 + η)} ≃ₜ {J : A // J * J = -1 ∧ IsUnit (j + J)} where
  toEquiv := cayleyEquiv j h2 hj
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    rw [Equiv.toFun_as_coe, show Subtype.val ∘ cayleyEquiv j h2 hj = cayleyParam j ∘ Subtype.val
      from funext (coe_cayleyEquiv_apply h2 hj)]
    exact continuousOn_cayleyParam.comp_continuous continuous_subtype_val fun η ↦ η.2.2
  continuous_invFun := by
    refine continuous_induced_rng.2 ?_
    rw [Equiv.invFun_as_coe, show Subtype.val ∘ (cayleyEquiv j h2 hj).symm =
      cayleyCoord j ∘ Subtype.val from funext (coe_cayleyEquiv_symm_apply h2 hj)]
    exact continuousOn_cayleyCoord.comp_continuous continuous_subtype_val fun J ↦ J.2.2

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
  rw [show cayleyParam j = fun η ↦ Ring.inverse (1 + η) * j * (1 + η) from
    funext (cayleyParam_def j)]
  obtain ⟨u, hu⟩ := hη
  have hinv : AnalyticAt 𝕜 (fun η : A ↦ Ring.inverse (1 + η)) η :=
    (hu ▸ analyticAt_inverse (𝕜 := 𝕜) u).comp (analyticAt_const.add analyticAt_id)
  exact (hinv.mul analyticAt_const).mul (analyticAt_const.add analyticAt_id)

/-- The Cayley parametrization is analytic on the open set where `1 + η` is invertible. -/
theorem analyticOnNhd_cayleyParam : AnalyticOnNhd 𝕜 (cayleyParam j) {η : A | IsUnit (1 + η)} :=
  fun _ hη ↦ analyticAt_cayleyParam hη

/-- The Cayley coordinate is analytic at every `J` with `j + J` invertible. -/
theorem analyticAt_cayleyCoord (hJ : IsUnit (j + J)) : AnalyticAt 𝕜 (cayleyCoord j) J := by
  rw [show cayleyCoord j = fun J ↦ (j - J) * Ring.inverse (j + J) from funext (cayleyCoord_def j)]
  obtain ⟨u, hu⟩ := hJ
  have hinv : AnalyticAt 𝕜 (fun J : A ↦ Ring.inverse (j + J)) J :=
    (hu ▸ analyticAt_inverse (𝕜 := 𝕜) u).comp (analyticAt_const.add analyticAt_id)
  exact (analyticAt_const.sub analyticAt_id).mul hinv

/-- The Cayley coordinate is analytic on the open set where `j + J` is invertible. -/
theorem analyticOnNhd_cayleyCoord : AnalyticOnNhd 𝕜 (cayleyCoord j) {J : A | IsUnit (j + J)} :=
  fun _ hJ ↦ analyticAt_cayleyCoord hJ

/-- **Analytic transition maps.** The transition from the Cayley chart at `j₀` to the Cayley
chart at `j₁` is analytic on its (open) domain of definition. -/
theorem analyticOnNhd_cayleyCoord_comp_cayleyParam (j₀ j₁ : A) :
    AnalyticOnNhd 𝕜 (cayleyCoord j₁ ∘ cayleyParam j₀)
      {η : A | IsUnit (1 + η) ∧ IsUnit (j₁ + cayleyParam j₀ η)} :=
  fun _ hη ↦ (analyticAt_cayleyCoord hη.2).comp (analyticAt_cayleyParam hη.1)

/-! ### The derivative of the Cayley parametrization -/

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
  have e : cayleyParam j = (fun η : A ↦ Ring.inverse (1 + η) * j) * fun η ↦ 1 + η :=
    funext fun η ↦ cayleyParam_def j η
  rw [e]
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
  rw [fderiv_cayleyParam_apply (by simp), cayleyParam_zero, hζ, add_zero, Ring.inverse_one,
    one_mul, sub_neg_eq_add, two_mul]

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
`cayleyParam j` at `η` carries `j * ζ` to `cayleyParam j η` times the image of `ζ`. When
`j * j = -1`, left multiplication by `j` and by `cayleyParam j η` are complex structures on the
`j`-antilinear elements and on the tangent space at `cayleyParam j η`
(`fderiv_cayleyParam_apply_mul_add_mul`), and this says that the derivative is complex linear. -/
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
