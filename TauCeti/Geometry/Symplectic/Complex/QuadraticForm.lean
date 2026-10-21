/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic

/-!
# Almost complex structures preserving a quadratic form

Let `Q` be a quadratic form on a real vector space `V` and `J` an almost complex structure on `V`
preserving `Q`. Then `J` preserves the polar form of `Q` and is antisymmetric for it. The
complex-linear extension of `J` to `ℂ ⊗[ℝ] V` preserves `Q.baseChange ℂ`, so its eigenspaces
`ker (J - i)` and `ker (J + i)` are totally isotropic: if `J w = ± i w` then
`Q w = Q (J w) = (± i)² Q w = -Q w`.

The pairing of the `(1,0)`- and `(0,1)`-parts `v^(1,0) = (v - i J v) / 2` and
`v^(0,1) = (v + i J v) / 2` is computed from the real polar form:

```text
polar (v^(1,0)) (w^(0,1)) = (polar Q v w + i · polar Q v (J w)) / 2.
```

## Main definitions

* `TauCeti.AlmostComplexStructure.toIsometry`: a `Q`-preserving almost complex structure as an
  isometry of `Q`.

## Main results

* `TauCeti.AlmostComplexStructure.polar_apply_apply` and
  `TauCeti.AlmostComplexStructure.polar_apply_left_eq_neg_polar_apply_right`: `J` preserves the
  polar form and is antisymmetric for it.
* `TauCeti.AlmostComplexStructure.isTotallyIsotropic_eigenspace_baseChange_I` and
  `TauCeti.AlmostComplexStructure.isTotallyIsotropic_eigenspace_baseChange_neg_I`: both
  eigenspaces of the complexified structure are totally isotropic.
* `TauCeti.AlmostComplexStructure.polar_holomorphicPart_antiholomorphicPart`: the pairing of the
  two parts in terms of the real polar form.
-/

public section

open Module.End QuadraticMap
open scoped TensorProduct

namespace TauCeti.AlmostComplexStructure

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)
  {Q : QuadraticForm ℝ V}

/-! ## `J` as an isometry of `Q` -/

/-- A `Q`-preserving almost complex structure, as an isometry of `Q`. -/
def toIsometry (hQJ : ∀ v, Q (J v) = Q v) : Q →qᵢ Q :=
  ⟨J.toLinearMap, hQJ⟩

@[simp]
theorem toIsometry_apply (hQJ : ∀ v, Q (J v) = Q v) (v : V) : J.toIsometry hQJ v = J v :=
  -- `(rfl)`, not `rfl`: the body of `toIsometry` is not `@[expose]`d.
  (rfl)

/-- The polar form of a quadratic form is preserved by a `Q`-preserving almost complex
structure. -/
@[simp]
theorem polar_apply_apply (hQJ : ∀ v, Q (J v) = Q v) (v w : V) :
    polar Q (J v) (J w) = polar Q v w := by
  simpa using (J.toIsometry hQJ).polar_apply v w

/-- The polar form of a `J`-preserved quadratic form is antisymmetric under moving `J` across:
`polar Q (J v) w = -polar Q v (J w)`. -/
theorem polar_apply_left_eq_neg_polar_apply_right (hQJ : ∀ v, Q (J v) = Q v) (v w : V) :
    polar Q (J v) w = -polar Q v (J w) := by
  have h := J.polar_apply_apply hQJ v (J w)
  rw [apply_apply, polar_neg_right] at h
  linear_combination -h

/-- The complexification of a `Q`-preserving almost complex structure preserves the
base-changed form. -/
@[simp]
theorem baseChange_apply_baseChange (hQJ : ∀ v, Q (J v) = Q v) (w : ℂ ⊗[ℝ] V) :
    Q.baseChange ℂ (J.toLinearMap.baseChange ℂ w) = Q.baseChange ℂ w := by
  have h := ((J.toIsometry hQJ).baseChange ℂ).map_app w
  rwa [← QuadraticMap.Isometry.coe_toLinearMap,
    QuadraticMap.Isometry.baseChange_toLinearMap] at h

/-! ## Isotropy of the eigenspaces -/

/-- The `i`-eigenspace of the complexification of a `Q`-preserving almost complex structure is
totally isotropic for the base-changed form. -/
theorem isTotallyIsotropic_eigenspace_baseChange_I (hQJ : ∀ v, Q (J v) = Q v) :
    (Q.baseChange ℂ).IsTotallyIsotropic
      (eigenspace (J.toLinearMap.baseChange ℂ) Complex.I) :=
  isTotallyIsotropic_iff.mpr fun _ hw => apply_eq_zero_of_apply_eq_smul
    (J.baseChange_apply_baseChange hQJ) ((isUnit_iff_ne_zero.mpr (by norm_num)).isSMulRegular _)
    (mem_eigenspace_iff.mp hw)

/-- The `-i`-eigenspace of the complexification of a `Q`-preserving almost complex structure is
totally isotropic for the base-changed form. -/
theorem isTotallyIsotropic_eigenspace_baseChange_neg_I (hQJ : ∀ v, Q (J v) = Q v) :
    (Q.baseChange ℂ).IsTotallyIsotropic
      (eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I)) :=
  isTotallyIsotropic_iff.mpr fun _ hw => apply_eq_zero_of_apply_eq_smul
    (J.baseChange_apply_baseChange hQJ) ((isUnit_iff_ne_zero.mpr (by norm_num)).isSMulRegular _)
    (mem_eigenspace_iff.mp hw)

/-! ## The pairing of the two parts -/

/-- **The pairing of the `(1,0)`- and `(0,1)`-parts.** For a quadratic form `Q` preserved by `J`,
the base-changed polar form pairs `v^(1,0)` with `w^(0,1)` to
`(polar Q v w + i · polar Q v (J w)) / 2`. -/
theorem polar_holomorphicPart_antiholomorphicPart (hQJ : ∀ v, Q (J v) = Q v) (v w : V) :
    polar (Q.baseChange ℂ) (J.holomorphicPart v) (J.antiholomorphicPart w) =
      (2 : ℂ)⁻¹ * (((polar Q v w : ℝ) : ℂ) + Complex.I * ((polar Q v (J w) : ℝ) : ℂ)) := by
  simp only [holomorphicPart_apply, antiholomorphicPart_apply, polar_smul_left, polar_smul_right,
    polar_sub_left, polar_add_right, QuadraticForm.polar_baseChange_tmul,
    J.polar_apply_apply hQJ, J.polar_apply_left_eq_neg_polar_apply_right hQJ, Complex.real_smul,
    smul_eq_mul, mul_one, Complex.ofReal_neg]
  linear_combination -(2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * ((polar Q v w : ℝ) : ℂ) * Complex.I_mul_I

end TauCeti.AlmostComplexStructure
