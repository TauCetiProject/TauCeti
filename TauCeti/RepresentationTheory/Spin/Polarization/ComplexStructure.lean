/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Complexification
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
public import TauCeti.RepresentationTheory.Spin.Polarization.Complement

/-!
# The polarization of a complexified quadratic space by a complex structure

Let `Q` be a quadratic form on a real vector space `V` and `J` an almost complex structure on `V`
preserving `Q`. The complex-linear extension of `J` to `ℂ ⊗[ℝ] V` has the two eigenspaces
`W = ker (J - i)` and `W' = ker (J + i)`, which are complementary
(`TauCeti.AlmostComplexStructure.isCompl_eigenspace_baseChange_I_neg_I`). Both are isotropic for
the base-changed form: if `J w = ± i w` then `Q w = Q (J w) = (± i)² Q w = -Q w`. When `Q` is
nondegenerate and `V` is finite-dimensional, `W` and `W'` therefore polarize `Q.baseChange ℂ`, and
the polar form pairs them perfectly. This is the polarization from which the exterior model `⋀ W`
of the spinor module of an even-dimensional Euclidean space with an orthogonal complex structure is
built; the geometric convention takes `Q (v) = -g (v, v)` for the metric `g`.

A real vector `v` decomposes as `1 ⊗ v = v^(1,0) + v^(0,1)`, with
`v^(1,0) = (v - i J v) / 2 ∈ W` and `v^(0,1) = (v + i J v) / 2 ∈ W'`. The pairing of these parts
is computed from the real polar form:

```text
polar (v^(1,0)) (w^(0,1)) = (polar Q v w + i · polar Q v (J w)) / 2.
```

## Main definitions

* `TauCeti.AlmostComplexStructure.spinPolarizationData`: the polarization of `Q.baseChange ℂ` by
  the `i`- and `-i`-eigenspaces of the complexified complex structure.
* `TauCeti.AlmostComplexStructure.holomorphicPart` and
  `TauCeti.AlmostComplexStructure.antiholomorphicPart`: the components `v^(1,0)` and `v^(0,1)` of
  a real vector.

## Main results

* `TauCeti.AlmostComplexStructure.isTotallyIsotropic_eigenspace_I` and
  `TauCeti.AlmostComplexStructure.isTotallyIsotropic_eigenspace_neg_I`: both eigenspaces are
  totally isotropic.
* `TauCeti.AlmostComplexStructure.holomorphicPart_add_antiholomorphicPart`: the two parts add up
  to the real vector.
* `TauCeti.AlmostComplexStructure.polar_holomorphicPart_antiholomorphicPart`: the pairing of the
  two parts in terms of the real polar form.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Chapter I, for spinor modules of
  even-dimensional Euclidean spaces.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for spinor modules attached to a
  decomposition into complementary totally isotropic subspaces.
-/

public section

open Module.End QuadraticMap
open scoped TensorProduct

namespace TauCeti.AlmostComplexStructure

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (J : AlmostComplexStructure V)
  {Q : QuadraticForm ℝ V}

/-! ## Isotropy of the eigenspaces -/

/-- The complexification of a `Q`-preserving almost complex structure preserves the
base-changed form. -/
private theorem baseChange_apply_baseChange (hQJ : ∀ v, Q (J v) = Q v) (w : ℂ ⊗[ℝ] V) :
    Q.baseChange ℂ (J.toLinearMap.baseChange ℂ w) = Q.baseChange ℂ w := by
  have h := (QuadraticMap.Isometry.baseChange (⟨J.toLinearMap, hQJ⟩ : Q →qᵢ Q) ℂ).map_app w
  rwa [← QuadraticMap.Isometry.coe_toLinearMap,
    QuadraticMap.Isometry.baseChange_toLinearMap] at h

/-- The `i`-eigenspace of the complexification of a `Q`-preserving almost complex structure is
totally isotropic for the base-changed form. -/
theorem isTotallyIsotropic_eigenspace_I (hQJ : ∀ v, Q (J v) = Q v) :
    (Q.baseChange ℂ).IsTotallyIsotropic
      (eigenspace (J.toLinearMap.baseChange ℂ) Complex.I) :=
  isTotallyIsotropic_iff.mpr fun _ hw => apply_eq_zero_of_apply_eq_smul
    (J.baseChange_apply_baseChange hQJ) ((isUnit_iff_ne_zero.mpr (by norm_num)).isSMulRegular _)
    (mem_eigenspace_iff.mp hw)

/-- The `-i`-eigenspace of the complexification of a `Q`-preserving almost complex structure is
totally isotropic for the base-changed form. -/
theorem isTotallyIsotropic_eigenspace_neg_I (hQJ : ∀ v, Q (J v) = Q v) :
    (Q.baseChange ℂ).IsTotallyIsotropic
      (eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I)) :=
  isTotallyIsotropic_iff.mpr fun _ hw => apply_eq_zero_of_apply_eq_smul
    (J.baseChange_apply_baseChange hQJ) ((isUnit_iff_ne_zero.mpr (by norm_num)).isSMulRegular _)
    (mem_eigenspace_iff.mp hw)

/-! ## The polarization -/

/-- **The polarization of a complexified quadratic space by a complex structure.** For a
nondegenerate quadratic form `Q` on a finite-dimensional real vector space and an almost complex
structure `J` preserving `Q`, the `i`- and `-i`-eigenspaces of the complexification of `J` are the
two isotropic summands of a polarization of `Q.baseChange ℂ`, with no orthogonal remainder. Its
pairing field identifies the `-i`-eigenspace with the dual of the `i`-eigenspace through the
polar form. -/
noncomputable def spinPolarizationData [FiniteDimensional ℝ V] (hQJ : ∀ v, Q (J v) = Q v)
    (hQ : Q.Nondegenerate) : SpinPolarizationData (Q.baseChange ℂ) :=
  SpinPolarizationData.ofIsCompl (QuadraticForm.Nondegenerate.baseChange hQ)
    J.isCompl_eigenspace_baseChange_I_neg_I (J.isTotallyIsotropic_eigenspace_I hQJ)
    (J.isTotallyIsotropic_eigenspace_neg_I hQJ)

section Polarization

variable [FiniteDimensional ℝ V] (hQJ : ∀ v, Q (J v) = Q v) (hQ : Q.Nondegenerate)

@[simp]
theorem spinPolarizationData_W :
    (J.spinPolarizationData hQJ hQ).W =
      eigenspace (J.toLinearMap.baseChange ℂ) Complex.I :=
  SpinPolarizationData.ofIsCompl_W ..

@[simp]
theorem spinPolarizationData_W' :
    (J.spinPolarizationData hQJ hQ).W' =
      eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) :=
  SpinPolarizationData.ofIsCompl_W' ..

@[simp]
theorem spinPolarizationData_line : (J.spinPolarizationData hQJ hQ).line = ⊥ :=
  SpinPolarizationData.ofIsCompl_line ..

end Polarization

/-! ## The `(1,0)` and `(0,1)` parts of a real vector -/

/-- The `(1,0)`-part `v^(1,0) = (v - i J v) / 2` of a real vector `v`, the component of `1 ⊗ v`
in the `i`-eigenspace of the complexified complex structure. -/
noncomputable def holomorphicPart : V →ₗ[ℝ] ℂ ⊗[ℝ] V :=
  (2 : ℂ)⁻¹ • ((TensorProduct.mk ℝ ℂ V 1) - Complex.I • (TensorProduct.mk ℝ ℂ V 1 ∘ₗ J.toLinearMap))

/-- The `(0,1)`-part `v^(0,1) = (v + i J v) / 2` of a real vector `v`, the component of `1 ⊗ v`
in the `-i`-eigenspace of the complexified complex structure. -/
noncomputable def antiholomorphicPart : V →ₗ[ℝ] ℂ ⊗[ℝ] V :=
  (2 : ℂ)⁻¹ • ((TensorProduct.mk ℝ ℂ V 1) + Complex.I • (TensorProduct.mk ℝ ℂ V 1 ∘ₗ J.toLinearMap))

theorem holomorphicPart_apply (v : V) :
    J.holomorphicPart v = (2 : ℂ)⁻¹ • ((1 : ℂ) ⊗ₜ v - Complex.I • (1 : ℂ) ⊗ₜ J v) := (rfl)

theorem antiholomorphicPart_apply (v : V) :
    J.antiholomorphicPart v = (2 : ℂ)⁻¹ • ((1 : ℂ) ⊗ₜ v + Complex.I • (1 : ℂ) ⊗ₜ J v) := (rfl)

/-- The `(1,0)`-part of a real vector lies in the `i`-eigenspace of the complexified complex
structure. -/
theorem holomorphicPart_mem_eigenspace_I (v : V) :
    J.holomorphicPart v ∈ eigenspace (J.toLinearMap.baseChange ℂ) Complex.I := by
  rw [mem_eigenspace_iff, holomorphicPart_apply, map_smul, map_sub, map_smul,
    LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, apply_apply, TensorProduct.tmul_neg]
  linear_combination (norm := module) Complex.I_mul_I • ((2 : ℂ)⁻¹ • (1 : ℂ) ⊗ₜ[ℝ] J v)

/-- The `(0,1)`-part of a real vector lies in the `-i`-eigenspace of the complexified complex
structure. -/
theorem antiholomorphicPart_mem_eigenspace_neg_I (v : V) :
    J.antiholomorphicPart v ∈ eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) := by
  rw [mem_eigenspace_iff, antiholomorphicPart_apply, map_smul, map_add, map_smul,
    LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, apply_apply, TensorProduct.tmul_neg]
  linear_combination (norm := module) Complex.I_mul_I • ((2 : ℂ)⁻¹ • (1 : ℂ) ⊗ₜ[ℝ] J v)

/-- A real vector is the sum of its `(1,0)`- and `(0,1)`-parts. -/
@[simp]
theorem holomorphicPart_add_antiholomorphicPart (v : V) :
    J.holomorphicPart v + J.antiholomorphicPart v = (1 : ℂ) ⊗ₜ v := by
  rw [holomorphicPart_apply, antiholomorphicPart_apply]
  module

/-- The `(1,0)`-part of `J v` is `i` times the `(1,0)`-part of `v`. -/
@[simp]
theorem holomorphicPart_apply_apply (v : V) :
    J.holomorphicPart (J v) = Complex.I • J.holomorphicPart v := by
  rw [holomorphicPart_apply, holomorphicPart_apply, apply_apply, TensorProduct.tmul_neg]
  linear_combination (norm := module) Complex.I_mul_I • ((2 : ℂ)⁻¹ • (1 : ℂ) ⊗ₜ[ℝ] J v)

/-- The `(0,1)`-part of `J v` is `-i` times the `(0,1)`-part of `v`. -/
@[simp]
theorem antiholomorphicPart_apply_apply (v : V) :
    J.antiholomorphicPart (J v) = -Complex.I • J.antiholomorphicPart v := by
  rw [antiholomorphicPart_apply, antiholomorphicPart_apply, apply_apply, TensorProduct.tmul_neg]
  linear_combination (norm := module) Complex.I_mul_I • ((2 : ℂ)⁻¹ • (1 : ℂ) ⊗ₜ[ℝ] J v)

/-! ## The pairing of the two parts -/

/-- The polar form of a `J`-preserved quadratic form is antisymmetric under moving `J` across:
`polar Q (J v) w = -polar Q v (J w)`. -/
private theorem polar_apply_left (hQJ : ∀ v, Q (J v) = Q v) (v w : V) :
    polar Q (J v) w = -polar Q v (J w) := by
  have h : polar Q (J v) (J (J w)) = polar Q v (J w) :=
    (⟨J.toLinearMap, hQJ⟩ : Q →qᵢ Q).polar_apply v (J w)
  rw [apply_apply, polar_neg_right] at h
  linear_combination -h

/-- **The pairing of the `(1,0)`- and `(0,1)`-parts.** For a quadratic form `Q` preserved by `J`,
the base-changed polar form pairs `v^(1,0)` with `w^(0,1)` to
`(polar Q v w + i · polar Q v (J w)) / 2`. -/
theorem polar_holomorphicPart_antiholomorphicPart (hQJ : ∀ v, Q (J v) = Q v) (v w : V) :
    polar (Q.baseChange ℂ) (J.holomorphicPart v) (J.antiholomorphicPart w) =
      (2 : ℂ)⁻¹ * (((polar Q v w : ℝ) : ℂ) + Complex.I * ((polar Q v (J w) : ℝ) : ℂ)) := by
  have hJJ : polar Q (J v) (J w) = polar Q v w :=
    (⟨J.toLinearMap, hQJ⟩ : Q →qᵢ Q).polar_apply v w
  rw [holomorphicPart_apply, antiholomorphicPart_apply, polar_smul_left, polar_smul_right,
    polar_sub_left, polar_add_right, polar_add_right, polar_smul_left, polar_smul_right,
    polar_smul_left, polar_smul_right, QuadraticForm.polar_baseChange_tmul,
    QuadraticForm.polar_baseChange_tmul, QuadraticForm.polar_baseChange_tmul,
    QuadraticForm.polar_baseChange_tmul, hJJ, J.polar_apply_left hQJ]
  simp only [mul_one, Complex.real_smul, smul_eq_mul, Complex.ofReal_neg]
  linear_combination -(2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * ((polar Q v w : ℝ) : ℂ) * Complex.I_mul_I

end TauCeti.AlmostComplexStructure
