/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.Complex.Conjugation
public import TauCeti.LinearAlgebra.Complex.Eigenspace

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Complexification of almost complex structures

An almost complex structure on a real vector space extends complex-linearly to its
complexification. Its square remains `-1`, and its `i`- and `-i`-eigenspaces are complementary.
These complementary eigenspaces supply the two pieces used to construct a weight-one Hodge
structure from the real almost complex structure. A real vector `v` decomposes as
`1 ⊗ v = v^(1,0) + v^(0,1)`, with `v^(1,0) = (v - i J v) / 2` in the `i`-eigenspace and
`v^(0,1) = (v + i J v) / 2` in the `-i`-eigenspace.

## Main declarations

* `TauCeti.AlmostComplexStructure.isCompl_eigenspace_baseChange_I_neg_I`: its `i`- and
  `-i`-eigenspaces are complementary.
* `TauCeti.AlmostComplexStructure.holomorphicPart` and
  `TauCeti.AlmostComplexStructure.antiholomorphicPart`: the components `v^(1,0)` and `v^(0,1)` of
  a real vector, with `TauCeti.AlmostComplexStructure.holomorphicPart_mem_eigenspace_baseChange_I`,
  `TauCeti.AlmostComplexStructure.antiholomorphicPart_mem_eigenspace_baseChange_neg_I` and
  `TauCeti.AlmostComplexStructure.holomorphicPart_add_antiholomorphicPart`.
* `TauCeti.AlmostComplexStructure.baseChange_holomorphicPart` and
  `TauCeti.AlmostComplexStructure.baseChange_antiholomorphicPart`: the complexified complex
  structure commutes with taking the `(1,0)`- and `(0,1)`-parts.
* `TauCeti.AlmostComplexStructure.tmulConj_holomorphicPart` and
  `TauCeti.AlmostComplexStructure.tmulConj_antiholomorphicPart`: conjugation of the
  complexification exchanges the `(1,0)`- and `(0,1)`-parts.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The `i`- and `-i`-eigenspaces of the complexification of an almost complex structure are
complementary. -/
theorem isCompl_eigenspace_baseChange_I_neg_I (J : AlmostComplexStructure V) :
    IsCompl (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I)
      (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I)) := by
  apply Module.End.isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id
  have h := congrArg (LinearMap.baseChange ℂ) J.square_neg
  simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_neg,
    LinearMap.baseChange_id] using h

/-! ## The `(1,0)` and `(0,1)` parts of a real vector -/

variable (J : AlmostComplexStructure V)

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

/-- The complexified complex structure maps the `(1,0)`-part of `v` to the `(1,0)`-part of
`J v`. -/
@[simp]
theorem baseChange_holomorphicPart (v : V) :
    J.toLinearMap.baseChange ℂ (J.holomorphicPart v) = J.holomorphicPart (J v) := by
  rw [holomorphicPart_apply, holomorphicPart_apply, map_smul, map_sub, map_smul,
    LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]

/-- The complexified complex structure maps the `(0,1)`-part of `v` to the `(0,1)`-part of
`J v`. -/
@[simp]
theorem baseChange_antiholomorphicPart (v : V) :
    J.toLinearMap.baseChange ℂ (J.antiholomorphicPart v) = J.antiholomorphicPart (J v) := by
  rw [antiholomorphicPart_apply, antiholomorphicPart_apply, map_smul, map_add, map_smul,
    LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]

/-- The `(1,0)`-part of a real vector lies in the `i`-eigenspace of the complexified complex
structure. -/
theorem holomorphicPart_mem_eigenspace_baseChange_I (v : V) :
    J.holomorphicPart v ∈ Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I := by
  rw [Module.End.mem_eigenspace_iff, baseChange_holomorphicPart, holomorphicPart_apply_apply]

/-- The `(0,1)`-part of a real vector lies in the `-i`-eigenspace of the complexified complex
structure. -/
theorem antiholomorphicPart_mem_eigenspace_baseChange_neg_I (v : V) :
    J.antiholomorphicPart v ∈ Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) := by
  rw [Module.End.mem_eigenspace_iff, baseChange_antiholomorphicPart,
    antiholomorphicPart_apply_apply]

/-! ## Conjugation of the `(1,0)` and `(0,1)` parts -/

/-- Conjugation of the complexification maps the `(1,0)`-part of a real vector to its
`(0,1)`-part. -/
@[simp]
theorem tmulConj_holomorphicPart (v : V) :
    tmulConj V (J.holomorphicPart v) = J.antiholomorphicPart v := by
  rw [holomorphicPart_apply, antiholomorphicPart_apply, map_smulₛₗ, map_sub, map_smulₛₗ,
    tmulConj_tmul, tmulConj_tmul, map_one, map_inv₀, map_ofNat, Complex.conj_I]
  module

/-- Conjugation of the complexification maps the `(0,1)`-part of a real vector to its
`(1,0)`-part. -/
@[simp]
theorem tmulConj_antiholomorphicPart (v : V) :
    tmulConj V (J.antiholomorphicPart v) = J.holomorphicPart v := by
  rw [← tmulConj_holomorphicPart, tmulConj_tmulConj]

end TauCeti.AlmostComplexStructure
