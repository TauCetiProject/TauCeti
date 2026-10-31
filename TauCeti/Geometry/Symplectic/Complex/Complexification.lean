/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.Complex.Conjugation
public import TauCeti.LinearAlgebra.Complex.Eigenspace
public import TauCeti.LinearAlgebra.Eigenspace.TensorProduct

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

A real bilinear map `B : V → V → V` anti-commuting with `J` in each argument, such as the
Nijenhuis tensor of an almost complex structure on a manifold, has a complex-bilinear extension
`LinearMap.BilinMap.baseChange ℂ B`. It anti-commutes with the complexified complex structure in
each argument, so it maps eigenvectors for `±i` in either argument into the eigenspace for `∓i`.
Hence it sends two vectors of type `(0,1)` to a vector of type `(1,0)`, two vectors of type
`(1,0)` to a vector of type `(0,1)`, and vanishes on a vector of type `(1,0)` and one of type
`(0,1)`.

A real-linear map `l : V → N` into a complex vector space extends complex-linearly to the
complexification by `LinearMap.liftBaseChange`. It is complex-linear for `J` exactly when its
extension vanishes on the vectors of type `(0,1)`, and conjugate-linear exactly when its extension
vanishes on the vectors of type `(1,0)`.

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
* `TauCeti.AlmostComplexStructure.bilinMap_baseChange_baseChange_left` and
  `TauCeti.AlmostComplexStructure.bilinMap_baseChange_baseChange_right`: the complex-bilinear
  extension of a bilinear map anti-commuting with `J` anti-commutes with the complexified `J`.
* `TauCeti.AlmostComplexStructure.bilinMap_baseChange_mem_eigenspace_neg_of_mem_left` and
  `TauCeti.AlmostComplexStructure.bilinMap_baseChange_mem_eigenspace_neg_of_mem_right`: the
  complex-bilinear extension of a bilinear map anti-commuting with `J` maps eigenvectors for `μ`
  in either argument into the eigenspace for `-μ`.
* `TauCeti.AlmostComplexStructure.bilinMap_baseChange_eq_zero_of_mem_eigenspace_I_of_mem_neg_I`:
  it vanishes on a vector of type `(1,0)` and one of type `(0,1)`.
* `TauCeti.AlmostComplexStructure.bilinMap_baseChange_antiholomorphicPart_antiholomorphicPart`
  and `TauCeti.AlmostComplexStructure.bilinMap_baseChange_holomorphicPart_holomorphicPart`:
  `B(v^(0,1), w^(0,1)) = (B v w)^(1,0)` and `B(v^(1,0), w^(1,0)) = (B v w)^(0,1)`.
* `TauCeti.AlmostComplexStructure.eigenspace_neg_I_le_ker_liftBaseChange_iff` and
  `TauCeti.AlmostComplexStructure.eigenspace_I_le_ker_liftBaseChange_iff`: complex-linear and
  conjugate-linear maps through their complex-linear extensions.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The complex-linear extension of an almost complex structure squares to minus the identity. -/
theorem baseChange_comp_self (J : AlmostComplexStructure V) :
    (J.toLinearMap.baseChange ℂ).comp (J.toLinearMap.baseChange ℂ) = -LinearMap.id := by
  simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_neg, LinearMap.baseChange_id]
    using congrArg (LinearMap.baseChange ℂ) J.square_neg

/-- The `i`- and `-i`-eigenspaces of the complexification of an almost complex structure are
complementary. -/
theorem isCompl_eigenspace_baseChange_I_neg_I (J : AlmostComplexStructure V) :
    IsCompl (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) Complex.I)
      (Module.End.eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I)) :=
  Module.End.isCompl_eigenspace_I_neg_I_of_sq_eq_neg_id _ J.baseChange_comp_self

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
  simp [holomorphicPart_apply, antiholomorphicPart_apply, Complex.conj_I, map_ofNat]

/-- Conjugation of the complexification maps the `(0,1)`-part of a real vector to its
`(1,0)`-part. -/
@[simp]
theorem tmulConj_antiholomorphicPart (v : V) :
    tmulConj V (J.antiholomorphicPart v) = J.holomorphicPart v := by
  rw [← tmulConj_holomorphicPart, tmulConj_tmulConj]

/-! ## Bilinear maps anti-commuting with the complex structure

A real bilinear map `B : V → V → V` with `B (J v) w = -J (B v w)` and `B v (J w) = -J (B v w)`,
such as the Nijenhuis tensor of an almost complex structure, has a complex-bilinear extension to
the complexification that sends two vectors of type `(0,1)` to a vector of type `(1,0)`, two
vectors of type `(1,0)` to a vector of type `(0,1)`, and vanishes on a vector of type `(1,0)` and
one of type `(0,1)`. Here a vector of type `(1,0)` or `(0,1)` is one in the `i`- or
`-i`-eigenspace of the complexified complex structure. -/

section AntiCommuting

open LinearMap (BilinMap)
open Module.End

variable {B : BilinMap ℝ V V}

/-- The complex-bilinear extension of a bilinear map anti-commuting with `J` in its first argument
anti-commutes with the complexified complex structure in its first argument. -/
theorem bilinMap_baseChange_baseChange_left (hl : ∀ v w, B (J v) w = -J (B v w))
    (X Y : ℂ ⊗[ℝ] V) :
    BilinMap.baseChange ℂ B (J.toLinearMap.baseChange ℂ X) Y =
      -J.toLinearMap.baseChange ℂ (BilinMap.baseChange ℂ B X Y) := by
  induction X using TensorProduct.inductionOn with
  | add X X' hX hX' => simp [hX, hX', add_comm]
  | tmul a v =>
    induction Y using TensorProduct.inductionOn with
    | add Y Y' hY hY' => simp only [map_add, hY, hY', neg_add]
    | tmul b w => simp [hl, TensorProduct.tmul_neg]

/-- The complex-bilinear extension of a bilinear map anti-commuting with `J` in its second
argument anti-commutes with the complexified complex structure in its second argument. -/
theorem bilinMap_baseChange_baseChange_right (hr : ∀ v w, B v (J w) = -J (B v w))
    (X Y : ℂ ⊗[ℝ] V) :
    BilinMap.baseChange ℂ B X (J.toLinearMap.baseChange ℂ Y) =
      -J.toLinearMap.baseChange ℂ (BilinMap.baseChange ℂ B X Y) := by
  induction X using TensorProduct.inductionOn with
  | add X X' hX hX' => simp [hX, hX', add_comm]
  | tmul a v =>
    induction Y using TensorProduct.inductionOn with
    | add Y Y' hY hY' => simp only [map_add, hY, hY', neg_add]
    | tmul b w => simp [hr, TensorProduct.tmul_neg]

/-- If a bilinear map anti-commutes with `J` in its first argument, its complex-bilinear extension
maps an eigenvector of the complexified complex structure for the eigenvalue `μ` in its first
argument into the eigenspace for `-μ`. -/
theorem bilinMap_baseChange_mem_eigenspace_neg_of_mem_left (hl : ∀ v w, B (J v) w = -J (B v w))
    {μ : ℂ} {X : ℂ ⊗[ℝ] V} (hX : X ∈ eigenspace (J.toLinearMap.baseChange ℂ) μ)
    (Y : ℂ ⊗[ℝ] V) :
    BilinMap.baseChange ℂ B X Y ∈ eigenspace (J.toLinearMap.baseChange ℂ) (-μ) := by
  rw [mem_eigenspace_iff] at hX ⊢
  rw [neg_smul, ← LinearMap.smul_apply, ← map_smul, ← hX,
    J.bilinMap_baseChange_baseChange_left hl, neg_neg]

/-- If a bilinear map anti-commutes with `J` in its second argument, its complex-bilinear extension
maps an eigenvector of the complexified complex structure for the eigenvalue `μ` in its second
argument into the eigenspace for `-μ`. -/
theorem bilinMap_baseChange_mem_eigenspace_neg_of_mem_right (hr : ∀ v w, B v (J w) = -J (B v w))
    (X : ℂ ⊗[ℝ] V) {μ : ℂ} {Y : ℂ ⊗[ℝ] V} (hY : Y ∈ eigenspace (J.toLinearMap.baseChange ℂ) μ) :
    BilinMap.baseChange ℂ B X Y ∈ eigenspace (J.toLinearMap.baseChange ℂ) (-μ) := by
  rw [mem_eigenspace_iff] at hY ⊢
  rw [neg_smul, ← map_smul, ← hY, J.bilinMap_baseChange_baseChange_right hr, neg_neg]

/-- The complex-bilinear extension of a bilinear map anti-commuting with `J` in each argument
vanishes on a vector of type `(1,0)` and a vector of type `(0,1)`. -/
theorem bilinMap_baseChange_eq_zero_of_mem_eigenspace_I_of_mem_neg_I
    (hl : ∀ v w, B (J v) w = -J (B v w)) (hr : ∀ v w, B v (J w) = -J (B v w)) {X Y : ℂ ⊗[ℝ] V}
    (hX : X ∈ eigenspace (J.toLinearMap.baseChange ℂ) Complex.I)
    (hY : Y ∈ eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I)) :
    BilinMap.baseChange ℂ B X Y = 0 :=
  Submodule.disjoint_def.1 J.isCompl_eigenspace_baseChange_I_neg_I.disjoint _
    (by simpa using J.bilinMap_baseChange_mem_eigenspace_neg_of_mem_right hr X hY)
    (J.bilinMap_baseChange_mem_eigenspace_neg_of_mem_left hl hX Y)

/-- The complex-bilinear extension of a bilinear map anti-commuting with `J` in each argument
vanishes on a vector of type `(0,1)` and a vector of type `(1,0)`. -/
theorem bilinMap_baseChange_eq_zero_of_mem_eigenspace_neg_I_of_mem_I
    (hl : ∀ v w, B (J v) w = -J (B v w)) (hr : ∀ v w, B v (J w) = -J (B v w)) {X Y : ℂ ⊗[ℝ] V}
    (hX : X ∈ eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I))
    (hY : Y ∈ eigenspace (J.toLinearMap.baseChange ℂ) Complex.I) :
    BilinMap.baseChange ℂ B X Y = 0 :=
  Submodule.disjoint_def.1 J.isCompl_eigenspace_baseChange_I_neg_I.disjoint _
    (by simpa using J.bilinMap_baseChange_mem_eigenspace_neg_of_mem_left hl hX Y)
    (J.bilinMap_baseChange_mem_eigenspace_neg_of_mem_right hr X hY)

/-- The complex-bilinear extension of a bilinear map anti-commuting with `J` in each argument
vanishes on the `(1,0)`-part of `v` and the `(0,1)`-part of `w`. -/
theorem bilinMap_baseChange_holomorphicPart_antiholomorphicPart
    (hl : ∀ v w, B (J v) w = -J (B v w)) (hr : ∀ v w, B v (J w) = -J (B v w)) (v w : V) :
    BilinMap.baseChange ℂ B (J.holomorphicPart v) (J.antiholomorphicPart w) = 0 :=
  J.bilinMap_baseChange_eq_zero_of_mem_eigenspace_I_of_mem_neg_I hl hr
    (J.holomorphicPart_mem_eigenspace_baseChange_I v)
    (J.antiholomorphicPart_mem_eigenspace_baseChange_neg_I w)

/-- The complex-bilinear extension of a bilinear map anti-commuting with `J` in each argument
vanishes on the `(0,1)`-part of `v` and the `(1,0)`-part of `w`. -/
theorem bilinMap_baseChange_antiholomorphicPart_holomorphicPart
    (hl : ∀ v w, B (J v) w = -J (B v w)) (hr : ∀ v w, B v (J w) = -J (B v w)) (v w : V) :
    BilinMap.baseChange ℂ B (J.antiholomorphicPart v) (J.holomorphicPart w) = 0 :=
  J.bilinMap_baseChange_eq_zero_of_mem_eigenspace_neg_I_of_mem_I hl hr
    (J.antiholomorphicPart_mem_eigenspace_baseChange_neg_I v)
    (J.holomorphicPart_mem_eigenspace_baseChange_I w)

/-- The complex-bilinear extension of a bilinear map anti-commuting with `J` in each argument
maps the `(0,1)`-parts of `v` and `w` to the `(1,0)`-part of `B v w`. -/
theorem bilinMap_baseChange_antiholomorphicPart_antiholomorphicPart
    (hl : ∀ v w, B (J v) w = -J (B v w)) (hr : ∀ v w, B v (J w) = -J (B v w)) (v w : V) :
    BilinMap.baseChange ℂ B (J.antiholomorphicPart v) (J.antiholomorphicPart w) =
      J.holomorphicPart (B v w) := by
  simp only [antiholomorphicPart_apply, holomorphicPart_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, BilinMap.baseChange_tmul, mul_one, hl, hr,
    map_neg, apply_apply, neg_neg, TensorProduct.tmul_neg]
  linear_combination (norm := module) Complex.I_mul_I • (-(4 : ℂ)⁻¹ • (1 : ℂ) ⊗ₜ[ℝ] B v w)

/-- The complex-bilinear extension of a bilinear map anti-commuting with `J` in each argument
maps the `(1,0)`-parts of `v` and `w` to the `(0,1)`-part of `B v w`. -/
theorem bilinMap_baseChange_holomorphicPart_holomorphicPart
    (hl : ∀ v w, B (J v) w = -J (B v w)) (hr : ∀ v w, B v (J w) = -J (B v w)) (v w : V) :
    BilinMap.baseChange ℂ B (J.holomorphicPart v) (J.holomorphicPart w) =
      J.antiholomorphicPart (B v w) := by
  simp only [antiholomorphicPart_apply, holomorphicPart_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, BilinMap.baseChange_tmul, mul_one, hl, hr,
    map_neg, apply_apply, neg_neg, TensorProduct.tmul_neg]
  linear_combination (norm := module) Complex.I_mul_I • (-(4 : ℂ)⁻¹ • (1 : ℂ) ⊗ₜ[ℝ] B v w)

end AntiCommuting

/-! ## Complex-linear extensions of real-linear maps

A real-linear map `l : V → N` into a complex vector space extends complex-linearly to the
complexification by `LinearMap.liftBaseChange`. The map `l` is complex-linear for `J`,
`l (J v) = i • l v`, exactly when its extension vanishes on the vectors of type `(0,1)`, and
conjugate-linear, `l (J v) = -i • l v`, exactly when it vanishes on the vectors of type `(1,0)`. -/

section LiftBaseChange

open Module.End

variable {N : Type*} [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
  (l : V →ₗ[ℝ] N)

/-- The complex-linear extension of `l` on the `(1,0)`-part of `v` is `(l v - i • l (J v)) / 2`. -/
@[simp]
theorem liftBaseChange_holomorphicPart (v : V) :
    l.liftBaseChange ℂ (J.holomorphicPart v) = (2 : ℂ)⁻¹ • (l v - Complex.I • l (J v)) := by
  simp [holomorphicPart_apply]

/-- The complex-linear extension of `l` on the `(0,1)`-part of `v` is `(l v + i • l (J v)) / 2`. -/
@[simp]
theorem liftBaseChange_antiholomorphicPart (v : V) :
    l.liftBaseChange ℂ (J.antiholomorphicPart v) = (2 : ℂ)⁻¹ • (l v + Complex.I • l (J v)) := by
  simp [antiholomorphicPart_apply]

/-- A real-linear map is complex-linear for `J` exactly when its complex-linear extension vanishes
on the vectors of type `(0,1)`. -/
theorem eigenspace_neg_I_le_ker_liftBaseChange_iff :
    eigenspace (J.toLinearMap.baseChange ℂ) (-Complex.I) ≤ LinearMap.ker (l.liftBaseChange ℂ) ↔
      ∀ v, l (J v) = Complex.I • l v := by
  refine ⟨fun h v ↦ ?_, fun hl X hX ↦ l.liftBaseChange_eq_zero_of_mem_eigenspace_baseChange
    J.toLinearMap hl (by norm_num [Complex.ext_iff]) hX⟩
  have hv := h (J.antiholomorphicPart_mem_eigenspace_baseChange_neg_I v)
  rw [LinearMap.mem_ker, liftBaseChange_antiholomorphicPart, smul_eq_zero] at hv
  have hv' := congrArg (Complex.I • ·) (eq_neg_of_add_eq_zero_right (hv.resolve_left (by simp)))
  simpa [smul_smul] using hv'

/-- A real-linear map is conjugate-linear for `J` exactly when its complex-linear extension
vanishes on the vectors of type `(1,0)`. -/
theorem eigenspace_I_le_ker_liftBaseChange_iff :
    eigenspace (J.toLinearMap.baseChange ℂ) Complex.I ≤ LinearMap.ker (l.liftBaseChange ℂ) ↔
      ∀ v, l (J v) = -Complex.I • l v := by
  refine ⟨fun h v ↦ ?_, fun hl X hX ↦ l.liftBaseChange_eq_zero_of_mem_eigenspace_baseChange
    J.toLinearMap hl (by norm_num [Complex.ext_iff]) hX⟩
  have hv := h (J.holomorphicPart_mem_eigenspace_baseChange_I v)
  rw [LinearMap.mem_ker, liftBaseChange_holomorphicPart, smul_eq_zero] at hv
  have hv' := congrArg (Complex.I • ·) (sub_eq_zero.1 (hv.resolve_left (by simp)))
  rw [neg_smul]
  exact neg_eq_iff_eq_neg.1 (by simpa [smul_smul] using hv'.symm)

end LiftBaseChange

end TauCeti.AlmostComplexStructure
